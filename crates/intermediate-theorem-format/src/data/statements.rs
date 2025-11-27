use crate::{ConstantValue, Expression, TempId, TheoremFunctionID, TheoremStructID, TheoremType};
use std::mem;

/// Structured statement (high-level control flow)
///
/// NOTE: If and While are now expressions (Expression::IfExpr, Expression::WhileExpr).
/// Statement-level control flow only exists for side-effect-only branches (rare).
#[derive(Debug, Clone)]
pub enum Statement {
    /// Sequence of statements
    Sequence(Vec<Statement>),

    /// Assignment: let var := expr (or let (var1, var2, ...) := expr for tuples)
    /// This is the primary way to bind values, including if/while expressions:
    ///   let (x, y) := if cond then (a, b) else (c, d)
    ///   let (x, y) := while cond { ... } with initial (a, b)
    Let {
        results: Vec<TempId>,
        operation: Expression,
        result_types: Vec<TheoremType>,
    },

    /// Return from function
    Return { values: Vec<Expression> },

    /// Abort execution
    Abort { code: Expression },

    /// Update a struct field (functional update via with-expression)
    /// Translates WriteRef to a field borrow: *(&mut struct.field) = value
    /// Generates: let struct := { struct with field := value }
    UpdateField {
        target: Expression,
        struct_id: TheoremStructID,
        field_index: usize,
        new_value: Expression,
    },

    /// Update a vector element (functional update)
    /// Translates WriteRef to a vector element borrow: *(vector::borrow_mut(&mut vec, i)) = value
    /// Generates: let vec := vec.set i value
    UpdateVectorElement {
        target: Expression,
        index: Expression,
        new_value: Expression,
    },

    /// Requires (precondition assertion)
    Requires { condition: Expression },

    /// Ensures (postcondition assertion)
    Ensures { condition: Expression },
}

impl Default for Statement {
    fn default() -> Self {
        Statement::Sequence(Vec::new())
    }
}

/// Traverse expressions in a statement.
/// Takes a ref pattern (`(ref)` or `(ref mut)`), a statement recurse action, and an expression action.
macro_rules! traverse_stmt_expression {
    ($target:expr, ($($ref_pattern:tt)*), $stmt_recurse:expr, $expr_action:expr) => {
        match $target {
            // First handle Sequence to recurse into child statements
            Statement::Sequence($($ref_pattern)* statements) => {
                for stmt in statements {
                    $stmt_recurse(stmt);
                }
            }
            // Then extract expressions from each statement variant
            Statement::Let { $($ref_pattern)* operation, .. } => $expr_action(operation),
            Statement::Return { $($ref_pattern)* values } => {
                for expr in values {
                    $expr_action(expr);
                }
            }
            Statement::Abort { $($ref_pattern)* code } => $expr_action(code),
            Statement::UpdateField { $($ref_pattern)* target, $($ref_pattern)* new_value, .. } => {
                $expr_action(target);
                $expr_action(new_value);
            }
            Statement::UpdateVectorElement { $($ref_pattern)* target, $($ref_pattern)* index, $($ref_pattern)* new_value } => {
                $expr_action(target);
                $expr_action(index);
                $expr_action(new_value);
            }
            Statement::Requires { $($ref_pattern)* condition } | Statement::Ensures { $($ref_pattern)* condition } => $expr_action(condition),
        }
    };
}

impl Statement {
    /// Mutably traverse the statement tree
    pub fn traverse_mut<F: Fn(&mut Statement)>(&mut self, f: F) {
        if let Statement::Sequence(statements) = self {
            for stmt in statements {
                stmt.traverse_mut(&f);
            }
        }
        f(self);
    }

    /// Map over the statement tree, transforming each statement (consuming)
    /// Applies f to children first (post-order), then to self.
    pub fn map<F: Fn(Statement) -> Statement + Copy>(mut self, f: F) -> Statement {
        if let Statement::Sequence(statements) = &mut self {
            *statements = mem::take(statements).into_iter().map(|s| s.map(f)).collect();
        }
        f(self)
    }

    /// Mutably traverse all expressions in the statement tree (recursively into expression children)
    pub fn traverse_expressions_mut<F: Fn(&mut Expression)>(&mut self, f: &F) {
        traverse_stmt_expression!(
            self,
            (ref mut),
            |s: &mut Statement| s.traverse_expressions_mut(f),
            |expr: &mut Expression| expr.traverse_mut(f)
        );
    }

    /// Map over the statement tree, transforming each expression (consuming, recursively into expression children)
    pub fn map_expressions<F: Fn(Expression) -> Expression + Copy>(mut self, f: F) -> Statement {
        traverse_stmt_expression!(
            &mut self,
            (ref mut),
            |s: &mut Statement| { *s = mem::take(s).map_expressions(f); },
            |expr: &mut Expression| {
                *expr = mem::replace(expr, Expression::Constant(ConstantValue::Bool(false))).map(f);
            }
        );
        self
    }

    /// Iterate over all statements in the tree (depth-first)
    pub fn iter(&self) -> StatementIter<'_> {
        StatementIter {
            stack: vec![self]
        }
    }

    /// Iterate over direct expressions in the statement tree (one per statement slot).
    /// Does NOT recurse into expression children - use `iter_all_expressions` for that.
    pub fn iter_expressions(&self) -> StatementExpressionIter<'_> {
        StatementExpressionIter {
            stmt_iter: self.iter(),
            expressions: Vec::new(),
        }
    }

    /// Iterate over ALL expressions in the statement tree (recursively into Expression children and blocks)
    pub fn iter_all_expressions(&self) -> impl Iterator<Item = &Expression> {
        self.iter_expressions().flat_map(|expr| expr.iter())
    }

    /// Get all function calls (recursively including nested blocks)
    pub fn calls(&self) -> impl Iterator<Item = TheoremFunctionID> + '_ {
        self.iter_all_expressions().filter_map(|expr| expr.called_function())
    }

    /// Check if this statement contains any monadic operations
    pub fn is_monadic(&self) -> bool {
        // Abort statements are inherently monadic
        if matches!(self, Statement::Abort { .. }) {
            return true;
        }
        // Check if any expression is monadic
        self.iter_all_expressions().any(|expr| expr.is_monadic())
    }

    /// Check if this statement terminates (all execution paths lead to Return or Abort)
    pub fn terminates(&self) -> bool {
        match self {
            // These statements always terminate
            Statement::Return { .. } | Statement::Abort { .. } => true,
            // Sequence terminates if any statement in it terminates
            // (because once we hit a terminator, the rest is unreachable)
            Statement::Sequence(stmts) => stmts.iter().any(|s| s.terminates()),
            // Let with IfExpr: terminates if both branches terminate
            Statement::Let { operation: Expression::IfExpr { then_block, else_block, .. }, .. } => {
                then_block.terminates() && else_block.terminates()
            }
            // All other statements don't terminate
            _ => false,
        }
    }

    /// Collect all function call IDs from expressions in this statement (recursively)
    pub fn collect_function_calls(&self) -> Vec<TheoremFunctionID> {
        self.calls().collect()
    }

    /// Collect all struct IDs from pack/unpack expressions in this statement
    pub fn collect_struct_references(&self) -> Vec<TheoremStructID> {
        self.iter_all_expressions()
            .filter_map(|expr| expr.struct_reference())
            .collect()
    }

    /// Collect all struct IDs from types in expressions in this statement
    pub fn collect_type_struct_ids(&self) -> Vec<TheoremStructID> {
        self.iter_all_expressions()
            .flat_map(Expression::collect_type_struct_ids)
            .collect()
    }

    pub fn combine(self, other: Statement) -> Statement {
        match (self, other) {
            (Statement::Sequence(mut first), Statement::Sequence(second)) => {
                first.extend(second);
                Statement::Sequence(first)
            }
            (Statement::Sequence(mut first), second) => {
                first.push(second);
                Statement::Sequence(first)
            }
            (first, Statement::Sequence(mut second)) => {
                second.insert(0, first);
                Statement::Sequence(second)
            }
            (first, second) => Statement::Sequence(vec![first, second]),
        }
        .collapse()
    }

    pub fn collapse(mut self) -> Statement {
        if let Statement::Sequence(inner) = &mut self {
            if inner.len() == 1 {
                return inner.pop().unwrap();
            }
        }
        self
    }
}

pub struct StatementIter<'a> {
    stack: Vec<&'a Statement>,
}

impl<'a> Iterator for StatementIter<'a> {
    type Item = &'a Statement;

    fn next(&mut self) -> Option<Self::Item> {
        let statement = self.stack.pop()?;

        if let Statement::Sequence(statements) = statement {
            for stmt in statements {
                self.stack.push(stmt);
            }
        }

        Some(statement)
    }
}

/// Iterator over direct expressions in statements (does not recurse into Expression children).
/// Use with `flat_map(|e| e.iter())` to get all expressions recursively.
pub struct StatementExpressionIter<'a> {
    stmt_iter: StatementIter<'a>,
    expressions: Vec<&'a Expression>,
}

impl<'a> Iterator for StatementExpressionIter<'a> {
    type Item = &'a Expression;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Return queued expressions first
            if let Some(expression) = self.expressions.pop() {
                return Some(expression);
            }

            // Get next statement and extract its immediate expressions
            let stmt = self.stmt_iter.next()?;
            let exprs = &mut self.expressions;
            traverse_stmt_expression!(
                stmt,
                (ref),
                |_: &Statement| {},
                |e| exprs.push(e)
            );
        }
    }
}