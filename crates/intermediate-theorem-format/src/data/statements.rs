use crate::{CallConvention, ConstantValue, Expression, TempId, TheoremFunctionID, TheoremStructID, TheoremType};
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

/// Traverse child statements (only Sequence has children now)
#[macro_export]
macro_rules! traverse_statement {
    ($target:expr, ($($mutability:tt)*), $action:expr) => {
        match $target {
            Statement::Sequence(statements) => {
                for statement in statements {
                    $action(statement);
                }
            }
            _ => {}
        }
    };
}

/// Traverse expressions in a statement (including nested in Let operations)
macro_rules! traverse_expression {
    ($target:expr, ($($ref_pattern:tt)*), ($($mutability:tt)*), $recurse:expr, $action:expr) => {
        // First: Recurse to child statements
        traverse_statement!($target, ($($mutability)*), $recurse);

        // Second: Extract expressions from current statement
        match $target {
            Statement::Let { $($ref_pattern)* operation, .. } => $action(operation),
            Statement::Return { $($ref_pattern)* values } => {
                for expr in values {
                    $action(expr);
                }
            }
            Statement::Abort { $($ref_pattern)* code } => $action(code),
            Statement::UpdateField { $($ref_pattern)* target, $($ref_pattern)* new_value, .. } => {
                $action(target);
                $action(new_value);
            }
            Statement::UpdateVectorElement { $($ref_pattern)* target, $($ref_pattern)* index, $($ref_pattern)* new_value } => {
                $action(target);
                $action(index);
                $action(new_value);
            }
            Statement::Requires { $($ref_pattern)* condition } | Statement::Ensures { $($ref_pattern)* condition } => $action(condition),
            _ => {}
        }
    };
}

impl Statement {
    /// Mutably traverse the statement tree
    pub fn traverse_mut<F: Fn(&mut Statement)>(&mut self, f: F) {
        traverse_statement!(self, (&mut), |child: &mut Statement| child.traverse_mut(&f));
        f(self);
    }

    /// Map over the statement tree, transforming each statement (consuming)
    /// Applies f to children first (post-order), then to self.
    pub fn map<F: Fn(Statement) -> Statement + Copy>(mut self, f: F) -> Statement {
        traverse_statement!(&mut self, (&mut), |child: &mut Statement| *child = mem::take(child).map(f));
        f(self)
    }

    /// Mutably traverse the expressions in the statement tree
    pub fn traverse_expressions_mut<F: Fn(&mut Expression)>(&mut self, f: F) {
        traverse_expression!(self, (ref mut), (&mut), |s: &mut Statement| s.traverse_expressions_mut(&f), |expr: &mut Expression| f(expr));
    }
    
    /// Map over the statement tree, transforming each expression (consuming)
    pub fn map_expressions<F: Fn(Expression) -> Expression + Copy>(mut self, f: F) -> Statement {
        traverse_expression!(&mut self, (ref mut), (&mut), |s: &mut Statement| { *s = mem::take(s).map_expressions(f); }, |expr: &mut Expression| {
            *expr = f(mem::replace(expr, Expression::Constant(ConstantValue::Bool(false))));
        });
        self
    }

    /// Iterate over all statements in the tree (depth-first)
    pub fn iter(&self) -> StatementIter<'_> {
        StatementIter {
            stack: vec![self]
        }
    }

    /// Iterate over all expressions in the statement tree
    pub fn iter_expressions(&self) -> ExpressionIter<'_> {
        ExpressionIter {
            stmt_iter: self.iter(),
            expressions: Vec::new(),
        }
    }

    /// Get all function calls (recursively including nested blocks)
    pub fn calls(&self) -> impl Iterator<Item = TheoremFunctionID> + '_ {
        self.collect_all_calls().into_iter()
    }

    /// Recursively collect all function calls, including those in nested IfExpr/WhileExpr blocks
    fn collect_all_calls(&self) -> Vec<TheoremFunctionID> {
        let mut calls = Vec::new();
        self.collect_calls_recursive(&mut calls);
        calls
    }

    /// Helper to recursively collect calls
    fn collect_calls_recursive(&self, calls: &mut Vec<TheoremFunctionID>) {
        match self {
            Statement::Sequence(stmts) => {
                for s in stmts {
                    s.collect_calls_recursive(calls);
                }
            }
            Statement::Let { operation, .. } => {
                Self::collect_calls_from_expr(operation, calls);
            }
            Statement::Return { values } => {
                for v in values {
                    Self::collect_calls_from_expr(v, calls);
                }
            }
            Statement::Abort { code } => {
                Self::collect_calls_from_expr(code, calls);
            }
            Statement::UpdateField { target, new_value, .. } => {
                Self::collect_calls_from_expr(target, calls);
                Self::collect_calls_from_expr(new_value, calls);
            }
            Statement::UpdateVectorElement { target, index, new_value } => {
                Self::collect_calls_from_expr(target, calls);
                Self::collect_calls_from_expr(index, calls);
                Self::collect_calls_from_expr(new_value, calls);
            }
            Statement::Requires { condition } | Statement::Ensures { condition } => {
                Self::collect_calls_from_expr(condition, calls);
            }
        }
    }

    /// Recursively collect calls from an expression
    fn collect_calls_from_expr(expr: &Expression, calls: &mut Vec<TheoremFunctionID>) {
        match expr {
            Expression::Call { function, args, .. } => {
                calls.push(*function);
                for arg in args {
                    Self::collect_calls_from_expr(arg, calls);
                }
            }
            Expression::BinOp { lhs, rhs, .. } => {
                Self::collect_calls_from_expr(lhs, calls);
                Self::collect_calls_from_expr(rhs, calls);
            }
            Expression::UnOp { operand, .. } => {
                Self::collect_calls_from_expr(operand, calls);
            }
            Expression::Cast { value, .. } => {
                Self::collect_calls_from_expr(value, calls);
            }
            Expression::Pack { fields, .. } => {
                for f in fields {
                    Self::collect_calls_from_expr(f, calls);
                }
            }
            Expression::FieldAccess { operand, .. } => {
                Self::collect_calls_from_expr(operand, calls);
            }
            Expression::Unpack { operand, .. } => {
                Self::collect_calls_from_expr(operand, calls);
            }
            Expression::VecOp { operands, .. } => {
                for o in operands {
                    Self::collect_calls_from_expr(o, calls);
                }
            }
            Expression::Tuple(exprs) => {
                for e in exprs {
                    Self::collect_calls_from_expr(e, calls);
                }
            }
            Expression::IfExpr { condition, then_block, else_block } => {
                Self::collect_calls_from_expr(condition, calls);
                // Recurse into block statements
                for s in &then_block.statements {
                    s.collect_calls_recursive(calls);
                }
                Self::collect_calls_from_expr(&then_block.result, calls);
                for s in &else_block.statements {
                    s.collect_calls_recursive(calls);
                }
                Self::collect_calls_from_expr(&else_block.result, calls);
            }
            Expression::WhileExpr { condition, body, state } => {
                for s in &condition.statements {
                    s.collect_calls_recursive(calls);
                }
                Self::collect_calls_from_expr(&condition.result, calls);
                for s in &body.statements {
                    s.collect_calls_recursive(calls);
                }
                Self::collect_calls_from_expr(&body.result, calls);
                for init in &state.initial {
                    Self::collect_calls_from_expr(init, calls);
                }
            }
            Expression::Temporary(_) | Expression::Constant(_) => {}
        }
    }

    /// Check if this statement contains any monadic operations
    pub fn is_monadic(&self) -> bool {
        // Abort statements are inherently monadic
        if matches!(self, Statement::Abort { .. }) {
            return true;
        }
        // Check if any expression is a monadic call
        self.iter_expressions().any(|expr| {
            matches!(expr, Expression::Call { convention: CallConvention::Monadic, .. })
        })
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
        self.collect_all_calls()
    }

    /// Collect all struct IDs from pack/unpack expressions in this statement
    pub fn collect_struct_references(&self) -> Vec<TheoremStructID> {
        self.iter_expressions()
            .filter_map(|expr| expr.struct_reference())
            .collect()
    }

    /// Collect all struct IDs from types in expressions in this statement
    pub fn collect_type_struct_ids(&self) -> Vec<TheoremStructID> {
        self.iter_expressions()
            .flat_map(|expr| expr.collect_type_struct_ids())
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
        
        traverse_statement!(statement, (&), |statement| self.stack.push(statement));
        
        Some(statement)
    }
}

pub struct ExpressionIter<'a> {
    stmt_iter: StatementIter<'a>,
    expressions: Vec<&'a Expression>,
}

impl<'a> Iterator for ExpressionIter<'a> {
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
            traverse_expression!(
                stmt,
                (ref),
                (&),
                |_: &Statement| {},
                |e| exprs.push(e)
            );
        }
    }
}