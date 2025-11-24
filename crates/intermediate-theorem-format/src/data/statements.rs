use crate::{CallConvention, ConstantValue, Expression, LoopVariable, TempId, TheoremFunctionID, TheoremStructID, TheoremType};
use std::mem;

/// Phi variable for merging values from control flow branches
#[derive(Debug, Clone)]
pub struct PhiVariable {
    /// The variable that receives the merged value
    pub result: TempId,
    /// Value from the then branch
    pub then_value: Expression,
    /// Value from the else branch
    pub else_value: Expression,
}

/// Loop condition with recomputation
#[derive(Debug, Clone)]
pub struct LoopCondition {
    /// Statements that recompute values needed for the loop condition
    pub recompute: Box<Statement>,
    /// The actual condition variable
    pub condition_var: TempId,
}

/// Structured statement (high-level control flow)
#[derive(Debug, Clone)]
pub enum Statement {
    /// Sequence of statements
    Sequence(Vec<Statement>),

    /// Assignment: let var := expr (or let (var1, var2, ...) := expr for tuples)
    Let {
        results: Vec<TempId>,
        operation: Expression,
        result_types: Vec<TheoremType>, // One type per result
    },

    /// Conditional: if cond then body1 else body2
    /// If phi_vars is non-empty, this is a value-producing if-expression.
    /// Renders as: let (phi1, phi2, ...) := if cond then (val1, val2, ...) else (val3, val4, ...)
    /// If phi_vars is empty, this is a statement-level if for control flow.
    If {
        condition: Expression,
        then_branch: Box<Statement>,
        else_branch: Box<Statement>,
        /// Phi variables that merge values from both branches (empty for statement-level if)
        phi_vars: Vec<PhiVariable>,
    },

    /// While loop: while cond do body
    ///
    /// Loop-carried variables are represented with proper SSA phi-nodes.
    /// Each LoopVariable captures the SSA values flowing through the loop.
    While {
        /// Loop-carried variables with phi-node information
        loop_vars: Vec<LoopVariable>,
        /// The loop condition with recomputation statements
        condition: LoopCondition,
        /// Loop body
        body: Box<Statement>,
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

#[macro_export]
macro_rules! traverse_statement {
    ($target:expr, ($($mutability:tt)*), $action:expr) => {
        match $target {
            Statement::Sequence(statements) => {
                for statement in statements {
                    $action(statement);
                }
            }
            Statement::If { then_branch, else_branch, .. } => {
                $action($($mutability)* **then_branch);
                $action($($mutability)* **else_branch);
            }
            Statement::While { condition: LoopCondition { recompute, .. }, body, .. } => {
                $action($($mutability)* **recompute);
                $action($($mutability)* **body);
            }
            _ => {}
        }
    };
}

macro_rules! traverse_expression {
    ($target:expr, ($($ref_pattern:tt)*), ($($mutability:tt)*), $recurse:expr, $action:expr) => {
        // First: Recurse to child statements (direct call, no closure!)
        traverse_statement!($target, ($($mutability)*), $recurse);

        // Second: Extract expressions from current statement
        match $target {
            Statement::Let { $($ref_pattern)* operation, .. } => $action(operation),
            Statement::If { $($ref_pattern)* condition, $($ref_pattern)* phi_vars, .. } => {
                $action(condition);
                for phi in phi_vars {
                    $action($($mutability)* phi.then_value);
                    $action($($mutability)* phi.else_value);
                }
            }
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
    pub fn map<F: Fn(Statement) -> Statement>(mut self, f: F) -> Statement {
        traverse_statement!(&mut self, (&mut), |child: &mut Statement| *child = f(mem::take(child)));
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

    /// Get all function calls
    pub fn calls(&self) -> impl Iterator<Item = TheoremFunctionID> + '_ {
        self.iter_expressions()
            .filter_map(|expr| expr.called_function())
    }

    /// Check if this statement contains any monadic operations
    pub fn is_monadic(&self) -> bool {
        self.iter_expressions().any(|expr| {
            matches!(expr, Expression::Call { convention: CallConvention::Monadic, .. })
        })
    }

    /// Check if this statement terminates (contains a Return or Abort)
    pub fn terminates(&self) -> bool {
        self.iter().any(|stmt| {
            matches!(stmt, Statement::Return { .. } | Statement::Abort { .. })
        })
    }

    /// Collect all function call IDs from expressions in this statement
    pub fn collect_function_calls(&self) -> Vec<TheoremFunctionID> {
        self.iter_expressions()
            .filter_map(|expr| expr.called_function())
            .collect()
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
            match stmt {
                Statement::Let { operation, .. } => self.expressions.push(operation),
                Statement::If { condition, phi_vars, .. } => {
                    self.expressions.push(condition);
                    for phi in phi_vars {
                        self.expressions.push(&phi.then_value);
                        self.expressions.push(&phi.else_value);
                    }
                }
                Statement::Return { values } => self.expressions.extend(values),
                Statement::Abort { code } => self.expressions.push(code),
                Statement::UpdateField { target, new_value, .. } => {
                    self.expressions.push(target);
                    self.expressions.push(new_value);
                }
                Statement::UpdateVectorElement { target, index, new_value } => {
                    self.expressions.push(target);
                    self.expressions.push(index);
                    self.expressions.push(new_value);
                }
                Statement::Requires { condition } | Statement::Ensures { condition } => {
                    self.expressions.push(condition);
                }
                _ => {}
            }
        }
    }
}