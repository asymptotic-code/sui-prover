use crate::{Expression, LoopVariable, TempId, TheoremFunctionID, TheoremStructID, TheoremType};

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

/// Structured statement (high-level control flow)
#[derive(Debug, Clone)]
pub enum Statement {
    /// Sequence of statements
    Sequence(Vec<Statement>),

    /// Assignment: let var := expr (or let (var1, var2, ...) := expr for tuples)
    Let {
        results: Vec<TempId>,
        operation: Expression,
        result_types: Vec<TheoremType>,  // One type per result
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
        /// The loop condition expression
        condition: Expression,
        /// Loop body
        body: Box<Statement>,
    },

    /// Return from function
    Return {
        values: Vec<Expression>,
    },

    /// Abort execution
    Abort {
        code: Expression,
    },

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
    Requires {
        condition: Expression,
    },

    /// Ensures (postcondition assertion)
    Ensures {
        condition: Expression,
    },
}

impl Statement {
    // ========================================================================
    // Functional Traversal API
    // ========================================================================

    /// Fold over all statements in the tree (pre-order traversal)
    /// The closure receives the accumulator and a reference to each statement
    pub fn fold<T>(&self, init: T, mut f: impl FnMut(T, &Statement) -> T) -> T {
        self.fold_impl(init, &mut f)
    }

    fn fold_impl<T>(&self, acc: T, f: &mut impl FnMut(T, &Statement) -> T) -> T {
        // First apply function to current statement
        let acc = f(acc, self);

        // Then recursively fold over children
        match self {
            Statement::Sequence(stmts) => {
                stmts.iter().fold(acc, |acc, stmt| stmt.fold_impl(acc, f))
            }
            Statement::If { then_branch, else_branch, .. } => {
                let acc = then_branch.fold_impl(acc, f);
                else_branch.fold_impl(acc, f)
            }
            Statement::While { condition: _, body, .. } => {
                body.fold_impl(acc, f)
            }
            Statement::Let { .. } | Statement::Return { .. } | Statement::Abort { .. } |
            Statement::UpdateField { .. } | Statement::UpdateVectorElement { .. } |
            Statement::Requires { .. } | Statement::Ensures { .. } => {
                // Leaf nodes, just return accumulator
                acc
            }
        }
    }

    /// Map over the statement tree, transforming each statement
    pub fn map(&self, f: &impl Fn(&Statement) -> Statement) -> Statement {
        let transformed = match self {
            Statement::Sequence(stmts) => {
                Statement::Sequence(stmts.iter().map(|s| s.map(f)).collect())
            }
            Statement::Let { results, operation, result_types } => {
                Statement::Let {
                    results: results.clone(),
                    operation: operation.clone(),
                    result_types: result_types.clone(),
                }
            }
            Statement::If { condition, then_branch, else_branch, phi_vars } => {
                Statement::If {
                    condition: condition.clone(),
                    then_branch: Box::new(then_branch.map(f)),
                    else_branch: Box::new(else_branch.map(f)),
                    phi_vars: phi_vars.clone(),
                }
            }
            Statement::While { loop_vars, condition, body } => {
                Statement::While {
                    loop_vars: loop_vars.clone(),
                    condition: condition.clone(),
                    body: Box::new(body.map(f)),
                }
            }
            Statement::Return { values } => {
                Statement::Return { values: values.clone() }
            }
            Statement::Abort { code } => {
                Statement::Abort { code: code.clone() }
            }
            Statement::UpdateField { target, struct_id, field_index, new_value } => {
                Statement::UpdateField {
                    target: target.clone(),
                    struct_id: *struct_id,
                    field_index: *field_index,
                    new_value: new_value.clone(),
                }
            }
            Statement::UpdateVectorElement { target, index, new_value } => {
                Statement::UpdateVectorElement {
                    target: target.clone(),
                    index: index.clone(),
                    new_value: new_value.clone(),
                }
            }
            Statement::Requires { condition } => {
                Statement::Requires { condition: condition.clone() }
            }
            Statement::Ensures { condition } => {
                Statement::Ensures { condition: condition.clone() }
            }
        };

        // Apply transformation function to the result
        f(&transformed)
    }

    /// Iterator over all operations (expressions) in the statement tree
    pub fn operations(&self) -> impl Iterator<Item = &Expression> {
        let mut ops = Vec::new();
        self.collect_operations_impl(&mut ops);
        ops.into_iter()
    }

    fn collect_operations_impl<'a>(&'a self, ops: &mut Vec<&'a Expression>) {
        match self {
            Statement::Let { operation, .. } => {
                ops.push(operation);
            }
            Statement::Sequence(stmts) => {
                for stmt in stmts {
                    stmt.collect_operations_impl(ops);
                }
            }
            Statement::If { condition, then_branch, else_branch, phi_vars } => {
                ops.push(condition);
                for phi in phi_vars {
                    ops.push(&phi.then_value);
                    ops.push(&phi.else_value);
                }
                then_branch.collect_operations_impl(ops);
                else_branch.collect_operations_impl(ops);
            }
            Statement::While { condition, body, .. } => {
                ops.push(condition);
                body.collect_operations_impl(ops);
            }
            Statement::Return { values } => {
                for expr in values {
                    ops.push(expr);
                }
            }
            Statement::Abort { code } => {
                ops.push(code);
            }
            Statement::UpdateField { target, new_value, .. } => {
                ops.push(target);
                ops.push(new_value);
            }
            Statement::UpdateVectorElement { target, index, new_value } => {
                ops.push(target);
                ops.push(index);
                ops.push(new_value);
            }
            Statement::Requires { condition } => {
                ops.push(condition);
            }
            Statement::Ensures { condition } => {
                ops.push(condition);
            }
        }
    }

    /// Iterator over all function calls in the statement tree
    /// Returns function IDs
    pub fn calls(&self) -> impl Iterator<Item = TheoremFunctionID> {
        self.operations()
            .filter_map(|op| {
                if let Expression::Call { function, .. } = op {
                    Some(*function)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .into_iter()
    }

    /// Check if any statement satisfies a predicate
    pub fn any(&self, mut predicate: impl FnMut(&Statement) -> bool) -> bool {
        self.fold(false, |acc, stmt| acc || predicate(stmt))
    }

    /// Check if all statements satisfy a predicate
    pub fn all(&self, mut predicate: impl FnMut(&Statement) -> bool) -> bool {
        self.fold(true, |acc, stmt| acc && predicate(stmt))
    }

    /// Check if this statement or any nested statement contains monadic operations
    /// A statement is monadic if any Let has a ProgramState result type,
    /// or if it's a While, Return, or Abort (which always use ProgramState monad)
    pub fn is_monadic(&self) -> bool {
        self.any(|stmt| {
            if let Statement::Let { result_types, .. } = stmt {
                // Check if any result type is ProgramState
                return result_types.iter().any(|ty| ty.is_monad());
            }
            matches!(stmt, Statement::While { .. } | Statement::Return { .. } | Statement::Abort { .. })
        })
    }
}
