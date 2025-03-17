use std::collections::HashSet;

use boolean_circuit::{Node, Operation};

/// Returns a hash set of all variables in the circuit.
pub fn variables_in_circuit(node: &Node) -> HashSet<&str> {
    node.iter()
        .filter_map(|n| match n.operation() {
            Operation::Variable(name) => Some(name.as_str()),
            _ => None,
        })
        .collect()
}

/// Returns a number `u` such that for any `i` >= `u`, there is no
/// variable called `v{i}` in the circuit.
pub fn next_free_variable(node: &Node) -> u64 {
    variables_in_circuit(node)
        .iter()
        .filter_map(|v| v.strip_prefix('v'))
        .filter_map(|v| v.parse::<u64>().ok())
        .max()
        .unwrap_or(0)
        + 1
}

pub struct VariableDispenser {
    next_variable: u64,
}

impl VariableDispenser {
    /// Creates a variable dispenser such that each call to `next` returns a
    /// variable name that does not occur in `existing_circuit`.
    pub fn new(existing_circuit: &Node) -> Self {
        Self {
            next_variable: next_free_variable(existing_circuit),
        }
    }

    /// Returns a new unique variable name.
    pub fn next(&mut self) -> String {
        let var = format!("v{}", self.next_variable);
        self.next_variable += 1;
        var
    }
}

/// Performs simple non-recursive constant propagation.
pub fn simplify(node: Node) -> Node {
    match node.operation() {
        Operation::Negation(n) => {
            if let Some(value) = n.try_to_constant() {
                Node::from(!value)
            } else {
                node
            }
        }
        Operation::Conjunction(left, right) => {
            match (left.try_to_constant(), right.try_to_constant()) {
                (Some(false), _) | (_, Some(false)) => Node::from(false),
                (Some(true), _) => right.clone(),
                (_, Some(true)) => left.clone(),
                _ => node,
            }
        }
        Operation::Disjunction(left, right) => {
            match (left.try_to_constant(), right.try_to_constant()) {
                (Some(true), _) | (_, Some(true)) => Node::from(true),
                (Some(false), _) => right.clone(),
                (_, Some(false)) => left.clone(),
                _ => node,
            }
        }
        Operation::Xor(left, right) => match (left.try_to_constant(), right.try_to_constant()) {
            (Some(true), _) => !right.clone(),
            (_, Some(true)) => !left.clone(),
            (Some(false), _) => right.clone(),
            (_, Some(false)) => left.clone(),
            _ => node,
        },
        Operation::Constant(_) | Operation::Variable(_) => node,
    }
}
