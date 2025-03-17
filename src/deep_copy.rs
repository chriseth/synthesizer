use std::{collections::HashMap, rc::Rc};

use boolean_circuit::{Node, Operation};

use crate::utils::VariableDispenser;

/// Creates a deep copy of the given circuit, assigning new names to all variables
/// except those in `variable_exceptions`.
/// Returns the new circuit and the variable substitution map.
pub fn deep_copy<'a>(
    node: &'a Node,
    variable_exceptions: &'a [String],
) -> (Node, HashMap<&'a str, Rc<String>>) {
    DeepCopy::new(node, variable_exceptions).copy(node)
}

struct DeepCopy<'a> {
    variable_substitution: HashMap<&'a str, Node>,
    variable_dispenser: VariableDispenser,
    node_substitutions: HashMap<usize, Node>,
}

impl<'a> DeepCopy<'a> {
    fn new(circuit: &'a Node, variable_exceptions: &'a [String]) -> Self {
        Self {
            variable_substitution: variable_exceptions
                .iter()
                .map(|name| (name.as_str(), Node::from(name.clone())))
                .collect(),
            variable_dispenser: VariableDispenser::new(circuit),
            node_substitutions: HashMap::new(),
        }
    }

    fn copy(mut self, node: &'a Node) -> (Node, HashMap<&'a str, Rc<String>>) {
        for n in node.post_visit_iter() {
            let substitution = match n.operation() {
                Operation::Variable(name) => {
                    if let Some(new_node) = self.variable_substitution.get(name.as_str()) {
                        new_node.clone()
                    } else {
                        let new_node = Node::from(self.variable_dispenser.next());
                        self.variable_substitution
                            .insert(name.as_str(), new_node.clone());
                        new_node
                    }
                }
                Operation::Constant(value) => Node::from(*value),
                Operation::Negation(inner) => !self.sub(inner),
                Operation::Conjunction(left, right) => self.sub(left) & self.sub(right),
                Operation::Disjunction(left, right) => self.sub(left) | self.sub(right),
                Operation::Xor(left, right) => self.sub(left) ^ self.sub(right),
            };
            self.node_substitutions.insert(n.id(), substitution);
        }
        let node = self.sub(node);
        let substitutions = self
            .variable_substitution
            .into_iter()
            .map(|(k, v)| {
                let Operation::Variable(name) = v.operation() else {
                    unreachable!()
                };
                (k, Rc::clone(name))
            })
            .collect();
        (node, substitutions)
    }

    fn sub(&self, node: &'a Node) -> Node {
        self.node_substitutions.get(&node.id()).unwrap().clone()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn simple() {
        let circuit = Node::from("v1");
        let copied_circuit = deep_copy(&circuit, &[]).0;
        assert_eq!(copied_circuit.to_string_as_tree(), "v2");
    }

    #[test]
    fn intermediate1() {
        let circuit = (Node::from("v1") & Node::from("v2")) | !Node::from("v1");
        let (copied_circuit, var_substitution) = deep_copy(&circuit, &[]);
        assert_eq!(var_substitution.len(), 2);
        assert_eq!(var_substitution["v1"].as_str(), "v3");
        assert_eq!(var_substitution["v2"].as_str(), "v4");
        assert_eq!(copied_circuit.to_string_as_tree(), "((v3 & v4) | !v3)");
    }

    #[test]
    fn intermediate2() {
        let circuit = (Node::from("v3") ^ Node::from("v3")) & Node::from(true) | Node::from(false);
        let copied_circuit = deep_copy(&circuit, &[]).0;
        assert_eq!(
            copied_circuit.to_string_as_tree(),
            "(((v4 ^ v4) & true) | false)"
        );
    }

    #[test]
    fn with_exceptions() {
        let circuit = Node::from("v1") & Node::from("v2");
        let variable_exceptions = vec!["v1".to_string()];
        let (copied_circuit, var_substitution) = deep_copy(&circuit, &variable_exceptions);
        assert_eq!(var_substitution.len(), 2);
        assert_eq!(var_substitution["v1"].as_str(), "v1");
        assert_eq!(var_substitution["v2"].as_str(), "v3");
        assert_eq!(copied_circuit.to_string_as_tree(), "(v1 & v3)");
    }
}
