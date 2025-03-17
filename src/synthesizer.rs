use boolean_circuit::{generate_cnf, Node};
use itertools::Itertools;

use crate::{
    deep_copy::deep_copy, interpolant::compute_interpolant, sat_solver::Solver,
    utils::VariableDispenser,
};

pub fn synthesize_function(
    solver: Solver,
    specification: Node,
    inputs: Vec<String>,
    output: String,
) -> Result<Node, String> {
    // Create a copy but keep the variables from `inputs`.
    let (copy, var_substitution) = deep_copy(&specification, &inputs);
    let copy_output = Node::from(var_substitution.get(&output.as_str()).unwrap().as_str());
    let left = specification & !Node::from(output);
    let right = copy & copy_output;

    let mut variable_dispenser = VariableDispenser::new(&(&left & &right));
    let left = generate_cnf(&left, &mut || variable_dispenser.next()).collect_vec();
    let right = generate_cnf(&right, &mut || variable_dispenser.next()).collect_vec();

    compute_interpolant(&left, &right, None, &solver, true)
}

#[cfg(test)]
mod test {
    use boolean_circuit::builder::eq;

    use super::*;

    #[test]
    fn interpolant_simple() {
        let solver = Solver::new("./cadical", &["--no-binary", "--frat=1"], true);
        let specification = eq(&Node::from("x"), &!Node::from("y"));
        let inputs = vec!["y".to_string()];
        let output = "x".to_string();
        let fun = synthesize_function(solver, specification, inputs, output).unwrap();
        assert_eq!(fun.to_string_as_tree(), "!y");
    }
}
