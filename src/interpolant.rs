use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    time::Duration,
};

use boolean_circuit::{builder::reduce_disjunction, Literal, Node};
use itertools::Itertools;

use crate::{
    sat_solver::{run_solver_on_cnf, ProofItem, Resolution, Solver, SolverResult},
    utils::simplify,
};

/// Computes a boolean circuit `f` in the common variables of `left` and `right` such that
/// `left -> f -> right`.
/// This only works if `left && right` is unsatisfiable.
/// If `symmetric` is true, then the interpolant uses [SPK09], otherwise regular McMillan interpolation is used.
pub fn compute_interpolant(
    left: &[Vec<Literal>],
    right: &[Vec<Literal>],
    timeout: Option<Duration>,
    solver_conf: &Solver,
    symmetric: bool,
) -> Result<Node, String> {
    let combined_clauses = left.iter().chain(right).cloned().collect_vec();
    let SolverResult::Unsat(proof) = run_solver_on_cnf(&combined_clauses, timeout, solver_conf)?
    else {
        return Err("Prover answered SAT".to_string());
    };
    let proof = proof.ok_or_else(|| "Prover did not provide proof".to_string())?;

    Ok(ComputeInterpolant::new(left, right, symmetric).compute_interpolant(proof))
}

struct ComputeInterpolant<'a> {
    /// If true, uses [SPK09] interpolation, otherwise McMillan interpolation.
    symmetric: bool,
    /// The clauses on the "left" side.
    left_clauses: HashSet<&'a [Literal]>,
    /// Variables common to the left and right side.
    common_variables: BTreeSet<&'a str>,
    /// Variables only in the left side.
    variables_only_in_left: BTreeSet<&'a str>,
    /// Generated circuit nodes by clause ID.
    nodes_for_clause: HashMap<usize, Node>,
    /// Clauses in the proof by ID
    clauses: BTreeMap<usize, Vec<Literal>>,
}

impl<'a> ComputeInterpolant<'a> {
    pub fn new(left: &'a [Vec<Literal>], right: &'a [Vec<Literal>], symmetric: bool) -> Self {
        let common_variables = vars_in_clauses(left)
            .intersection(&vars_in_clauses(right))
            .cloned()
            .collect::<BTreeSet<_>>();
        let variables_only_in_left = vars_in_clauses(left)
            .difference(&common_variables)
            .cloned()
            .collect();
        Self {
            symmetric,
            left_clauses: left.iter().map(AsRef::as_ref).collect(),
            nodes_for_clause: HashMap::new(),
            clauses: BTreeMap::new(),
            common_variables,
            variables_only_in_left,
        }
    }

    pub fn compute_interpolant(&mut self, proof: Vec<ProofItem>) -> Node {
        let mut last_node = None;
        println!("Processing proof, which has {} items", proof.len());
        let len = proof.len();
        for (i, item) in proof.into_iter().enumerate() {
            if (i + 1) * 100 / len > i * 100 / len && ((i + 1) * 100 / len) % 5 == 0 {
                println!("Processed {} %", (i + 1) * 100 / len);
            }
            let clause_id = item.clause_id();
            let node = match &item {
                ProofItem::OriginalClause(_, clause) => self.process_original_clause(clause),
                ProofItem::Resolution(res) => self.process_resolution(res),
            };
            last_node = Some(node.clone());
            self.nodes_for_clause.insert(clause_id, node);
            self.clauses.insert(clause_id, item.clause());
        }
        last_node.unwrap()
    }

    fn process_original_clause(&self, clause: &'a [Literal]) -> Node {
        if self.left_clauses.contains(&clause) {
            if self.symmetric {
                false.into()
            } else {
                let filtered_clause = clause
                    .iter()
                    .filter(|l| self.common_variables.contains(l.var()))
                    .map(|l| l.into())
                    .collect_vec();
                if filtered_clause.is_empty() {
                    false.into()
                } else {
                    reduce_disjunction(filtered_clause)
                }
            }
        } else {
            true.into()
        }
    }

    fn process_resolution(&self, res: &'a Resolution) -> Node {
        let (clause, node) = res
            .clause_refs
            .iter()
            .map(|id| (self.clauses[id].clone(), self.nodes_for_clause[id].clone()))
            .rev()
            .reduce(|(clause_a, node_a), (clause_b, node_b)| {
                let pivot = find_pivot(&clause_a, &clause_b);
                let n = simplify(if self.variables_only_in_left.contains(pivot.var()) {
                    &node_a | &node_b
                } else if self.symmetric && self.common_variables.contains(pivot.var()) {
                    simplify(Node::from(&pivot) & node_a) | simplify(Node::from(&!&pivot) & node_b)
                } else {
                    &node_a & &node_b
                });
                let resolvent = clause_a
                    .iter()
                    .chain(clause_b.iter())
                    .filter(|l| l.var() != pivot.var())
                    .unique()
                    .cloned()
                    .collect_vec();
                (resolvent, n)
            })
            .unwrap();
        assert_eq!(
            clause.iter().collect::<HashSet<_>>(),
            res.resolvent.iter().collect()
        );
        node
    }
}

fn vars_in_clauses(clauses: &[Vec<Literal>]) -> BTreeSet<&str> {
    clauses
        .iter()
        .flat_map(|c| c.iter())
        .map(|l| l.var())
        .collect()
}

/// Returns the pivot literal for a resolution of the clause `a` with the
/// clause `b`, i.e. a literal from `a` such that its negation occurs in `b`.
fn find_pivot(a: &[Literal], b: &[Literal]) -> Literal {
    let lits_in_a: HashSet<_> = a.iter().cloned().collect();
    let negated_lits_in_b = b.iter().map(|l| !l).collect();
    let intersection = lits_in_a.intersection(&negated_lits_in_b);
    if let [pivot] = intersection.collect_vec().as_slice() {
        (*pivot).clone()
    } else {
        panic!("Expected exactly one pivot variable");
    }
}

#[cfg(test)]
mod test {

    use boolean_circuit::{builder::eq, evaluate, generate_cnf};

    use super::*;

    #[test]
    fn interpolant_simple() {
        let mut var_cnt = 0;
        let mut new_var = || {
            var_cnt += 1;
            format!("v{var_cnt}")
        };
        let mut circ1 = generate_cnf(
            &eq(&(Node::from("x1") ^ Node::from("y")), &Node::from("r")),
            &mut new_var,
        )
        .collect_vec();
        let mut circ2 = generate_cnf(
            &eq(&(Node::from("x2") ^ Node::from("y")), &Node::from("r")),
            &mut new_var,
        )
        .collect_vec();
        circ1.push(vec![Literal::from("x1")]);
        circ2.push(vec![!&Literal::from("x2")]);

        let cadical = Solver::new("./cadical", &["--no-binary", "--frat=1"], true);
        for symmetric in [false, true] {
            let interpolant =
                compute_interpolant(&circ1, &circ2, None, &cadical, symmetric).unwrap();
            // Interpolant should be a circuit in variables y and r and compute x such that x ^ y = r.
            for (y, r) in [false, true].iter().cartesian_product([false, true].iter()) {
                let assignments = [("y".to_string(), *y), ("r".to_string(), *r)]
                    .iter()
                    .cloned()
                    .collect();
                let x = evaluate(&interpolant, &assignments);
                assert!(x ^ *y == *r);
            }
        }
    }
}
