use std::{
    collections::HashMap,
    fs::{self, File},
    io::{BufRead, BufReader, BufWriter, Read},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    rc::Rc,
    time::Duration,
};

use boolean_circuit::{file_formats::dimacs::to_dimacs, generate_cnf, Literal, Node};
use itertools::Itertools;

#[derive(Clone)]
pub struct Solver {
    pub binary_path: String,
    pub options: Vec<String>,
    pub request_proof: bool,
}

impl Solver {
    pub fn new(binary_path: &str, options: &[&str], request_proof: bool) -> Self {
        Self {
            binary_path: binary_path.to_string(),
            options: options.iter().map(|&s| s.to_string()).collect(),
            request_proof,
        }
    }
}

#[derive(Debug)]
pub enum SolverResult {
    Sat(HashMap<String, bool>),
    Unsat(Option<Vec<ProofItem>>),
}

#[derive(Debug)]
pub enum ProofItem {
    OriginalClause(usize, Vec<Literal>),
    Resolution(Resolution),
}

impl ProofItem {
    pub fn clause_id(&self) -> usize {
        match self {
            ProofItem::OriginalClause(id, _) => *id,
            ProofItem::Resolution(res) => res.id,
        }
    }

    pub fn clause(self) -> Vec<Literal> {
        match self {
            ProofItem::OriginalClause(_, clause) => clause,
            ProofItem::Resolution(res) => res.resolvent,
        }
    }
}

#[derive(Debug)]
pub struct Resolution {
    pub id: usize,
    pub resolvent: Vec<Literal>,
    pub clause_refs: Vec<usize>,
}

pub fn run_solver_on_circuit(
    node: &Node,
    new_var: &mut impl FnMut() -> String,
    timeout: Option<Duration>,
    solver_conf: &Solver,
) -> Result<SolverResult, String> {
    let cnf = generate_cnf(node, new_var).collect_vec();
    run_solver_on_cnf(&cnf, timeout, solver_conf)
}

pub fn run_solver_on_cnf(
    cnf: &[Vec<Literal>],
    timeout: Option<Duration>,
    solver_conf: &Solver,
) -> Result<SolverResult, String> {
    let mut solver = Command::new(&solver_conf.binary_path);
    let solver = solver.args(&solver_conf.options);
    let mut solver = 
    // if solver_conf.request_proof {
    //     solver.arg(proof_file.path().to_str().unwrap())
    // } else {
        solver
//    }
    .stdout(Stdio::piped())
    .spawn()
    .unwrap();

    let stdin = solver.stdin.as_mut().unwrap();
    let var_map = to_dimacs(BufWriter::new(stdin), cnf);
    let stdout = solver.stdout.take().unwrap();
    let parsed_output = parse_output(stdout, &var_map, timeout)?;
    solver.wait().unwrap();
    if let Some(result) = parsed_output {
        Ok(SolverResult::Sat(result))
    // } else if solver_conf.request_proof {
    //     let proof = read_proof(proof_file.path(), &var_map)?;
    //     Ok(SolverResult::Unsat(Some(proof)))
    } else {
        Ok(SolverResult::Unsat(None))
    }
}

fn nonempty_items(items: &str) -> impl Iterator<Item = &'_ str> {
    items.split(" ").filter(|v| !v.is_empty())
}

/// Parse the output. If the solver returns SAT, return the model.
/// If the solver returns UNSAT, return None.
fn parse_output(
    output: impl Read,
    var_map: &HashMap<u32, String>,
    timeout: Option<Duration>,
) -> Result<Option<HashMap<String, bool>>, String> {
    let start = std::time::Instant::now();
    let mut model = HashMap::new();
    for line in BufReader::new(output).lines() {
        if let Some(timeout) = timeout {
            if start.elapsed() > timeout {
                return Err("Timeout".to_string());
            }
        }
        let line = line.unwrap();
        // print!("{}", line);
        if let Some(comment) = line.strip_prefix("c ") {
            if timeout.is_none() {
                println!("{comment}");
            }
        } else if let Some(sat) = line.strip_prefix("s ") {
            if sat != "SATISFIABLE" {
                return Ok(None);
            }
        } else if let Some(vars) = line.strip_prefix("v ") {
            model.extend(
                nonempty_items(vars)
                    .map(|v| v.parse::<i32>().unwrap())
                    .filter(|&v| v != 0)
                    .map(|v| {
                        let name = var_map[&v.unsigned_abs()].clone();
                        (name, v > 0)
                    }),
            );
        }
    }
    Ok(Some(model))
}

fn read_proof(
    proof_file_path: &Path,
    var_map: &HashMap<u32, String>,
) -> Result<Vec<ProofItem>, String> {
    let proof_file = fs::File::open(proof_file_path).map_err(|e| e.to_string())?;
    let mut proof_items = vec![];
    for line in BufReader::new(proof_file).lines() {
        //for each `a` line, we get the new clause and then the clauses to resolve on in reverse order.
        let line = line.map_err(|e| e.to_string())?;
        if let Some(original) = line.strip_prefix("o ") {
            let mut items = nonempty_items(original).map(|s| s.parse::<i32>().unwrap());
            let id = items.next().unwrap() as usize;
            let mut lits = items.collect_vec();
            assert_eq!(lits.pop().unwrap(), 0);
            let clause = lits
                .into_iter()
                .map(|l| to_named_literal(l, var_map))
                .collect_vec();
            proof_items.push(ProofItem::OriginalClause(id, clause));
        } else if let Some(resolvent) = line.strip_prefix("a ") {
            let mut items = nonempty_items(resolvent);
            let id = items.next().unwrap().parse::<usize>().unwrap();
            let mut clause = vec![];
            for lit in items.by_ref() {
                if lit == "0" {
                    break;
                }
                clause.push(to_named_literal(lit.parse::<i32>().unwrap(), var_map));
            }
            assert_eq!(items.next(), Some("l"));
            let mut clause_refs = items.map(|s| s.parse::<usize>().unwrap()).collect_vec();
            assert_eq!(clause_refs.pop(), Some(0));
            proof_items.push(ProofItem::Resolution(Resolution {
                id,
                resolvent: clause,
                clause_refs,
            }));
        }
    }
    Ok(proof_items)
}

fn to_named_literal(literal: i32, var_map: &HashMap<u32, String>) -> Literal {
    let name = Rc::new(var_map[&literal.unsigned_abs()].clone());
    if literal < 0 {
        Literal::Neg(name)
    } else {
        Literal::Pos(name)
    }
}

#[cfg(test)]
mod test {

    use boolean_circuit::builder::eq;

    use super::*;

    #[test]
    fn simple_sat() {
        let solver = Solver::new("./kissat", &[], false);
        let x = "x".into();
        let y = "y".into();
        let mut var_cnt = 0;
        let mut new_var = &mut || {
            var_cnt += 1;
            format!("v_{var_cnt}")
        };
        let r = run_solver_on_circuit(&eq(&x, &y), &mut new_var, None, &solver).unwrap();
        assert!(matches!(r, SolverResult::Sat(_),));
    }

    #[test]
    fn simple_unsat() {
        let solver = Solver::new("./kissat", &[], false);
        let x = "x".into();
        let mut var_cnt = 0;
        let mut new_var = &mut || {
            var_cnt += 1;
            format!("v_{var_cnt}")
        };
        let r = run_solver_on_circuit(&eq(&x, &!&x), &mut new_var, None, &solver).unwrap();
        assert!(matches!(r, SolverResult::Unsat(..)));
    }

    #[test]
    fn constants() {
        let solver = Solver::new("./kissat", &[], false);
        let mut var_cnt = 0;
        let mut new_var = &mut || {
            var_cnt += 1;
            format!("v_{var_cnt}")
        };
        let r = run_solver_on_circuit(&Node::from(true), &mut new_var, None, &solver).unwrap();
        assert!(matches!(r, SolverResult::Sat(..)));
        let r = run_solver_on_circuit(&Node::from(false), &mut new_var, None, &solver).unwrap();
        assert!(matches!(r, SolverResult::Unsat(..)));
    }

    #[test]
    fn simple_unsat_proof() {
        let solver = Solver::new("./cadical", &["--no-binary", "--frat=1"], true);
        let x = Node::from("x");
        let mut var_cnt = 0;
        let mut new_var = &mut || {
            var_cnt += 1;
            format!("v_{var_cnt}")
        };
        let r = run_solver_on_circuit(&(&x & &!&x), &mut new_var, None, &solver).unwrap();
        let SolverResult::Unsat(proof) = r else {
            panic!();
        };
        let proof = proof.unwrap();
        assert_eq!(proof.len(), 9);
        for (i, item) in proof.iter().enumerate() {
            if i < 6 {
                assert!(matches!(item, ProofItem::OriginalClause(..)));
            } else {
                assert!(matches!(item, ProofItem::Resolution(..)));
            }
        }
    }
}
