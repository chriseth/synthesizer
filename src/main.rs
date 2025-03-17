use std::{fs::File, io::Seek};

use boolean_circuit::{
    builder::{reduce_conjunction, reduce_disjunction},
    file_formats::{
        aiger::{from_aiger, to_aiger_binary},
        dimacs::from_dimacs,
    },
    Node,
};
use clap::Parser;
use sat_solver::Solver;
use synthesizer::synthesize_function;

mod deep_copy;
mod interpolant;
mod sat_solver;
mod synthesizer;
mod utils;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Location of sat solver binary. Only `cadical` is supported for now.
    solver: String,

    /// File either in DIMACS or AIGER format to contain the specification of the function,
    /// i.e. a formula that is true if the inputs and outputs match.
    specification: String,

    /// Comma-separated list of variable names that are the inputs of the function to synthesize.
    inputs: String,

    /// Variable name that is the output of the function to synthesize.
    output: String,

    /// File to write the synthesized function to.
    output_file: String,
}

fn main() {
    let cli = Cli::parse();

    let solver = Solver::new(&cli.solver, &["--no-binary", "--frat=1"], true);

    let mut specification_file = match File::open(&cli.specification) {
        Err(e) => {
            eprintln!("Error opening file: {}: {e}", cli.specification);
            std::process::exit(1);
        }
        Ok(s) => s,
    };
    let specification_aiger = from_aiger(&specification_file);
    specification_file.rewind().unwrap();
    let specification_dimacs = from_dimacs(specification_file);
    let specification = match (specification_aiger, specification_dimacs) {
        (Ok(specification), _) => specification,
        (_, Ok(specification)) => reduce_conjunction(
            specification
                .into_iter()
                .map(|clause| reduce_disjunction(clause.into_iter().map(|l| Node::from(&l)))),
        ),
        (Err(aiger_err), Err(dimacs_err)) => {
            eprintln!("Unsupported file format. Only AIGER and DIMACS are supported.");
            eprintln!("Error reading AIGER format: {aiger_err}");
            eprintln!("Error reading CNF format: {dimacs_err}");
            std::process::exit(1);
        }
    };

    let inputs = cli.inputs.split(',').map(|s| s.to_string()).collect();
    let output = cli.output.clone();
    match synthesize_function(solver, specification, inputs, output) {
        Err(e) => {
            eprintln!("Error synthesizing function: {e}");
            std::process::exit(1);
        }
        Ok(fun) => {
            let (vars, gates) = fun.gate_count();
            println!("Synthesized a function with {gates} gates and {vars} variables.");
            let output_file = match File::create(&cli.output_file) {
                Err(e) => {
                    eprintln!("Error creating file: {}: {e}", &cli.output_file);
                    std::process::exit(1);
                }
                Ok(f) => f,
            };
            match to_aiger_binary(output_file, &fun) {
                Err(e) => {
                    eprintln!("Error writing AIGER format: {e}");
                    std::process::exit(1);
                }
                Ok(_) => {
                    println!("Function written to {}.", cli.output_file);
                }
            }
        }
    }
}
