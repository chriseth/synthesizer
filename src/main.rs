use std::path::PathBuf;

use clap::{Parser, Subcommand};

mod interpolant;
mod sat_solver;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Location of sat solver binray. Only `cadical` is supported for now.
    solver: String,

    /// File either in CNF or AIGER format to contain the specification of the function,
    /// i.e. a formula that is true if the inputs and outputs match.
    specification: String,

    /// List of variable names that are the inputs of the function to synthesize.
    inputs: Vec<String>,

    /// Variable name that is the output of the function to synthesize.
    output: String,
}

fn main() {
    let cli = Cli::parse();

    // // You can check the value provided by positional arguments, or option arguments
    // if let Some(name) = cli.name.as_deref() {
    //     println!("Value for name: {name}");
    // }

    // if let Some(config_path) = cli.config.as_deref() {
    //     println!("Value for config: {}", config_path.display());
    // }

    // // You can see how many times a particular flag or argument occurred
    // // Note, only flags can have multiple occurrences
    // match cli.debug {
    //     0 => println!("Debug mode is off"),
    //     1 => println!("Debug mode is kind of on"),
    //     2 => println!("Debug mode is on"),
    //     _ => println!("Don't be crazy"),
    // }

    // // You can check for the existence of subcommands, and if found use their
    // // matches just as you would the top level cmd
    // match &cli.command {
    //     Some(Commands::Test { list }) => {
    //         if *list {
    //             println!("Printing testing lists...");
    //         } else {
    //             println!("Not printing testing lists...");
    //         }
    //     }
    //     None => {}
    // }

    // Continued program logic goes here...
}
