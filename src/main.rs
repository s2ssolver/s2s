use std::{path::Path, process::exit, time::Instant};

use clap::{Parser as ClapParser, ValueEnum};

use satstr::{model::Evaluable, solve, Parser, SolverResult};

/// The command line interface for the solver
#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)] // Read from `Cargo.toml`
struct Options {
    /// The format of the input file
    #[arg(short, long, value_enum, default_value = "auto")]
    format: Format,

    #[arg(long)]
    skip_preprocess: bool,

    /// If this is set to true, the solver will double-check that the found model is correct.
    #[arg(long)]
    verify_model: bool,

    /// The maximum variable bound to check before returning `unsat`
    #[arg(short = 'b', long, value_enum, default_value = None)]
    max_bound: Option<usize>,
    /// The minimal initial variable bound to start the search with
    #[arg(long, short = 'm', value_enum, default_value = "1")]
    min_bound: usize,

    /// Print the model
    #[arg(long)]
    model: bool,

    /// The input file to use, must be either in SMT2 or WOORPJE format, according to the `format` argument
    file: String,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
enum Format {
    Woorpje,
    Smt,
    // Detect format using file extension
    Auto,
}

/// The main function of the solver. Parses the command line arguments and runs the solver.
fn main() {
    env_logger::init();
    let ts = Instant::now();
    let cli = Options::parse();
    let parser = match cli.format {
        Format::Woorpje => Parser::WoorpjeParser,
        Format::Smt => Parser::Smt2Parser,
        Format::Auto => {
            let ext = cli.file.split('.').last();
            match ext {
                Some("eq") => Parser::WoorpjeParser,
                Some("smt2") | Some("smt") | Some("smt25") | Some("smt26") => Parser::Smt2Parser,
                Some(other) => {
                    log::error!(
                        "Format set to 'auto', but the file extension is no supported: {}",
                        other
                    );
                    println!("error");
                    exit(-1);
                }
                None => {
                    log::error!(
                        "Format set to 'auto', but could not detect format from file extension of file {}",
                        cli.file
                    );
                    println!("error");
                    exit(-1);
                }
            }
        }
    };
    let file = Path::new(&cli.file);
    if !file.exists() {
        panic!("File not found: {}", cli.file);
    }
    let mut instance = parser.parse(file.to_path_buf()).unwrap();
    if let Some(bound) = cli.max_bound {
        instance.set_ubound(bound);
    }
    if cli.model {
        instance.set_print_model(true);
    }
    instance.set_lbound(cli.min_bound);
    // Keep a copy of the formula since the solver might modify it during preprocessing
    // We want to validate the model against the original formula
    let original_formula = instance.get_formula().clone();

    let res = solve(&mut instance).unwrap();

    log::info!("Done ({}ms).", ts.elapsed().as_millis());
    match res {
        SolverResult::Sat(model) => {
            if cli.verify_model {
                match original_formula.eval(&model) {
                    Some(true) => {}
                    Some(false) => panic!("Model is incorrect ({})", model),
                    None => panic!("Model is incomplete ({})", model),
                }
            }
            println!("sat");
            if instance.get_print_model() {
                println!("{}", model);
            }
        }
        SolverResult::Unsat => println!("unsat"),
        SolverResult::Unknown => println!("unknown"),
    }
}
