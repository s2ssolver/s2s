use std::{path::Path, process::exit, time::Instant};

use clap::{Parser as ClapParser, ValueEnum};

use satstr::{
    get_solver,
    model::{Evaluable, Substitution},
    preprocess, Parser, PreprocessingResult,
};

/// The command line interface for the solver
#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)] // Read from `Cargo.toml`
struct Options {
    /// The format of the input file
    #[arg(short, long, value_enum, default_value = "auto")]
    format: Format,

    #[arg(long)]
    skip_preprocess: bool,

    /// Skip the verification of the solution. If this is set to true, the solver will not check if the model is correct.
    #[arg(long)]
    skip_verify: bool,

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
    let _ts = std::time::Instant::now();
    let cli = Options::parse();
    let parser = match cli.format {
        Format::Woorpje => Parser::WoorpjeParser,
        Format::Smt => Parser::Smt2Parser,
        Format::Auto => {
            let ext = cli.file.split('.').last();
            match ext {
                Some("eq") => Parser::WoorpjeParser,
                Some("smt2") | Some("smt") => Parser::Smt2Parser,
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

    // Preprocess the formula
    let ts = Instant::now();

    // Keep a copy of the formula before preprocessing for validating the model
    let original_formula = instance.get_formula().clone();
    let mut subs = Substitution::new();
    match preprocess(&instance) {
        (PreprocessingResult::Unchanged(_), s) => {
            assert!(s.is_empty());
            log::debug!("No preprocessing applied.");
        }
        (PreprocessingResult::Changed(c), s) => {
            subs = s;
            instance.set_formula(c)
        }
    }
    log::info!("Preprocessing done ({}ms).", ts.elapsed().as_millis());
    log::debug!("Formula post preprocessing: {}", instance.get_formula());

    // Check if the formula is trivial
    match instance.get_formula().eval(&subs) {
        Some(true) => {
            log::info!("Formula is trivially true");
            println!("sat");
            if instance.get_print_model() {
                subs.use_defaults();
                println!("{}", subs);
            }
        }
        Some(false) => {
            log::info!("Formula is trivially false");
            println!("unsat");
        }
        None => {
            let mut solver = get_solver(instance.clone()).unwrap();

            let res = match solver.solve() {
                Ok(res) => res,
                Err(r) => {
                    log::error!("Error while solving: {}", r);
                    println!("error");
                    exit(-1);
                }
            };
            log::info!("Done ({}ms).", ts.elapsed().as_millis());

            match res {
                satstr::SolverResult::Sat(m) => {
                    let mut model = subs.compose(&m);
                    model.use_defaults();
                    if !cli.skip_verify {
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
                satstr::SolverResult::Unsat => println!("unsat"),
                satstr::SolverResult::Unknown => println!("unknown"),
            }
        }
    }
}
