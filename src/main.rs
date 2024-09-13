use std::{path::Path, process::exit, time::Instant};

use clap::{Parser as ClapParser, ValueEnum};

use satstr::{solve_smt, SolverOptions, SolverResult};

/// The command line interface for the solver
#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)] // Read from `Cargo.toml`
struct Options {
    /// The format of the input file
    #[arg(short, long, value_enum, default_value = "auto")]
    format: Format,

    #[arg(long)]
    skip_simp: bool,

    /// If this is set to true, the solver will double-check that the found model is correct.
    #[arg(long)]
    verify_model: bool,

    /// If this is set to true, the solver will not actually solve the instance, but terminate after preprocessing.
    #[arg(long)]
    dry: bool,

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
    let file = Path::new(&cli.file);
    if !file.exists() {
        panic!("File not found: {}", cli.file);
    }

    let opts = convert_options(&cli);
    let smt = std::io::BufReader::new(std::fs::File::open(file).unwrap());
    let res = match solve_smt(smt, Some(opts)) {
        Ok(res) => res,
        Err(err) => {
            log::error!("Error: {}", err);
            println!("unknown");
            exit(1);
        }
    };

    log::info!("Done ({}ms).", ts.elapsed().as_millis());
    match res {
        SolverResult::Sat(Some(model)) => {
            println!("sat");
            if cli.model {
                println!("{}", model);
            }
        }
        SolverResult::Sat(None) => {
            println!("sat");
        }
        SolverResult::Unsat => println!("unsat"),
        SolverResult::Unknown => println!("unknown"),
    }
}

fn convert_options(options: &Options) -> SolverOptions {
    let mut opts = SolverOptions::default();
    opts.dry(options.dry);
    if let Some(max) = options.max_bound {
        opts.max_bounds(max);
    }
    if options.skip_simp {
        opts.simplify(false);
    }
    opts
}
