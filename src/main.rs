use std::{path::Path, process::exit, time::Instant};

use clap::Parser as ClapParser;

use blastr::{solve_smt, SolverOptions};

/// The command line interface for the solver
#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)] // Read from `Cargo.toml`
struct Args {
    /// Skip the simplfication during preprocessing
    #[arg(long)]
    skip_simp: bool,

    /// Skip guessing values for Boolean variables during preprocessing
    #[arg(long)]
    skip_guessing: bool,

    /// If this is set to true, the solver will not actually solve the instance, but terminate after preprocessing.
    #[arg(long)]
    dry: bool,

    /// The maximum variable bound to check before returning `unknown`
    #[arg(short = 'B', long, value_enum, default_value = None)]
    max_bound: Option<u16>,

    /// The minimal initial variable bound to start the search with
    #[arg(long, short = 'b')]
    init_bound: Option<i32>,

    /// If set, returns `unsat` instead of `unknown` if the maximum bound set by `max_bound` is reached
    #[arg(long)]
    unsat_on_max_bound: bool,

    /// Print the model
    #[arg(long)]
    model: bool,

    /// Print the preprocessed formula in SMT-LIB format
    /// Use together with `--dry` to only preprocess the formula
    #[arg(long)]
    print_preprocessed: bool,

    /// The input file to use, must be either in SMT2 or WOORPJE format, according to the `format` argument
    file: String,
}

/// The main function of the solver. Parses the command line arguments and runs the solver.
fn main() {
    env_logger::init();
    let ts = Instant::now();
    let cli = Args::parse();
    let file = Path::new(&cli.file);
    if !file.exists() {
        panic!("File not found: {}", cli.file);
    }

    let opts = convert_options(&cli);
    let smt = std::io::BufReader::new(std::fs::File::open(file).unwrap());
    match solve_smt(smt, opts) {
        Ok(_) => (),
        Err(err) => {
            log::error!("Error: {}", err);
            println!("unknown");
            exit(1);
        }
    };

    log::info!("Done ({}ms).", ts.elapsed().as_millis());
}

fn convert_options(options: &Args) -> SolverOptions {
    let mut opts = SolverOptions::default();
    if options.dry {
        opts.dry = true;
    }
    if let Some(max) = options.max_bound {
        opts.set_max_bound(max);
    }
    if options.skip_simp {
        opts.simplify = false;
    }
    if options.skip_guessing {
        opts.guess_bools = false;
    }
    if options.unsat_on_max_bound {
        opts.unsat_on_max_bound = true;
    }
    if let Some(b) = options.init_bound {
        opts.init_upper_bound = b;
    }
    if options.print_preprocessed {
        opts.print_preprocessed = true;
    }
    if options.model {
        opts.get_model = true;
    }
    opts
}
