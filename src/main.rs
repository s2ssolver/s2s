use std::{path::Path, process::exit, time::Instant};

use clap::{Parser as ClapParser, ValueEnum};

use satstr::{preprocess, ConjunctiveSolver, Parser, PreprocessingResult, Solver};
#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)] // Read from `Cargo.toml`
struct Options {
    /// What mode to run the program in
    #[arg(long, short, value_enum, default_value = "woorpje")]
    solver: SolverType,
    /// The format of the input file
    #[arg(short, long, value_enum, default_value = "auto")]
    format: Format,

    /// Skip the verification of the solution. If this is set to true, the solver will not check if the model is correct.
    #[arg(short = 'x', long)]
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
enum SolverType {
    Woorpje,
    Iwoorpje,
    Bindep,
    Full,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum, Debug)]
enum Format {
    Woorpje,
    Smt,
    // Detect format using file extension
    Auto,
}

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
    match preprocess(instance.get_formula(), instance.get_var_manager()) {
        PreprocessingResult::Unchanged => {
            log::debug!("No preprocessing applied.");
        }
        PreprocessingResult::Changed(c) => instance.set_formula(c),
        PreprocessingResult::False => {
            println!("unsat");
            return;
        }
        PreprocessingResult::True => {
            println!("sat");
            return;
        }
    }
    log::info!("Preprocessing done ({}ms).", ts.elapsed().as_millis());

    let mut solver = ConjunctiveSolver::new(instance.clone()).unwrap();

    let res = solver.solve();
    log::info!("Done ({}ms).", ts.elapsed().as_millis());

    match res {
        satstr::SolverResult::Sat(m) => {
            if !cli.skip_verify {
                match instance.get_formula().evaluate(&m) {
                    Some(true) => println!("sat\n{}", m),
                    Some(false) => panic!("Model is incorrect"),
                    None => panic!("Model is incomplete"),
                }
            } else {
                println!("sat");
                if instance.get_print_model() {
                    println!("{}", m);
                }
            }
        }
        satstr::SolverResult::Unsat => println!("unsat"),
        satstr::SolverResult::Unknown => println!("unknown"),
    }
}
