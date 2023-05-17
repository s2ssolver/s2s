use std::path::Path;

use clap::{Parser as ClapParser, ValueEnum};

use satstr::{preprocess, Bindep, IWoorpje, Parser, Solver, Woorpje};
#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)] // Read from `Cargo.toml`
struct Options {
    /// What mode to run the program in
    #[arg(long, short, value_enum, default_value = "woorpje")]
    solver: SolverType,
    /// The format of the input file
    #[arg(short, long, value_enum, default_value = "woorpje")]
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
}

fn main() {
    env_logger::init();
    let ts = std::time::Instant::now();
    let cli = Options::parse();
    let parser = match cli.format {
        Format::Woorpje => Parser::WoorpjeParser,
        Format::Smt => Parser::Smt2Parser,
    };
    let file = Path::new(&cli.file);
    if !file.exists() {
        panic!("File not found: {}", cli.file);
    }
    let mut instance = parser.parse(file.to_path_buf()).unwrap();
    if let Some(bound) = cli.max_bound {
        instance.set_ubound(bound);
    }
    instance.set_lbound(cli.min_bound);
    instance.set_formula(preprocess(instance.get_formula()));

    let mut solver = match cli.solver {
        SolverType::Woorpje => Box::new(Woorpje::new(&instance).unwrap()) as Box<dyn Solver>,
        SolverType::Iwoorpje => Box::new(IWoorpje::new(&instance).unwrap()) as Box<dyn Solver>,
        SolverType::Bindep => Box::new(Bindep::new(&instance).unwrap()) as Box<dyn Solver>,
        SolverType::Full => unimplemented!("Full solver not implemented yet"),
    };

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
                println!("{}", m);
            }
        }
        satstr::SolverResult::Unsat => println!("unsat"),
        satstr::SolverResult::Unknown => println!("unknown"),
    }
}
