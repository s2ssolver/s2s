use std::path::Path;

use blastr::{node::NodeManager, parse_script, smt::Interpreter, SolverOptions};
use test_generator::test_resources;

#[test_resources("res/tests_sat/*.smt2")]
fn test_sat(smt: &str) {
    let file = Path::new(smt);
    let smt = std::io::BufReader::new(std::fs::File::open(file).unwrap());
    let mut mngr = NodeManager::default();
    let options = SolverOptions::default();
    let script = parse_script(smt, &options, &mut mngr).unwrap();
    let mut interpreter = Interpreter::new(options, &mut mngr);

    for a in script.iter_asserts() {
        interpreter.assert(a);
    }

    match interpreter.check_sat() {
        Ok(res) => assert!(res.is_sat()),
        Err(err) => panic!("{}", err),
    }
}

#[test_resources("res/tests_unsat/*.smt2")]
fn test_unsat(smt: &str) {
    let file = Path::new(smt);
    let smt = std::io::BufReader::new(std::fs::File::open(file).unwrap());
    let mut mngr = NodeManager::default();
    let options = SolverOptions::default();
    let script = parse_script(smt, &options, &mut mngr).unwrap();
    let mut interpreter = Interpreter::new(options, &mut mngr);

    for a in script.iter_asserts() {
        interpreter.assert(a);
    }

    match interpreter.check_sat() {
        Ok(res) => assert!(res.is_unsat()),
        Err(err) => panic!("{}", err),
    }
}
