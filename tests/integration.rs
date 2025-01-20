use std::path::Path;

use blastr::solve_smt;
use test_generator::test_resources;

#[test_resources("res/tests_sat/*.smt2")]
fn test_sat(smt: &str) {
    let file = Path::new(smt);
    let smt = std::io::BufReader::new(std::fs::File::open(file).unwrap());
    let mut mngr = NodeManager::default();
    let script = parse_script(smt, &mut mngr).unwrap();
    let mut interpreter = Interpreter::new(SolverOptions::default(), &mut mngr);

    for a in script.iter_asserts() {
        interpreter.assert(a);
    }

    match interpreter.check_sat() {
        Ok(res) => assert!(res.is_sat()),
        Err(err) => panic!("{}", err),
    }
}
