use std::path::Path;

use satstr::{solve, Parser, SolverResult};
use test_generator::test_resources;

#[test_resources("res/tests_sat/*.smt2")]
fn test_sat(smt: &str) {
    let file = Path::new(smt);
    let mut instance = Parser::Smt2Parser.parse(file.to_path_buf()).unwrap();
    assert!(matches!(solve(&mut instance), Ok(SolverResult::Sat(_))));
}
