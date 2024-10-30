use std::path::Path;

use satstr::solve_smt_old;
use test_generator::test_resources;

#[test_resources("res/tests_sat/*.smt2")]
fn test_sat(smt: &str) {
    let file = Path::new(smt);
    let smt = std::io::BufReader::new(std::fs::File::open(file).unwrap());
    match solve_smt_old(smt, None) {
        Ok(res) => assert!(res.is_sat()),
        Err(err) => panic!("{}", err),
    }
}
