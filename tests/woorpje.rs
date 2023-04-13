use satstr::{Parser, Solver, Woorpje};
use test_generator::test_resources;

#[test_resources("res/track1/*.eq")]
fn track1(f: &str) {
    let mut instance = Parser::WoorpjeParser.parse(f.into()).unwrap();
    // All equations have solution with bounds at most 80
    instance.set_bound(80);
    let mut solver = Woorpje::new(&instance).unwrap();

    let res = solver.solve();
    assert!(res.is_sat());
}
