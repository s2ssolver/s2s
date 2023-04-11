use satstr::{Parser, Solver, Woorpje};
use std::{fs, io::Write};

#[test]
fn track1() {
    env_logger::init();
    let paths = fs::read_dir("./tests/track1").expect("Could not find tests/track1 directory");

    for path in paths {
        let path = path.unwrap().path();

        let test_name = format!("{}", path.display());
        println!("Name: {}", test_name);
        std::io::stdout().flush().unwrap();
        let mut instance = Parser::WoorpjeParser.parse(path.to_path_buf()).unwrap();
        instance.set_bound(20);
        let mut solver = Woorpje::new(&instance).unwrap();

        let res = solver.solve();
        assert!(res.is_sat());
    }
}
