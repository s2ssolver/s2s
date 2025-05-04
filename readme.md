# s2s

[![Build](https://github.com/splortsolver/s2s/actions/workflows/build.yml/badge.svg)](https://github.com/splortsolver/s2s/actions/workflows/build.yml)

**s2s** is an SMT solver for the quantifier-free theory of strings combined with linear integer arithmetic (QF_SLIA).  
It encodes the problem into propositional logic and calls a SAT solver to check satisfiability.

⚠️ **Work in Progress**:  This project is in an early stage. Some features may be incomplete or unstable.

## Fragment

It currently supports a limited fragment of the [SMT-LIB Theory of Strings](https://smt-lib.org/theories-UnicodeStrings.shtml).
More precisely, it supports:

- String terms that are variables, constant string, and concatenations thereof.
- All grounded regular expression that do not contain complements over anything but `re.range`, `str.to_re`
- Word equations: Atoms of the form `(= l r)` where `l` and `r` are string terms
- Regular constraints: Atoms of the form `(str.in_re l R)` where `l` is a string term and `R` a regular expression
- Linear arithmetic constraints: Atoms of the from `(<op> l r)` where `l` and `r` are linear integer terms over integer variables and string lengths, and `<op>` is one of `<, <=,=, >=, >`

The solver makes a best-effort to solve formulas containing unsupport constructs but can fail, in which case it returns `unknown`.

## Build Instructions

1. Ensure that the [Rust toolchain](https://www.rust-lang.org/tools/install) is installed.
2. Install dependencies:
    - On Ubuntu: `sudo apt-get install libssl-dev pkg-config libclang-dev`
    - On MacOs: `brew install pkgconf openssl`
    - Windows is currently not supported
3. Clone the repository and build the project using `cargo build --release`

The compiled binary will be located at `target/release/s2s`.

## Usage

```bash
s2s [OPTIONS] <FILE>
```

- `<FILE>` is the path to an SMT-LIB file (QF_SLIA).
- `[OPTIONS]` is a list of options. Available options can be obtained by running `s2s --help`.

### Example

To run the solver on an SMT file, use

```bash
$ s2s res/tests_sat/regex_simp.smt2
sat
```

In order to obtain a model (on SAT), use the `--model` option

```bash
$ s2s res/tests_sat/regex_simp.smt2
sat
(
(define-fun X () String "xeeeex")
)
```

If the problem is unsat, then `--model` will print an error

```bash
$ s2s res/tests_unsat/levis_simp.smt2 --model
unsat
error: no model to get
```

More example problems are in `res/tests_sat/` and `rest/tests_unsat/`.

## License

Licensed under either of:

- [MIT License](https://opensource.org/licenses/MIT)
- [Apache License, Version 2.0](https://www.apache.org/licenses/LICENSE-2.0)

at your option.
