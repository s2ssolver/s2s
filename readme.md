# Blastr

[![Build](https://github.com/splortsolver/s2s/actions/workflows/build.yml/badge.svg)](https://github.com/splortsolver/s2s/actions/workflows/build.yml)

**Blastr** is an SMT solver for the quantifier-free theory of strings combined with linear integer arithmetic (QF_SLIA).  
It currently supports a limited subset of SMT-LIB constraints.

⚠️ **Work in Progress**  
This project is experimental, under active development, and subject to frequent changes. Some features may be incomplete or unstable.

---

## Build Instructions

1. Ensure that the [Rust toolchain](https://www.rust-lang.org/tools/install) is installed.
2. Install dependencies:
    - On Ubuntu: `sudo apt-get install libssl-dev pkg-config libclang-dev`
    - On MacOs: `brew install pkgconf openssl`
    - Windows is currently not supported
3. Clone the repository and build the project using `cargo build --release`

The compiled binary will be located at `target/release/blastr`.

## Usage

```bash
blastr [OPTIONS] <FILE>
```

- `<FILE>` is the path to an SMT-LIB file (QF_SLIA).
- Example files can be found in the `res/tests_sat/` directory.

### Options

| Option | Description |
|--------|-------------|
| `--dry` | Stop after preprocessing. Returns `unknown` if satisfiability can't be determined from preprocessing alone. |
| `--print-preprocessed` | Output the preprocessed formula (in SMT-LIB format) to stdout. Use with `--dry` to only preprocess a formula. |
| `--init-bound`, `-b <b>` | Initial bound for variable domains. The bound is soft, the solver may choose larger bounds if needed. |
| `--max-bound`, `-B <B>` | Maximum bound to check satisfiability for. Terminates after checking all satisfiability where all string lengths are in `[0, B]` and integers are in `[-B, B]`. If no model is found, returns `unknown`. If not set, the solver may run indefinitely. |
| `--unsat-on-max-bound` | In combination with `--max-bound`, returns `unsat` (instead of `unknown`) if no model is found within the given bound. |
| `--model` | Prints the model after `(check-sat)`. Equivalent to including `(get-model)` in the input. If both are used, the model is printed twice. |
| `--skip-simp` | Skips the simplification phase during preprocessing. |
| `--help`, `-h` | Print help message. |
| `--version`, `-V` | Print version information. |
