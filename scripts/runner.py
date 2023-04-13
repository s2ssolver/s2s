#!/usr/bin/python3
import argparse
import os
from subprocess import Popen, PIPE
from timeit import default_timer as timer
import joblib


def parse():
    parser = argparse.ArgumentParser()
    parser.add_argument("dir", help="Directory containing the benchmarks")
    parser.add_argument("-b", help="Max bound", type=int, default=10)
    return parser.parse_args()


def run(file, bound):
    print(file, end=": ")
    start = timer()
    (stdout, stderr) = Popen(["./target/release/satstr", "-b", str(bound),  str(file)],
                             stdout=PIPE, stderr=PIPE).communicate()

    time = timer() - start
    if stderr is not None and stderr.decode("utf-8").strip() != "":
        print(stderr.decode("utf-8").strip())
    if stdout is not None:
        res = stdout.decode("utf-8").strip().splitlines()
        if res[0] == "sat":
            print(f"✅ SAT ({time:.2f}s)")
            return (file, "sat")
        elif res[0] == "unsat":
            print(f"❌ UNSAT ({time:.2f}s)")
            return (file, "unsat")
        else:
            print("❔ UNKNOWN")
            return (file, "unknown")


if __name__ == "__main__":
    args = parse()
    print("⚙️ Building...")
    Popen(["cargo", "build", "--release"],
          stdout=PIPE, stderr=PIPE).wait()
    results = joblib.Parallel(n_jobs=8)(joblib.delayed(run)(os.path.join(args.dir, file), args.b)
                                        for file in os.listdir(args.dir))
    unsasts = [res[0] for res in results if res[1] == "unsat"]
    sats = [res[0] for res in results if res[1] == "unsat"]
    print(f"#️⃣  Total {len(results)}")
    print(f"❌ Unsats {len(unsasts)}: ")
    print(" ".join(unsasts).strip(), end="")
    print(f"✅ Sats {len(sats)}: ")
    print(" ".join(sats).strip(), end="")

# 80
