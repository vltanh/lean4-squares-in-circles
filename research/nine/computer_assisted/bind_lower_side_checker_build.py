#!/usr/bin/env python3
"""Compile the complete delivered checker and bind it to the replayed binary."""
from pathlib import Path
import hashlib
import json
import subprocess

BASE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = BASE / "verify_lower_side_exact.cpp"
    replayed = BASE / "verify_lower_side_exact"
    fresh = BASE / "verify_lower_side_exact.delivered"
    before = digest(source)
    previous = digest(replayed)
    argv = ["g++", "-O3", "-std=c++17", source.name, "-o", fresh.name]
    subprocess.run(argv, cwd=BASE, check=True)
    after, current, rebuilt = digest(source), digest(replayed), digest(fresh)
    if before != after or previous != current or current != rebuilt:
        raise RuntimeError("source changed, replayed binary changed, or complete recompilation differs")
    report = dict(result="PASS", source=source.name, source_sha256=after,
                  replayed_executable=replayed.name, replayed_executable_sha256=current,
                  fresh_executable=fresh.name, fresh_executable_sha256=rebuilt,
                  entire_delivered_source_compiled=True, executables_byte_identical=True,
                  compile_argv=argv,
                  compiler=subprocess.check_output(["g++", "--version"], text=True).splitlines()[0],
                  binding_script_sha256=digest(Path(__file__)))
    text = json.dumps(report, indent=2) + "\n"
    (BASE / "lower_side_no_extra_build_binding.json").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
