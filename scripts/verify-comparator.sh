#!/usr/bin/env bash
# Check the library against Challenge.lean the way the Palomar registry does:
# with the `lake comparator` of this project's toolchain, which builds
# Challenge.lean and the root module SquaresInCircles in a sandbox, checks
# that the theorems of comparator.json have the same statements over identical
# definitions and use only the permitted axioms, and replays the proofs
# through Lean's kernel and the toolchain's independent kernels NanoDa and
# con-ron.
#
# Challenge.lean restates the definitions of SquaresInCircles/Geometry.lean
# word for word. Edit Geometry.lean only, and run with --write to copy its
# definitions into Challenge.lean before the check; the header of
# Challenge.lean and its theorems are left as they are.
#
# Needs Linux, python3 and bubblewrap (`bwrap`), which sandboxes the build.
# Run from anywhere: scripts/verify-comparator.sh [--write]
set -euo pipefail
cd "$(dirname "$0")/.."

write=0
case "${1-}" in
  --write) write=1 ;;
  "") ;;
  *) echo "usage: scripts/verify-comparator.sh [--write]" >&2; exit 2 ;;
esac

# The definitions run from `noncomputable section` to the end of the
# namespace in Geometry.lean, and to the theorems in Challenge.lean.
python3 - "$write" <<'PY'
import sys
from pathlib import Path

write = sys.argv[1] == "1"
challenge_path = Path("Challenge.lean")
challenge = challenge_path.read_text()
geometry = Path("SquaresInCircles/Geometry.lean").read_text()
start = "noncomputable section\n"
first = challenge.index(start)
last = challenge.index("/-! ### The theorems -/")
original = geometry[geometry.index(start):geometry.rindex("end SquaresInCircles")]
original = original.rstrip() + "\n\n"
if challenge[first:last] != original:
    if not write:
        raise SystemExit(
            "error: the definitions in Challenge.lean differ from "
            "SquaresInCircles/Geometry.lean; run scripts/verify-comparator.sh --write"
        )
    challenge_path.write_text(challenge[:first] + original + challenge[last:])
    print("Challenge.lean: copied the definitions of SquaresInCircles/Geometry.lean")
PY

# Palomar ignores `enable_nanoda` and registers the toolchain's kernels itself;
# a copy of comparator.json does the same here.
prefix=$(lean --print-prefix)
config=$(mktemp "${TMPDIR:-/tmp}/comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import sys

source, destination, prefix = sys.argv[1:]
with open(source) as file:
    config = json.load(file)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
with open(destination, "w") as file:
    json.dump(config, file, indent=2)
PY

lake comparator --config "$config"
