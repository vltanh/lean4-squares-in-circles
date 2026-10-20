#!/usr/bin/env bash
# Check the library against Challenge.lean the way the Palomar registry does:
# with the `lake comparator` of this project's toolchain, which builds
# Challenge.lean and the root module SquaresInCircles in a sandbox, checks
# that the theorems of comparator.json have the same statements over identical
# definitions and use only the permitted axioms, and replays the proofs
# through Lean's kernel and the toolchain's independent kernels NanoDa and
# con-ron.
#
# Challenge.lean restates the pure definition bodies of Geometry.lean,
# StatementEight.lean, StatementEightGeometric.lean, and Optimal.lean in that
# order. The source-only helper
# scripts/sync-challenge.py performs this synchronization; --write copies the
# definitions before the comparator check. The Challenge header and theorem
# region are left as they are. To materialize source without any build, run
# only: python3 scripts/sync-challenge.py --write
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

# This helper only copies source text or reports textual drift. The build
# and independent-kernel work begin below, not inside the source helper.
sync_args=()
if [[ "$write" == 1 ]]; then
  sync_args+=(--write)
fi
python3 scripts/sync-challenge.py "${sync_args[@]}"

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
