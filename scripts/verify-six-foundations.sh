#!/usr/bin/env bash
# Local-only validation of the Six foundation modules, NOT full n=6 acceptance.
set -euo pipefail
cd "$(dirname "$0")/.."

out="${1:-.lake/six-verification}"
mkdir -p "$out"
python3 scripts/audit-six-sources.py --json "$out/source-audit.json" > "$out/source-audit.stdout"

for tool in lean lake; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'NOT COMPILED: required local executable %s is missing.\n' "$tool" >&2
    printf 'No Lean kernel or n=6 theorem acceptance is claimed.\n' >&2
    exit 127
  fi
done
expected='leanprover/lean4:v4.35.0-rc3'
if [[ "$(tr -d '\r\n' < lean-toolchain)" != "$expected" ]]; then
  echo 'Refusing to validate against a different pinned Lean toolchain.' >&2
  exit 2
fi
lake env lean --version | tee "$out/lean-version.txt"
if ! grep -Eq 'version 4[.]35[.]0-rc3([, )]|$)' "$out/lean-version.txt"; then
  echo 'The actual compiler is not the pinned Lean 4.35.0-rc3.' >&2
  exit 2
fi
lake build SquaresInCircles.Six 2>&1 | tee "$out/build.log"
lake env lean SixAxiomAudit.lean 2>&1 | tee "$out/axioms.log"
python3 scripts/audit-six-sources.py --axioms "$out/axioms.log" \
  --json "$out/foundation-audit.json"
echo 'Foundation modules compiled and their listed axiom dependencies checked.'
echo 'This does NOT establish Six.Goals.LowerBound or Six.Goals.Uniqueness.'
