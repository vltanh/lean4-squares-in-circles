# Conditional actual-AB terminal for strict 011/00

This package applies the accepted seven-square actual-AB two-link theorem to
the **original nine-square strict-radius `011/00` predicate**. It adds no
original-cell or whole-mask closure. It makes no claim for the closed face
`q = 1105/256`, and it does not change the current `001/00` proof.

For either original extra `X = H` or `X = I`, the conditional terminal requires

\[
\theta_D\ge0,\quad y_G\ge y_D,\quad |x_G-x_D|<1,\quad
x_B\le x_X\le x_D,\quad |y_X-y_B|+|y_D-y_X|\le3/5.
\]

The exact `011/00` mask supplies actual AB, EF, and FG. The accepted theorem
therefore gives `q >= 1105/256`, which excludes the strict-radius target.
BC and CD retain their original strictly weak comparisons. Actual BC is
used only by the separate `001/00` equality blocker, which is not invoked.
All nine frames, 36 corners, 36 physical pairs, and five original center
cones remain part of the caller.

## Accepted dependencies

- [Actual-AB full-angle two-link theorem](https://github.com/vltanh/lean4-squares-in-circles/tree/30c2b2894e5c8ce95838adbedef9e0d3591a5cf1/research/nine/computer_assisted/actual_AB_two_link_row_v1).
  Its premise binding is SHA256
  `3261f48cec76aae54ee9a920dbf0176cadfa3d90194f9cd2dd6c54d4a143e6ac`.
  Its exact scalar proof has 28 domains, 103 leaves, and 12,875 rational
  Bernstein coefficients.
- [Literal H/I label substitution](https://github.com/vltanh/lean4-squares-in-circles/tree/2cb33747ac2fe9f611412f59e1d8c5f5a6f9641f/research/nine/computer_assisted/row_label_substitutions_v1).
  The inherited actual-extra source binding is SHA256
  `1217223d16f854c8f97b15befa954e9465d5ff943b7f87037c87bae766d5bf68`.

The source binding for this application is SHA256
`ab7b5f0bcd5545a34cefc4ce2bc5424960c16eae9b5fe424bac71656f8ff52f3`.
Root's physical and code review accompanies the package. The `source/`
directory contains byte-identical frozen helpers and the application hand
argument. This README and the root review are kept outside that directory.

## Interface and proof-use gate

The producer exports

```python
evaluate(state, extra, mask="011/00", radius_mode="strict")
```

where `extra` is 7 for H or 8 for I. The independent checker exports

```python
verify_literal(printed, state, mask="011/00", radius_mode="strict")
```

Wrong-mask and closed-radius calls are rejected. A passed literal verifies
only the quantitative guard implication from the supplied certified state.
**Actual proof use still requires independently certified strict `011/00`
ancestry and a fresh replay of the accepted scalar proof.** Every domain
outside this guard must also be covered before claiming a complete mask.
The literal controls below provide none of those missing closure steps.

## Clean-folder literal controls

From the repository root, the following command first checks every frozen
source hash, then runs the controls in a fresh temporary directory. It does
not modify the published inputs or replay the scalar theorem.

```sh
python3 -B -S - <<'PY'
from pathlib import Path
from tempfile import TemporaryDirectory
import hashlib, json, shutil, subprocess, sys

source = Path("research/nine/computer_assisted/strict_011_actual_AB_application_v1/source")
binding_file = source / "PREMISE_BINDINGS.json"
assert hashlib.sha256(binding_file.read_bytes()).hexdigest() == \
    "ab7b5f0bcd5545a34cefc4ce2bc5424960c16eae9b5fe424bac71656f8ff52f3"
binding = json.loads(binding_file.read_text())
with TemporaryDirectory(prefix="strict011_literal_") as temporary:
    target = Path(temporary)
    for entry in binding["files"]:
        original = source / entry["path"]
        assert hashlib.sha256(original.read_bytes()).hexdigest() == entry["sha256"]
        shutil.copyfile(original, target / entry["path"])
    shutil.copyfile(binding_file, target / binding_file.name)
    subprocess.run([sys.executable, "-B", "-S",
                    str(target / "check_strict_011_actual_ab_guard.py")],
                   cwd=target, check=True)
    report = json.loads((target / "EXACT_APPLICATION_CONTROLS.json").read_text())
    assert report["status"] == "PASS_CONDITIONAL_STRICT_01100_APPLICATION_CONTROLS"
    assert report["new_original_cells"] == report["new_masks"] == 0
    assert report["closed_Q_claim"] is False
PY
```

Expected controls: 120 synthetic quantitative-guard states, 12 passing
conditional guards, 72 rejected damaged literals, and 72 rejected calls
with the wrong target. These are exact arithmetic and application-scope
controls; the synthetic states are not asserted to be physical packings.
