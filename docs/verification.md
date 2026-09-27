# Verification

[Back to the README](../README.md)

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
lake env lean SanityChecks.lean
scripts/verify-comparator.sh
```

Requires Elan/Lake and network access for mathlib. The build uses Lean
`4.35.0-rc3` and mathlib `v4.35.0-rc3`: a release candidate, because
`lake comparator` first ships with Lean `4.35.0-rc2`, and the Palomar registry
requires it. The source contains no `sorry`, no `axiom` declarations and no
`native_decide`.

- `lake build` must report zero `declaration uses 'sorry'` warnings.
- Every `#print axioms` line in the audit must read exactly
  `[propext, Classical.choice, Quot.sound]`.
- `sorryAx` in that output would indicate an unproved lemma;
  `Lean.ofReduceBool` would indicate `native_decide` and compiler trust.
- The audit also prints `Packing`, `Congruent`, `axisSquare`,
  `optimalRadius`, `optimalPackings`, `Optimum`, the column packings of seven
  squares and the theorem signatures for inspection.
- `SanityChecks.lean` checks the radius and model tables, re-proves the exact
  rational margins and the contact points of the contact polygons that the
  proofs rely on, restates the public theorems, checks that the optimal model
  of each `n ≤ 5` is congruent to itself, and checks the column packings of
  seven squares, among them one with a single middle square moved; it must
  elaborate without errors.
- `scripts/verify-comparator.sh` checks the library against `Challenge.lean`
  as the Palomar registry does. It first checks that the definitions in
  `Challenge.lean` are word for word those of `SquaresInCircles/Geometry.lean`;
  with `--write` it copies them there instead, so that only `Geometry.lean` is
  ever edited. It then runs `lake comparator` on
  `comparator.json`, which builds both modules in a `bwrap` sandbox and checks
  that `optimal_radius` and `optimal_packings` have the same statements in
  both, that every definition they use is identical, and that the proofs use
  no axiom beyond `propext`, `Quot.sound` and `Classical.choice`; it then
  replays the proofs through the independent kernels NanoDa and con-ron that
  ship with the toolchain, and through Lean's.
  It must end with `Your solution is okay!`. It needs Linux and bubblewrap.

[`.github/workflows/lean.yml`](../.github/workflows/lean.yml) runs these steps
on every push to `main` and on pull requests, using `leanprover/lean-action`.
Its axiom audit covers every declaration under `SquaresInCircles`, not only the
ones printed by `AxiomAudit.lean`.
[`.github/workflows/palomar.yml`](../.github/workflows/palomar.yml), started by
hand, runs the Palomar registry's own mechanical verification of a commit, the
job the registry runs after a submission, without submitting it; its report
must end with `status: pass`.

The proof pages in [`docs/proof/`](proof/README.md) link every Lean name they
cite to its declaration, by file and line.
[`scripts/link_lean.py`](../scripts/link_lean.py) regenerates these links, and
fails on a name that matches no declaration or more than one.
[`.github/workflows/docs.yml`](../.github/workflows/docs.yml) runs
`python3 scripts/link_lean.py --check` on every push to `main` and every pull
request that touches the Lean sources or the docs, and fails if a link is
stale. To refresh the links after changing a Lean file, run
`python3 scripts/link_lean.py` and commit the result. To have this done before
every commit, run `pre-commit install` once:
[`.pre-commit-config.yaml`](../.pre-commit-config.yaml) then refreshes the links
whenever a commit touches the Lean sources or the docs, and stops the commit if
any link moved, so that the refreshed pages can be staged.

The figures of the proof pages are drawn by the scripts in
[`scripts/figures/`](../scripts/figures):
[`proof_figures.py`](../scripts/figures/proof_figures.py) holds the drawing
helpers and runs one module per chapter (`fig_*.py`). Every figure is computed
from the same geometry as the proofs, and most assert the facts their captions
state; running `python3 scripts/figures/proof_figures.py` redraws all of them.

Build from the committed `lake-manifest.json`, which pins every dependency by
hash. Avoid `lake update`: seven transitive packages track `main` or `master`
and would be re-resolved.

**Trusted base:** Lean, Lake, mathlib. Every numeric margin is an exact rational
inequality closed by `norm_num`, `linarith` or `nlinarith`; `π` enters only
through mathlib's rational bounds `3.14 < π < 3.1416` (and weaker ones such as
`3 < π`), and for seven squares also `3.1415 < π` and
`3.141592 < π < 3.141593`.
