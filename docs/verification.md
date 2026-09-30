# Verification

[Back to the README](../README.md)

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
lake env lean SixAxiomAudit.lean
lake env lean SanityChecks.lean
scripts/verify-comparator.sh
```

Needs Elan and network access for mathlib. Lean and mathlib are at
`v4.35.0-rc3`, a release candidate whose toolchain ships `lake comparator`,
which the Palomar registry uses. These commands are the acceptance criteria for
the repository. On PR #7 the new six-square source has not yet completed the
final build, Comparator and axiom-audit run, so the expected three-axiom result
is not recorded here as an executed fact.

- `lake build` must succeed without warnings; an unfinished proof would show as
  `declaration uses 'sorry'`.
- Every `#print axioms` line in the audit must read
  `[propext, Classical.choice, Quot.sound]`: an unproved lemma would add
  `sorryAx`, and `native_decide`, which trusts the compiler,
  `Lean.ofReduceBool`. The audit also prints `Packing`, `Congruent`,
  `axisSquare`, `optimalRadius`, `optimalPackings`, `Optimum`, the column
  packings and the theorem signatures for inspection.
- `SanityChecks.lean` must elaborate without errors. It checks the radius and
  model tables, re-proves the rational margins and polygon contact points the
  proofs use, restates the public theorems, checks each unique model of `n ≤ 6`
  congruent to itself, and checks column packings of seven squares, one with a
  single middle square moved.
- `scripts/verify-comparator.sh` (Linux, bubblewrap) checks the library against
  `Challenge.lean` as Palomar does, and must end with `Your solution is okay!`.
  It first checks that `Challenge.lean` restates the definitions of
  `SquaresInCircles/Geometry.lean` word for word (with `--write` it copies them,
  so only `Geometry.lean` is edited). Then `lake comparator` builds both modules
  in a sandbox, checks that `optimal_radius` and `optimal_packings` have the
  same statements over identical definitions and use only the three standard
  axioms, and replays the proofs through the toolchain's NanoDa and con-ron
  kernels and Lean's.

[`.github/workflows/lean.yml`](../.github/workflows/lean.yml) runs these steps
on every push to `main` and on pull requests; its axiom audit covers every
declaration under `SquaresInCircles`.
[`.github/workflows/palomar.yml`](../.github/workflows/palomar.yml), run by
hand, runs Palomar's own mechanical verification of a commit without submitting
it; its report must say `status: pass`.

The proof pages link every Lean name they cite to its declaration, by file and
line. `python3 scripts/link_lean.py` regenerates the links and fails on a name
that matches no declaration or several;
[`.github/workflows/docs.yml`](../.github/workflows/docs.yml) runs it with
`--check` on pushes and pull requests that touch the Lean sources or the docs.
After `pre-commit install`,
[`.pre-commit-config.yaml`](../.pre-commit-config.yaml) refreshes the links on
every such commit and stops it if a link moved, so the refreshed pages can be
staged.

`python3 scripts/figures/proof_figures.py` redraws every figure of the proof
pages; it holds the drawing helpers and runs one module per chapter
([`scripts/figures/`](../scripts/figures)). The figures are computed from the
geometry of the proofs, and most assert the facts their captions state.

Build from the committed `lake-manifest.json`, which pins every dependency by
hash. Avoid `lake update`: seven transitive packages track `main` or `master`
and would be re-resolved.

**Trusted base:** Lean, Lake, mathlib. Every numeric margin is an exact rational
inequality closed by `norm_num`, `linarith` or `nlinarith`; `π` enters only
through mathlib's rational bounds `3.14 < π < 3.1416` (and weaker ones such as
`3 < π`), and for seven squares also `3.1415 < π` and
`3.141592 < π < 3.141593`.
