# Verification

[Back to the README](../README.md)

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
lake env lean SanityChecks.lean
scripts/verify-comparator.sh
```

Needs Elan and network access for mathlib. Lean and mathlib are at
`v4.35.0-rc3`, a release candidate whose toolchain ships `lake comparator`,
which the Palomar registry uses. Every proof is complete and rests on
`propext`, `Classical.choice` and `Quot.sound` alone.

For eight squares, the active proof restores the checked-table strategy of
`4bea747b3efa13c869b956cb28435efaf21526fa`. The table-free case analysis has
been retired. The geometric five-corner radius and the five-parameter optimal
family remain the public statement. `Eight/Construction.lean` proves that
these models pack the disk and reach its circle. `Eight/Rigidity/Classification.lean`
classifies optimal packings in stationary coordinates, and
`Eight/Uniqueness.lean` transfers that classification through the geometric
bridges into one `Optimum`, as in the other seven cases. Its lower bound and
packing equivalence follow from the shared `Optimum` theorems. Full verification includes
these bridges and all three kernels below.

The central-square estimates now use geometric supports and one-variable
calculus. Both rectangle widths follow from radial projection, circular arcs
and elementary angle bounds; their former 230 interval rows are gone.
The central-band polynomial bounds use positive quadratic lower bounds and
square completion. The core angle estimates use tangent addition and a cubic
bound, while the seven-step type budget follows from coloring an odd cycle
and counting its boundary crossings. The final pullback uses corner containment and linear implications from the
retained separating axes. The global capture still uses the
checked tables described in [Chapter 11](proof/11-eight.md). The stationary
coordinate bounds follow directly from circle equations and short decimal
brackets. The local Hessian follows from circle curvatures, monotone frame
projections and a shear by `3/5`; its former sixteen grid checks are gone.
The radius-slope bound also follows by differentiating the circle equations.
Circle-coordinate comparisons give opposite signs at the extreme corners of the pose box;
monotonicity and the intermediate value theorem give the adaptive root at every tilt.
Root existence uses only the broad radius interval, with no refined root-sign certificates.
The root moves at speed between `2/3` and `13/6`; height loses at most `0.7` per unit of
position and gains at least `1.8` per unit of tilt. It therefore increases along the family.
Comparison with the known stationary root bounds the endpoint positions. Two circle
equations then bound their heights; no root-bracket or height certificates remain. The HE
factor in reserve 5 also increases along the roots: its position gain `0.91 * 2/3` exceeds its tilt
loss `0.6`. At the lower tilt, coarse circle bounds give `L ≥ 1.023`, `V/Y ≥ 0.9088` and
`E ≤ 0.9564`. Thus the margin is at least `1/40` on that whole face, giving reserve 5 and
then the larger reserve 0, with no margin certificate.

Force balance makes ED the largest raw contact weight, and the circle-weight mass is at
least `6/5` of ED. Normalization bounds every contact by `5/6`, replacing all 224 contact
checks. The same estimate gives `epsilon ≥ 2/3` and contact proportions; these bound five
owner reserves by `1/80`. The last two reserves share an unnormalized cut that decreases
with position. Bounded tilt curvature extends two midpoint values and two slopes to
`0.412 ≤ N₀ ≤ 0.44` on the entire pose rectangle. Since `omega ≥ 3/5`, these reserves
are at least `3/250 > rho`. Circle equations at the middle tilt supply the cut values and
slopes, so all nine reserves follow from geometry and calculus. The adaptive interval
certificates, their generator, the graph cover and its numbered formula nodes are gone. The cut identities are algebraic; the force identities for reserves 0
and 5 are applied at position-stationary chains.
Positivity of the radicands and structural differentiation replace
the former regularity checks. The quadratic and cubic terminal remainders use
coordinate and weight bounds at the endpoints of the tilt interval, replacing
64 interval checks on graph hulls. The family box is admissible by half-angle
formulas, Cauchy–Schwarz and separating projections; it has no separate
interval-expression generator.

- `lake build` must succeed without warnings; an unfinished proof would show as
  `declaration uses 'sorry'`.
- Every `#print axioms` line in the audit must read
  `[propext, Classical.choice, Quot.sound]`: an unproved lemma would add
  `sorryAx`, and `native_decide`, which trusts the compiler,
  `Lean.ofReduceBool`. The audit also prints `Packing`, `Congruent`,
  `axisSquare`, `optimalRadius`, `optimalPackings`, `Optimum`, the model of
  six squares with its turned square, the column packings and the theorem
  signatures for inspection.
- `SanityChecks.lean` must elaborate without errors. It checks the radius and
  model tables, re-proves the rational margins and polygon contact points the
  proofs use, restates the public theorems, checks each model of `n ≤ 6`
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

The library and `Challenge.lean` use Lean's module system, which Palomar
requires: every file begins with `module`, imports with `public import` and
puts its declarations in an `@[expose] public section`, so that they and the
bodies of its definitions stay visible to the files that import it.
`AxiomAudit.lean` and `SanityChecks.lean` are modules too, which import the
library.

Build from the committed `lake-manifest.json`, which pins every dependency by
hash. Avoid `lake update`: seven transitive packages track `main` or `master`
and would be re-resolved. Keep mathlib on its release tag `v4.35.0-rc3`, the
one that matches the toolchain: after verifying a submission, Palomar renders
`Challenge.lean` with Verso's release for the same toolchain and merges
Verso's Lake manifest into this one, and the render fails if a package that
both pin, `plausible` or `Cli`, has two different revisions. On the tag both
match Verso's; on mathlib `master` they soon drift.

**Trusted base:** Lean, Lake, mathlib. Every numeric margin is an exact rational
inequality closed by `norm_num`, `linarith` or `nlinarith`; `π` enters only
through mathlib's rational bounds `3.14 < π < 3.1416` (and weaker ones such as
`3 < π`), and for seven squares also `3.1415 < π` and
`3.141592 < π < 3.141593`.
