# Replacing the n=8 computed tables by geometry

Started 2026-10-18 UTC, from PR #10 head
`e352b87f9e0c49846ff63d3c90001b4d15c500fd`.

## Objective and completion rule

Replace the large finite computations in the proof of the unrestricted
eight-square theorem and its five-parameter equality classification by
geometric arguments with small, explicit arithmetic. Preserve the stated
constant, all signed separating axes, and boundary contacts.

A removal gate closes only when its replacement has the same geometric
hypotheses and conclusion and the public proof no longer imports the old
computation. An abstract inequality with the hard estimate as a hypothesis,
a shorter data encoding, or a successful numerical experiment does not close
such a gate. New uncompiled Lean bodies are source implementations; no
claim of successful elaboration or compilation time follows from them.

The user's existing instructions remain in force: **do not compile Lean or
run CI**. Research calculations and source inspection are allowed. Every
implementation commit uses `[skip ci]`. This work does not change the
toolchain, independent statement, or definition of the equality family.

## G0 — Identify the actual dependencies: complete

The source import closure of `SquaresInCircles.Eight.Theorem` at the starting
commit contains 252 repository modules, of which 235 are n=8 modules. It
still imports all ten affine tables, totaling 660,370 rows:

| Input | Rows | Geometric purpose |
|---|---:|---|
| `GLowerAffine` | 9,087 | Exclude the lower G tangent tail. |
| `GUpperAffine` | 9,796 | Exclude the upper G tangent tail. |
| `TLowerAffine` | 49,971 | Exclude the lower T tangent tail. |
| `TUpperAffine` | 7,078 | Exclude the upper T tangent tail. |
| `HLowerAffine` | 48,050 | Exclude the lower H tangent tail. |
| `DUpperAffine` | 24,197 | Exclude the upper D tangent tail. |
| `CandidateCoarseMismatch` | 129,031 | Start the total mismatch contraction. |
| `Mismatch026To01Affine` | 131,255 | Contract to mismatch less than 1/10. |
| `Mismatch01To015Affine` | 107,196 | Contract to mismatch less than 3/200. |
| `Mismatch015To001Affine` | 144,709 | Contract to mismatch less than 1/1000. |

The root-localization module still calls `CompactRootCover.certify` with
depth 48. Its retained diagnostic reports 22,601 visited nodes; that number
is not a measured Lean cost. Owner capture imports 48 quarter bundles,
15 mixed bundles and 59 tilt bundles, with 21 alternatives per tilt bundle.
The four-type pair and wrong-word layers also call recursive `RealBox`
searches. They must not be overlooked when assessing future compilation.

The reproducible source inventory is
[`table_dependencies.py`](table_dependencies.py), with its initial report
in [`TABLE_DEPENDENCIES_BASELINE.json`](TABLE_DEPENDENCIES_BASELINE.json).
It reads imports and declarations without expanding or evaluating a table.

## G1 — Replace stationary-root subdivision by the family geometry: open

The manuscript already contains a substantially more geometric proof in
`HUMAN_FIVE_CORNER.md`, `HUMAN_FAMILY_ENCLOSURE.md`, and
`HUMAN_FAMILY_CLOSURE.md`. Transfer its actual reasoning instead of
reconstructing a root-subdivision tree in Lean.

1. **G1.1 — Position convexity.** Prove strict convexity of the complete
   radical-chain defect at each fixed tilt, including the closed radical
   endpoints. Instantiate the semicircle and composition inequalities for
   the actual five-corner coordinates.
2. **G1.2 — Envelope uniqueness.** Prove interiority and differentiability
   of the unique position minimizer. At every critical tilt prove the
   positive Hessian determinant from the six broad inequalities in the
   family-closure manuscript. This must not assume zero defect. It then
   excludes two critical tilts by the intervening maximum argument.
3. **G1.3 — Exact root identification.** Combine strict radius monotonicity
   with the already supplied explicit endpoint tests. Identify this unique
   broad-strip solution with `sharpData` and the pure statement root.
   Remove the import of `Generated.StationaryLocalization` only after the
   existing broad-domain uniqueness theorem has a complete replacement.

The fixed-tilt argument alone does not justify deleting the root cover:
uniqueness of the minimizing tilt and the radius are distinct obligations.
Detailed execution belongs in `STATIONARY_GEOMETRY.md`.

## G2 — Remove angular subdivisions by exact contact geometry: open

For a signed half-angle parameter, a square's sine, cosine and width have
a common positive denominator. All four original separating-axis margins
then have quadratic numerators. Since the charged angular cost is strictly
increasing for the charges used here, its minimum on a feasible angular
component occurs at a closed domain endpoint or a contact root.

1. **G2.1 — Exact quadratic identities.** Retain both signs, every original
   axis, and the quarter increment. Prove the numerator identities on the
   whole declared angle interval.
2. **G2.2 — Contact-root reduction.** Prove attainment and the endpoint or
   contact alternative, including a double root, an identically zero
   numerator, and shared endpoints. At most two nontrivial contact roots
   occur for each signed axis and fixed pair of states.
3. **G2.3 — Continuous state inequality.** Supply and prove explicit
   role-dependent marker functions on the whole source and target state
   domains. Prove the charged cost at every contact/root alternative.
   This is the remaining global inequality; G2.1–G2.2 do not imply it.

The full target is the same `ChargedBound` used by the candidate assembly,
or a stronger direct capture theorem that bypasses that assembly. Reusing
462 piecewise state labels without proving their complete inequalities is
not removal of the coarse table. Detailed execution belongs in
`MISMATCH_GEOMETRY.md`.

## G3 — Eliminate owner and tilt regions by direct circle stresses: open

First eliminate free slider centers symbolically from the original
separating inequalities. Use nonnegative stress weights and disk support
on the remaining constrained corners. Keep total frame error as one
shared budget rather than charging every edge independently.

1. **G3.1 — Nonpositive tilt.** Prove a single whole-region exclusion at
   mismatch at most 1/1000 using the exact zero-tilt five-corner stress.
   Cover tilt zero explicitly. If this closes, remove all negative-only
   tilt bundles from the active import and coverage lists.
2. **G3.2 — Remaining owner alternatives.** Group alternatives by the
   actual wrong separator, and prove a whole-region geometric obstruction
   for each group. Retain the original four axes until eliminated.
3. **G3.3 — Positive tilt tails.** Apply the reduced five-corner chain and
   an adaptive geometric stress or the family envelope. A frozen stress
   that is sharp at the optimum need not remain a useful lower bound away
   from the optimum; establish its sign before using it on a tail.

Detailed execution belongs in `OWNER_GEOMETRY.md`.

## G4 — Replace finite word and pair searches: open

The four geometric labels form a small weighted graph. Replace the
enumeration of all 4^7 walks by a short odd-cycle potential argument.
This removes that enumeration while leaving the continuous pair theorem
as a separate obligation. The complete core/core hand argument uses
inscribed disks, center separation, and a uniform marker bound; transfer
it without enumerating separating axes. Continue with the already written
whole-domain pair arguments, then the seven quarter-word classes.

No proof about the weighted graph discharges an inequality for actual
pairs of squares. Track the combinatorial and geometric changes separately.

## G5 — Integration and final acceptance: open

For each established replacement:

- Connect it to the existing candidate or stationary theorem with its
  original geometric hypotheses.
- Remove only generated inputs made unnecessary by that connection.
- Re-run the source import inventory and document the actual reduction.
- Preserve every unchanged computed dependency explicitly in the status.

The desired final import graph has no large affine table, root search, or
recursive whole-domain `RealBox` decision. Small identities, radical sign
checks and a bounded set of explicit polynomial inequalities are acceptable.
Compilation and a measured resource check remain outside this execution
because the user has prohibited them. No fast-compilation claim is made
until that measurement is authorized and actually performed.
