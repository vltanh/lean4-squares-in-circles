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

**G1.1 implemented:** `ExactFamily.CircleConvexity` derives the complete
radical-domain convexity and strict position convexity from circle chords,
including radical endpoints. `Stationary.familyValue_position_strictConvex`
connects it to the existing scalar family. `TiltCurvature` additionally
proves `F_tt + 4 F > 91/45` on that whole domain from circle support and
the span-three relation, with derivatives of the actual trigonometric
function. It does not assume nonpositive defect. The root cover remains
active in `Stationary`: the envelope and radius gates are still needed.
These new Lean proof bodies remain uncompiled.

**G1.2 position gate implemented:** one comparison position, `u=87/100`,
and five circle-derived coefficient bounds give
`F_u/(2 c²) ≤ -81/20000` throughout the complete radius and tilt strip.
Strict convexity then places every stationary position to its right.
`Stationary.stationary_geometric_position_bounds` connects this argument
to the original stationary coordinates and is used in `stationary_local`.
The same secant argument proves that a derivative-zero position is the
global fixed-tilt minimum, including comparison with radical endpoints.
The remaining envelope and radius gates still require proof; this
checkpoint does not remove the root checker.

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

**G2.1–G2.2 implemented:** `Candidate.GeometricMismatch` gives the exact
sixteen signed quarter/axis numerator identities, charged-cost monotonicity,
and the endpoint/contact-root reduction, including linear, constant,
double-root, and disconnected feasible-set cases. The actual-frame
adapter retains every originally feasible axis. G2.3 remains open.

**Whole-state exclusion integrated:** the full frame range implies that a
zero-quarter primary separator needs the corresponding primary coordinate
above one. A core arc has primary coordinate at most `7/12`. The active
coarse and enhanced coverage dispatchers now exclude these impossible
regions geometrically, retaining all original checks on the other regions.
This removes 6,028 entire angle chains from the Lean row payload, reducing
the shared coarse table from 129,031 to 123,003 rows. Historical research
input is preserved. The active total across all affine tables is now
654,342 rows, and all remaining table-backed charged stages are explicit.

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

**G3.1 implemented:** `Candidate.GeometricOwners.negative_tilt_excluded`
now handles the entire closed half-chart `-3/8 ≤ z ≤ 0`, including zero,
under the actual terminal-owner and shared-mismatch hypotheses. The four
circle weights give the exact reserve `34477/144000000` above `Q0`.
`tilt_window` uses this theorem before consulting positive-tail certificates.
The 18 negative-only bundles `Tilt000`–`Tilt017` have been deleted from
source and from the import and coverage lists: 378 quartic certificates,
1,890 Bernstein coefficient checks, and 16,740 generated lines removed.
The generator now skips precisely those bundles. The 41 positive-tail
bundles and the remaining owner alternatives are still active. All new
Lean proof bodies remain uncompiled.

**G3.2 first whole class implemented:** if `B→T` has an intended owner
and `D→E` a forbidden owner, the three aligned inequalities on
`B→T→D→E` telescope to `3-(3/2)S ≤ a_B+a_E`. Containment gives
`a_B+a_E < 283/100`, contradicting `S ≤ 1/10`. This uses the original
feasible axes, allows ties, and is independent of tilt and mixed owners.
`quarter_owners` now applies this obstruction before the remaining
32-pattern certificate dispatch. Sixteen complete quarter bundles have
been deleted: 480 quartics and 20,688 generated lines. Together with
G3.1, 34 modules, 858 quartics, 4,290 Bernstein coefficient checks,
and 37,428 generated lines have been removed. The remaining B-forbidden
and mixed-owner classes are open.

**G3.2 second whole class implemented:** for a forbidden B separator and
G-axis 2, the `G→A→B→T` chain and a single rotated-corner support yield
`5/2-(3/2)S ≤ a_T+q/4`. Containment contradicts this at `S ≤ 3/200`,
with exact reserve `209/2500`. The proof covers the whole tilt chart,
both D directions, and every E owner. `Quarter024`–`Quarter031` have
been removed: eight modules, 240 quartics, and 10,344 lines. The total
owner/tilt removal is now 42 modules, 1,098 quartics, 5,490 Bernstein
coefficient checks, and 47,772 lines. The 24 retained quarter patterns
use an explicit index formula and 24 concrete projections; the previous
enumeration of functions `Fin 7 → Fin 4` has also been removed.

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

**G4.1 implemented:** the seven-walk enumeration in `Frames.lean` has
been replaced by two alternating vertex potentials and 32 edge comparisons.
The proof, including its sharp weighted-graph witness, is in
[`ODD_CYCLE_GEOMETRY.md`](ODD_CYCLE_GEOMETRY.md). The continuous pair and
quarter-word gates remain open; the new source has not been compiled.

**G4.2 core/core implemented:** `Arithmetic.CorePairGeometry` proves the
entire core/core pair bound from center separation, two circle chords,
and a uniform bound on the original vertex marker. `cycle_pair` now
handles this case before finite dispatch. The four core/core recursive
chart declarations, representing 32 source-axis/sign problems, have
been deleted. The exact pair reserve is `233/15000`. The remaining
21 chart-pair decisions and quarter-word exclusions are still active.
See [`CORE_PAIR_GEOMETRY.md`](CORE_PAIR_GEOMETRY.md).

**G4.3 common core/core word block implemented:** the original common
marker has signed correction in `(-7/40,7/40)` on both closed core charts.
Center separation gives the cost `>59/60`, exceeding every common
increment threshold by at least `7/1200`. `WordGeometry.common_pair`
now uses this geometry before its finite dispatcher. All 192 common
core/core recursive certificate declarations and their generator entries
have been removed; the common block has 240 retained declarations.
The two wrong-word role tables remain active. See
[`CORE_WORD_GEOMETRY.md`](CORE_WORD_GEOMETRY.md).

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
