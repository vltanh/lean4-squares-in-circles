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

**G1.2 norm gate implemented:** a single trial chain at `u=15/16`
and one cubic endpoint-chord identity prove `k₁²+k₂²<4` at every
position minimum throughout the full radius strip and `0≤tan(t)≤1/5`.
The proof permits positive defect. Its scalar adapter is
`familyValue_position_stationary_norm_lt_four`. This supplies the norm
input for the critical-Hessian argument; the mixed derivative and
global envelope uniqueness still remain to be connected.

**G1.2 critical-Hessian gate implemented:** on the complete position strip
`87/100≤u≤1`, rational circle supports give `p>3/2-u`,
`w-1-(6/7)u>3/70`, and the actual curvature bounds. The two critical
equations then imply all six normalized Hessian estimates, with
`det(Hess F)>(237/5000)k₁²>0`. The hypothesis permits positive defect.
`CriticalDifferentiation` identifies the formulas with derivatives of the
actual nested radicals, and `stationary_geometric_hessian_positive`
connects the result to the original broad stationary predicate. This
closes the quantitative Hessian gate on that strip; interiority, the
smooth minimizing-position function, and its global envelope argument
remain necessary before removing root localization.

**G1.2 actual envelope completed:** the fixed window `[87/100,11/10]`
has opposite endpoint derivative signs and positive `F_uu` throughout.
Its unique position minimum is interior and globally minimizes over the
full radical domain. A whole-interval tangent-cross-product inequality
excludes every critical position `u≥1`, without a defect-sign assumption.
`EnvelopeDifferentiation` applies the scalar implicit-function theorem
to the actual radical equation and proves both envelope derivatives.
The positive Hessian determinant now implies a strict local minimum at
every critical tilt. The intervening-maximum argument gives uniqueness
and global minimality over the closed tilt interval. Finite circle
inclusion also proves strict radius decrease of the actual envelope.
The final gate is connecting these results to the original stationary
coordinates and replacing the root-cover call; it remains active at this
checkpoint.

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

**Four whole-state exclusions integrated:** the full frame range implies
that a zero-quarter primary separator needs the corresponding primary
coordinate above one. A core arc has primary coordinate at most `7/12`.
At every angle a core center's projection is at most `5/6`, excluding
two further secondary-axis classes when the other transverse coordinate
has the incompatible sign. The active coverage dispatchers apply these
geometric obstructions across all ten affine tables, retaining every
original check on the remaining regions. They remove 77,480 row
constructors, with complete angle chains removed together. The shared
coarse table decreases from 129,031 to 115,463 rows, and the affine total
from 660,370 to 582,890. The state cover transports signed products, so
zero-coordinate and radial junctions retain their original coverage.
Historical research inputs are preserved. All four complete charged
stages still depend on their retained table domains.

**Fifth whole-state exclusion integrated:** on a quarter edge with two
core endpoints and opposite transverse signs `(+,-)`, the physical gap
cap `7/4` bounds the sum of their two core angles. The arctangent chord
then bounds their total transverse projection, excluding all four
original separating axes on both closed error-sign intervals. This
removes another 1,256 complete-chain affine rows. The active total is
581,634, a reduction of 78,736 from the historical 660,370; the shared
coarse table has 115,231 rows. No new angular subdivision is introduced.

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

**G3.2 third whole class implemented:** when both quarter directions are
forbidden, two weighted chains and the T circle force `b_A ≥ 81/100`.
A single supporting line of the A circle then excludes G-axis 0 over
the full tilt chart, independently of the E owner. Its final reserve
at `S ≤ 3/200` is `1/400`. This removes `Quarter000`–`Quarter003`:
four modules, 120 quartics, and 5,172 generated lines. The cumulative
owner/tilt removal is 46 modules, 1,218 quartics, 6,090 Bernstein checks,
and 52,944 lines. The 20 remaining quarter patterns have a direct
five-direction-pair selector with four E choices each. The 15 mixed
patterns and 41 positive tilt bundles remain active.

**G3.2 D-direction capture completed:** a forbidden D separator forces
`a_E≥39/40`. Every E axis then excludes `sin(t)≤-9/20`. On the remaining
arc, the large A transverse coordinate excludes G-axis 3 directly and
G-axis 1 by four E-axis arguments: two H-circle supports and two
telescoping chains. Their post-error reserves are respectively
`1423/10000`, `1423/10000`, `143/800`, and `113/400`.
`D_quarter_owners` now captures every feasible D axis geometrically,
including axis ties, before any owner-table lookup. This removes
`Quarter012`–`Quarter015` and `Quarter036`–`Quarter039`, eight modules
and 240 quartics. Cumulative owner/tilt removal is 54 modules,
1,458 quartics, 7,290 Bernstein coefficient checks, 63,288 generated
lines, and 4,250,177 source bytes. The remaining quarter family has
12 patterns and 465 rows; mixed has 15 patterns and 729 rows; positive
tilt has 41 bundles and 861 rows. Both owner completeness proofs now
use explicit selectors for their varying axes instead of enumerating
all functions `Fin 7 → Fin 4`.

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
have been removed; this first checkpoint leaves 240 common declarations.
See
[`CORE_WORD_GEOMETRY.md`](CORE_WORD_GEOMETRY.md).

**G4.4 four separator classes integrated in every word:** the same
primary and secondary core obstructions apply to an arbitrary quarter
lift before candidate capture. `original_not_core_excluded` proves that
the original feasible axis avoids those semantic classes, preserving
zero-coordinate cases. Another 424 individual recursive declarations
have been removed: 40 common, 192 short-word, and 192 second-word cases.
The word layer now contains 1,184 individual finite decisions instead
of 1,800: 200 common and 492 for each wrong word. Every retained
individual certificate statement and every role label is unchanged.

**G4.5 opposite-sign core quarter class integrated:** the same fifth
geometric class applies to arbitrary quarter lifts using the original
physical gaps. It removes 64 more wrong-word declarations, 32 per
family, leaving 1,120 individual declarations: 200 common and 460 for
each wrong word. The cumulative reduction is 680 of the original 1,800.
All retained statements are unchanged; the remaining decisions are
explicit dependencies, not discharged by this exclusion.

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
