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
commit contains 253 repository modules, of which 236 are n=8 modules. It
imports all ten affine tables, totaling 660,370 rows:

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

At the starting commit, the root-localization module calls `CompactRootCover.certify` with
depth 48. Its retained diagnostic reports 22,601 visited nodes; that number
is not a measured Lean cost. Owner capture imports 48 quarter bundles,
15 mixed bundles and 59 tilt bundles, with 21 alternatives per tilt bundle.
The four-type pair and wrong-word layers also call recursive `RealBox`
searches. They must not be overlooked when assessing future compilation.

The reproducible source inventory is
[`table_dependencies.py`](table_dependencies.py), with its initial report
in [`TABLE_DEPENDENCIES_BASELINE.json`](TABLE_DEPENDENCIES_BASELINE.json).
It reads imports and declarations without expanding or evaluating a table.

The inventory was corrected during this execution to follow `public meta
import` and count every literal `certify` occurrence, including individual
word-certificate statements. The same revised script now reads the original
commit directly with `--revision`, so before/after counts are comparable.
The original word layer contains 1,800 individual certificate declarations;
its four-type pair layer contains 25 chart declarations. These counts are
distinct from recursion nodes and from definitions or proof references to
the checker. `--details` optionally lists all source occurrences; the
default report keeps compact per-module counts. No checker is evaluated.

## G1 — Replace stationary-root subdivision by family geometry: implemented

`GeometricStationary.stationary_chain_unique` now proves equality of any
two chains satisfying the original broad `Coordinates.IsStationary`
predicate. The active proof no longer imports or calls the root search.
The proof does not assume a local root box, a defect sign, envelope
regularity, a Hessian sign, or global minimality as an extra hypothesis.

The implementation follows six geometric steps:

1. `CircleConvexity` derives strict position convexity of the actual
   nested-radical defect on its complete closed radical domain, including
   comparison with radical endpoints.
2. `PositionLocalization` and `EnvelopePosition` give opposite derivative
   signs on the fixed window `[87/100,11/10]`. Its interior position root
   is the unique global minimum on the full radical domain. A single
   trial chain at `u=15/16` supplies the norm bound needed below, including
   at minima with positive defect.
3. `EnvelopeDifferentiation` applies the scalar implicit-function theorem
   to the actual position equation. Uniqueness identifies the smooth local
   root with the chosen minimizer. It proves `u'=-F_ut/F_uu`, `M'=F_t`,
   and the actual envelope's second derivative `M''=F_tt-F_ut^2/F_uu`.
4. `EnvelopeCriticalPosition` excludes critical positions `u>=1` by a
   whole-interval circle comparison. On `87/100<=u<=1`, six actual-chain
   estimates in `CriticalHessian` give
   `det(Hess F)>(237/5000)*k1^2>0`. Every critical envelope point is
   therefore a strict local minimum, regardless of its defect sign.
   An intervening interior maximum excludes two critical points and gives
   global minimality over the complete closed tilt interval.
5. `RadiusMonotonicity` uses finite circle inclusion to prove
   `M(q1,t)<M(q0,t)-(q1-q0)` when `q0<q1`. Two stationary zeros at
   different radii would contradict the global angular lower bounds.
6. The exact angle `2*atan(z)`, critical-point uniqueness, strict position
   convexity, and the four signed circle radicals identify all coordinates.
   `Stationary.stationary_unique` applies this theorem to `sharpData`;
   `stationary_local` then follows from equality with that witness.

`Generated.StationaryLocalization.lean` has been deleted. The unchanged
fixed-box enclosure routine has been extracted to `IntervalEnclosure`,
so neither `CompactRootCover` nor `RootCover` remains in the public entry
point's import closure. The historical search is available only through
the stationary generator's explicit `--legacy-root-cover` option.

**Retained finite work:** the analytic witness and numerical brackets use
49 local formula certificates. The separate adaptive curve estimates use
256 indices and 21 scalar bounds per index, or 5,376 fixed-box checks.
Their removal is not claimed. All replacement Lean remains uncompiled.
Details and the positive-defect coverage argument are in
[`STATIONARY_GEOMETRY.md`](STATIONARY_GEOMETRY.md).

## G2 — Remove angular subdivisions by exact contact geometry: partly implemented

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

**Whole coarse core/core cost implemented:** the labels selected by the
original 462-arc cover remain unchanged. On each of its 124 core arcs,
arctangent curvature and endpoint bounds control the exact same signed
marker throughout the closed interval; corner labels use monotonicity.
The finite marker obligations are 496 rational endpoint inequalities,
plus seven scalar budgets. Center separation then supplies the complete
two-state core/core inequality, including shared chart endpoints.
`GeometricCoreCoverage` handles that branch before row dispatch. This
removes another 4,806 rows, leaving **110,425 coarse rows and 576,828
active affine rows in total**, a cumulative reduction of **83,542**.
All remaining coarse rows have an outer endpoint. The D-positive marker
keeps its actual upper bound `643/1000`; its impossible outgoing core
pair is excluded geometrically rather than by tightening that bound.

## G3 — Eliminate owner and tilt regions by circle stresses: partly implemented

Eliminate slider coordinates symbolically from the original separating
inequalities, then use nonnegative circle stress weights. The total frame
error is spent as one shared budget. Every originally feasible axis and
closed boundary remains covered until a geometric contradiction excludes it.

The following entire classes are now handled before finite dispatch:

| Geometric class | Argument | Deleted modules | Deleted quartics |
|---|---|---:|---:|
| Nonpositive tilt, including zero | Four-circle stress on the complete half-chart, with reserve `34477/144000000` over `Q0` at `S<=1/1000`. | 18 | 378 |
| Intended B, forbidden D | `B→T→D→E` telescopes to `3-(3/2)S<=a_B+a_E`, contradicting containment at `S<=1/10`. | 16 | 480 |
| Forbidden B, G axis 2 | Rotated-corner support on `G→A→B→T`, with reserve `209/2500`. | 8 | 240 |
| Both B and D forbidden, G axis 0 | Two weighted chains force `b_A>=81/100`; one A-circle support gives reserve `1/400`. | 4 | 120 |
| Remaining forbidden D cases | Every E axis excludes the long negative arc; two circle supports and two chains exclude the remaining G axes. | 8 | 240 |
| Forbidden B, G axis 3 | H-circle geometry forces `sin(t)>-3/8`; one four-circle stress covers all E axes with final reserve `7/500`. | 4 | 120 |
| **Total** | | **58** | **1,578** |

`D_quarter_owners` now captures every originally feasible D axis by
geometry, including ties, without a quarter/mixed table lookup. Quarter
completeness uses eight explicit vectors, and mixed completeness uses a
direct 15-vector selector; neither enumerates functions `Fin 7 → Fin 4`.
The generator and manifests omit exactly the removed geometric classes.

The cumulative deletion is **7,890 Bernstein coefficient checks,
68,460 generated lines, and 4,593,946 source bytes**. The remaining
quarter family has 8 patterns and 345 rows; mixed has 15 patterns and
729 rows; positive tilt has 41 bundles and 861 rows.

Remaining work is to eliminate the other B/G/E owner classes and both
positive tilt tails under their original mismatch assumptions. A stress
sharp only at the optimum cannot be assumed to stay useful on a whole
tail. Detailed hypotheses, weights, identities, boundary coverage, and
source-only checks are in [`OWNER_GEOMETRY.md`](OWNER_GEOMETRY.md).

## G4 — Replace finite word and pair searches: partly implemented

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
