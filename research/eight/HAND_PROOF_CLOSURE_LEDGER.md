# Hand-proof closure ledger

Initial reconciliation base: `6aa2ff635707ad2117048d6be983ef3fa124aa81`.
The ten-commit saved patch starts at `bd095cb3f2e8380233691bc396d7580df2529037`;
it is not the same history as the six intervening remote commits.
This note supplements both roadmaps without overwriting either history.
The outer-center continuation starts at
`6f75c7313b5a87e37dfb6fe00beacdfce87eca6c`.

## Fixed target

Let R8 be the attained least radius for eight interior-disjoint unit squares.
Let Rhat be the unique stationary five-corner radius selected in
HUMAN_FAMILY_CLOSURE.md. The existing construction gives R8 <= Rhat.
The missing assertion is R8 >= Rhat, not existence of another stationary
configuration and not a definition of Rhat by unrestricted minimization.

Computer calculations may discover or test identities, inequalities, and
counterexamples. A claimed theorem must have a written argument covering
its full stated domain. No finite sample closes a case.

## Reconciliation and completed steps

HUMAN_CONTACT_COMPONENTS.md covers the principal connected-stress and
actual-component conclusions developed independently in the saved patch.
HUMAN_ACTUAL_BRIDGES.md additionally treats actual, not merely positive-weight,
bridges. HUMAN_CENTRAL_COMPACTNESS.md gives semicircle capacity and a uniform,
unspecified positive central core. HUMAN_CYCLE_BOUNDARY_COUNT.md forces an
interior square on an exterior five-cycle, but does not prove its degree two.

The saved three-square cap argument has been checked and integrated as
HUMAN_THREE_SQUARE_CAP.md. It proves R^2>=(h+1)^2+9/4 for 0<=h<=1/3,
including the equality family. Together with the two-square cap theorem,
HUMAN_OPPOSITE_CAP_OCCUPANCY.md excludes opposite central-side populations
of three and two below q=2257/576. These are whole-square cap memberships,
not merely center positions.

Further completed hand-proof steps from that continuation are:

* HUMAN_BOUNDARY_VISIBILITY.md: a square with center norm at least one has
  a center ray missing every other circle-contact square. A component
  separated from zero solely by boundary squares and the circle cannot
  contain another whole unit. Empty pockets are not excluded.
* HUMAN_HIGH_SLICE_BOUND.md: for h>=1/10 and 63/100<=d<=71/100, a square
  tangent to x=h whose chord at x=h+1/2 is wholly above y=d has a vertex
  of squared norm greater than 1+(d+1)^2. Derivative signs and concavity
  cover the full orientation range.
* HUMAN_OUTER_INTERIOR_TRANSMITTER.md: in a minimum-contact radius minimizer
  with sqrt(2)+1/2<R<=sqrt(9789)/50, a nonisolated circle-free square at
  distance greater than sqrt(R^2-1)-1 has exactly two actual neighbors,
  on opposite sides perpendicular to its nearest-point side. This excludes
  extra zero-weight actual contacts. The near-distance case is not covered.

## New outer-center reduction

HUMAN_OUTER_CENTER_VISIBILITY.md proves the following for R<=2, without
requiring circle contact. Call a square outer if its center norm is at
least one. Its entire positive center ray misses every other outer square.
Moreover the segment from zero to any square center misses every different
outer square. The proof uses the exact farthest-vertex bound, the relation
between the two coordinate widths and the relative frame width, and two
explicit polynomial sign identities. All four separating axes are excluded
in the hypothetical ray-intersection case.

It follows that actual outer contacts occur only between consecutive outer
center directions. An outer contact cycle must use all outer squares;
its contact polygon winds once about every noncycle unit's open interior.
This statement is about the actual-contact graph, without choosing stress.

HUMAN_OUTER_GRAPH_REDUCTION.md combines this result with the existing chord
area bound. The induced outer graph is either a disjoint union of paths
and isolated vertices or a full cycle of six or seven squares. A six-cycle
encloses the remaining two units, and a seven-cycle encloses C. In a
minimum-contact radius minimizer every nontrivial outer path has inner
neighbors at both ends. All inner squares, meaning center norm below one,
are strictly inside the containing circle.

In particular every exterior actual five-cycle has a noncentral vertex S
with |p_S|<1 and dist(0,S)<1/2. This strengthens the earlier circle-free
vertex conclusion, but it does not give degree two. It forces a genuine
near-center case: sqrt(R^2-1)-1>1/2 in the relevant radius interval, so the
outer-distance transmitter theorem cannot be applied to this guaranteed
vertex. A short all-outer cycle also cannot be a proper part of a longer
induced outer cycle; a subgraph of a simple cycle has no proper cycle.

## Parallel endpoint completed independently

HUMAN_PARALLEL_EIGHT_OPTIMUM.md proves that every packing of eight parallel
unit squares satisfies q>=2257/576 and gives an equality construction.
The lower bound does not assume a contact graph or a column arrangement.
After the analytic central theorem, classifying the seven other centers
by which coordinate axes their squares cross leaves exactly two occupancy
patterns. Coordinate disjointness reduces each to four disk vertices with
opposite spans three and two, and cross spans three. Reflection and convex
averaging give sqrt(q-1)+sqrt(q-9/4)>=3, hence the exact bound.

This handles a complete restricted case, not a normalization of arbitrary
orientations. The tilted sharp construction lies strictly below that value,
so proving all eight frames parallel would not be a valid route to equality.

## Atomic implications

| ID | Claim required | Status |
| --- | --- | --- |
| A1 | Prove the three-square cap bound and its equality cases. | Complete; HUMAN_THREE_SQUARE_CAP.md |
| A2 | Combine the opposite three- and two-square cap bounds. | Complete; HUMAN_OPPOSITE_CAP_OCCUPANCY.md |
| B1 | Define whole-square side memberships and genuine corner exceptions, retaining overlapping memberships. | Existing definitions; not a global classification |
| B2 | Couple corner exceptions to the adjacent side populations. | Open |
| B3 | Obtain the forbidden 3+2 occupancy, the five-corner chain, or a sharp alternative in every surviving occupancy. | Open |
| C0 | Exclude a whole unit in a pocket separated from zero only by circle-contact squares. | Complete; HUMAN_BOUNDARY_VISIBILITY.md |
| C1a | Exclude extra neighbors of a circle-free cycle vertex above the specified outer-distance threshold. | Complete; HUMAN_OUTER_INTERIOR_TRANSMITTER.md |
| C1b | Handle a circle-free cycle vertex at distance at most sqrt(R^2-1)-1. | Open; a vertex with distance below 1/2 is now forced on any exterior five-cycle |
| C1 | Account jointly for an exterior five-cycle, its near-center vertices, and its two unused exterior units. | Open |
| C2 | Account for an exterior six-cycle and its unused exterior unit. | Open |
| C3 | Obtain the sharp obstruction for a seven-square exterior cycle. | Open |
| D1 | Treat central stress degree two in its side and diagonal forms, retaining zero-weight contacts. | Partial results only |
| D2 | Treat central stress degree at least three by collective motion or a sharp inequality. | Open |
| E1 | Under the twin hypothesis, place all four remaining squares. | Open |
| E2 | Obtain both oblique inequalities with compatible P1,P4,P5 and one common frame. | Open |
| P1 | Prove the complete parallel-frame eight-square optimum. | Complete; HUMAN_PARALLEL_EIGHT_OPTIMUM.md |
| R1 | Prove private center rays for all center-norm-at-least-one squares. | Complete; HUMAN_OUTER_CENTER_VISIBILITY.md |
| R2 | Reduce the induced outer graph to paths or a six-/seven-cycle, placing all noncycle units. | Complete; HUMAN_OUTER_GRAPH_REDUCTION.md |
| R3 | Force a vertex with center norm below one on every exterior five-cycle. | Complete; HUMAN_OUTER_GRAPH_REDUCTION.md, section 4 |
| R4 | Prove the sharp radius bound for a six-outer cycle enclosing two inner units. | Open |
| R5 | Prove the sharp bound for a seven-outer cycle enclosing C, retaining possible contacts with C. | Open |
| R6 | Prove the sharp bound for outer paths with inner attachments and any isolated outer units. | Open |
| F1 | Apply the conditional five-corner theorem only after its five hypotheses are established, or prove a sharp alternative. | Pending a complete global route |
| F2 | Combine the unrestricted lower bound with the exact construction. | Pending F1 |

B, C/D, E, and R are alternative or overlapping routes. The three cases
R4--R6 exhaust the new outer-graph reduction; their sharp estimates have
not been proved. Connectedness, a near-center cycle vertex, or a moment
circulation is not a substitute for F1.

## Computational checks and limits

Symbolic calculations checked the displayed sign identities and derivatives
used in the new analytical arguments. Fixed-separating-branch constrained
optimizations were also used to test candidate seven-square rings and
possible geometric shortcuts. They neither exhaust the allowed branches
nor certify a global minimum. Small negative separation residuals are not
accepted as improved packings. None of these optimization outputs appears
as a premise in a claimed hand proof.

## Exact current status

The unconditional construction R8<=Rhat and the sharp conditional family
optimization are available. The unrestricted reverse inequality is not yet
derived. The outer-graph reduction and the parallel endpoint theorem are
additional proved steps, not a declaration of closure.

The remaining global argument must handle the long outer cycles and the
inner attachments, including the forced near vertex in the five-cycle case,
or replace that analysis by an inequality valid for all eight-square
packings. No square is moved, assigned to a cap, or declared parallel merely
to make the desired five-corner hypotheses true.

## Publication rule

Commit reviewable mathematical results and corrections with [skip ci].
Verify the remote commit after writing. Keep all changes in research/eight/.
No Lean proof is attempted. Closure will be recorded only when F1 and F2
have complete hand proofs; this ledger does not claim them.


## 2026-10-11: sharp outer-pair sector theorem and limitations

HUMAN_SHARP_OUTER_PAIR_SECTOR.md now supplies a complete hand proof that at
squared radius `q0=5/2+sqrt(2)`, every unit square whose center norm is at
least one and whose center direction lies within pi/8 of a chosen bisector
contains the fixed point at distance `(2+sqrt(2))/3` on that bisector.
The two equality squares are axis parallel, with centers
`((1+sqrt(2))/2, +/-1/2)`; they share a side. Consequently two disjoint
outer-center squares have angular gap at least pi/4 at `q<=q0`, and
strictly greater than pi/4 at `q<q0`. The proof handles the entire
orientation and center-radius domain using exact support inequalities,
a monotone longitudinal comparison, and strict transverse concavity.

The result has **not** closed the n=8 lower bound: the exact search ceiling
`9789/2500` is above q0, and the construction supplied in
HUMAN_OUTER_ANGLE_COUNTEREXAMPLE.md shows a pi/4 touching pair already fits
at q0. A separate rational pair even has center gap strictly below pi/4
within the radius-two disk. Thus a universal strict pi/4 gap may not be
used at the eight-square search ceiling.

HUMAN_EXTERIOR_CENTER_ORDER.md gives the weaker angular gap for *all*
exterior centers: greater than pi/8 for R<=2, improved to greater than
pi/7 at q<=9789/2500. This makes their labeled cyclic order robust under
continuous packing deformations, but not their contact adjacency.

The genuinely open unrestricted cases remain the seven-outer contact
cycle and the outer paths with inner attachments (as in
HUMAN_OUTER_GRAPH_REDUCTION.md). The new pair theorem does not assign
the exterior-owned corner separators, exclude the near-center jam
branch, produce the twin motif, or imply the five-corner projected chain.
No equality `R8=Rhat` is claimed without those global steps.


## Further checked hand results in the latest continuation

* HUMAN_STABLE_OUTER_ANGLE.md: at q<=9789/2500, any two
  interior-disjoint unit squares with center norms at least one have
  angular center gap strictly larger than pi/4-1/500. This uses
  uniform interior slack of 1/1500 in the fixed-point pair theorem
  and a radial perturbation shorter than 7/15000; no assumed contact
  axis or sampled inequality is involved.
* HUMAN_CONTACT_ANGLE_UPPER.md: when two such outer squares actually
  touch, their center gap is at most pi/2; equality is uniquely the
  parallel corner-contact pair with centers (1,0),(0,1), up to
  rotation. Hence an actual outer contact in the sharp search domain
  has gap in (pi/4-1/500, pi/2].
* HUMAN_SEVENFOLD_RING_BOUND.md: seven pairwise disjoint squares which
  are rotated copies of one square under exact sevenfold rotational
  symmetry about the containing disk origin require R>2. The proof
  reduces the full frame interval to two rationally bounded regions.
  It **does not** symmetrize an arbitrary seven-square ring.
* RATIONAL_SEVEN_OUTER_COUNTEREXAMPLE.md: an explicit eight-square
  packing of squared radius 397/100<4 has a central square and
  **all seven** exterior centers at norm greater than one. All
  positions and orthonormal frames are rational; every pair has a
  displayed positive separating margin, and every farthest vertex
  has squared norm below 397/100. Thus a general assertion that
  R<2 forces an additional inner-center square is false, though
  the witness radius is above the sharp candidate.
* HUMAN_NO_LINEAR_TILT_POTENTIAL.md: two exact disjoint outer-square
  pairs inside q0=5/2+sqrt(2) prove that no constant k can make
  delta+k*(alpha_target-alpha_source)>=2*pi/7 valid for **every**
  outer pair. The first touching pair forces k<=-1/7 and the second,
  with strictly interior unambiguous frame tilts, violates the
  inequality for every such k. Nonlinear, type-sensitive, and odd
  seven-cycle potentials are not excluded.

The exact unresolved implication is still
`R8>=Rhat`. A general seven-outer actual-contact cycle is **not**
a sevenfold symmetric orbit; the parallel/symmetric hand bounds do
not apply to it. The other main branch, outer paths connected
through inner attachments, contains the tilted candidate itself
and cannot be discarded. No displayed global inequality yet
classifies those attachments or forces the five-corner chain.


## Latest pair-radius elimination and the odd-cycle obstruction

HUMAN_RADIAL_ENDPOINT_PAIR.md proves an exact pairwise existential
reduction: at fixed two center directions and two frames, disjointness
for **some** permitted center norms >=1 occurs if and only if it occurs
at at least one of the four radial corner pairs
`(1,1),(1,m_j),(m_i,1),(m_i,m_j)`.
This follows because every signed separating-axis projection gap is
affine in the two center radii. It reduces the pair feasibility test
to 16 unsigned / 32 signed trigonometric branches in the two relative
tilts and one center-angle gap. It does **not** allow selecting the
radial corners simultaneously for all seven squares or substituting
endpoint-selected state potentials for the original center radii.

HUMAN_NO_UNIFORM_STATE_POTENTIAL.md strengthens the previous affine
negative result: two explicitly separated outer pairs inside
q_plus=9789/2500, with the same two rotation-invariant states
`(r,alpha)` in opposite order, each have gap
`delta=arccos(5/8)<2*pi/7`. Every potential
`psi(r,alpha)`, even discontinuous or nonlinear, cancels around
this exact two-step cycle. Thus a **uniform** 2*pi/7 pair gap
with one state potential is impossible. A seven-step odd-cycle
budget with nonuniform type edge weights remains a genuine option.

Exploratory finite-state min-plus and LP calculations suggest a
positive seven-step reserve for a *selected finite sample* of
outer states. That is neither a continuum certificate nor a
proof for interior center radii; separate pairwise endpoint
choices need not be jointly consistent. No such numerical
result is a premise of the claimed hand lemmas.

**Global target still open:** the unrestricted lower bound
`R8>=Rhat`. The seven-outer-cycle and outer paths with
near-center attachments have not been converted into the five-corner
chain or an equally sharp alternative inequality. No hand proof of
the unrestricted n=8 equality is claimed.
