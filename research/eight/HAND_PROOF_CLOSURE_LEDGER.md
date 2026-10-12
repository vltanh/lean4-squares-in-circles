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


## New unconditional outer-center quadrant restriction

HUMAN_OUTER_QUADRANT_CAPACITY.md now proves, entirely by hand,
that below q<=9789/2500 no three packed unit squares
with centers of norm at least one can have all three
center directions inside any angular sector of width
`pi/2+1/40` (the initial proof gave `pi/2+1/120` and the sharpened section 6 proves this stronger bound). The proof combines the established
sharp q0=5/2+sqrt(2) common-point theorem and
its stable q_plus perturbation bound with a new
**two-point interior-margin lemma**: for an outer
square centered on the positive axis and fitting
at q0, one of the two points at angles +/-pi/8
and radius (2+sqrt(2))/3 lies inside the square
with an explicit full disk margin 1/30 (after the sharpened bounds in section 6).
The full continuous angle and radius domains are
handled by the derivative bound already proved
for the longitudinal coordinate, Cauchy--Schwarz,
and exact rational slack comparisons.

Thus seven outer center directions, if present,
have 2,2,2,1 populations in any generic four
quadrants, and any closed sector of angular width
pi/2+1/40 has capacity two. Every generic diameter divides seven outer centers into 3 and 4. This is a
**center-ray** restriction. It does not imply
whole-square membership in the central side caps
and does not exclude the seven-outer-cycle case.

HUMAN_OUTER_RADIALIZATION_COUNTEREXAMPLE.md
supplies two rational strictly disjoint outer
squares at q<9789/2500 which overlap after
radially translating one outward, while both
remain within that same disk. Thus global
outward radialization is invalid even when
all moved centers are outer. This does not
invalidate the pair-only existential radial
endpoint lemma.

The missing unrestricted inference remains
`R8>=Rhat`. Neither the new quadrant bound
nor the failed radialization shortcut proves the
five-corner inequalities or classifies the
remaining outer-path inner attachments.


## 2026-10-11: central-fan and opposite-separator hand lemmas

HUMAN_SEVEN_OUTER_FAN_GRAPH.md gives a complete actual-contact
classification in the case where all seven noncentral centers have
norm at least one, for a radius minimizer selected with minimum
actual contact count:

* The induced outer graph is the **full seven-cycle**, with
  possible contacts/spokes to the central square C; the
  central square is either isolated or has at least two
  distinct spokes, never exactly one.
* Otherwise the outer graph has **at least one nontrivial path**
  and possibly other paths/isolates; both endpoints of every
  nontrivial path touch C. Every actual contact cycle must
  pass through C and follow a subpath of one outer path.
  There can be at most two outer vertices isolated in the
  induced graph yet attached to C as leaves; their radial
  directions are perpendicular and their positions are
  exactly those of the previous leaf theorem. Globally
  isolated squares remain possible.

The proof reuses the already established outer-ray adjacency,
actual-leaf theorem, absence of nontrivial contact trees,
and uniqueness of the nontrivial actual-contact component.
It does **not** equate actual and stressed contacts.

HUMAN_OPPOSITE_CENTRAL_ANGLE.md proves an arbitrary-frame
three-square inequality: when A and B lie beyond opposite
central-square supports in direction n and its opposite,
their center rays satisfy

    cos(delta) < 1-1250*(1+W)^2/5041,
    W=|n dot e_C|+|n dot f_C|, 1<=W<=sqrt(2),

throughout squared radius q<=9789/2500. In particular
delta>pi/2-1/100; a 45-degree central separator gives
delta>5*pi/8. This is a quantitative obstruction for the
two-opposing-contact transmission branch but does not
force that branch to arise in a minimizer.

**Pairwise-cyclic numerical exploration (not a proof).**
A trial seven-step angle budget which independently optimizes
both endpoint radii *for each pair* can sum below 2*pi.
When each state instead shares its radius across its two
neighbors, finite-state sampled budgets become more restrictive,
but the continuum and the nonadjacent constraints remain
uncertified. Thus neither calculation may exclude the
seven-outer full-cycle case. A correct proof must retain
radial compatibility around the entire seven-cycle, and
must separately handle the central fan of outer paths.

**Global status:** R8<=Rhat remains proved by the exact
construction, and the sharp conditional five-corner
optimum is established. No argument in these new notes
proves the necessary unrestricted reverse inequality.


## New two-force closure and stressed-ring flux structure

HUMAN_TWO_FORCE_SQUARE_CLASSIFICATION.md proves a true
**two-force member** theorem for any circle-free square:
exactly two nonzero contact resultants must act along
the same line and at support points separated by
`2*h_S(n)*n`. For a unit square this forces the
normal to be one of its four side directions or four
vertex diagonals. All strictly intermediate vertex
normal-cone directions are excluded by force **and
moment** balance, not by selecting one favorite
separating axis. A diagonal two-force square in a
minimum-contact representative must have an additional
**zero-weight actual neighbor**, since a strictly
interior square with actual degree two is aligned to
one of its sides (HUMAN_CYCLE_ANALYSIS.md section 8).

HUMAN_OPPOSITE_CENTRAL_ANGLE.md quantifies opposite
central separator angles: two opposing neighbors have
center-ray gap >pi/2-1/100, or >5*pi/8 for an exact
central diagonal. This is an analytical three-square
projection bound valid at q<=9789/2500.

HUMAN_SEVEN_OUTER_FLUX.md describes the stressed
seven-outer actual-contact ring. With no positive
central spoke, **all seven ring edges carry positive
stress and the same positive directed contact-moment
flux**. With exactly two central stressed spokes,
the two positive central forces are collinear and
the seven ring moments have only **two constant
plateaus**, one on each arc between the spokes.
At least one plateau is positive, by the absence
of stress tree components. Thus the positive ring
support is either the full ring or one contiguous
arc. This retains the distinction between actual
and positive-stress edges.

**Remaining work.** Neither the two-force direction
classification nor the ring-flux plateau identity
proves that arbitrary minimizers have central
stress degree <=2. Even under those hypotheses the
sharp geometric inequality comparing the ring or
central-fan path case with the five-corner family
has not been proved. The cases with >=3 central
forces and those with one or more additional inner
square centers remain. The global reverse bound
`R8>=Rhat` is therefore explicitly **OPEN**.


## New exact near-sharp all-outer-center construction

RATIONAL_NEAR_SHARP_SEVEN_OUTER.md records eight **rational**
interior-disjoint unit squares at squared radius `979/250=3.916`
with a central square and seven other square centers of norm
greater than one. Its proof supplies all eight rational
orthonormal frames, eight farthest-vertex inequalities and
one strictly positive rational separating-line witness for
every one of the 28 unordered pairs. The seven consecutive
outer pairs have verified strict margins exceeding
`19/1000000`; all other pairs have margins over
`1/1000`. This replaces the earlier weaker all-outer
example at squared radius `397/100` with a near-candidate
construction.

This example is *above* the conjectured exact candidate
squared radius (`3.915534...`) and gives no improved
upper bound for the unrestricted problem. But it **refutes**
any proposed proof route claiming that seven outer centers
alone require squared radius at least, for example,
`3.92` or `4`. The complete seven-outer-center case
must be treated almost as sharply as the actual candidate,
and cannot be eliminated using a coarse universal radius
estimate or just the existing quadrant capacity bounds.

Unlike the seven-outer contact-cycle branch, the
rational example has **strict** pair gaps. It therefore
does not settle the optimal radius of a full ring of
actual contacts, nor the outer-path-with-inner-attachment
cases. The remaining unrestricted implication
`R8>=Rhat` is still open.


## Stronger exact result: the five-corner optimum itself has seven outer centers

ANALYTIC_SHARP_SEVEN_OUTER_CONSTRUCTION.md proves, from
the whole-domain analytic inequalities already established
in ANALYTIC_EXACT_CONSTRUCTION.md, that the `G` square
may slide through the entire interval

    -(k1-1)/2 <= eta <= 0

without increasing the exact conditional radius `Rhat`
or losing any of the 28 pair separations. At the
negative endpoint the center of G satisfies
`f dot G=1-k2-k1/2<-1`; the other six
noncentral centers are also strictly outer.
The proof uses only `k1^2+k2^2=q`,
`(79/40)^2<q<9789/2500`, and elementary
inequalities `1<k1<38/25`, `k2<2`,
not a tiny numerical root box.

**This supersedes the strategic force of the previous
q=3.916 all-outer-center rational witness.**
That rational witness remains a valid easy arithmetic
example, but now an exact eight-square packing of
radius **Rhat itself** has seven outer centers.
Accordingly **neither all-seven-outer center geometry
nor the central-fan outer-path branch may be excluded
outright at the sharp target radius**. Any lower-bound
argument asserting that every packing at or below
Rhat must contain a noncentral center of norm less
than one is false.

The seven-outer **full actual-contact ring** remains
a distinct case: the sharp construction with seven
outer centers need not be such a ring. The crucial
open step is to derive the five-corner projected
obstruction, or an equally sharp inequality, in
the centrally connected outer-path configuration
which the exact candidate now demonstrably realizes.

The user-requested unrestricted equality R8=Rhat
has **not** been proved by this new construction.


## Sharp seven-outer actual-contact ring: an equality construction, not an impossible branch

Section 8 of ANALYTIC_SHARP_SEVEN_OUTER_CONSTRUCTION.md
strengthens the earlier outer-center result:
the exact five-corner candidate itself, at
**exactly Rhat**, admits seven outer centers
forming an **actual-contact seven-cycle**

    A-B-T-D-E-H-G-A,

together with central spokes C-B and C-D.
Every shared boundary point is checked
analytically. The two rotated vertex-to-edge
contacts E-H and G-A are not inferred just
from equal support projections: the note proves
their support vertices lie strictly within
the corresponding edge intervals. The
proof uses the already established analytical
stationary bounds `u>87/100`, `v<589/1000`
from HUMAN_FAMILY_CLOSURE.md, and no tiny
root-isolation box.

This **falsifies** any proposed structural lemma
that would exclude the full seven-outer
actual-contact ring at radius <=Rhat, or
that would force a *noncentral* inner center
in every radius-Rhat packing. Both the
full-seven-outer-ring and the central-fan
path branches remain potential equality
cases. The ring's sharp lower inequality
must permit the explicit candidate above.

It also explains why the seven-outer
search cannot be separated from the
central obstacle: the candidate seven-cycle
has two actual spokes to the central square.
When these spokes carry nonzero stress,
the uniform-flux hypothesis of the
stress-free ring lemma fails; its flux
plateau analysis is conditional, not a
universal obstruction.

**Global proof still open:** the construction
yields R8<=Rhat only. An arbitrary eight-square
minimizer has not been reduced to the
five-corner inequality or an equally
sharp alternative.


## Sharp conditional chain with only two aligned end frames

HUMAN_TWO_ALIGNED_ENDS.md supplies a complete hand proof
of a **strictly broader structural implication** than the
former six-common-frame/tilted-pair description.
Only the end squares A and E must share one
axis-parallel frame. The four other chain squares
B,D,G,H may have *arbitrary orientations*.
Given the three directed outer-chain support
separators (including an intervening square
contributing one unit of width between B and D),
and the three coherent oblique separator
directions along e,e,f, the five disk points
satisfying the exact five-corner obstruction
exist. The result immediately yields R>=Rhat
under these **explicit conditional hypotheses**.

The key universal lemma constructs four canonical
points inside every rotated unit square, at
offsets `(1-L/2)(+/-a+/-b)` from its center,
where `L=2h_S(a)=2h_S(b)`. Membership follows
from `(1-L/2)L=1/2-(L-1)^2/2<=1/2`.
This handles rotated B,D and gives a single
oblique witness P5 inside an arbitrarily
rotated H. The inflated projected supports
of rotated middle squares exactly cancel
the shorter canonical-corner displacements.
Neither G nor H needs a frame aligned with e,f.

The remaining global theorem must **force
two appropriate aligned end squares and the
six directed separator inequalities**, or
prove sharp inequalities for other configurations.
It is not legitimate to infer these axis
choices merely from an actual-contact edge,
nor to declare all frames parallel.
Thus unrestricted R8>=Rhat remains OPEN.


## Orientation defects, anchored end uniqueness, and equality recovery

HUMAN_ROTATED_END_CORNER_DEFECTS.md proves two **sharp
whole-orientation point-selection inequalities** for a
unit square whose chosen point must lie in the bottom
unit-height cap of its own projected support strip.
For `z=tan(t/2)`, the best universal sums of
oblique support plus cap-point projection are
`1-z` along e and `2z/(1+z)` along f.
Their exact losses relative to aligned corners
are `epsilon_A=sin(t)*(1-sin(t))/(1+cos(t))`
and `epsilon_E=(1-cos(t))*(1-sin(t))/cos(t)`.
A piecewise trigonometric hand proof includes
both signed orientations, concavity/monotonicity,
and explicit sharpness examples.

Under the six directed separators of the
two-aligned-end conditional theorem, but with
**all six frames arbitrary**, the resulting
five-point chain retains its exact 2,3,2
first-three spans and has weakened oblique
thresholds `3-z` and `1+2z/(1+z)`.
The note also gives an exact orientation-sensitive
separator-slack sufficient criterion restoring
the sharp family lower bound. More generally,
translating only P5 by the two remaining deficits
proves the robust conditional inequality
`R>=Rhat-sqrt(a^2+b^2)`.
This is a quantified obstruction to simply
erasing the two end-alignment assumptions.

HUMAN_ANCHORED_END_RIGIDITY.md proves that
the candidate's right-hand end square A is
**globally unique in position and frame**
when its two neighbor support thresholds
are held fixed and the disk radius is
unchanged. The hand proof expresses its
circle radial normal as a positive
combination of the two separator axes.
A weighted sum of three square support
functions is strictly concave between
only three angular breakpoints; exact
values at those breakpoints force the
unique standard frame and then the center.
It uses only broad analytical family
bounds, not a tiny root box. Neighbor
positions/directions are **assumed fixed**;
collective rearrangements are not excluded.

HUMAN_TWO_END_EQUALITY_RIGIDITY.md now
derives the equality cases of the enlarged
two-aligned-end theorem: at exactly Rhat,
the five witness points must be *on the
disk circle* and all five projected
inequalities tight. The canonical points
in arbitrary B,D,H are strictly interior
to those squares unless their projected
width is one. Hence equality forces
B,D parallel to A,E and H parallel
to the oblique e,f frame. Equality of
the two e separators also gives
`h_G(e)=1/2`, forcing G parallel to H.
If a central square supplies the B-D
middle projected span, it too aligns
with A,E. Tight support projections
do not by themselves assert common
physical contact points.

**Still open globally:** none of these
conditional rigidity/equality theorems
forces the two end squares and six
directional separator hypotheses in
an arbitrary eight-square minimizer.
The unrestricted lower bound
`R8>=Rhat` has not been proved.


## Latest conditional progress: sharp orientation defects and equality reconstruction

HUMAN_ROTATED_END_CORNER_DEFECTS.md establishes sharp
analytical cap-point estimates for both arbitrarily
rotated **end** squares, as functions of tilt t:
`h_A(e)+e dot(X_+-p_A)>=1-tan(t/2)` and
`h_E(f)+f dot(X_--p_E)>=2*tan(t/2)/(1+tan(t/2))`.
The proof treats every orientation sign and the
entire interval `0<=t<=pi/4` by explicit
edge points, concavity, and monotonicity.
Both constants are sharp for square frame angle t.
The same note gives an exact orientation-sensitive
separator-slack criterion recovering R>=Rhat
with **no frame assumptions**, and a robust
quantitative bound
`R>=Rhat-sqrt(a^2+b^2)` when the two
remaining oblique deficits are a,b>=0.
All remain **conditional** on six coherent
directed separation inequalities.

HUMAN_ANCHORED_END_RIGIDITY.md proves the
candidate's right-hand end square A is the
unique unit square of **any orientation**
fitting the exact disk while preserving its
two fixed A-B and A-G directional support
thresholds. Its normalized radial vertex
normal has positive decomposition
`v=lambda*e-mu*b`, and the weighted
support width W(theta) is strictly concave
between three frame-angle breakpoints.
Three explicit positive comparisons at
the breakpoints give W(theta)>W(0)
unless theta=0, which then pins the center.
No root isolating box is needed. This is
not a simultaneous multi-square deformation
theorem because neighbor lines are fixed.

HUMAN_TWO_END_EQUALITY_RIGIDITY.md proves that
at **exactly** Rhat, any five-corner chain
extracted via the two-aligned-end theorem
has all five witness points on the disk
boundary and all five projection inequalities
tight. The constructed points in B,D,H
would lie strictly inside their square
interiors if their frames were rotated;
hence B,D are forced parallel to A,E and
H forced parallel to the oblique e,f frame.
The tight A-G-H chain forces
`h_G(e)=1/2`, so G also aligns with e,f.
Section 6 reconstructs the five *unique*
disk witness points and centers A,B,D,E,H
of the stationary exact family, and leaves
only `p_G=p_H+e+eta*f` as a genuine
one-dimensional G slider. Any intermediate
square providing B-D's two-unit horizontal
center span also aligns with A,E and has
the fixed horizontal center coordinate.

This is a genuine *equality rigidity*
theorem **inside the conditional branch**,
not a global n=8 uniqueness result.
The central missing obligation is still
to deduce the six directed separators and
the relevant two-end structure from an
arbitrary eight-square minimizer, or to
prove an equally sharp alternative.
`R8>=Rhat` remains OPEN.


## Current continuation: exact orientation compensation and a solved seven-ring separator branch

HUMAN_ROTATED_END_CORNER_DEFECTS.md proves the optimal
universal bottom-cap point projections for **any**
end-square orientations, with sharp shortfall
`epsilon_A(t)`, `epsilon_E(t)` relative to
the original five-corner thresholds.
If the two directed oblique separators have
additional projection slack covering the
orientation-specific losses, the sharp
five-corner radius bound follows with no
orientation hypotheses on any square.
With residual shortfalls `a,b>=0`, the
same point construction gives the robust
conditional bound
`R>=Rhat-sqrt(a^2+b^2)`.
It does not force the directed separators.

HUMAN_ANCHORED_END_RIGIDITY.md gives a
whole-orientation, unique-center theorem
for the candidate's right end square A
when two neighboring support thresholds
are held fixed. A weighted support
function of its free frame is strictly
concave between finitely many fixed
normal-alignment angles, and three
exact positive endpoint comparisons
force the horizontal/vertical frame
and the reference center. This does
not exclude collective rearrangements.

HUMAN_TWO_END_EQUALITY_RIGIDITY.md
establishes that in the enlarged
**two-aligned-end** five-corner branch,
equality at Rhat forces all five
constructed witness points to lie on
the container circle, all five
inequalities tight, B,D to share
the aligned end frame, and G,H to
share the oblique frame. It
reconstructs the five anchored
centers and the one-dimensional G
slider from the unique exact family.
An intervening middle-square frame
is also forced if its opposite
side projections supply the
B-D horizontal span.

HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md
now states a clean theorem using **seven
whole squares only**: if the seven
directed projected pair separators
of the candidate ring A-B-T-D-E-H-G-A
are justified and its end squares
A,E are aligned, then `R>=Rhat`,
even with independent arbitrary
orientations of the other five squares.
Equality forces every one of the
seven square frames into the candidate
two-frame pattern, fixes the five
outer support centers, and leaves
the legitimate G-transverse and
T-height sliders. The seventh T
square, rather than the central C,
supplies the B-D two-unit center
projection in this version. The
exact sharp construction realizes
the hypotheses, so the bound is
optimal **within that directed
separator class**.

HUMAN_FINITE_ORIENTATION_DUAL.md proves
that any nonnegative weighted sum of
unit-square support widths in *fixed*
directions is strictly concave between
finitely many side-normal alignment
angles. HUMAN_FINITE_DUAL_SEPARATOR_BOUND.md
combines that fact with the disk support
inequality to give a general
orientation-free dual radius lower
bound for **any fixed directed
separator graph**, requiring at most
degree+1 orientation checks per
square. It is an inner exact
reduction, not a classification of
which separators arbitrary packings use.

HUMAN_LEFT_END_FROZEN_DUAL_OBSTRUCTION.md
shows analytically why a naive
single-linear-dual closure fails
even in the candidate graph: at
the left end E, the weighted
radial-support sum with fixed
two separator normals is
**strictly lower** when E's frame
is rotated by t than when aligned,
for the exact family inequalities.
This refutes that frozen-support
certificate, not the full nonlinear
disk radius constraint or the
conjectured optimum.

**Remaining decisive global gate.**
Neither the seven-ring directed
separator class nor the anchored
dual assumes the orientation of
the other five squares, but both
still require the **appropriate
directed separator pattern and the
two aligned end squares**. Those
facts are not known to follow from
arbitrary eight-square nonoverlap
and disk containment. The other
contact patterns with inner square
attachments also remain. No
complete hand proof of
`R8>=Rhat` is available in this
ledger; the unrestricted
n=8 packing optimum remains OPEN.


## Boundary contact angular shadow: exact six-member winding obstruction

HUMAN_SIX_BOUNDARY_SHADOW.md proves the following
entire-orientation hand theorem:
every unit square **touching** a disk circle with

    R^2 >= 3841/1000

has a complete angular shadow (directions of its
points as seen from the origin) strictly smaller
than pi/3. Its proof reduces every square frame
to the maximum of two explicit angular widths,
then checks two rational tangent inequalities.
The difficult left-versus-bottom case reduces
to positivity of a quadratic
`62989404409 C^2-794438999000 CS+2524218152409 S^2`;
the discriminant criterion is the exact positive
integer identity

    4*62989404409*2524218152409
      -(794438999000)^2
      =4862668942395193285124 >0.

No numerical grid or root isolation is used.
The theorem works for all larger squared radii;
it does not require contact at a square vertex,
nor any common square frame.

Consequently, **at squared radius q>=3841/1000**,
no winding curve around the disk center can be
supported by at most six *circle-contact*
exterior squares; a k<=6 exterior winding
contact cycle must include a square strictly
inside the containing circle.

**This is conditional on q>=3841/1000.**
The purely analytical unconditional lower bound
in HUMAN_ANALYTIC_LOWER_BOUND.md is currently
`R8>sqrt(2)+1/2`, whose square is strictly
below 3841/1000. The earlier computed marker
certificate q>19/5 is also below that threshold
and is not an allowed hand-proof premise here.
One may not apply the new angular-shadow
theorem to a hypothetical smaller-radius
packing without independently proving
`q>=3841/1000` or separately handling
the smaller radius range.

**Crucial limitation:** this does not
force *two* circle-free squares on a
seven-square outer ring. Six boundary
squares have shadow total under 2pi,
but the seventh (circle-free) square
could cover the remaining directions.
The seven-outer full-contact ring is
already a sharp candidate equality case
and must not be excluded merely
by a shadow count.

The unrestricted lower bound
`R8>=Rhat` remains OPEN.


## Unrestricted-frame improvement of the parallel obstruction

HUMAN_SEVEN_EXTERIOR_PARALLEL.md proves the exact sharp lower
bound `R^2>=2257/576` whenever the **seven exterior squares**
are mutually parallel, regardless of the orientation and position
of the center-containing eighth square. The proof is a complete
two-case hand classification of the seven parallel exterior
centers using their own x/y frame; a rotated central square is
used only to ensure no other square contains the disk origin.
Four actual vertices among the seven exterior squares already
satisfy the four-point 3-by-2 span obstruction.

Thus rotating **only the central square** cannot improve
the parallel eight-square optimum. The exact tilted candidate
has smaller squared radius, so any packing at that radius
must have at least two different exterior-square orientations.
This is an unconditional statement for the entire
sharp search region, independent of chosen contact axes
and without assuming an actual-contact graph.

The theorem does not exclude just one rotated exterior
square among six parallel exterior squares; nor does it
force the exact two tilted-square placement of the
candidate. The sharp unrestricted lower bound
`R8>=Rhat` is still OPEN.


## Current global representative and sharp equality-branch correction

HUMAN_CONNECTED_MAX_CONTACT_REPRESENTATIVE.md proves a new
**unconditional global normal form**: in every packing of
eight unit squares in a radius-R<2 disk with a central
square, there is a same-radius packing with connected
actual-contact graph and containing all initial
contacting pairs. The key is a new radial-band lemma:
every exterior square has nearest norm
`d<=R-1<1` and farthest norm >1, so it
intersects the unit circle **through an open arc
of its interior**. Rigid rotation about the
origin must eventually bring any two exterior
contact components together. A final
central-square translation attaches the central
square if it is still isolated. Thus every
maximum-actual-contact-count radius minimizer
has connected actual graph.

Crucially, section 6 of that note gives a
**core-preserving** version: begin at the
minimum-actual-contact-count radius minimizer
whose unique nontrivial component J has the
physical stresses of HUMAN_CONTACT_COMPONENTS.md.
Keep every square in J **fixed**. Rotate/merge
the originally isolated exterior components,
and move the originally isolated central
square only if necessary. Every original
contact and every chosen positive stress on
J survives unchanged, while the final full
actual-contact graph is connected. All
new contacts can have zero stress weight.
This is a compatible two-representative
reduction, not a claim that min and max
actual contact counts coincide.

ANALYTIC_SHARP_FOUR_CENTRAL_CONTACTS.md proves
a second critical fact about **equality**:
the exact least-five-corner candidate at
R=Rhat can be realized with the central
square C having **four actual neighbors
B,D,T,G** while the seven outer squares
still form their original actual contact
ring. The full parameter-domain hand proof
uses the topmost point Y of G in the
middle column strip, placing standard
middle squares in [Y,Y+1] and [Y+1,Y+2].
It checks all 28 nonoverlap relations and
the strict T circle slack with the identity

    (79/40)^2-(17/24)^2-(479/260)^2
       =583/121680>0.

This **disproves** the shortcut that a
radius-Rhat packing necessarily has
central *actual* contact degree two,
or that the maximal-contact connected
representative can be chosen to have
only two central contacts. The
two-contact transmitter theorems remain
valid only with their original
minimum-contact/degree hypotheses.

Both developments preserve the true
global target: `R8>=Rhat` for **every**
packing. Neither connectedness nor
the exhibition of high-contact
equality candidates derives the
five-corner chain for arbitrary
orientations/contact patterns.
The unrestricted sharp lower bound
is still OPEN.


## Unified central two-spoke and connected-core normalization

HUMAN_TWO_CENTRAL_NEIGHBOR_REPRESENTATIVE.md proves an
**unrestricted hand theorem** for every eight-square
packing in the search radius range: with the other
seven squares fixed and the central frame fixed,
one may choose the central square's location so
it touches **at least two distinct neighbors**.
The feasible center set is the complement of
the interiors of seven convex Minkowski polygons
inside the disk-admissible center set. By the
analytic central-square theorem, every feasible
central placement still contains zero, and
therefore every central vertex has radius
strictly below sqrt(2)<R. Thus the feasible
center set is compact and stays away from
the disk-center-set boundary. An open free
component has a polygonal boundary; a
convex-hull extreme vertex with a strict
corner cannot be supplied by just one
convex forbidden polygon (its exterior
contains a local open half-disk). At least
two distinct forbidden polygons meet,
giving two actual central neighbors.
No orientation or contact-graph pattern
is assumed.

Section 6 combines this result with
HUMAN_CONNECTED_MAX_CONTACT_REPRESENTATIVE.md:
starting from a **minimum-contact** radius
minimizer, keep its stressed nontrivial
component **fixed**, rigidly rotate all
isolated exterior components until they
attach, then if C was originally isolated
reposition it into at least two contacts.
The resulting single representative has

* **connected full actual-contact graph**;
* **at least two actual central neighbors**;
* the same **normalized physical stress**
  and unchanged support-bearing core as
  the original minimum-contact minimizer.

The new contacts may all have weight zero.
None of the original minimum-contact
actual-degree-two or radial-bridge claims
is automatically transferred to this
modified, more-connected representative.
This is a global reduction on **representative
selection**, not the missing sharp radius
inequality. In particular it does not
force the two central contact normals to
be opposite, or the five-corner chain
in arbitrary minimizers.

The candidate's exact equality family
can have **four** actual central neighbors
(ANALYTIC_SHARP_FOUR_CENTRAL_CONTACTS.md),
so no universal central degree<=2
classification is possible.
`R_8>=R_hat` remains OPEN.


## Exact seven-exterior-ring counterexample and central-pocket obstruction

RATIONAL_SEVEN_EXTERIOR_CONTACT_CYCLE.md gives **seven
exterior unit squares** with rational frames and centers in
the disk q=1957/500=3.914. Every consecutive edge of
the seven-cycle is a **genuine** square-square contact,
all 14 nonconsecutive pairs have strict rational
separation margins, all vertices lie strictly in the
circle, and the contact polygon winds +1 about zero.
This is a **seven-square** example, *not an eight-square
packing*. Two of its exterior-square center norms are
strictly below one (p0 and p4), so it does **not**
disprove a putative bound for a ring of seven squares
whose **centers** are all outer.

HUMAN_RATIONAL_RING_POCKET_AREA.md computes that the
area available in the origin-containing bounded
contact-polygon pocket, after removing the pieces
of its seven ring squares, is exactly

    23288171643871/26015100250000<1.

The polygon's signed shoelace area is
`120475483627389/41624160400000<29/10`,
while seven explicitly clipped inward pieces
sum to more than `39/20`. This is a short
hand-checkable demonstration that **no eighth
unit square containing the origin can be added
to that particular ring**, regardless of frame.
It directly quantifies the missing central
obstacle rather than replacing it with an empty
point at zero.

HUMAN_RATIONAL_FIVE_CORNER_GAP.md supplies a
new **whole-domain hand support certificate**
that the exact globally minimized five-corner
family requires

    Rhat>2473/1250=1.9784,
    Rhat^2>6115729/1562500
         =1957/500+26/390625.

The proof uses four rational weighted five-corner
support functionals over the entire admissible
tilt range 0<=tan t<=1/5. Strict concavity
reduces each interval to two endpoint checks,
and eight explicit integer-square-root certificates
prove every endpoint inequality. Therefore the
seven-ring is *rigorously* smaller in radius
than the exact five-corner optimum, **without
using the rounded Cantrell value or a numerical
isolating box**.

The exact implication that remains OPEN is:
every actual eight-square packing below Rhat must
be excluded by **the central square together with
all seven exterior squares**, across unrestricted
orientations and separator choices. A ring-only
contact, winding or area constraint cannot be
substituted for that coupled obstruction.


## Case rejection is now explicit, not an assumed candidate graph

See **PATTERN_REJECTION_MATRIX.md** for the current
hand-proved pattern eliminations and their precise
whole-square/center/actual-contact qualifications.
The strongest cardinality theorem is the **existing**
HUMAN_CENTRAL_COMPACTNESS.md semicircle consequence:
at q<=98/25 no four entire unit squares lie in a
half-disk through zero, so every central side
serves at most **three** squares. The subsequent
HUMAN_FOUR_SQUARE_CAP_SLICE.md gives only an
independent elementary proof when its cap
offset h>=1/100; the analytic semicircle theorem
removes that apparent small-offset exception.
Do not treat it as an unresolved four-side branch.

New exact opposite-side refinement:
for a central side normal n and
t=n dot p_C, if **both opposite sides
serve two whole exterior squares**, then

    |t| <= sqrt(q-1)-3/2 <5/24

at q<=9789/2500. Indeed the more distant
side has h=1/2+|t|>=1/2, so the
two-square cap theorem gives
q>=(3/2+|t|)^2+1; a value
|t|>=5/24 would imply
q>=2257/576>9789/2500.
A side serving **three** forces its
threshold h<3/10, its central center
projection t<-1/5, and at most
**one** whole square on the opposite
side. All orientation and contact
patterns are allowed in these
side-occupancy assertions.

The matrix also records the already
proven exclusion of straight
four-square chains, seven
parallel **exterior** squares with
arbitrary central frame, cycles on
3--6 centers of norm at least one,
and opposing central-contact
neighbors which themselves touch.
The seven-exterior actual-contact
ring, **central degree four**
equality examples, corner-owned
separators, and mixed exterior
orientations are **not eliminated**.
None of the new bookkeeping
establishes unrestricted R8>=Rhat.


## Exhaustive finite-vs-continuous pattern taxonomy

FINITE_PATTERN_TAXONOMY.md distinguishes three independent
coarse classifications without pretending that they determine
the exact packing geometry:

1. Each of the seven exterior squares has one of **twelve**
   exhaustive central-separator statuses: four single
   central-side labels, four adjacent side-pair labels,
   or four own-axis corner-only labels. There is at most
   one corner-only square in each corner, and at least
   three distinct exterior squares are side-separated.
2. Each opposite central-side count pair belongs to one
   of **eight** profiles up to reflection:
   0+0,0+1,0+2,0+3,1+1,1+2,1+3,2+2.
   There are 13 signed versions per axis, at most
   169 combined four-side count profiles, and 36
   profiles up to central-frame reflection/axis swap.
   At least three distinct side-separated squares
   eliminates five of these 36 coarse numerical
   profiles, leaving **at most 31 for further pruning**.
   They are necessary profiles, not 31 certified
   realizable arrangements.
3. A newly proved elementary center-count lemma
   shows at most five of eight square centers
   can have norm <1 (six such centers would have
   angular gap <=pi/3 and center distance <1).
   Thus the number k of center-norm-at-least-one
   outer squares satisfies 3<=k<=7.
   Their induced actual contact graph is a
   union of paths and isolates for k=3,4,5,6;
   for k=7 it is paths/isolates or the full
   seven-cycle. The path alternatives allow
   noncentral inner squares and their contacts.

For formal exhaustiveness beyond these hand-geometric
profiles, each pair of squares has at most eight
signed separating-axis choices, giving <=8^28
symbolic SAT-owner branches for 28 pairs. Every
branch consists of polynomial equalities and
inequalities in actual centers and unit square
frame vectors (after finite absolute-value
sign splits), hence is a continuous **semialgebraic**
feasibility problem. The nontrivial exact slider
interval in the sharp construction shows
infinitely many positions occur even at one
radius with the same full exterior contact ring.

**Strategic conclusion:** finite contact types do not
mean a finite list of isolated configurations.
The proof must reject every surviving
continuous family by inequalities incorporating
all eight squares, or replace the enumeration
with one universal sharp obstruction.
No equality R8=Rhat is inferred merely from
the finite taxonomy.


## New exact sector/corner-status pruning (October 12 continuation)

HUMAN_ORIGIN_SECTOR_REPLICATION.md proves a
universal rotation-replication hand theorem:
if m whole unit squares fit in an origin
sector of opening <=2pi/k within q<=98/25,
then k*m<=7. The 90-degree case gives
**capacity one for any whole quadrant**;
the 45-degree case says no whole unit square
can have an angular shadow narrower than
pi/4. In particular each central
adjacent-double separator status RU,RD,LU,LD
has multiplicity at most one.

HUMAN_SHARP_DOUBLE_CORNER_CAP.md establishes
the stronger **exact one-square** corner
radius envelope

    S subset {x>=h_x,y>=h_y}, h_x,h_y>=0
         => R^2>=(1+h_x)^2+(1+h_y)^2,

without orienting S. The short proof
forms a nonnegative weighted mean of two
actual far-corner squared norms. Equality
forces axis alignment with the two cap
lines. Applied to the central square
at p_C=(a,b), this excludes **both
opposite pairs of double-side statuses**:
RU with LD, and RD with LU.
At most two double statuses can occur,
and any two must be adjacent and share
a signed side.

A pair of adjacent double statuses
on R implies a<-5/24 and prevents
a two-square population on L.
Its rotated/reflected analogues hold.
Any one RU status requires
a+b<-487/2500, with the analogous
signed displacement inequalities
for other corners.

If |a|,|b|<=1/10, all double
statuses are impossible. If
|a|,|b|<=5/24, at most one
double status can occur. Theorem 5
sharpens triple-side h to <7/24;
its opposite side offset then
exceeds 17/24 and **no member of
that opposite cap may also lie
beyond a perpendicular central
side**. Theorem 6 summarizes these
orientation-free central-center
regimes.

HUMAN_DISTANT_SIDE_TRANSVERSE_LANE.md
proves that a side at offset
h>=17/24 can serve at most one
whole square, whose center transverse
coordinate has absolute value <1/2,
whose open interior crosses the
perpendicular diameter, and which
has **no** adjacent double-side
separator. This is especially useful
inside a still-surviving 3+1 profile.

PATTERN_REJECTION_MATRIX.md and
FINITE_PATTERN_TAXONOMY.md now record
the **fully qualified** status filters.
Under the finite necessary status
rules, the number of labeled
seven-exterior-square status
assignments falls from 8,551,760
to **3,995,040** (about 53.3%
pruned), including the triple-side
distant-corner rule. These are
counts of discrete assignments,
not packings or certificates
that each surviving assignment
is geometrically feasible. All 31
coarse opposite-side count profiles
still admit some assignment.

The decisive global obstruction
R8>=Rhat is **not proved** by
these local prunings. Further
work must join the remaining
separator statuses to the
seven-square contact geometry
and central occupancy, without
incorrectly eliminating genuine
candidate equality branches.
