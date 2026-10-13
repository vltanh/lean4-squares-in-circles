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


## Refined macro-branch stratification after latest corner-cap pruning

HUMAN_SHARP_DOUBLE_CORNER_CAP.md, Theorem 7,
proves that if two adjacent double-side
statuses RU and RD both occur, their shared
side coordinate a and transverse coordinate
b obey the exact strict region

    -1/2<a<-5/24,        |b|<5/24.

The proof combines two opposite-y versions
of the sharp two-coordinate corner cap
envelope, and uses q_plus<2257/576.
Reflections/rotations give all other
two-double arrangements.

REMAINING_DOUBLE_STATUS_BRANCHES.md is
now the preferred compact case queue:
**D0** no adjacent double-side member
(forced when both central coordinates
are within 1/10);
**D1** exactly one double (signed diagonal
central displacement and <=4 corner-only);
**D2** exactly two *adjacent* doubles,
sharing a side, with the central
center trapped in the one-large/
one-small coordinate region above
and at most one whole square on the
opposite side.

All three macro-branches retain
the k=3..7 outer-center/contact
classification independently. The
full seven-outer contact ring and
multi-contact central square are
**possible sharp equality branches**.
A sharp global geometric estimate is
still required inside each surviving
continuous case; no universal
R8>=Rhat theorem is asserted by
this macro-branch enumeration.


## 2026-10-12: radial-axis routing clears more continuous triple-side subcases

HUMAN_TRIPLE_SIDE_RAY_PENETRATION.md proves
that **every three-square whole central-side
cap**, at *every* positive offset, has at
least one single-side status member whose
**open interior crosses that side's outward
origin cardinal ray**. The proof uses only
the one-per-quadrant sector replication
theorem. If the triple contains RU and RD
on a common R side, its third R member
is necessarily that ray-crossing unit.

At offsets h>=13/60, combine with the
older three-square whole-quadrant witness
theorem: the three squares are **uniquely
classified in transversal location** as
one wholly in the upper origin quadrant,
one crossing the outward radial ray, and
one wholly in the lower origin quadrant.
The full angular/frame continuum remains
possible, but the three geometric roles
are compulsory.

HUMAN_OPPOSITE_TRIPLE_DIAMETER_CHAIN.md
proves every opposite 3+1 side-population
has two **distinct single-side exterior
square open interiors** crossing the
two opposite cardinal rays, with the
origin-containing central square between
them. Thus a far-side singleton in a
3+1 pattern cannot lie wholly in either
adjacent origin quadrant. No contact
or common-frame assumption is needed.

HUMAN_SATURATED_TYPE_A_RAY_ROUTING.md
specializes to maximally saturated
Type A (3+1,3+1) with exact seven
statuses RU,R,R,L,U,U,D. It forces
**four different** cardinal-ray crossing
single-side units and an RU quadrant
unit crossing the NE diagonal. When
both triple offsets >=13/60, the
remaining R and U singles must be
wholly in the SE and NW origin
quadrants respectively. Otherwise
at least one triple offset <13/60
and its opposite singleton has a
narrow transverse center coordinate
absolute value <9/25. This is
an exhaustive exact two-subcase
routing for Type A.

HUMAN_CORNER_ONLY_DOUBLE_RAY_BOUND.md
supplies a strict nonlinear placement
condition for own-axis corner-only
members wrapping two adjacent outward
origin rays: their central-corner
offsets A,B>0 must satisfy
sqrt(A)+sqrt(B)<sqrt(2). In
particular if the central square
center has nonnegative coordinates
toward that corner, double-ray
wrapping by a corner-only square
is impossible.

**Limitations and guards:** These
are genuine *continuous geometric
placement exclusions*, not further
Boolean 12-status exclusions. The
finite assigned-status count remains
**3,995,040** under the existing
filters. A pair of disjoint cap
squares can *both* cross one ray:
an exact rational witness is recorded
in the triple-ray note. It would be
incorrect to promote ray-crossing
uniqueness to the small-offset triple
case or to arbitrary pairs.

The exact unrestricted lower bound
R8>=Rhat remains OPEN. The next
unresolved step is to combine the
compulsory radial chords and
whole-quadrant owners with the disk
and mutual separators into a sharp
radius inequality, preserving the
real candidate equality Type S4.


## 2026-10-12: far two-cap polarization clears transverse center subcases

HUMAN_FAR_TWO_CAP_POLARIZATION.md establishes a new
**arbitrary-orientation, exact rational** center-sign theorem:
if two whole unit squares occupy a cap at outward
offset h>=3/5 under q<=9789/2500, their center
coordinates perpendicular to the cap's outward
normal must have **opposite strict signs** and
each absolute value must exceed **7/25**.

The hand proof combines the already proved
single-square cap center envelope and
universal center-radius bound. They constrain
each perpendicular coordinate to absolute
value <133/200 and the longitudinal
center-coordinate difference to absolute
value <8/25. If one of two centers were
within 7/25 of the perpendicular diameter,
their separation would be <sqrt(39817/40000)<1,
contradicting their disjoint inscribed
half-unit disks. No selected pair separator
or common frame is used.

This gives two targeted necessary
continuous-domain splits:

* Saturated Type C (2+2,2+2), with one RU double,
  has a+b<-1/5. Thus a<-1/10 or b<-1/10,
  so **at least one** of its far L/D two-square
  caps has centers of strictly opposite
  transverse signs and absolute coordinate
  >7/25. Both caps polarize when both
  coordinates are <-1/10.
* Saturated Type B (3+1,2+2) has, on its
  2+2 axis, either central signed coordinate
  |t|<1/10 or the more distant cap's
  two centers polarized by >7/25.

No new entire twelve-status combination
was excluded on these bounds alone.
The correct remaining *symbolic* count
is still 3,995,040 labeled assignments;
this is a continuous geometric refinement
aimed at the sharp unproved radius
obstruction R8>=Rhat.


## Two Type C / outer-center macro-cases are now genuinely excluded

HUMAN_TYPE_C_FIVE_OUTER_MINIMUM.md establishes the
first new **joint status-by-outer-center rejection**
of this continuation: saturated Type C has exact
fine statuses RU,R,L,L,U,D,D, central opposite
counts 2+2 on both axes, and must possess
**at least five center-norm-at-least-one
exterior squares**, independent of all their
orientations. Thus Type C with k=3 or k=4
outer centers is **impossible**.

The proof combines: RU is necessarily outer
from |a|,|b|<5/24; the two pairs on sides
with outward offsets >=1/2 are entirely
outer; and in either mixed-sign central
position, one additional pair on a cap
of offset >59/120>2/5 must have at least
one outer center. The last fact is an exact
inscribed-center-distance contradiction
for two centers of norm <1 in that cap.
This is indexed in PATTERN_REJECTION_MATRIX.md,
section 9, with its three-case hand proof.

This removes two **macro-cells** (Type C,
k=3 and Type C,k=4). It does *not*
decrease the earlier 3,995,040 purely
twelve-status labeled assignment count,
which did not encode center norms.
The remaining Type C k=5,6,7 branches
and all other geometrically surviving
types still require a sharp obstruction.
The candidate D0/S4 equality branch
is untouched.


## Additional outer-center pruning in exclusive single-side S2--S4

HUMAN_SINGLE_SIDE_OUTER_K_PRUNING.md gives an exact
hand proof that **every three-square whole cap**
at nonnegative radial offset has at least one
square center with norm >=1. Three *inner*
centers in such a cap would lie in a 120-degree
angular sector, while each pair of centers of
norm <1 must be separated by strictly more
than 60 degrees (by their disjoint inscribed
radius-1/2 disks). This is impossible for three.

Together with the existing cap-inner-pair
lemma (two squares at h>=2/5 cannot both
have inner centers), and the fact that
every cap square at h>=1/2 has an outer
center, the note eliminates these entire
joint macro/continuous subcases:

    S2=(3+0,2+2), k=3, |t_2+2|<=1/14;
    S3=(3+1,2+1), k=3, h_2>=2/5;
    S4=(2+1,2+2), k=3, h_2>=2/5;
    S4=(2+1,2+2), k=4, h_2>=2/5,
         |t_2+2|<=1/14.

Here h_2 is the outward offset of the
two-member side on the 2+1 axis.
These are only assertions about the
**exclusive one-side, no-corner** S2--S4
branches; they cannot be copied into
branches with double-side memberships,
where cap populations overlap in square
labels. The exact S4 candidate's possible
central position is not excluded.

HUMAN_TWO_CAP_CENTER_SIGN_SPLIT.md also
shows, at h>=3/7, two whole cap squares
must have centers on opposite sides of
the perpendicular origin diameter;
at h>=1/2 both are outer with absolute
transverse center coordinates >1/10.
At h>17/24 the unique far-cap singleton
is outer and openly crosses the outward
diameter ray. The inequalities are
proved by exact rational comparisons and
disjoint half-unit inscribed disks.

No claim of unrestricted R8>=Rhat
follows from these macro-cell eliminations.


## 2026-10-12: stronger midpoint-slice hand lemmas (post-9c747b1)

Two further arbitrary-frame lemmas sharpen the October 12 continuous
separator/outer-center queue without eliminating the S4 equality branch.

**Shared square in perpendicular triples.**
[HUMAN_PERPENDICULAR_TRIPLE_IMPROVED.md](HUMAN_PERPENDICULAR_TRIPLE_IMPROVED.md)
improves the earlier \(h_R,h_U\ge1/10\) fixed-point result to
\[
h_R,h_U\ge1/11
\quad\Longrightarrow\quad
\text{an actual common double-side square}.
\]
It uses the midpoint chord formula, the exact decreasing-in-width
reserve \(\ell>9405/10000\), and a common open-interior segment at both
slices. In exclusive-single-side S1=(3+0,3+1), this forces
\(\min(h_{\mathrm{triple},1},h_{\mathrm{triple},2})<1/11\)
(or \(\min(a,b)<-9/22\) for R/U triples).
If the exceptionally small triple is on the 3+1 axis,
its opposite singleton has strict transverse center
\(|z|<1/48\) by the existing arbitrary-frame single-square cap
envelope. The latter bound is **not** asserted for a small triple
on the 3+0 axis.

**Two outer centers in a single triple cap.**
[HUMAN_TRIPLE_CAP_TWO_OUTER_IMPROVED.md](HUMAN_TRIPLE_CAP_TWO_OUTER_IMPROVED.md)
lowers the older \(7/50\) threshold to \(13/100\): each triple of
whole squares beyond a side with \(h\ge13/100\) has two **distinct**
center-norm-\(>1\) squares, selected by the top/bottom midpoint chords.
The proof is global over square frames, splitting the extreme square
at \(L=\cos\theta+\sin\theta=69/50\). Below that point its own chord
has length at least one; above, an exact increasing quadratic yields
\(|p|^2>100222049/100000000>1\).

As immediate joint outer-count restrictions, S1/k=3 requires **both**
triple offsets \(<13/100\); S2's triple \(\ge13/100\) implies
\(k\ge4\) (and \(k\ge5\) when the 2+2 offset coordinate is
\(\le1/10\) in absolute value); S3/k=3 requires its triple
\(<13/100\); and Type A with both triple offsets \(\ge13/100\)
has \(k\ge5\). These sharpen *continuous-region/outer-count*
subcases, **not** the previously enumerated 3,995,040 purely symbolic
assignments.

Both new notes are written hand arguments with exact rational margins,
not Lean files. They retain the nontrivial small-offset S1 continuum,
other D0 branches, double-side/corner-only branches, and the real
S4/k=7 candidate equality. The sharp unrestricted target
\(R_8\ge\widehat R\) remains **OPEN**.


### Additional high-offset whole-quadrant improvement

[HUMAN_TRIPLE_CAP_QUADRANT_IMPROVED.md](HUMAN_TRIPLE_CAP_QUADRANT_IMPROVED.md)
sharpens the full-square upper/lower quadrant witness threshold in the
actual n=8 search radius window from \(13/60\) to \(17/80\).
For **three whole** squares in a cap at offset \(h\ge17/80\),
the top and bottom midpoint-chord labels are wholly in the opposite
open origin quadrants, for arbitrary independent orientations.
The proof fixes the smaller offset \(17/80\), uses the improved rational
disk chord bound \(B<164779/100000\), establishes that all three
midpoint chords have length at least one, and bounds the *full vertical
projection* of the extreme square with
\(\ell-L\ge\sqrt2-R+17/80\). The resulting strict full-square
ordinate margin is \(11/100000>0\).

This strengthens Type A's high-offset **whole-quadrant owner**
routing, not its Boolean status count, and does not force the
sharp five-corner chain. It assumes the already analytically proved
eight-square lower-radius range \(\sqrt2+1/2<R\); it does **not**
claim the same \(17/80\) threshold for all arbitrary three-square
caps without that premise. Earlier stronger-in-scope but
weaker-in-threshold \(13/60\) results remain valid.


### 2026-10-12: low-offset S1 hole and asymmetric analytic gate

The fixed-segment technique also works **below** the uniform
\(1/11\) threshold on a two-dimensional domain:
[HUMAN_PERPENDICULAR_TRIPLE_LOW_OFFSET.md](HUMAN_PERPENDICULAR_TRIPLE_LOW_OFFSET.md)
proves that perpendicular triple caps whose outward offsets are both
in the closed interval \([1/16,1/10]\) share an actual square,
regardless of all frames. It uses the distinct fixed slice interval
\([789/800,5197/5000]\), actual midpoint chords
\(\ell>9121/10000\), and an exact \(1/625\) upper overlap margin.
Hence the full closed central-center rectangle
\([-7/16,-2/5]^2\) is forbidden in the exclusive-single-side S1
R/U-triple normalization. This genuinely removes a low-offset S1
region **not** excluded by the original \(1/11\) theorem.

The same note couples this result to the sharp one-square cap
envelope: on S1's 3+1 axis the triple offset is **strictly**
\(h_{31}>17/200\), because the opposite singleton would otherwise
need squared radius larger by \(13/8000\).
Thus if \(h_{31}\le1/10\), the perpendicular 3+0 triple offset
must lie **outside** \([1/16,1/10]\); if both triple offsets
are \(\le1/10\), necessarily \(h_{30}<1/16\).

[HUMAN_ASYMMETRIC_TRIPLE_PIERCE_GATE.md](HUMAN_ASYMMETRIC_TRIPLE_PIERCE_GATE.md)
records the full-domain symbolic follow-up. For arbitrary offsets
\(h_R,h_U\ge0\) serving whole triple caps, write
\(X(h)=(R+h)/2\),
\(B(h)=\sqrt{R^2-X(h)^2}\), and
\(\lambda(h)=\min(1,2\sqrt2-R+h)\).
If **both** \(3\lambda(h_R)-B(h_R)>X(h_U)\)
and \(3\lambda(h_U)-B(h_U)>X(h_R)\), the populations share an
actual double-side square. Therefore an exclusive-single-side S1
configuration must violate at least one of those inequalities.
This is a proven exact *necessary continuous-domain condition*, not
a sampled classifier and not a sufficiency claim for S1 existence.

[verify_improved_cap_arithmetic.py](verify_improved_cap_arithmetic.py)
now also audits the low-offset midpoint bounds and \(17/200\)
singleton comparison using exact fractions. The script has been
executed successfully; the analytical arguments remain the premises.
No general S1 closure, S4 equality exclusion, or unrestricted
\(R_8\ge\widehat R\) is claimed.


## 2026-10-12 further continuation: exact inner-center cap threshold and a local counterexample

[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md)
proves a **sharp, full-orientation** replacement for the previously
reused h>=2/5 two-inner-center cap exclusion. Two distinct unit
squares wholly beyond the same nonnegative offset line, with both
centers of norm <1, require
\[
h<(\sqrt3-1)/2=:H_*.
\]
The proof only uses that the center normal projections exceed
h+1/2, and that two centers of norm <1 with mutual distance >=1
must have angular separation strictly greater than 60 degrees.
It also proves that such two inner centers have **opposite signed
transverse coordinates**, and one has transverse absolute coordinate
>(h+1/2)/sqrt(3). A pair of aligned vertically stacked squares
with centers (x,±1/2), x approaching sqrt(3)/2 from below, shows
that H_* is actually **sharp for a standalone two-square cap inside
the n=8 disk ceiling**, not merely for a center-disk relaxation.

Writing \(T_*=1-\sqrt3/2\), the exact new joint status/outer-center
restrictions are: S2/k=3 requires
\(|t_{2+2}|>T_*\), S3/k=3 requires
\(h_{\mathrm{2-member},2+1}<H_*\),
S4/k=3 requires its 2+1 two-member offset \(<H_*\), and
S4/k=4 with two-member offset \(\ge H_*\) requires
\(|t_{2+2}|>T_*\). None eliminates S4 equality or all
D1/D2 cases. The 12-status symbolic count is unchanged.

[RATIONAL_PERPENDICULAR_CAP_COUNTEREXAMPLE.md](RATIONAL_PERPENDICULAR_CAP_COUNTEREXAMPLE.md)
records five **exact rational** disjoint unit squares at
\(R^2=3911/1000<q_{\mathrm{plus}}\), including the open
origin-containing central square, a three-member right whole cap,
and a far lower singleton. All 20 true square vertices and all
10 unordered square pairs have explicit exact certificates in
[verify_perpendicular_cap_counterexample.py](verify_perpendicular_cap_counterexample.py).
The example has a genuine RU double-side square, so it
**does not** contradict the S1-exclusive-single-side deductions.
It refutes only the tempting shortcut of excluding a perpendicular
triple plus far singleton **without retaining double-side status**.

No new general eight-square lower bound or complete proof for D0,D1,D2
is claimed. The target \(R_8\ge\widehat R\) remains open.


## 2026-10-12: sharp two-inner cap geometry and two full low-k eliminations

[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md)
proves, for arbitrary frames, that two whole squares in one
nonnegative offset cap with **both** centers of norm <1 require
\[
h<(\sqrt3-1)/2.
\]
The threshold is sharp for standalone axis-parallel squares
within the n=8 radius ceiling. Both inner center rays
must straddle the outward normal with strict opposite transverse
signs, and one has transverse coordinate magnitude
\(>(h+1/2)/\sqrt3\).
This strictly improves the older \(h\ge2/5\) inner-pair cap
center-count argument.

[HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md](HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md)
gives a strict quarter-circle inequality for **four distinct
inner centers**, two in each of two perpendicular whole-side caps:
\[
(h_x+1/2)^2+(h_y+1/2)^2<1.
\]
It forces explicit narrow center-ray lanes in
[HUMAN_S1_K3_FOUR_INNER_LANES.md](HUMAN_S1_K3_FOUR_INNER_LANES.md)
and [HUMAN_S2_K3_INNER_FAN.md](HUMAN_S2_K3_INNER_FAN.md).
Those latter S2/k3 conclusions are now superseded by the stronger
global macro-cell exclusion below.

**Genuine new complete macro-case exclusions.**
[HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md](HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md)
proves an orientation-free **six-square forbidden-cap pattern**:
two distinct inner squares in one positive cap, two distinct
inner squares in a perpendicular cap of offset \(h>7/24\),
and two distinct outer squares in its opposite cap at
offset \(1-h\) cannot all coexist under
\(R^2\le9789/2500\).

The core hand proof forces an inner R center with radius \(>4/5\)
at polar angle \(<-\arcsin(19/24)\), bounds both far D
outer center rays to a southern interval by their large signed
normal component and the universal center radius
\(<283/200\), and invokes the established **outer-outer**
angular gap \(>\pi/4-1/500\).
The inscribed-center distance inequality forces each D ray
more than \(\pi/6+1/100\) away from the near-outer R center.
An exact arctangent comparison
\(\arcsin(19/24)+\arctan(4/3)>7\pi/12\)
leaves available arc width \(<\pi/4-1/100\), contradictory.
[verify_far_two_cap_angular_margins.py](verify_far_two_cap_angular_margins.py)
audits the displayed rational comparisons; it is **not**
a substitute for the geometric argument.

**Consequently the entire exclusive S2/k=3 cell and the
entire exclusive S4/k=3 cell are eliminated, without
any central-offset exception.** The latest D0/S=7
outer-count queue is:
\[
\begin{array}{ll}
{\rm S1}:&k=3,4,5,6,\\
{\rm S2}:&k=4,5,6,\\
{\rm S3}:&k=3,4,5,6,7,\\
{\rm S4}:&k=4,5,6,7.
\end{array}
\]
The exact S4/k=7 candidate equality construction is
untouched. Corner-only cases, D1/D2, other outer-path
attachments, and the unrestricted sharp radius
\(R_8\ge\widehat R\) remain **OPEN**.

The exact rational five-square local counterexample with
one actual RU double-side member is recorded separately in
[RATIONAL_PERPENDICULAR_CAP_COUNTEREXAMPLE.md](RATIONAL_PERPENDICULAR_CAP_COUNTEREXAMPLE.md);
it guards against applying an **exclusive single-side**
exclusion to arbitrary side-population counts.


### Why S2/k=4 still needs actual-square geometry

After excluding S2/k=3, the next low-outer-center S2 branch is
k=4. In the subcase with *both near-2+2 centers inner*, the
far-2+2 cap supplies two outer centers, and the perpendicular
triple must supply at least two more outer centers (otherwise
the six-square forbidden-cap theorem applies).

[RATIONAL_S2_K4_CENTER_RELAXATION.md](RATIONAL_S2_K4_CENTER_RELAXATION.md)
records an **exact rational eight-center constellation**
that meets all 28 center-center unit-distance inequalities,
the prescribed four outer/three exterior inner norms,
strict central-side *necessary* projection bounds,
and the universal necessary scalar disk center-radius envelope
\(r^2+r+1/2\le9789/2500\). The smallest
squared pair-distance margin is exactly
\(21156861/5000000000>0\), and the smallest cap-center
normal-projection margin is \(211/100000>0\).
[verify_s2_k4_center_relaxation.py](verify_s2_k4_center_relaxation.py)
checks all those rational conditions.

**This is explicitly NOT a valid eight-square packing.**
No square orientations, actual vertex circle containment,
or SAT separators between the whole squares have been given.
It merely disproves the prospect that these *weaker center-only
conditions alone* could exclude the subcase. Any sharp
S2/k4 obstruction must retain actual square frames,
vertex containment, or pair support inequalities.
The global \(R_8\ge\widehat R\) remains OPEN.


## 2026-10-12 continuation: five-square inner/outer fan rules out a full S3/k=3 offset region

[HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md](HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md)
proves a **global, arbitrary-frame five-square obstruction** for
two distinct inner-center squares in each of two perpendicular
whole caps (R and U), and a fifth **outer-center** square
in the R cap. Under the actual n=8 ceiling,
the five-square configuration is impossible when
\[
h_R>17/200,\qquad h_U\ge21/100.
\]
The proof uses only the actual inscribed-center distance
constraint, the farthest-vertex center-radius bound
\(r<283/200\), and the four-inner angular fan.
Its two exact mixed inner/outer angular margins are:
* for inner radii \(>7/10\): outer angle gap \(>2\pi/9\);
* for inner radii \(>117/200\): outer angle gap \(>7\pi/36\).

The three forced inner rays R-,R+,U+ bracket any R-outer ray
strictly in \((-\pi/9,7\pi/36)\), which lies *too close*
to R+; thus no such fifth square exists.
[verify_five_square_angular_fan.py](verify_five_square_angular_fan.py)
audits the exact rational squared-distance margins, not
the whole-continuum proof or the unrestricted n=8 theorem.

**New S3/k=3 rejection:** exclusive S3=(3+1,2+1)
with k=3 necessarily has one R-outer, two R-inner,
two U-inner, and far L/D outer singletons.
The distant L singleton forces \(h_R>17/200\);
therefore the entire \(h_U\ge21/100\) subdomain
is impossible. The surviving S3/k=3 offset must satisfy
\[
17/200<h_R<13/100,\qquad
17/200<h_U<21/100.
\]
This supersedes the older \(h_U<(\sqrt{26311}-100)/200\)
bound, but does **not** eliminate S3/k=3 entirely.

[HUMAN_S3_K3_REMAINING_TWO_LANES.md](HUMAN_S3_K3_REMAINING_TWO_LANES.md)
gives a further **exact positional split** within that
small rectangle. The sole outer R center ray angle \(\psi\)
must lie in one of two disjoint open sectors:
\[
-5\pi/36<\psi<-2\pi/45
\quad\text{or}\quad
7\pi/36<\psi<13\pi/45.
\]
The far L/D singleton transverse center coordinates obey
\[
|p_L.y|<3/20,\qquad |p_D.x|<11/32,
\]
placing their center rays within \(\pi/24\) of the
negative x axis and \(\pi/12\) of the negative y axis,
respectively. All assertions use **whole-square cap**
hypotheses, not merely center sign or arbitrarily chosen
separating directions.

**New S1/k=3 conditional restriction:** if the 3+1
triple offset \(h_U\ge21/100\), its perpendicular
3+0 triple must have \(h_R\le17/200\), or the same
five-square theorem applies. This does not finish S1/k=3.

These results remove genuine **continuous geometric subregions**,
not additional Boolean twelve-status words. The previous
S2/k=3 and S4/k=3 entire macro-cell exclusions remain valid.
S4/k=7 sharp equality, D0 corner-only branches, D1/D2,
and the unrestricted reverse bound \(R_8\ge\widehat R\)
are **still OPEN**.


## 2026-10-12 continuation: S2 near-inner 2+2 pair forces k=4 and outer-R sign polarization

[HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md](HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md)
proves a new, **all-frame six-square angular theorem**:
if two **inner-center** squares lie in a positive U cap,
two **outer-center** squares occupy its opposite D cap at
complementary offset \(1-h_U\), with \(7/24<h_U<H_*\),
then at most **two** additional outer centers can belong
to any perpendicular positive R whole-square cap.

For exactly two R outer members, let their center-ray
angles be ordered \(\psi_1<\psi_2\).
The outer-outer gap, U+ inner/outer mixed gap,
and exact far-D polar elevation force
\[
-\pi/4+17/125<\psi_1<-\pi/18+1/500<0
\]
and
\[
0<67/500<\psi_2<7\pi/36.
\]
Thus they **strictly straddle the outward positive x ray**,
with quantified open angular margins. A third R outer
ray cannot fit inside the same narrow interval
\((-\pi/4+17/125,7\pi/36)\), whose width is
strictly less than twice the rigorous outer-pair gap
\(\pi/4-1/500\).

**New exact S2 outer-count consequence:** in exclusive
S2=(3+0,2+2), with the nearer 2+2 U cap containing
**two inner centers**, the opposite farther D cap
already contributes two outer centers.
The earlier six-square exclusion
HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md
rules out *one* outer R member, and the new
outer-center angle theorem rules out *three*.
Therefore this entire conditional S2 branch has
**exactly two outer R centers, one inner R center,
and k=4**. The S2/k=5 subcase with both near-U
centers inner is **now impossible**, while
S2/k=4 with both near-U centers inner remains
a genuine unresolved continuous cell.

This is not a change to the purely symbolic
3,995,040 labeled separator-status assignments:
the new restrictions depend on actual square
center norms and their polar angular order.
Do not infer that the two outer R squares are
whole origin quadrants merely from their
opposite transverse center signs.

The sharp S4/k=7 equality family and the missing
global \(R_8\ge\widehat R\) remain **unaffected**.


### Stronger conclusion: S2 near-inner k=4 also forces its right triple offset below 1/10

[HUMAN_S2_K4_NEAR_INNER_SMALL_TRIPLE.md](HUMAN_S2_K4_NEAR_INNER_SMALL_TRIPLE.md)
takes the preceding opposite-sign outer R center-ray lanes
and includes the **third, inner** member of the R triple.
When the R triple's outward side offset \(h_R\ge1/10\),
that inner center must have radius \(r\ge3/5\).
Every inner-to-outer pair at the actual n=8 radius
ceiling then has angular separation
\[
>631/1000\ {\rm radians},
\]
proved by four exact squared-center-distance endpoint
comparisons, with worst bound \(998731/1000000<1\).

The two successive outer-ray gaps into which the R-inner
square could fall — from the upper D outer to the lower
R outer, or between the two R outers — each have total
width
\[
<4\pi/9-17/125
<9929/7875<2(631/1000).
\]
Thus the inner center cannot occupy either gap. Its
other hypothetical position, above both R outer rays,
would put it within \(<\pi/3\) of the **positive-x
inner U** center, contradicting the inner-inner
unit-distance angular theorem. The inner center cannot
lie below the uppermost D outer ray because the former
has x projection at least \(3/5\), whereas the latter
has a more southerly polar angle than
\(-\arcsin(4/5)\).

Therefore the full still-unresolved **exclusive S2
branch with both nearer-U centers inner** now satisfies
\[
\boxed{k=4,\quad0<h_R<1/10,}
\]
plus the earlier explicit negative/positive
R-outer ray lanes. The entire \(h_R\ge1/10\)
continuous subdomain is **newly excluded**.
This is genuine pruning, **not** elimination of all
S2/k4 packings and not a change in the purely symbolic
12-status assignment count.

[verify_s2_k4_small_triple_margins.py](verify_s2_k4_small_triple_margins.py)
provides an exact-fraction check of the rational
cosine Taylor and angular-gap inequalities.
It is an arithmetic audit, not a formal n=8 proof
or an oracle for continuous feasibility.

The original S4/k=7 exact equality construction
remains allowed. The unrestricted
\(R_8\ge\widehat R\) remains OPEN.


### 2026-10-12: further halving the S2/k=4 near-inner offset to 1/20

[HUMAN_S2_K4_NEAR_INNER_FIVE_HUNDREDTHS.md](HUMAN_S2_K4_NEAR_INNER_FIVE_HUNDREDTHS.md)
proves a new fully analytic, arbitrary-square-frame
**strict improvement** of the S2 near-inner subcase:

\[
\boxed{\text{exclusive S2, both near U centers inner}
\ \Longrightarrow\ k=4,\quad 0<h_R<1/20.}
\]

The essential new ingredient is a single-square far-cap
**polar elevation beyond 60 degrees**: in the disk
\(R^2\le9789/2500\), any whole square in
\(y\le-h\) for \(h\ge5/8\) has
\(|p_x|<(-p_y)/\sqrt3\), obtained from the
sharp arbitrary-frame cap envelope. Since
the nearer U inner pair forces \(h_U<
(\sqrt3-1)/2<3/8\), the two outer
far-D centers lie in one southern arc of
width \(<\pi/3\). Combined with the
rigorous outer-outer angular gap \(>\pi/4-1/500\),
both consecutive upper outer gaps (upper D to
lower R, lower R to upper R) have width
strictly smaller than
\[
13\pi/36+1/250<57/50.
\]
A separate cosine-law bound shows any inner
center of radius \(r\ge11/20\) must have angular
gap \(>57/100\) radians from any outer center.
An R-inner square at offset \(h_R\ge1/20\)
would therefore fail to fit in either gap,
while the space above both R outers is excluded
by the existing positive-x U-inner center.

[verify_s2_k4_five_hundredths_margins.py](verify_s2_k4_five_hundredths_margins.py)
audits the exact rational endpoint comparisons and has
been executed successfully. The **written angular argument**
proves the continuous case; the script is not a grid, Lean proof,
or optimization oracle.

This removes the entire previous residual interval
\(1/20\le h_R<1/10\), but **does not exclude
all S2/k=4**, all S2 near-cap outer statuses, or any
S4 equality-bearing configuration. The unrestricted
\(R_8\ge\widehat R\) remains OPEN.


### 2026-10-12: two quantitative transverse anchors on each opposing S2 2+2 side

[HUMAN_S2_K4_TRANSVERSE_CENTER_ANCHORS.md](HUMAN_S2_K4_TRANSVERSE_CENTER_ANCHORS.md)
adds four strict **center-coordinate** bounds within the
exclusive S2 branch where both near-U squares have inner
centers. After ordering both U and D pairs by x coordinate,
\[
x_{U_-}<-9/25<0<9/25<x_{U_+},
\]
\[
x_{D_-}<-29/100<0<29/100<x_{D_+}.
\]
The first bound uses inner-center unit separation and
the whole-cap normal projection \(p_y>19/24\),
forcing a transverse signed separation
\(>\sqrt{551}/24\), while either inner center has
\(|p_x|<\sqrt{215}/24\).
The second uses the newly proved >60-degree far-D
polar elevation, two outer D centers' angular separation
\(>\pi/4-1/500\), and the exact strict tangent
lower comparison
\[
\tan(\pi/12-1/500)>1315/5006.
\]

These inequalities supplement the newly proved **k=4
and \(0<h_R<1/20\)** and opposite-sign right-outer
ray requirements. They **do not** imply the corresponding
whole squares lie inside open origin quadrants. All their
frames and actual inter-exterior separators remain free.
[verify_s2_transverse_center_anchors.py](verify_s2_transverse_center_anchors.py)
has been executed successfully to audit the exact rational
margins. The global sharp lower bound
\(R_8\ge\widehat R\) remains **OPEN**.


## 2026-10-12: S3/k=3 upper offset and outer-ray sectors tightened further

[HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md)
strictly improves the previously established five-square
mixed inner/outer angular fan cutoff from
\(h_U\ge21/100\) to **\(h_U\ge1/5\)**.
It proves a sharper mixed-center angular gap
\(>311/500\) radians whenever the inner center
radius is \(>117/200\), using the exact
cosine Taylor lower bound \(>13/16\) and the
four rational corner distances already present in
the previous proof. The key endpoint comparison
\[
\arcsin(7/10)>4\pi/9-311/500
\]
is established with the rational upper bound
\(\pi<22/7\) and a strict fifth-degree sine
Taylor inequality at \(31/40\).

Thus in **exclusive S3=(3+1,2+1), k=3**
the surviving two-member U cap offset satisfies
\[
17/200<h_U<1/5
\]
alongside \(17/200<h_R<13/100\).
The far D singleton transverse center coordinate
improves to \(|p_D.x|<13/40\);
the L singleton retains \(|p_L.y|<3/20\).
This is a genuine continuous-region exclusion,
not a closure of S3/k=3.

[HUMAN_S3_K3_SHARPER_OUTER_RAYS.md](HUMAN_S3_K3_SHARPER_OUTER_RAYS.md)
uses the refined mixed-angle bound to sharpen the sole
R-outer center's two alternative ray sectors further:
\[
-\pi/9<\psi<-2041/10500
\quad\text{or}\quad
311/500<\psi<8959/10500.
\]
The exact sine inequality at \(31/50\) gives
\(\arcsin(h_U+1/2)>31/50\).
The right-minus inner center has radial norm \(>7/10\),
so it repels the outer R center by \(>2\pi/9\),
while U-plus and R-plus repel it by
\(>311/500\); these are center-ray bounds,
not assertions of whole-square quadrant membership.

The optional exact-fraction scripts
[verify_five_square_fan_refined.py](verify_five_square_fan_refined.py)
and [verify_s3_k3_sharper_rays.py](verify_s3_k3_sharper_rays.py)
have been executed successfully for the displayed rational margins.
The continuous proofs remain in the Markdown notes.

**Audit/correction:** the previously recorded rational
eight-center relaxation in
[RATIONAL_S2_K4_CENTER_RELAXATION.md](RATIONAL_S2_K4_CENTER_RELAXATION.md)
satisfies only its explicitly enumerated *weak* center
inequalities. Its outer pairs R1-D2 and D1-D2 have
exact acute angular tangent <9/10, thus violate the
known outer-angle gap \(>\pi/4-1/500\).
The note and verifier now explicitly flag both failures.
It is **not** evidence of actual S2/k4 feasibility,
nor proof that all center-ray-only methods must fail.

The exact S4/k=7 sharp equality configuration is
still retained. The unrestricted bound
\(R_8\ge\widehat R\) remains **OPEN**.


### 2026-10-12: S3/k=3 negative outer ray eliminated; distant lower center forced southwest

[HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md](HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md)
closes **one entire previously surviving outer-R ray sector**
in exclusive S3=(3+1,2+1), k=3.
The outer R center can no longer have negative polar angle.
The proof iterates two *proved exact* mixed
inner/outer center-angle thresholds:

* negative outer-R ray would force the R-minus
  inner-center angle below \(-22/25\) radians,
  making its inner radius \(>9/10\) from the
  actual R whole-side projection \(p_x>117/200\);
* that larger radius requires mixed angular
  gap \(>77/100\) radians, pushing R-minus below
  \(-24/25\), where its center x projection
  must be \(<117/200\), contradiction.

The cosine Taylor signs and all four distance
corner comparisons are audited by
[verify_s3_k3_negative_sector.py](verify_s3_k3_negative_sector.py).

Thus the sole R outer ray has **only one** remaining
strict interval:
\[
311/500<\psi<8959/10500.
\]

[HUMAN_S3_K3_DISTANT_D_NEGATIVE_X.md](HUMAN_S3_K3_DISTANT_D_NEGATIVE_X.md)
then proves the *far D singleton center* has
strictly negative transverse x coordinate. In
the positive R-outer sector, the R-plus-to-outer
mixed gap \(>311/500\) and the R-minus-to-R-plus
inner gap \(>\pi/3\) force the inner R-minus ray
angle \(<-163/200\), and its radius \(>17/20\).
The corresponding exact mixed center-distance
inequality forces angular gap \(>77/100\) from
the far D outer center. If \(x_D\ge0\), the
far D cap polar angle is in \([-\pi/2,-\pi/3)\),
giving a smaller gap and a contradiction.
Thus \(x_D<0\), and with the existing far cap envelope
\[
-13/40<x_D<0,\qquad y_D<0.
\]
The exact rational margins are audited by
[verify_s3_k3_distant_d_sign.py](verify_s3_k3_distant_d_sign.py).

These are **genuine continuous geometric exclusions**,
but they do **not** close the surviving **positive**
S3/k=3 outer-R sector, the S2/k4 small-offset
near-inner case, D1/D2, or the unrestricted
\(R_8\ge\widehat R\). The S4/k7 sharp
candidate equality is preserved.


### Exact transverse clearance of the sole remaining S3/k3 distant D center

The previous S3/k3 far D **negative x sign** theorem
now has a quantitative strict strengthening:
\[
\boxed{-13/40<x_D<-9/500.}
\]
See the appended section of
[HUMAN_S3_K3_DISTANT_D_NEGATIVE_X.md](HUMAN_S3_K3_DISTANT_D_NEGATIVE_X.md).

Indeed the R-minus inner angle and mixed
inner/outer center-angle inequalities force
the D polar ray at least
\[
1427/1750+77/100-\pi/2
>1427/1750+77/100-11/7=7/500
\]
radians *left* of the downward origin diameter.
Since the far D singleton's
longitudinal center coordinate satisfies
\(-y_D>13/10\), the elementary
\(\tan t>t\) gives
\(-x_D>(13/10)(7/500)=91/5000>9/500\).
The script verify_s3_k3_distant_d_sign.py now
also audits the exact rational comparison.

**This is still a necessary center coordinate,
not a whole-square quadrant separator.**
The positive outer-R ray S3/k3 continuum
is unresolved. The global sharp n=8 proof
and Lean handoff remain OPEN.


## 2026-10-12: the entire S3/k=3 branch is now excluded

[HUMAN_S3_K3_FULL_EXCLUSION.md](HUMAN_S3_K3_FULL_EXCLUSION.md)
closes an entire previously unresolved
**exclusive-one-side S3=(3+1,2+1), k=3
outer-center macro-cell**, including its last positive
outer-R angular sector. This is a **whole-domain
analytical impossibility** within that macro-cell,
not another numerical-sample or central-offset strip.

Under k=3 the far L/D singletons are the
first two outer centers; the right R triple
contains one outer and two inner centers,
and both U pair centers are inner.
Previously proved S3/k3 lemmas force
\(h_R>17/200\), \(h_U<1/5\) and sole
outer R ray \(311/500<\psi<8959/10500\).

The **new missing ingredient** is the inner-R-pair
center-height reserve: their both-whole-right
cap projections \(p_x>117/200\), inner radii
\(<1\), and mandatory mutual distance \(\ge1\)
force the *positive-y* inner R center
\[
p_{R_+}.y>49/500.
\]
But the outer R square is **R-only**, hence
**not** wholly beyond central U. Its vertical
center satisfies \(q_y<h_U+\sqrt2/2<227/250\).
The outer-ray interval and radial ceiling
\(r<283/200\) force
\(1/2<q_x<230079/200000\) and \(q_y>1/2\).
With \(117/200<p_{R_+}.x<1\), their squared
center distance obeys
\[
|q-p_{R_+}|^2<
(113079/200000)^2+(81/100)^2
=1-\frac{969139759}{40000000000}<1.
\]
This contradicts disjoint open inscribed half-unit
disks. [verify_s3_k3_global_exclusion.py](verify_s3_k3_global_exclusion.py)
has been executed and checks every rational
margin, but the all-frame geometry is proved
in the written hand note, not by the script.

Thus **S3/k=3 is impossible for every signed
central position and arbitrary frame**.
The former S3/k3 narrow rectangles, angle
sectors and distant singleton deductions should
now be treated as *historical intermediate
conditional theorems*, not still-open branches.

The current *exclusive D0/S=7* k queue is
S1 k=3..6, S2 k=4..6, S3 k=4..7,
S4 k=4..7. The genuine sharp S4/k7 equality
configuration remains. **D0 with corner-only
statuses, D1, D2, exterior contact paths/rings
and the unrestricted \(R_8\ge\widehat R\)
remain open.** No Lean handoff is claimed.


## 2026-10-12: entire S2 nearer-U two-inner-center branch eliminated

[HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md](HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md)
now proves the **complete impossibility** of the
previously narrowed exclusive S2 subbranch
in which both centers on the nearer 2+2
whole cap U have norm **strictly less than one**.
This is a **full continuous-center/orientation
subbranch exclusion**, not merely another bound
on h_R and not a claim that S2 in its entirety
has been excluded.

Under the forbidden antecedent, the previous
outer-polarity theorem forces **two outer**
R-square centers, one inner R center, two
inner U centers, and two outer D centers.
The unique inner R center must lie angularly
*between* the two outer R rays. If it lay
below, its larger radius would put it
too close in angle to the upper far D
outer center; if above, it would be
within 60 degrees of the positive-x
U inner center. The exact mixed center-angle
bound \(>12/25\) radians then forces the
upper outer R ray into the strict interval
\[
43/100<\psi_2<31/50.
\]

The positive-x inner U center is forced into
the strict coordinate rectangle
\[
9/25<u_x<31/50,\qquad
79/100<u_y<47/50.
\]
The positive-y outer R center has radius
\(1\le s<283/200\), and positive ray in
the interval above. A short **hand concavity
reduction** of its squared distance from
the U inner center gives only four rational
vertex bounds, with greatest
\[
|q-u|^2<
4923651/5000000
=1-76349/5000000<1.
\]
This contradicts the mandatory center
distance at least one for two distinct
whole unit squares. All square frames remain
unrestricted. The rational margins are checked
independently in
[verify_s2_near_inner_full_exclusion.py](verify_s2_near_inner_full_exclusion.py),
which has been executed successfully; the
full-domain continuous argument is written
in the theorem note.

**This supersedes the earlier S2 near-inner
conditional conclusions k=4,
h_R<1/10, h_R<1/20, and the transverse
center anchors:** their **antecedent is now
impossible**, so those notes are historical
intermediate proofs, not still-feasible
near-inner subcases.

Every surviving exclusive S2 packing
must instead have **at least one outer-center
square on the nearer 2+2 cap**.
Thus S2/k=4, if any, has exactly one
near-U outer and exactly one R-triple outer
alongside the two far-D outers. Cases with
k=5,6 and other outer-center allocations
remain unresolved. This does **not** alter
the purely symbolic 12-status count or
the equality-bearing S4/k=7 branch.

Alongside the previous **full S3/k=3 exclusion**,
these are genuine branch closures, but
the unrestricted \(R_8\ge\widehat R\)
and Lean handoff remain **OPEN**.


## 2026-10-12: both centers in a very high two-square cap are outer

[HUMAN_TWO_OUTER_HIGH_CAP.md](HUMAN_TWO_OUTER_HIGH_CAP.md)
proves a new **arbitrary-frame, exact whole-cap**
result at the established n=8 disk ceiling:
if two *distinct actual whole squares* lie
beyond a line at outward offset
\[
h\ge97/200,
\]
**both** their centers have norm at least one.
This improves the formerly automatic
single-square outer-center cutoff \(h\ge1/2\)
in the two-square-cap setting, without
presuming aligned square frames.

For a hypothetical inner center p, put
\(a=h+1/2\ge197/200\);
then \(p_x\in[a,1)\) and
\(|p_y|<\sqrt{1-a^2}<173/1000\).
For the other square, the sharp arbitrary-frame
one-square cap envelope gives transverse center
\(|q_y|<81/100\), while the universal norm bound
\(|q|<283/200\) supplies
\(q_x<\sqrt{(283/200)^2-q_y^2}\).
Elementary exact rational comparisons imply
\[
|p-q|^2<
(283/200)^2+1
-2(197/200)(29/25)
+2(81/100)(173/1000)
=1-\frac{543}{200000}<1.
\]
Thus the two center inscribed half-unit disks
would overlap, contradiction.
[verify_two_outer_high_cap.py](verify_two_outer_high_cap.py)
audits the exact inequalities and has been executed
successfully; it is **not** a substitute for
the continuous hand argument.

**New S2/k4 region exclusion:**
on S2's opposite 2+2 axis, with central
signed coordinate t, the nearer cap offset
is \(1/2-|t|\).
If \(|t|\le3/200\), **both** nearer
2+2 centers are now forced outer,
the farther pair are outer, and the
separate perpendicular triple has at least
one outer label: **k>=5**.
Therefore
\[
\boxed{\text{exclusive S2/k=4 requires }|t|>3/200.}
\]
This eliminates an entire closed *central offset
strip* from the newly remaining S2/k4 case,
without claiming that all S2/k4 configurations
are impossible. The valid S4/k7 equality
family is unaffected.

Alongside the recent full S3/k3 and S2
near-inner branch closures, this provides
further genuine continuous-region pruning.
The global \(R_8\ge\widehat R\) remains OPEN.


## 2026-10-12 further continuation: mixed inner/outer near-cap angular polarization

[HUMAN_MIXED_NEAR_CAP_POLARITY.md](HUMAN_MIXED_NEAR_CAP_POLARITY.md)
proves a reusable **arbitrary-frame, full-continuum**
center-angle statement. If two distinct whole
squares in a cap \(y\ge h\ge7/24\) have
one inner center (norm <1) and one outer
center (norm >=1) in the disk with
\(R^2\le9789/2500\), their **polar center-ray
gap is strictly larger than \(3/4\) radians**.
This follows from the exact cosine bound
\[
\cos(3/4)>\frac{73}{100}
\]
and four convex radial endpoint inequalities,
the largest squared-distance upper bound being
\(715289/720000<1\).

If their *transverse center x signs are the same*
(strictly positive or strictly negative),
then the inner center is tightly pinned to
\[
|x_{\rm inner}|<1/4,
\]
while the outer center is forced away:
\[
|x_{\rm outer}|>7/10.
\]
The outer center's polar ray is farther from
the positive y axis: lower polar angle in
the +x half-plane and higher angle in the -x
half-plane. This is a statement about
**centers**, not whole-square quadrant
containment. The latter cannot be inferred
from a center sign.

In particular the remaining **exclusive S2/k=4**
case has one inner and one outer on its nearer
2+2 cap, by the previously proved global
S2 near-inner exclusion and the outer-count
identity. Hence **every** surviving S2/k4
configuration has the strict \(>3/4\) mixed
near-cap gap; each *same-sign* transverse
subcase must also satisfy the two absolute
coordinate inequalities above.
The *opposite-sign* subcases are **not**
eliminated by this argument.

[verify_mixed_near_cap_polarity.py](verify_mixed_near_cap_polarity.py)
audits the exact rational margins and has been
executed locally, but does not replace the
hand center-angle argument or prove the
unrestricted eight-square theorem.

This additional continuous geometric pruning
does **not** finish S2/k4, S1/S3/S4, D0
corner-only branches, D1/D2, contact-graph
alternatives, or \(R_8\ge\widehat R\).
The genuine S4/k7 equality packing remains.


## 2026-10-12: further all-frame mixed-center near-cap polarity and near-axis exclusions

A completed reusable lemma is
[HUMAN_MIXED_NEAR_CAP_POLARITY.md](HUMAN_MIXED_NEAR_CAP_POLARITY.md):
for two distinct whole unit squares in a common cap
at offset \(h\ge7/24\), one inner-center and one
outer-center, their **polar center-ray gap
exceeds \(3/4\) radians** for arbitrary
square orientations. This follows from the
actual inscribed-center unit distance, the
cap-projection radial bounds
\(19/24\le r_{\rm inner}<1\),
\(1\le r_{\rm outer}<283/200\),
and an elementary separately convex
cosine-law rectangle with largest upper
corner \(715289/720000<1\).

For the *same strict transverse x sign*,
the inner member is forced near the origin
diameter \(|x_{\rm inner}|<1/4\)
and the outer member far away
\(|x_{\rm outer}|>7/10\). The outer
center ray is farther from the positive
y diameter (ordered downward in +x,
upward in -x). There is no claim that
a center sign gives a whole-square quadrant
separator.

A second independent all-frame theorem,
[HUMAN_MIXED_HIGH_CAP_SIGN_SPLIT.md](HUMAN_MIXED_HIGH_CAP_SIGN_SPLIT.md),
uses the **sharp one-square cap transverse
envelope**, valid at \(h\ge2/5\), to prove that
such a mixed inner/outer pair in one cap
**must have strictly opposite transverse
center signs**. In the hypothetical same-sign
case its outer x coordinate would obey
\(7/10<|x_{\rm outer}|<9/10\)
and outer y coordinate \(9/10\le y_{\rm outer}
<123/100\); the inner center has
\(|x_{\rm inner}|<1/4\) and
\(9/10\le y_{\rm inner}<1\).
Their squared separation would then be
\[
< (9/10)^2+(33/100)^2
=9189/10000<1,
\]
contradicting the two inscribed half-unit disks.
The margin \(811/10000\) is exact.

The **same-side arbitrary-frame case below
h=2/5 is *not* claimed eliminated**.
[HUMAN_SAME_SIDE_NEAR_AXIS_CAP.md](HUMAN_SAME_SIDE_NEAR_AXIS_CAP.md)
gives a complementary **open near-axis orientation
exclusion**: if two distinct whole cap members at
\(h\ge7/24\) have the same weak transverse
center sign, **both** frames cannot be within
\(1/2600\) radians of the central axes.
Each actual square would otherwise contain
a centered axis-aligned \(2600/2601\)-square;
the two parallel smaller squares would require
\[
R^2\ge
(7/24+2600/2601)^2
+(9/4)(2600/2601)^2
=q_+ +21634201/270608040000>q_+.
\]
This result is conditional on both small frame
tilts; it neither asserts arbitrary-frame
impossibility nor changes the S4 equality construction.

**S2/k=4 application.** Exactly one nearer
2+2 center is inner and one outer. Their
polar gap is always \(>3/4\); when
\(h_{\rm near}\ge2/5\) their transverse x
center signs are necessarily **opposite**.
When \(7/24<h_{\rm near}<2/5\),
a same-sign pair must have
\(|x_{\rm inner}|<1/4\),
\(|x_{\rm outer}|>7/10\) and at least one
frame deviation \(>1/2600\) radians.
These are explicit **necessary continuous
positional cases**, not finished S2/k=4
or unrestricted n=8 proof.

The three optional exact-fraction audit scripts
verify all cited strict rational margins and
have been executed locally. The global
\(R_8\ge\widehat R\), D0 corner-only, D1/D2
and equality classification remain OPEN.


## 2026-10-12: exact surviving S2/k4 three-cell queue and common true-square slice

[HUMAN_S2_K4_THREE_CELL_QUEUE.md](HUMAN_S2_K4_THREE_CELL_QUEUE.md)
combines the latest proved *necessary* constraints into
an exhaustive **three-cell continuous S2/k4 queue**.
The case has R:3,L:0,U:2,D:2 with U nearer, and
\[
0<h_R<13/100,\qquad
7/24<h_U<97/200.
\]
There are exactly two far-D outer centers, one
near-U **inner**, one near-U **outer**, and
one outer/two inner right-triple centers.
The D outer pair has opposite signed transverse
center coordinates. Every mixed U pair has strict
polar gap \(>3/4\) radians.

The three exhaustive cells are:

* **A:** \(2/5\le h_U<97/200\). The near-U inner
  and outer centers must have **strictly opposite**
  transverse x signs, by the new
  [HUMAN_MIXED_HIGH_CAP_SIGN_SPLIT.md](HUMAN_MIXED_HIGH_CAP_SIGN_SPLIT.md).
* **B:** \(7/24<h_U<2/5\), with near-U transverse
  center signs strictly opposite. No frame
  alignment is inferred.
* **C:** \(7/24<h_U<2/5\), with near-U transverse
  center sign product **nonnegative**. The
  inner x absolute value is \(<1/4\), outer x
  absolute value \(>7/10\) (including the
  possible inner x=0 boundary); at least one
  actual near-U frame must be tilted **more
  than \(1/2600\) radian** from the central axes.

The **outer** near-U center can never have
zero transverse x coordinate, by the
boundary-completed mixed polar lemma.
Thus the three cells include every zero-sign
boundary and no false omitted case.

[HUMAN_TWO_CAP_SHARED_MIDSLICE_CHORDS.md](HUMAN_TWO_CAP_SHARED_MIDSLICE_CHORDS.md)
adds a useful **actual whole-square** ordering
common to all A/B/C: the line
\(y=(R+h_U)/2\) intersects each nearer-U
square in a horizontal open chord of length
**at least one**, for any independent frame.
The two chords are disjoint and have a real
left-to-right order; rotated frames give
strictly longer chords. On a sloping
flank the complete-domain chord lower bound
is \(>667/600\), by exact \(R<99/50\) and
\(h_U>7/24\).

This **does not** assert horizontal projections
of the entire oblique squares are disjoint.
Nor are A/B/C proved empty: the next goal is
to couple those common-slice segments to
disk vertices, outer-center angular lanes,
actual inter-square separating axes, and the
remaining five exterior squares. No sampling
result has been promoted to an analytic proof.

The previously proved sharp S4/k7 equality
configuration is preserved. The unrestricted
radius theorem \(R_8\ge\widehat R\), full
equality classification, and Lean n=8
handoff remain **OPEN**.


## 2026-10-12 continuation: actual rotated two-square guardrail, quadrant owner, local five-square S1 pruning

Three further results clarify the exact still-open
exclusive S2/k4 and S1/k3 continua.

**1. A positive exact *local counterexample* against
a universal two-square same-sign cap exclusion.**
[RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md](RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md)
exhibits two *actual* independently rotated,
interior-disjoint unit squares with both center
x coordinates strictly positive, both wholly
above the offset \(h=881/3000=7/24+1/500\),
and both contained in a disk of squared radius
\[
7040861/1800000<9789/2500.
\]
The rational SAT separating-axis gap is
\(31/48120>0\), and the disk radius reserve is
\(7219/1800000>0\). Its exact verifier checks
all **eight true square vertices**.
**Both example centers are outer**, so it does
*not* show the full S2/k4 *mixed inner/outer*
cell C is feasible. It proves only that a
blanket, all-frame, same-sign **two-square**
cap theorem would be false.

**2. A genuine whole-quadrant owner in mixed
same-sign caps.**
[HUMAN_MIXED_CAP_WHOLE_QUADRANT_OWNER.md](HUMAN_MIXED_CAP_WHOLE_QUADRANT_OWNER.md)
strengthens the existing polar gap
\(>3/4\) radians when two whole squares
in a cap \(y\ge h\ge7/24\) have one inner
and one outer center with **nonnegative
transverse center-sign product**. The outer
whole square is forced into **one entire
open origin quadrant**, not merely its
center: its signed x distance from the
vertical diameter is
\[
>\frac{14953}{20480}-\frac{71}{100}
=\frac{2061}{102400}>\frac1{50}.
\]
This holds for all square frames and also
covers the inner x=0 boundary. The earlier
quadrant-capacity theorem then forbids
any *other entire square* from occupying
that same quadrant. It is an additional
true-square constraint on the still-open
S2/k4 cell C, **not** a full cell exclusion.

**3. A reusable local five-square theorem
prunes exclusive S1/k3.**
[HUMAN_FIVE_SQUARE_LOCAL_RU_OBSTRUCTION.md](HUMAN_FIVE_SQUARE_LOCAL_RU_OBSTRUCTION.md)
extracts the actual five-square geometric
core of the former exclusive S3/k3 proof.
If a right whole cap at \(h_R>17/200\)
contains *two inner-center and one outer-center*
square, a perpendicular upper cap at
\(h_U>17/200\) contains *two more distinct
inner-center squares*, and the R-outer square
is **not** wholly beyond the U side, then
the five units cannot all fit in the
\(q_+=9789/2500\) disk. The proof splits
at \(h_U=1/5\): above it, use the general
refined five-square angular theorem;
below it, use the exact four-inner ray
order, negative outer-R ray exclusion,
inner R+ height reserve \(>49/500\),
and the outer R's lack of an U cap to force
the strict center-distance upper bound
\[
|q-p_{R+}|^2<
1-\frac{969139759}{40000000000}<1.
\]
Crucially this five-square statement
**does not require S3**, a far singleton,
or any of the other three exterior labels.

In **exclusive S1=(3+0,3+1), k=3**,
normalize the 3+1 triple to R and its
opposite far singleton to L. The L square
and one member of each perpendicular
triple are the three distinct outer
labels, so R and U each have exactly
two inner and one outer centers. The
far L singleton forces the R (3+1)
triple offset \(h_{31}>17/200\).
The local five-square theorem consequently
gives the new strict-position requirement
\[
\boxed{0<h_{30}\le17/200}
\]
for the perpendicular **3+0** triple side.
If \(h_{31}\le1/10\), the earlier exact
low-offset piercing rectangle improves
this further to \(0<h_{30}<1/16\).
**S1/k3 is still open** in its remaining
small-offset continuum.

None of these results excludes the actual
S4/k7 sharp equality construction or
proves the unrestricted reverse bound
\(R_8\ge\widehat R\). D0 corner-only,
D1/D2, contact graph alternatives and
the eventual Lean handoff remain OPEN.


### 2026-10-12: S1/k3 tightened to a uniform h30<1/16

[HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md](HUMAN_FIVE_SQUARE_RU_ONE_SIXTEENTH.md)
substantially strengthens the preceding
R-only five-square theorem:
the necessary perpendicular U offset
is now **only \(h_U\ge1/16\)** rather than
the older \(h_U>17/200\). The three R-cap
squares still require \(h_R>17/200\),
two R inner-center labels, and one
outer R-only label. The two U inner
labels must be **distinct** from all
three R members.

The new low-perpendicular-offset proof
uses \(\arcsin(h_U+1/2)>\!297/500\)
and a *new* radius-\(>9/16\) inner/outer
polar gap \(>59/100\) radians. It also
proves a strengthened \(>779/1000\)
polar gap whenever the inner center
radius is \(>9/10\). If the R outer
ray is negative, exact Taylor and radial
endpoint comparisons force its R-minus
inner center to violate the mandatory
\(p_x>117/200\). If the R outer ray
is positive, it lies between
\(311/500\) and \(2392/2625\),
and the same R-only upper nonmembership
and positive-y inner R center reserve
as in the previous full S3/k3 proof
force squared center separation
\(<1-969139759/40000000000\).

The exact-fraction script
[verify_five_square_ru_one_sixteenth.py](verify_five_square_ru_one_sixteenth.py)
replays the new strict cosine, sine and
four-corner radial margins, with **all**
new rational identities checked. It is not
a computer classifier or Lean formalization.

Consequently, for **exclusive S1=(3+0,3+1)
with exactly k=3 outer centers**, the far
singleton on the 3+1 axis implies its
triple offset \(h_{31}>17/200\). Each
perpendicular triple has exactly
two inner and one outer labels, and
all selected whole-side statuses are
exclusive. The five-square theorem
then excludes *every*
\(h_{30}\ge1/16\). The new exact
necessary region is therefore
\[
\boxed{0<h_{30}<1/16}
\]
**uniformly for all permitted \(h_{31}\)**.
This replaces the earlier weaker
\(h_{30}\le17/200\) or conditional
\(h_{30}<1/16\) statements.

The **remaining tiny-offset S1/k3
continuum remains open**. No claim is
made that S1/k3 is globally impossible,
or that the unrestricted
\(R_8\ge\widehat R\) has been closed.
The valid S4/k7 sharp equality packing
remains admitted.


### 2026-10-12: S1/k3 far 3+1 singleton lies strictly opposite the 3+0 triple

[HUMAN_S1_K3_FAR_SINGLETON_OPPOSITE_SIGN.md](HUMAN_S1_K3_FAR_SINGLETON_OPPOSITE_SIGN.md)
eliminates a further genuine continuous
**signed-center subbranch** inside the still-open
exclusive S1=(3+0,3+1), k=3 macro-case.

Normalize the 3+1 axis as R:3, L:1
and the perpendicular 3+0 axis as U:3,D:0.
If the far L singleton's actual center
were on or above the horizontal origin
diameter (\(y_L\ge0\)), the outer
L center's angle \(\phi_L\le\pi\)
would repel the northwest U-inner
center \(U_-\) by the previously proved
mixed center-angle gap \(>2\pi/9\).
This forces its center ray
\(\theta_{U-}<7\pi/9\).

The three consecutive pairwise
inner-center angular gaps \(>\pi/3\)
then force
\[
\theta_{U+}<4\pi/9,\quad
\theta_{R+}<\pi/9,\quad
\theta_{R-}<-2\pi/9.
\]
That last R-inner bound makes its radial
norm \(>7/10\), so the sole outer R ray
cannot lie below it. Nor can the outer R
ray lie above the U+ inner ray because
of the exact mixed \(>12/25\)-radian
center-gap lemma.

If the outer R ray lay below R+, a
strict \(>2\pi/9\) mixed gap would force
R-minus below \(-24/25\) radians,
violating its *whole R-cap*
x projection \(>117/200\).
If it lay above R+, it would satisfy
\[
311/500<\psi_R<\pi/3;
\]
its required **R-only** failure of U
whole-cap membership then forces
squared distance \(<1-969139759/40000000000\)
from the positive-y inner R center,
another contradiction.

Therefore the strict necessary
center-sign condition is
\[
\boxed{y_L<0}
\]
for the far L singleton in that
normalization. Under rotations/reflections,
its transverse sign is **opposite to
the 3+0 triple's outward side normal**.
All rational trigonometric margins are
audited by
[verify_s1_k3_far_singleton_sign.py](verify_s1_k3_far_singleton_sign.py).

Combined with the separately proved
uniform \(0<h_{30}<1/16\) condition,
this narrows S1/k3 to tiny perpendicular
offsets and one far-singleton center side.
**It does not close the residual S1/k3
continuum**, the other S1 outer counts,
or the unrestricted radius inequality
\(R_8\ge\widehat R\).


### Stronger 2026-10-12 S1/k3 far-singleton transverse clearance

The *signed far singleton* S1/k3 lemma
has a strict quantitative upgrade in
[HUMAN_S1_K3_FAR_SINGLETON_CLEARANCE.md](HUMAN_S1_K3_FAR_SINGLETON_CLEARANCE.md).

In R=3,L=1,U=3,D=0 normalization,
the single L-square's far-left center has
\[
\boxed{-3/20<y_L<-1/75}.
\]
Its far-side whole-cap envelope establishes
the absolute bound \(|y_L|<3/20\).
To obtain the new strict **negative
clearance**, suppose \(-1/75\le y_L<0\).
The far-L ray would deviate from
the negative x direction by less than
\(4/411<1/100\) radians because
\(-x_L>137/100\). The mixed inner/outer
ray gap \(>2\pi/9\) then forces
the northwest U-inner ray below
\(7\pi/9+1/100\), giving the three
successive strict inner ray upper/lower
bounds with +1/100 slack.
The sole outer R-center ray cannot
lie below R+, or the R-minus inner
center loses its whole-side x projection;
if it lies above R+, its **R-only**
non-U membership again forces center
squared distance \(<1-969139759/40000000000\)
from R+.

The new exact-fraction audit
[verify_s1_k3_far_singleton_clearance.py](verify_s1_k3_far_singleton_clearance.py)
checks all displayed strict margins.
The resulting **still-open** S1/k3
region satisfies
\[
17/200<h_{31}<13/100,\quad
0<h_{30}<1/16,\quad
-3/20<y_L<-1/75.
\]
All conditions are necessary, not
existence certificates or a global S1
exclusion. In particular, the valid
S4/k7 equality construction survives,
and the unrestricted
\(R_8\ge\widehat R\) remains OPEN.


## 2026-10-12: successful computer-to-hand cap breakthrough and next attack roadmap

[COMPUTER_ASSISTED_ATTACK_ROADMAP.md](COMPUTER_ASSISTED_ATTACK_ROADMAP.md)
now specifies the actual numerical experiment,
a completed analytic theorem extracted from it,
and the prioritized still-open proof tasks.
The exploratory script
[computer_two_square_cap_probe.py](computer_two_square_cap_probe.py)
models **true square vertices**, eight signed
separating axes, genuine whole caps, and mixed
inner/outer centers, using local nonconvex
SLSQP. Reproducible 5-start runs at h=7/24,
1/3 and 37/100 found **near-axis** candidates.
The numerical solvers had tiny negative
constraint residuals and unsuccessful termination:
the numeric values are **not certified**
global optima or exclusion proofs.
The **exact axis-aligned reference geometry**
requires
\[
q_{\rm axis}(h)=(1+h)^2+9/4,
\quad q_{\rm axis}(7/24)=2257/576
>q_+=9789/2500.
\]

**Successful computer-to-hand conversion.**
[HUMAN_CAP_ENVELOPE_37_100.md](HUMAN_CAP_ENVELOPE_37_100.md)
proves a new **full-frame, full-position**
sharp single-square cap envelope at the
established n=8 disk ceiling:
\[
S\subseteq D_R\cap\{x\ge h\},\
R^2\le q_+,\ h\ge37/100
\Longrightarrow
R^2\ge(h+1)^2+(|p_y|+1/2)^2.
\]
The prior standalone theorem had only
h>=2/5. The hand proof derives
\(y<1,\ h+y<7/5\) independently of its
conclusion, applies negative-frame vertex
concavity, and checks a **four-vertex
affine-polynomial positivity certificate**
over every positive frame angle. The
tightest new polynomial tangent margin
is \(553/78125>0\). Its verifier
[verify_cap_envelope_37_100.py](verify_cap_envelope_37_100.py)
was executed with exact Fractions;
the continuum result is proved in the
note and not inferred from the numerical
optimizer.

The consequent
[HUMAN_MIXED_HIGH_CAP_37_100.md](HUMAN_MIXED_HIGH_CAP_37_100.md)
proves **every mixed inner/outer two-square
whole-cap pair** at offset \(h\ge37/100\)
has strictly **opposite transverse
center signs**, for arbitrary independent
frames. If signs were weakly same, the
older mixed polar lemma would force
\(|x_{\rm inner}|<1/4\) and
\(|x_{\rm outer}|>7/10\); the new cap
envelope forces \(|x_{\rm outer}|<93/100\),
and the universal radial ceiling forces
vertical center separation \(<9/25\).
Thus their squared center distance would obey
\[
< (93/100)^2+(9/25)^2
=1989/2000=1-11/2000<1,
\]
a genuine strict hand contradiction.
[verify_mixed_high_cap_37_100.py](verify_mixed_high_cap_37_100.py)
audits all exact rational margins.

**Updated exhaustive exclusive S2/k4 three cells:**
* A: \(37/100\le h_U<97/200\), opposite x signs.
* B: \(7/24<h_U<37/100\), opposite x signs.
* C: \(7/24<h_U<37/100\), weak same x signs,
  with earlier stringent inner/outer coordinate,
  whole-quadrant and frame-defect conditions.

This **strictly removes** the old same-sign
interval \(37/100\le h_U<2/5\) (in addition
to the earlier high-offset region).
**None of A/B/C is now globally empty.**
The new computer experiment suggests a
stronger, *unproved* whole mixed same-sign
pair bound \(R^2\ge(h+1)^2+9/4\) for h>=7/24.
That should be attacked using the **actual
SAT-owner/sign branches** and rationalized
frame angles, not assumed from the optimizer.

Do not discard the real S4/k7 sharp equality
packing. D0 corner-only cases, D1/D2,
higher-k outer paths/rings, unrestricted
\(R_8\ge\widehat R\), equality classification
and Lean 4 formalization remain OPEN.


### Exact opposite-sign mixed cap pair as a negative control for S2 cells A/B

[RATIONAL_OPPOSITE_SIGN_MIXED_CAP_PAIR.md](RATIONAL_OPPOSITE_SIGN_MIXED_CAP_PAIR.md)
provides two *actual axis-parallel unit squares* in a cap
at \(h=2/5\), one with inner center
\((-3/10,9/10)\) and one with outer center
\((4/5,9/10)\), in **opposite transverse
origin half-planes**. They have exact
strict SAT separation \(1/10>0\), and all
eight true vertices fit inside squared radius
\(73/20<q_+\) with margin \(166/625>0\).
[verify_opposite_sign_mixed_cap_pair.py](verify_opposite_sign_mixed_cap_pair.py)
checks their exact true vertices and center classes.

This is **only a two-square local witness**, not
a valid S2/k4 eight-square arrangement. It proves
that neither remaining opposite-sign cell A nor B
can be eliminated **solely** by the near-U
inner/outer two-square cap constraints:
their far-D pair, right triple, central square,
or further true-square SAT inequalities must
be used. Unlike this exact feasible
opposite-sign pair, the same-sign mixed pair
at h>=37/100 is rigorously impossible by
the new cap envelope hand proof.

The roadmap and the still-open unrestricted
\(R_8\ge\widehat R\) status are unchanged.


## 2026-10-12: second computer-to-hand cap breakthrough and exact counterexample boundary

A second round of **genuine computer-assisted discovery**
plus exact human mathematics has improved the previous
mixed-cap sign cutoff in three increasingly strong,
fully proved stages: \(h\ge1/3\), \(h\ge8/25\),
and finally
\[
\boxed{h\ge79/250=0.316.}
\]
The earlier full-frame 37/100 theorem remains valid but
is now superseded in threshold.

**Sharp one-square cap theorem at 79/250.**
[HUMAN_CAP_ENVELOPE_79_250.md](HUMAN_CAP_ENVELOPE_79_250.md)
proves that if an arbitrary-frame whole
unit square S with center (x,y) lies in a disk with
\(R^2\le q_+:=9789/2500\) and in the cap \(x\ge h\ge79/250\),
then
\[
R^2\ge(1+h)^2+(|y|+1/2)^2.
\]
The true-square proof first obtains \(h+y<7/5\)
from the actual (1,1) support direction.
Computer-assisted **exact rational Bernstein
coefficient search** located a four-parameter-vertex
positivity certificate for the genuine positive-frame
two-vertex polynomial. The certificate covers all
real tilt half-tangents \(z\in[0,\sqrt2-1]\subset[0,1/2]\):
**63 exact degree-six Bernstein coefficients**
over nine rational subintervals have positive
minima, with smallest \(4322111/1310720000>0\).
The top-edge certificate at
\(y=49/50\) is used **before** deriving the
center-height bound \(y<49/50\),
avoiding circular reliance on the desired
cap envelope. Negative-frame squared-vertex
concavity contributes the exact diagonal margin
\(57/2500>0\).

The proof is completely analytic over all
frames, positions, signs and disk-containment
parameters; the optional exact
[verify_cap_envelope_79_250.py](verify_cap_envelope_79_250.py)
replays arithmetic only.
The exploratory script
[computer_cap_bernstein_discover.py](computer_cap_bernstein_discover.py)
reproduces rational coefficient-search successes
and failures, but a negative scan is NOT
proof of any theorem's failure.

**Sharp mixed-inner/outer center sign theorem at 79/250.**
[HUMAN_MIXED_HIGH_CAP_79_250.md](HUMAN_MIXED_HIGH_CAP_79_250.md)
combines that exact single-square envelope
with the older universal mixed polar
\(>3/4\) gap and radial center bound
\(|q|<283/200\).
If two **whole squares** in the same
cap \(h\ge79/250\) have one inner and
one outer center, their transverse
center coordinates must have
**strictly opposite signs**.
For same weak signs, normalize
\(0\le p_x<1/4<7/10<q_x<489/500\),
\(a:=102/125\le p_y<1\)
and \(q_y\ge a\).
Keeping the coupled outer radial
inequality, the two possible y-orders
force respectively
\[
|p-q|^2<999361/1000000<1,
\quad
|p-q|^2<49517/50000<1.
\]
The nearest tight **positive reserve**
is \(639/1000000>0\). Exact checks
are in [verify_mixed_high_cap_79_250.py](verify_mixed_high_cap_79_250.py).
The weak inner x=0 boundary is included
correctly by using \(|q_x-p_x|\le q_x\);
the final contradiction remains strict
from the radial bound.

**Critical mathematical counterexamples.**
[RATIONAL_DIAGONAL_CAP_ENVELOPE_COUNTEREXAMPLE.md](RATIONAL_DIAGONAL_CAP_ENVELOPE_COUNTEREXAMPLE.md)
gives a true \(45^\circ\) square at
\(h=293/1000>7/24\) which fits
under \(q_+\) but *violates*
the aligned-square one-cap envelope.
A stronger **fully rational-frame**
witness in
[RATIONAL_ROTATED_CAP_ENVELOPE_THREE_TENTHS.md](RATIONAL_ROTATED_CAP_ENVELOPE_THREE_TENTHS.md)
also violates that inequality at
\(h=3/10=0.3\), with exact genuine
four-vertex circle reserve
\(1953173771/272891522000>0\).
Neither one-square counterexample is
a mixed-center two-square arrangement,
so neither contradicts the new 79/250
mixed-pair theorem. They **prohibit**
silently extending the same one-square
envelope to the remaining offset interval.

**Latest S2/k4 exact three cells, all still open:**
A \(79/250\le h_U<97/200\), opposite signs;
B \(7/24<h_U<79/250\), opposite signs;
C \(7/24<h_U<79/250\), weak same signs,
with its prior whole-quadrant owner,
strict center magnitudes, and mandatory
frame-defect constraints. The entire
previous same-sign offset band
\([79/250,37/100)\) is now excluded.
The residual width of C is
\[
79/250-7/24=73/3000.
\]
**No A/B/C cell is yet entirely eliminated.**

The roadmap
[COMPUTER_ASSISTED_ATTACK_ROADMAP.md](COMPUTER_ASSISTED_ATTACK_ROADMAP.md)
now prioritizes **true two-square separating-axis
inequalities** in this remaining C interval
instead of indefinitely tightening one-square
thresholds. Separate opposite-sign A/B local
pairs are actually feasible, so A/B require
the far-D pair/right-R triple/central square
and valid inter-square axes.

The entire unrestricted radius inequality
\(R_8\ge\widehat R\), global equality
classification, and Lean formalization
remain OPEN; the exact sharp S4/k7
equality ring must be retained.


## 2026-10-12: decisive switch to whole-packing stress architecture

**This work is deliberately not another cap threshold update.**

[HUMAN_GLOBAL_STRESS_ROOTS.md](HUMAN_GLOBAL_STRESS_ROOTS.md)
combines the existing rigorous
physical-contact/stress theorems into
**four exhaustive global minimizer roots**:

* **A:** full seven-outer *actual-contact
  cycle*, explicitly realized by the sharp
  equality candidate;
* **B2:** central square C has exactly two
  positive-stress contact neighbors,
  hence two opposite contact normals;
* **B3:** C has at least three positive-stress
  neighbors (true central branching);
* **X:** no positive C contact; the unique
  nontrivial stress component has an
  exterior directed moment cycle of
  5..7 squares containing an actual
  **noncentral inner-center** label.

[HUMAN_EXTERIOR_STRESS_INNER_WITNESS.md](HUMAN_EXTERIOR_STRESS_INNER_WITNESS.md)
proves the root-X witness is a genuinely
**circle-free exterior square** with
\(1/2<|p|<1\), and has at least
two positive-moment incident contacts.
In a minimum-*actual*-contact representative,
an *actual-degree-two* witness is
a genuinely aligned opposite-side
transmitter with neighbors at exact
distance one; **actual degree>=3**
is kept as a separate unsolved branch.
Positive degree two alone does not
justify the transmitter theorem.

**New global graph normal form.**
[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md)
proves that with **seven outer centers,
no full outer actual cycle, and C
positive stress degree two**, the unique
nontrivial positive-stress component
is exactly one C-rooted cycle
\[
C-S_1-\cdots-S_m-C,\quad 3\le m\le7,
\]
of circularly consecutive outer labels,
with **no dangling positive-stress
outer edges**. Every positive outer
edge has nonzero signed contact moment,
which forces it onto a directed
cycle through C. Exactly two C forces
are opposite/equal. A short independent
graph enumeration checks seven labeled
supports per m, 35 total before geometry;
these are *graph templates*, not feasible
square packing certificates.

**Complete exclusion of an entire global stress subcase.**
[HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md](HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md)
proves, for any two genuine whole
squares beyond opposite supports of
the origin-containing C,
\[
p_A\cdot p_B<-4/25,\qquad
\angle(p_A,p_B)>\pi/2+1/13.
\]
The four-band exact all-frame hand
argument uses the established sharp
one-square cap envelope **only at
offset h>=2/5**, and radial bounds
on the smaller-cap side. The listed
seven exact rational square comparisons
are audited independently in
[verify_opposite_central_neighbor_angle.py](verify_opposite_central_neighbor_angle.py).

[HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md](HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md)
then eliminates **m=7** from the
seven-outer, actual-path, C-positive-degree-two
stress root: six true outer contact
gaps each \(>\pi/4-1/500\)
force the *missing* seventh gap
\[
\gamma<\pi/2+3/250,
\]
whereas the opposite C contact normals
force \(\gamma>\pi/2+1/13\).
The contradiction has an exact positive
rational reserve \(211/3250>0\).
There is **no geometry-dependent
parameter exception** to this m=7
exclusion. The real candidate has
a **full outer actual contact cycle**,
so belongs to root A and remains
valid.

Thus the **currently unexcluded k7/B2
actual-path stress cycle sizes** are
\[
\boxed{m=3,4,5,6},
\]
with seven labeled cyclic placements
each: **28** conditional positive
stress graph supports. The exterior
zero-stress spectators (7-m actual
squares) still occupy physical space.
The m=7 support branch is **completely
closed**, not merely a narrowed
offset strip.

[STRUCTURAL_GLOBAL_CLOSURE_ROADMAP.md](STRUCTURAL_GLOBAL_CLOSURE_ROADMAP.md)
is now the **primary forward research
roadmap**, replacing small cap-constant
tuning. It prioritizes the k7/B2 m=6
cycle **including its one spectator**,
then m=5..3, the equality-preserving
outer ring A, the C-branching B3 case,
and the exterior near-center inner
witness X case, together with k<=6
central-stressed variants. Every
computer probe must use all 32 true
square vertices, all 28 genuine SAT
pair constraints, and independently
checked stress force/torque balance.

**Unresolved:** the sharp global
\(R_8\ge\widehat R\), root A,
remaining B2 cycle lengths, B3,
X, k<=6, D0 corner-only/D1/D2
and full equality classification,
and Lean 4 formalization.


## 2026-10-12 structural continuation: true central-force axes, diagonal bracing and outer path vertex covers

**This continuation closes actual contact-graph subcases, not
additional numerical cap-offset bands.** The new primary
roadmap is
[STRUCTURAL_GLOBAL_CLOSURE_ROADMAP.md](STRUCTURAL_GLOBAL_CLOSURE_ROADMAP.md),
with the current proof gate indexed at its top.

**Central positive-degree-two forces have only four axes.**
[HUMAN_TWO_CENTRAL_FORCE_AXES.md](HUMAN_TWO_CENTRAL_FORCE_AXES.md)
proves that if the circle-free central unit C has
exactly two positive-stress contact neighbor
pairs, force balance gives opposite equal
normals ±n and **torque balance quantizes
n to just four central-frame axes**:
the two side axes or the two diagonals.
In side mode their two true contact points
lie on opposite C sides at the **same
transverse coordinate**. In diagonal mode
they lie at opposite C vertices.
No continuously oblique third force
mode survives true equilibrium.

**Diagonal central support requires two-sided real bracing.**
[HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md](HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md)
proves that in a *minimum-actual-contact*
least-radius representative, diagonal
positive C degree two is incompatible with
fewer than **four distinct actual C
contact neighbors**. The two additional
actual contact pairs have **zero positive
stress** and their genuine outward
separating normals have **opposite signed
tangential projections** against the
stressed diagonal. The hand proof
rotates C to open both opposite
diagonal corner contacts by
\((1-\cos\theta)/\sqrt2>0\),
then translates tangentially with
magnitude \(K|\theta|\) to release
every one-sided extra contact.
Without opposing auxiliary normals
all true C contacts disappear while
preserving disk and noncontact gaps,
contradicting the minimum-contact
choice. This fully eliminates the
bare-diagonal-two-spoke and
diagonal-plus-one-brace subcases.

**All k7/B2 stressed path endpoints have boundary/spectator obligations.**
[HUMAN_B2_ENDPOINT_BOUNDARY_OR_SPECTATOR.md](HUMAN_B2_ENDPOINT_BOUNDARY_OR_SPECTATOR.md)
proves that when C has **exactly
two actual neighbors** and the k7
positive stressed path uses m=3..6
consecutive outer labels, each stressed
endpoint **must** have either a
true circle vertex or an actual
contact with its next spectator.
Both endpoints circle-free requires
m<=5. In m5 it forces the complete
seven-outer actual-contact graph to
be a path missing *only* the single
edge between the two spectators.
A finite graph enumeration (independently
checked) gives 392 purely combinatorial
outer actual supergraphs across m3..6
(217,105,49,21), none assumed feasible.

**Whole m6 case has a three-mode actual contact structure.**
[HUMAN_M6_THREE_ACTUAL_CONTACT_MODES.md](HUMAN_M6_THREE_ACTUAL_CONTACT_MODES.md)
proves an exhaustive P/S/K split
for k7, C-positive-degree-two, m6:
P has only two actual C neighbors and
at least one true circle-contact
outer stressed endpoint; S has exactly
one additional C actual contact to
the sole spectator T, which **must
have a true circle vertex**; K has
an actual zero-weight C chord to
some stressed internal path square.
Diagonal C two-force mode necessarily
belongs to K and has extra
two-sided tangential bracing. With
only one spectator, if T does not
touch C the diagonal case has **at
least two distinct internal actual
C chords with opposite tangential
normal signs**.

**A leaf monopolizes its side, forcing an orthogonal scaffold.**
[HUMAN_LEAF_EXCLUSIVE_CENTRAL_SIDE.md](HUMAN_LEAF_EXCLUSIVE_CENTRAL_SIDE.md)
proves an actual one-contact leaf
square T in a minimum-contact n8
minimizer is radial, parallel to C
and wholly beyond a **unique**
C side cap of offset
\(b=\sqrt{R^2-1/4}-1>4/5\).
No second whole unit square can
occupy the same high cap under
the search ceiling: the rigorous
all-frame pair center squared-distance
upper bound is \(164761/360000<1\).
Consequently in **side-stressed
B2** any actual C leaf must attach
on one of the **two perpendicular
central sides**, not on either of
the positively stressed side
normals. The m6 spectator leaf
specialization is in
[HUMAN_M6_PERPENDICULAR_SPECTATOR_LEAF.md](HUMAN_M6_PERPENDICULAR_SPECTATOR_LEAF.md).

**New internal stressed-path *vertex-cover invariant*.**
[HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md](HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md)
proves, *for every k7/B2 stressed
outer path m=3..6*, each pair of
consecutive internal stressed squares
has at least one member that **truly
touches the circle or has an actual
C chord**. Otherwise the pair
would be adjacent strictly circle-free
actual-degree-two aligned transmitters,
forbidden at R<2. Thus the true
circle-or-chord internal anchors
form a path vertex cover, with minimum
counts \(0,1,1,2\) for m=3,4,5,6.
An exact 0/1 graph verifier audits
the combinatorial statement.

**Immediate strong m6 consequences:**
P and S have **no internal C
chords**. Each must therefore have
at least **two different internal
outer stressed square circle contacts**.
P also forces at least one stressed
path **endpoint** circle contact,
and S forces the **spectator**
circle contact. Thus **P and S
each have at least THREE distinct
true circle-contact exterior squares**.
In K, at least two distinct
internal labels must be circle
contacts or genuine C-chord
endpoints: a *single* internal
chord with no other circle/chord
anchor is **fully impossible**.

**A new m3 parallel scaffold consequence.**
When m=3 and C has exactly two
actual contacts, its only stressed
internal square S2 has exactly
two actual outer contacts.
If S2 is circle-free, C and S2
are two distinct aligned transmitters
sharing the *same two endpoint
neighbors* S1 and S3. The existing
shared-transmitter theorem
HUMAN_CYCLE_ANALYSIS.md section 9
then forces **all four true frames
C,S1,S2,S3 parallel**. If not,
S2 itself is circle-contacting.
This is a real global route to
the four-square parallel candidate
scaffold, not an assumed frame
choice or local cap inequality.

**Remaining decisive proof:** derive a
sharp \(R\ge\widehat R\)
inequality from these **real**
outer boundary contacts, central
chords, orthogonal leaf scaffolds,
or the m3 forced parallel motif;
then handle outer full-contact ring
root A, central branching B3,
exterior stress root X and k<=6.
None of P, S or K has yet been
eliminated in full. The real
S4/k7 equality construction is
preserved. Unrestricted optimality,
equality classification and Lean 4
formalization remain OPEN.


### Major global graph collapse: 364 spectator-edge supertemplates impossible; pure B2 spectators isolated

A stronger, **complete actual-contact theorem**
now supersedes the broad 392-supertemplate
enumeration in the **k7/B2
central-*actual*-degree-two** root:
[HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md](HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md).

The positive stressed outer path
\(S_1-\cdots-S_m\), m=3..6,
has 7−m spectators on its
complementary seven-ray angular arc.
Every possible extra actual outer
contact belongs to that complementary
spectator path. Since the outer actual
graph is not the full seven-cycle,
a nonempty proper set of such extra
edges must contain a **terminal
spectator of actual contact degree one**.
But with C touching *only* its two
positive stressed endpoints, this
terminal spectator has a
**noncentral sole neighbor**,
contradicting the exact
HUMAN_STRESS_GRAPH.md
minimum-contact leaf theorem.

Therefore **no extra spectator
edges whatsoever can occur**.
The complete actual contact graph
must be precisely
\(C-S_1-\cdots-S_m-C\)
plus **7−m actually isolated
outer square labels**.
The exact graph audit
[verify_B2_isolated_spectators.py](verify_B2_isolated_spectators.py)
checks all 392 formerly
graph-permissible supertemplates:
**364 contain forbidden extra
spectator edges**, leaving
**seven bare graph supports per
m**, or 28 complete
actual-contact templates
for m=3,4,5,6.

Both stressed endpoints then have
**exactly two actual neighbors**
(C and one path neighbor).
Since C is a circle-free actual-
degree-two transmitter, neither
endpoint can also be a circle-free
degree-two transmitter. Thus
**both stressed endpoints have
true disk-circle vertices**.

The internal circle-or-C-chord
vertex-cover theorem has no C
chords in this pure Cactual2
root. It therefore forces
minimum numbers of **distinct
stressed outer circle-contact
square labels**:

| m | 3 | 4 | 5 | 6 |
| --- | ---: | ---: | ---: | ---: |
| Minimum true circle-contact path labels | **2** | **3** | **3** | **4** |

This **supersedes** the older
m6/P conclusion "at least three"
boundary outer squares with a
stronger **at least four**.

A further exact
[HUMAN_ISOLATED_OUTER_CIRCLE_FREE_NORMALIZATION.md](HUMAN_ISOLATED_OUTER_CIRCLE_FREE_NORMALIZATION.md)
shows any actually isolated outer
square can be translated a tiny
distance **radially inward** until
all its true vertices have strict
disk clearance, while preserving
its outer center class,
all actual square contacts and
the attained global minimum
radius. Indeed for a square
center of norm r>=1 and
true vertex \(z=p+v\),
\[
(p/r)\cdot z\ge r-1/\sqrt2>0,
\]
so every true vertex squared
radius strictly decreases.
A center at r=1 was already
strictly circle-free because
\(1+1/\sqrt2<R\).
Consequently in the pure
Cactual2 root there is an
equally contact-minimal
representative with **all
spectators both actually
isolated and circle-free**.
They remain *real* unit squares
and cannot be discarded from
the eight-square packing bound.

**Root-wide m6 spectator classification:**
[HUMAN_M6_SPECTATOR_CONTACT_TRICHOTOMY.md](HUMAN_M6_SPECTATOR_CONTACT_TRICHOTOMY.md)
proves that the unique spectator T
in *any* k7/B2/m6 root,
irrespective of central actual degree,
is exactly one of:
(I) actually isolated;
(L) a C-only actual leaf,
radial/C-parallel and with two
true circle vertices;
or (\(\triangle\)) a true
C-T-S1-C or C-T-S6-C
contact triangle, with T also
circle-contacting. An outer-only
T leaf would contradict the
actual-leaf theorem; touching
both endpoints would close the
excluded full outer ring.
The exact 3-bit graph check
has four labelled surviving
incidence words out of eight.

This is **genuine global structural
progress beyond small cap constants**.
It does not yet prove the sharp
unrestricted lower bound
\(R_8\ge\widehat R\).
The next hand obstruction must
account for **all isolated spectators**
and prove the candidate radius
from the now much cleaner
circle-anchored stressed core,
or from the braced zero-contact
chord and spectator-triangle
alternatives. The valid S4/k7
full actual outer contact ring
remains deliberately admitted;
equality classification and
Lean formalization remain OPEN.


## 2026-10-13: complete k7/B2 m3 stress-cycle exclusion by global circle-force semicircle

**New full global stress-support branch closure,
not a local cap interval.**

[HUMAN_SEVEN_OUTER_M3_SEMICIRCLE_EXCLUDED.md](HUMAN_SEVEN_OUTER_M3_SEMICIRCLE_EXCLUDED.md)
proves the *entire* k7,
outer-actual-forest, C-positive
degree two, m3 positive
stressed cycle
\(C-S_1-S_2-S_3-C\)
is impossible. This holds even
with additional zero-positive-
stress C or outer actual contacts.

The three positive-stress outer
center ray labels are consecutive
in the angular cyclic order
of **all seven outer squares**.
Five complementary outer center
gaps each exceed the exact
\(\pi/4-1/500\) separation,
so the stressed three-center
ray arc has length
\[
<3\pi/4+1/100.
\]
Every true circle vertex of
a genuine unit square is at
distance \(\sqrt2/2\) from its
center. The proved eight-square
radius lower bound
\(R>\sqrt2+1/2\) yields the
strict **circle-vertex ray
shadow bound**
\[
\angle(\text{center},\text{circle vertex})
<31/80.
\]
The exact rational certificate
uses
\[
\sqrt2/2R<495/1337
<\sin(31/80).
\]
Therefore **all** potentially
positively weighted true circle
vertices of the three
consecutively stressed outer
squares belong to one arc of
width strictly
\[
<3\pi/4+1/100+31/40
=3\pi/4+157/200<\pi.
\]

C is circle-free and every
spectator outside the unique
positive-stress component
has **zero** circle multipliers
by the physical force/circle
equivalence \(F_i=0\iff m_i=0\).
So the entire normalized
circle multiplier support lies
in a common **open half-plane
through the disk origin**.
Its positive weighted
circle-position vectors
therefore cannot sum to zero,
contradicting global physical
force equilibrium
\(\sum\mu x=0\).

This is a **complete m3
positive-support elimination**,
far stronger than the historical
pure central-actual-degree-two
circle-free parallel-scaffold
and zero-circle-multiplier
subcase exclusions. It
does not touch the genuine
seven-outer *full actual
contact ring* equality root.

Current **k7/B2 outer-forest
stressed path lengths** are
\[
\boxed{m=4,5,6},
\]
exactly 7 circular placements
per positive path size, hence
**21 combinatorial positive
stress supports** before
actual geometry and spectator
placement. The m7 path
was eliminated earlier by
opposite central cap normals.

[HUMAN_GLOBAL_STRESS_CIRCLE_ARC_SPREAD.md](HUMAN_GLOBAL_STRESS_CIRCLE_ARC_SPREAD.md)
makes the force balance
principle reusable: the
center-ray support of **every
positive disk-circle multiplier**
must occupy angular span
strictly larger than
\(\pi-31/40\).

**New complete k7/B3 minimal-core graph normal form.**
[HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md](HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md)
proves that a positive-stress
component with **C and exactly
three outer square labels**,
and central positive degree
three, must be
\[
\boxed{\text{triangle }C-X-Y-C
\text{ plus radial positive
bridge }C-Z}.
\]
A positive outer-edge forest
with zero edges would have
no moment cycle; two edges
would make three consecutive
outer rays and violate the
new global semicircle theorem.
Thus exactly one positive
outer pair X-Y exists, and
Z is not an angular neighbor
of X or Y. The positive
bridge C-Z is truly **radial
about the disk origin** and
its normal is among the eight
signed central side/corner-ray
directions; \(m_Z>0\)
and at least one of
\(m_X,m_Y\) is positive.

There are **seven** choices
of the unique adjacent
outer pair X,Y and **three**
remaining nonadjacent ray
positions for Z, or exactly
**21 labeled positive graph
supports** before continuous
feasibility. This count
is checked in
[verify_B3_triangle_leaf_ray_labels.py](verify_B3_triangle_leaf_ray_labels.py).

The sharp unrestricted
\(R_8\ge\widehat R\)
remains **OPEN**.
Future work should use the
now compact m4/m5/m6
positive-circle-force cycle
geometry, the B3 radial
triangle-leaf geometry,
full ring A, root X and
k<=6. Do not return to
tiny cap threshold optimization
without a new global bridge.


## 2026-10-13: global minimal B3 radial triangle structural closures

The smallest k7/B3 positive stress graph remains
the actual stressed triangle \(C-X-Y-C\) plus
radial positive C-Z bridge. All X,Y,Z have **strictly
positive physical circle multipliers**. SAT ownership
leaves three genuine bridge interfaces:
SS (C side/Z side), CS (C corner/Z side),
SD (C side/Z diagonal). The C-corner/Z-diagonal
case was fully excluded previously.

**Entire global SS all-C-side triangle subcase excluded.**
[HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md](HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md)
uses the earlier force/torque fact that with SS Z
and all three true C contact normals being C side
normals, both X,Y positively contact the
*opposite* C side, with actual C contact points
straddling the radial n line. One of them has
true transverse contact ordinate \(|\tau|\le1/2\)
on the side \(n\cdot z=-k\), with
\(k=2-\sqrt{R^2-1/4}\in(0,1/2)\).
A new **all-frame exact square-vertex lemma**
proves any genuine square wholly beyond that
negative side with a support-face point at
\((-k,\tau)\) satisfies
\[
\max_{\text{all true vertices }v}|v|^2
\le(k+1)^2+9/4
=R^2-(6\sqrt{R^2-1/4}-11)<R^2.
\]
Its key trigonometric frame-width identity is
\[
2k(L-1)+(D-1)\le L+D-2\le0,\quad
L=c+s,\ D=c-s.
\]
Thus the corresponding X or Y square is
**strictly circle-free**, contradicting its
mandatory strictly positive circle multiplier.
This eliminates the entire previously surviving
all-C-side SS opposite-face triangle, not merely
an offset interval. The exact algebra is
audited in
[verify_B3_SS_opposite_side_exclusion.py](verify_B3_SS_opposite_side_exclusion.py).

**Surviving SS triangle normals are corner-forced.**
[HUMAN_B3_SS_TRANSVERSE_CORNER_FORCING.md](HUMAN_B3_SS_TRANSVERSE_CORNER_FORCING.md)
shows the positive C--X and C--Y normals have
nonzero **opposite transverse projections**,
their actual C contact points occupy the top and
bottom transverse support sides, and at least
one C contact is a genuine corner on the
side opposite radial Z.
The CS bridge independently also forces
nonzero opposite transverse triangle normal
projections, by
[HUMAN_B3_CS_TRANSVERSE_FORCE_REQUIRED.md](HUMAN_B3_CS_TRANSVERSE_FORCE_REQUIRED.md):
otherwise all positive contact edges have
zero origin moment, contrary to the true
nonradial positive stress component theorem.
Do not promote either result to SD.

**Complete auxiliary actual spectator paths.**
[HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md](HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md)
proves that if C has **exactly three actual
neighbors X,Y,Z**, each of the two complementary
outer-ray spectator arcs between Y-Z and Z-X
must be either entirely present as true contacts
or entirely absent. A partial nonempty arc
would have a degree-one spectator whose only
actual neighbor is noncentral, violating the
minimum-contact actual-leaf theorem.
Both arcs complete would be the excluded
full seven-outer actual ring.
Hence there are exactly **three graph patterns
per 21 positive ray-label triples**, or **63
combinatorial actual-contact templates**, not
63 feasible packings. The exact
[verify_B3_complete_spectator_arcs.py](verify_B3_complete_spectator_arcs.py)
checks all 1,344 optional edge masks:
1,260 partial arcs create actual noncentral leaves,
21 form a full ring, 63 remain.

Contact-minimal CS/SD bridge modes **require**
an additional actual Z-to-spectator contact;
therefore they must use one of the two
**complete** auxiliary arcs when C actual degree
is exactly three.

**Actual circle-vertex and transmitter support
along zero-positive-weight spectator paths.**
[HUMAN_B3_AUXILIARY_ARC_BOUNDARY_COVER.md](HUMAN_B3_AUXILIARY_ARC_BOUNDARY_COVER.md)
proves the s=1,2,3 spectators on a complete
auxiliary arc each have exactly two actual square
neighbors, none C. Adjacent circle-free
two-contact spectator transmitters cannot occur.
Therefore true circle-contact spectator labels
cover the internal spectator path, requiring
at least \(\lfloor s/2\rfloor\) such labels.
For a single-spectator arc (s=1), the
circle-free alternative is a genuine aligned
unit-width transmitter between the two
stressed core endpoints, which must have
exact **closed-square distance one**.
The Z ray positions i+3,i+4,i+5 give
complementary arc spectator sizes
(1,3),(2,2),(3,1).

These are **genuine structural geometric
conditions on full squares**, not a sharp
global radius proof. The SS corner-forced
case, CS/SD braced complete spectator paths,
other actual C-contact-degree variants,
B2 m4..6, all other global roots and the real
S4/k7 equality ring remain open.
