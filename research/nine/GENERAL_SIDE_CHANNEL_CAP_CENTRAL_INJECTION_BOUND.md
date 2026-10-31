# A simple cycle with only single-transmitter channels has total completion capacity at most two

Date: October 26, 2026.

**Status: accepted complete uniform geometric assembly, after full-source
and original-parent reviews in
REVIEW_CHANNEL_CAP_CENTRAL_INJECTION_ROOT_2026_10_26.md and
REVIEW_GENERAL_CAP_CENTRAL_INJECTION_GLOBAL_2026_10_26.md.**
Its new local input is the complete proximity theorem in
`FOUR_C6_SIDE_OCCUPIED_CAP_TRANSMITTER_PROXIMITY.md`, Sections 1--4.
No shared ledger or historical source is changed.

Put Q=1105/256. Work with the original compatible physical certificate
and all actual unit squares in 2<=R<=sqrt(Q). Let the entire selected
positive component be a simple cycle with at least three positively
circle-loaded bodies. Assume every channel between consecutive loaded
bodies has either no unloaded vertex or exactly one actual unloaded
degree-two transmitter. Each latter transmitter keeps its actual width
one or sqrt(2), its original support equations and full transverse mean.

Retain every actual circle mask, individual zero or positive corner
weight, force and normal, additional zero-weight physical contact,
physical square and further completion square. In particular, no
positive chord or attached positive force is deleted to create this
cycle hypothesis.

**Theorem.** At most two additional pairwise interior-disjoint physical
unit squares can complete such a cycle inside the same disk.

The theorem does not require a diameter bound for the ring centers, a
convex center polygon, a bound of one on central capacity, or an
individual force-value classification of its loaded bodies.

## 1. Every enclosed extra is close to the origin and all its vertices are farther away

Every actual unit center c in the candidate disk has |c|<M0=91/60,
because a farthest corner gives

    |c|^2+|c|+1/2<=Q,
    M0^2+M0+1/2-Q=31/57600>0.

`C7_INNER_SIDE_CORNER_RESTRICTIONS.md`, Sections 1--2, is explicitly
stated for an arbitrary finite physical ring and one or more enclosed
units. Despite its filename, it has no seven-body, diameter, stress,
circle-contact, convexity or common-frame premise. Its complete
geometric inputs are the above strict center-radius bound, actual
disjoint unit interiors, and the outgoing-ray encounter with a true
ring body. Its uniform radial-tail and diagonal-tail proofs give, for
each enclosed unit T separately,

    every own center coordinate has magnitude <k=3721/7200,
    every actual vertex norm >sqrt(5/2)-91/60>19/300.      (1)

Here is the full enclosure check for the present caller. The actual
physical center/contact routing of a simple positive cycle is a Jordan
ring, with the established compact-interior convention at weak contact
junctions. Each central extra has its entire open interior on the
bounded side. Every ray from an interior point continuing to infinity
must meet the occupied ring; otherwise its nonzero winding number
could not become zero at infinity. A first encounter after leaving the
extra lies in an actual ring unit. An auxiliary center-hull edge is
never substituted for that physical encounter.

If extra zero-weight contacts subdivide the central free union, this
argument applies to each enclosed unit in every resulting component.
At a weak junction, fix a compact inner portion before passing to the
arbitrarily small physical Jordan routing. It remains a positive
distance from the closed core union, so its winding is stable. This is
the complete enclosure convention of
`SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md`, Sections 2--3. It is also stated
explicitly in Sections 1--2 of
`SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md`; the outgoing-ray
argument in those sections does not use that source's later diameter
hypothesis. The present proof uses the local source (1) directly and
does not invoke its pair-capacity theorem.

Since k=1/2+121/7200, the own-coordinate bounds imply

    dist(O,T)<sqrt(2)*121/7200<1/40.                     (2)

For example sqrt(2)<10/7 gives the upper bound 121/5040, smaller than
1/40 by 1/1008. Also sqrt(5/2)>79/50, and
79/50-91/60=19/300>3/50. Hence every enclosed extra meets the disk of
radius 1/40 and every one of its vertices lies outside radius 3/50.
These statements hold for every enclosed unit independently, with no
assumption on how many such units there are.

## 2. Every exterior extra gives a distinct actual near-origin transmitter

The complete routing theorem
`SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md`, Sections 1--3, assigns the whole
open interior of each extra to the central free union or to one actual
exterior region between consecutive loaded bodies. Connectedness and
the compact-interior convention give a single eventual label even at
coincident junctions or genuine side-mean endpoints. Closure puts the
whole square in that region's closed version.

Its proof also checks the two possible omitted exterior types. A
physical radial loaded body's small cap between its own two circle
corners cannot contain a unit, by the sharp unit supporting-height
bound. A direct loaded/loaded contact has an empty exterior pair
pocket, by the complete physical pair-pocket theorem. Extra zero-weight
circle contacts or contacts among the original units can subdivide a
channel pocket but cannot let an extra cross its occupied boundary.
Thus every noncentral extra is in one of the actual single-transmitter
channel pockets in the present theorem.

For an actual diagonal transmitter, the entire exterior pocket is empty
by `FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md`. That accepted local theorem
is for any entire simple positive cycle with at least three loads; it
has no four-load or six-body premise. It retains every actual physical
radial or unique endpoint mask and the original side-interior means.

For an actual side-normal transmitter U, the complete local capacity
theorem `GENERAL_SIDE_CHANNEL_EXTERIOR_CAPACITY_ONE.md` gives at most
one extra in its whole exterior pocket, including every subdivision.
If that pocket is occupied, the local whole-channel theorem in
`FOUR_C6_SIDE_OCCUPIED_CAP_TRANSMITTER_PROXIMITY.md`, Sections 1--4,
gives

    dist(O,U)<1/60<1/40.                                (3)

This applies to the actual transmitter and its unchanged slider. It
does not move the exterior extra, infer whole vertical separation, or
replace a genuine mean. The full-mask port theorem in
`SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md`,
Sections 1--3, additionally gives

    every actual vertex norm of U>7/100>3/50.            (4)

## 3. The assignment is injective into actual units

For each additional physical unit E define its assigned unit A(E):

* If E is central, set A(E)=E itself.
* If E occupies a side-normal channel pocket, set A(E) to that pocket's
  actual original transmitter U.

Section 2 exhausts every extra, so this is defined on the complete
completion set. Distinct central extras are distinct physical units.
Two exterior extras cannot be assigned to the same transmitter, because
its whole pocket has capacity at most one. Different channels use
different actual unloaded vertices of the original cycle. A central
extra is not any original core unit. Therefore A is injective.

Every A(E) is an actual unit from the unchanged packing. In particular
all assigned units have pairwise disjoint open interiors; disjointness
is not inferred from their abstract region labels. Equations (1)--(4)
show that each meets the disk of radius delta=1/40 and every one of
its vertices has norm greater than d=3/50.

The angular lemma in
`SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md`,
Section 4, applies since delta/d=5/12<1/2 and d<1/2. It proves that
each such unit occupies more than 2pi/3 of the circle of radius d in
its open interior, so at most two pairwise interior-disjoint units
satisfy these conditions. Injectivity now gives at most two extras,
proving the theorem.

No assertion that the central region contains at most one unit entered
this argument. If three extras were central, their three images would
already contradict the same angular lemma. Every mixture of central
and exterior extras is covered by the one injective assignment.

## 4. Complete original bare-C6 application

Keep the original selected simple positive six-cycle, the same nine
physical unit squares, and its three additional units. The accepted
same-nine-square theorem `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md` gives
R>2, so all local hypotheses above hold throughout the original
candidate radius range. This does not assert R>2 for an isolated
six-square core.

The exact no-positive-chord row of
`SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md`, Sections 2--4.1, gives
the following complete six positive-load orbits, with all dihedral
images acting on the original physical data:

| Actual loaded representatives on 0,1,2,3,4,5 | Full original exit |
| --- | --- |
| 013, cyclic gaps (1,2,3) | `SIX_CYCLE_THREE_LOAD_LONG_CHANNEL_EXCLUSION.md` excludes its complete two-transmitter-channel family, all masks and means. |
| 0123, adjacent unloaded vertices | `BOUNDARY_THREE_EDGE_PATH_DIAMETER.md`, Section 3, excludes its complete two-transmitter channel through the actual three-edge boundary path. |
| 024, alternating three loads | All three channels have one actual transmitter, so Sections 1--3 give capacity at most two for the three original extras. |
| 0124, unloaded cyclic distance two | Both positive-reserve channels have one actual transmitter; the same uniform theorem excludes the three-extra completion. |
| 0134, opposite unloaded vertices | Both positive-reserve channels have one actual transmitter; the same uniform theorem excludes the three-extra completion. |
| 01234, five loads | Its only positive-reserve channel has one actual transmitter; the same uniform theorem excludes the three-extra completion. |

The first two rows retain their full accepted core obstructions. In
every other row, a true transmitter has its original width one or
sqrt(2). Diagonal pockets are empty, and occupied side pockets supply
the distinct near-origin units just proved. No restriction on which
loaded bodies are physically radial, on any individual circle weight,
on the actual channel means, on central occupancy, or on the position
of any of the three extras is added.

These six complete alternatives prove that the entire selected simple
positive C6 has no nine-square completion in the candidate disk. In
particular the exact original FOUR_ZERO_DISTANCE2.CAPS,
FOUR_ZERO_DISTANCE3.CAPS, FOUR_ZERO_DISTANCE2, FOUR_ZERO_DISTANCE3 and
C6.ALL obligations all have whole-domain exits after independent
acceptance of the local proximity theorem and this assembly.

## 5. Caller-scoped dependency replacement and remaining scope

For this whole bare-C6 caller, Sections 1--4 give a shorter proof chain.
The alternating three-load row no longer calls its separate all-unique,
one-radial, two-radial, strict-turn/share or force-value scalar
classifications. The four- and five-load rows no longer call their
special central-capacity or endpoint-diameter theorems. The entire
caller needs only the two complete long-channel core exits, the
uniform actual pocket routing, the all-mask local cap theorems, the
local inner-square restrictions, the actual port margin, the occupied
side-cap proximity theorem and the angular obstruction.

This is a dependency replacement for the present assembled theorem,
not a claim that those earlier results were false or that their
certificates are globally unused. Historical sources and reviews are
retained. In particular the accepted same-nine R>2 theorem still uses
its explicitly counted five fixed mass charges and one fixed derivative
enclosure. The diagonal empty-cap theorem still retains its stated
balanced-case scalar dependencies. This source does not assert that
those inherited certificates are retired. It introduces no new
computational certificate, sampled parameter cover or numerical premise.

The theorem requires the entire positive component to be the indicated
simple cycle. Positive chords or attached positive forces keep their
actual equations and degrees and are outside this caller. Chorded
hexagon families, the complete coarse cell C1.6.b0, the unrestricted
sharp bound, original equality classification and Lean integration
remain separate obligations. No historical file is deleted, and no
Lean compilation, CI, remote write or shared-ledger edit is performed.
