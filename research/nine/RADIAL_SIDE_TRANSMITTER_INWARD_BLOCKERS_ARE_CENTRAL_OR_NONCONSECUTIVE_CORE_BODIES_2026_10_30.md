# A radial-incident side transmitter is blocked from inside the cycle

Date: October 30, 2026. Author: common-certificate continuation.
Input mathematical tree: 3132896f3c306faecfdd69daafb0b577bf7d70a1.

**Status: complete proposed hand theorem, awaiting separate full review.**
At the original radius/Phi minimum, a side transmitter next to a physical
two-circle loaded square has a genuine additional obstruction to its
inward slide. Every such obstructing completion square is central. The
other possible obstruction is a nonconsecutive body of the positive
cycle itself. Both conclusions include actual shared segments, corner
junctions, zero-weight contacts and every physical circle mask.

The proof distinguishes an actual neighbor from an actual blocker. A
point contact at opposite corners of an aligned four-square junction
can be an exterior neighbor, but it permits the inward slide along a
common separator. It is therefore not a blocker. This observation
removes the need for a new generic-normal or shared-block assumption.

## 1. Original domain and exact statements

Keep the actual finite packing at the original lexicographic minimum
of radius R and

\[
                         \Phi=\sum_i |c_i|^2.
\]

Keep its common compatible physical certificate, all original forces,
torques, means, actual circle corners and the physical plane embedding.
Work in the closed original interval

\[
                   \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
                                                               \tag{1.1}
\]

Suppose an entire positive component is a simple cycle with at least
three loaded bodies. Let X--U--Y be an original channel with one true
unloaded full-positive-degree-two side transmitter U. The endpoints
X,Y are loaded, and X has two physical circle corners. An individual
circle coefficient at X may vanish. Every physical corner and every
physical neighbor of U and of all other bodies remains present.

Use orthonormal channel coordinates, with the origin unchanged, in
which the original applications are

\[
P_X=(l,h),\qquad P_Y=(l+1,h),\qquad h>0,
                                                               \tag{1.2}
\]

and the direction N=(0,1) points out of the cycle. The complete
radial-endpoint support theorem gives

\[
h>\frac12,\qquad
U=[l,l+1]\times[b-1/2,b+1/2],\qquad |h-b|<\frac12.
                                                               \tag{1.3}
\]

In particular b>0, and both original channel applications are in the
relative interiors of the two vertical sides of U. They are the
unchanged applications, including their original transverse mean.

For an actual touching square T, orient a common unit separator n
from U toward T:

\[
 \max_{x\in U} n\cdot x=\min_{y\in T}n\cdot y.
                                                               \tag{1.4}
\]

Call T an **inward blocker at U** if every such common separator has

\[
                              n\cdot N<0.                    \tag{1.5}
\]

This definition uses all common separators of the whole actual
squares. A selected zero or positive coefficient at the pair has no
role in it.

**Theorem 1.1 (complete blocker routing).** At least one actual square
other than X,Y is an inward blocker at U. Every inward blocker is
either:

1. a nonconsecutive body of the same positive cycle; or
2. an actual additional square whose entire open interior has the
   central winding label of that physical cycle.

Every additional square in the second alternative is physically
circle-clear. No actual exterior-pocket square is an inward blocker.

**Corollary 1.2 (short-cycle common central blocker).** If the same
cycle has at most seven bodies and all its unloaded vertices are
isolated, there is at most one additional square that can be an inward
blocker at any radial-incident side transmitter. Thus every such U
has a nonconsecutive core blocker, or is blocked by the same one
possible central additional square. The statement does not assert
that different transmitters require different blockers.

For a seven-body cycle in the same nine-square packing, if any such U
has no nonconsecutive core blocker, the two actual completion squares
are necessarily one central blocker and one exterior square. The
accepted no-long completion theorem places the latter in an actual
side-transmitter pocket. This is a necessary joint location, not an
exclusion of its coexistence.

## 2. The complete physical inward slide forces (1.5)

The canonical minimum used here is the original finite-packing minimum
in ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md.
The final contact-count tie-break of the earlier transmitter source
is unnecessary for this side-normal motion.

Translate only U by -epsilon N, with epsilon>0 small. The two vertical
support lines in (1.2) are unchanged, so the original support halfplanes
continue to separate U from the entire actual endpoint squares X,Y.
No assertion that a former application stays a contact in the competing
packing is needed.

The exact maximum squared corner norm after translation is

\[
 (|l+1/2|+1/2)^2+(|b-\epsilon|+1/2)^2.
                                                               \tag{2.1}
\]

For 0<epsilon<b, this is strictly smaller than the original value.
It retains all initially active physical circle corners of U. The
change to the objective is exactly

\[
                  |c_U-\epsilon N|^2-|c_U|^2
                       =-2b\epsilon+\epsilon^2<0.          \tag{2.2}
\]

Now suppose every other actual neighbor T of U admits at least one
common separator with n.N>=0. Choose one such physical separator
for each of the finitely many neighbors, only for the feasibility
test of this motion. Its U-support changes by -epsilon(n.N)<=0,
so it continues to separate the whole translated U from T. This is
not a reselection of a force normal in the original certificate.

Every original nonneighbor has positive distance from the compact
square U. All those pairs stay disjoint for a sufficiently small
translation. Thus all original squares, all their mutual disjointness
conditions and the disk containment remain satisfied. Equation (2.2)
contradicts the original Phi minimum. Some additional actual neighbor
therefore satisfies (1.5), proving existence in Theorem 1.1.

For clarity, (1.5) really describes an obstruction to this translation.
For a touching pair define, over the unit circle,

\[
 F(n)=\max_U n\cdot x-\min_T n\cdot y\ge0.
\]

The zero set is the nonempty compact set of common separators. If
(1.5) holds, -n.N has a positive lower bound on that zero set and
remains positive in a neighborhood of it. Off that neighborhood,
F has a positive minimum. Consequently, for all sufficiently small
positive epsilon,

\[
                   F(n)-\epsilon n\cdot N>0
\]

for every unit n. Convex separation then implies that the two open
interiors overlap after the downward translation. Conversely, a
separator with n.N>=0 preserves disjointness exactly as above.

## 3. The genuine contact is on the inward face

Take an inward blocker T. Every common separator has negative vertical
component. The support face of the axis-aligned U for any such normal
is contained in

\[
                          B_U=[l,l+1]\times\{b-1/2\},     \tag{3.1}
\]

the actual bottom face of U. Since every point in U intersect T
lies on that support face, the whole actual intersection is in B_U.
The original channel chord lies strictly above it because
h>b-1/2 in (1.3).

The complete own-pocket cap theorem already excludes an own-pocket
blocker: an additional square in U's exterior channel pocket is
wholly in y>=h, whereas B_U has height b-1/2<h. The argument below
also excludes every other exterior pocket, including weak junctions.

We will use the following exact local contact fact.

**Lemma 3.1 (a genuine inward blocker leaves no second core passage).**
If T is not a core body, one can choose a point p in U intersect T
such that no positive cycle edge not incident to U can have its
physical contact at p. Moreover p is not either original positive
application of U.

*Proof.* The last assertion follows immediately from (1.2)--(1.3).
For the first, distinguish the complete contact possibilities.

If U intersect T is a positive-length segment, choose p in its
relative interior and in the relative interior of B_U. Both squares
have opposite open half-plane tangent sectors there. No third square
can meet p without overlapping an open interior. In particular no
other positive cycle edge can meet there.

If the intersection is one point p and p is in the relative interior
of a side of either square, its sector angle is pi and the other
square contributes at least pi/2. At most one other square can meet
p. An edge of the core not incident to U would need two other core
squares there, since T is additional, which is impossible.

It remains that p is a vertex of both U and T. If at most three
squares meet p, the same two-other-core-bodies argument applies.
If four meet, all four inward sectors must have angle pi/2 and fill
the full turn. Their frames agree and their actual union is a full
aligned 2x2 block, as proved in Section 1 of the physical uncrossing
source. Adjacent quadrants share a whole unit side. Because U and T
have only the point p in common, they must occupy opposite quadrants.
One of the vertical lines through p is then a common separator of
U and T, with horizontal unit normal. It has n.N=0, contrary to
(1.5). Thus the four-square point-only alternative is impossible
for a genuine inward blocker. These cases exhaust actual square
intersections. QED.

This lemma does not require a coefficient or a genericity condition
at a zero-weight pair. In particular it does not treat both opposite
pairs of a four-junction as positive and does not change its sector
order. The potentially troublesome opposite extra is directly
excluded as a blocker by a physical separator.

## 4. Full weak-junction central routing

Suppose now that the inward blocker T is additional to the core.
We prove its central label, retaining the actual weak-boundary
convention of SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md, Section 2.

That complete routing theorem permits the occupied center/contact
path inside each convex unit to be homotoped to the segment joining
its two original boundary applications. At U this segment is exactly

\[
                             P_XP_Y\subset\{y=h\}.        \tag{4.1}
\]

Its open segment is in the open interior of U by (1.3). The physical
spoke order and the outward channel crosscut identify its upper side
as exterior and its lower side as central. Thus every point of

\[
                U^\circ\cap\{y<h\}                      \tag{4.2}
\]

has the bounded-side winding label after this homotopy. This is a
statement about the occupied physical cycle, not about the position
of a concurrence polygon. The full physical routing may be perturbed
arbitrarily little into a Jordan cycle while retaining that local
segment and its two side labels.

Choose p from Lemma 3.1. In the unperturbed occupied drawing every
half-edge is in its own open core square except at its physical
contact endpoint. Consequently an edge belonging to other core
bodies could pass through p only if its contact endpoint were p.
Lemma 3.1 excludes this. The U path (4.1) also misses p by a positive
distance. Therefore the compact occupied cycle drawing has positive
distance from p. All sufficiently small compatible junction routings
can be chosen to miss one fixed disk about p.

Choose x in the lower open portion (4.2) sufficiently near p, and
choose y in the open interior of T sufficiently near p. Join x to
p through U and p to y through T. These short segments lie in that
fixed disk, which misses the routed cycle. Since x is central, y
has the same bounded-side winding label.

To pass from this local point to the whole additional square, fix
any other y' in T's open interior and a compact path in that open
interior from y to y'. It has positive distance from the entire
closed core union. Choose the physical junction perturbations still
smaller than that distance. This path then avoids the routed cycle,
so y' has the same central label. Because y' was arbitrary, the
whole connected open interior of T is central in the unchanged
weak-boundary convention. Taking closure gives the corresponding
closed central region for all of T.

This proof includes side means at endpoints, coincident contact
points elsewhere, additional zero-weight contacts and every small
physical subdivision of an exterior pocket. No actual interior path
is allowed to cross occupied core. The short comparison path through
U near p is used only to compute the winding label of the drawn
cycle; it does not claim a free path through U for a completion body.

Thus every additional inward blocker is central, proving the routing
part of Theorem 1.1. If the blocker is itself a nonconsecutive core
body, its interior contains a portion of the positive cycle and the
last connected-interior argument does not apply. That is precisely
the explicit first alternative of the theorem.

## 5. Central blockers are physically circle-clear

Let T be an additional central square. Suppose it had an actual
circle corner z. No point of the containing circle can belong to
two contained packing squares, by the short inward-radial-segment
argument in the physical uncrossing source. Thus z is not in any
core square.

Take a point y in T's open interior. The closed segment yz is
disjoint from the closed core: its points other than z are in
T's open interior, and z is unshareable. It is compact, so it has
positive distance from the core union. Sufficiently small physical
Jordan routings therefore avoid yz. But y has the bounded-side
label, whereas z is on the containing circle and hence in the
unbounded face of the routed core cycle, which lies strictly inside
that circle. This is impossible. Hence every corner of T is strictly
inside the containing disk.

The conclusion concerns the complete physical circle mask, including
corners whose selected circle coefficient would be zero.

## 6. Simultaneous short-cycle caller and its precise remainder

Assume now that the core has at most seven bodies and that no two
unloaded vertices are adjacent. The full theorem
ISOLATED_TRANSMITTER_CYCLES_HAVE_SHORT_CENTER_DIAMETER_AND_CENTRAL_CAPACITY_ONE_2026_10_30.md
gives capacity at most one in the entire central free union. It
retains the actual winding label of every additional square and
counts all bounded subdivisions together.

Every additional inward blocker just proved has exactly that central
label. Therefore there is at most one such actual square across all
radial-incident side transmitters. At every one of those transmitters,
Theorem 1.1 supplies either this common central square or an actual
nonconsecutive core blocker. This proves Corollary 1.2 without a
distinct-blocker count or any assumption that all physical contacts
belong to the positive graph.

In the seven-body/nine-square caller, if some U has no nonconsecutive
core blocker, at least one of the two actual extras is central.
Central capacity one puts the other extra outside. The complete
no-long completion theorem places it in an actual side-transmitter
pocket: direct pockets and whole diagonal pockets are empty. It
cannot block any of the radial-incident side transmitters by the
routing theorem above. All such U without a core blocker consequently
depend on the same original central square.

This is the exact remaining joint geometry. A central square may
touch several inward transmitter faces. Nothing here says it cannot
do so, that it lacks other physical neighbors, or that it can be
moved while its neighbors are fixed. Likewise a nonconsecutive core
contact can prevent the one-body slide and has not been removed by
a graph drawing. These alternatives require further geometry or a
complete collective motion before any original mixed-mask parent
can be called closed.

The theorem is uniform over the original four-, five- and six-load
no-long C7 patterns whenever the selected transmitter has a physical
two-circle endpoint. It does not cover an internal two-circle body
with no incident transmitter, and it makes no diagonal-transmitter
motion claim.

### 6.1 The occupied pocket has a physical-unique loaded endpoint

There is also a direct whole-mask join that requires no canonical
motion. The accepted no-long completion theorem supplies an occupied
actual side pocket in every surviving short C7 with its two actual
completion squares. Section 7 of
RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md proves that a side channel
with two physical-two-circle loaded endpoints has an empty whole
exterior pocket. Therefore every occupied side pocket has at least
one loaded endpoint with a unique physical circle corner.

In particular every surviving short C7 has a physical-unique loaded
body incident to an actual occupied side-transmitter pocket. This is
stronger than merely asserting that some loaded mask is unique, but
it makes no statement about that body's contact ownership or physical
neighbors. In the six-load C7 the only unloaded body is side normal,
its only channel pocket is occupied, and at least one of its two
loaded endpoints is physically unique. If the other endpoint is
physically two-circle, Theorem 1.1 routes the inward blocker at that
same transmitter to the central-or-nonconsecutive-core alternatives.

All corner-weight endpoints and all zero-weight contacts remain in
this join. The complete empty-pocket theorem is used at its original
two-radial-endpoint scope; no capacity from different pockets is added.

## 7. Complete direct sources and verification boundary

| Complete direct source | SHA-256 | Literal role |
| --- | --- | --- |
| ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md | `be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06` | Original global radius/Phi minimum; all actual bodies retained in a competing packing. |
| CANONICAL_TRANSMITTER_CENTERING_AND_TWO_CIRCLE_CHANNEL_PHYSICAL_BLOCKERS_2026_10_30.md | `6b98f1ab4bf1a28b6dc8f4dd233caaf8c14fae6565757e4e9ea82563938d0aa0` | Existing side slide and full radial support cover; the stronger physical blocker test is proved here. |
| RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md | `2d78bc2892c11e58007881ff84d57cc6606dce201bb46d412ef216c12577191e` | Actual radial endpoint, strict transmitter-side interior, unchanged channel height greater than one half; Section 6.1 also uses its entire two-radial-endpoint pocket exclusion. |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | `bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe` | Complete local tangent-sector classification, compatible physical routing and unshareable circle corner. |
| SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md | `f9a008a8cebb02825891d773afeafa0fa953f5c499988bdaae0bac947ff6f1e7` | Actual outward channel and whole-cycle winding labels, occupied-chord homotopy and compact-interior weak-boundary convention. |
| ISOLATED_TRANSMITTER_CYCLES_HAVE_SHORT_CENTER_DIAMETER_AND_CENTRAL_CAPACITY_ONE_2026_10_30.md | `e5a4522cad96c419ea0d65eea515557b9118c66e910660cfe4ea873a64a98f6b` | Only Section 6: capacity one in the full original central free union. |
| NO_LONG_SMALL_CYCLES_REQUIRE_OCCUPIED_SIDE_POCKETS_AND_EXCLUDE_SIX_LOAD_DIAGONAL_SEVEN_CYCLES_2026_10_30.md | `243dcc2fd0b87e42c679198b5ea1bb1ac80efe0d82f0256c3db3564ce0307621` | Only the same-nine-square final location of the exterior extra in an actual side pocket. |

All seven complete direct sources were read. Their accepted transitive
capacity and physical-certificate prerequisites retain their original
scope; this source does not replace them by a new selection assertion.

No original gate or ledger is changed. No numerical pose search,
angle grid, computational packing certificate, Lean/Lake invocation,
CI dispatch, force-normal reselection, changed original application,
remote edit or publication was used.
