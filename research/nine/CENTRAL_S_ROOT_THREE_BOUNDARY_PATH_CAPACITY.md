# A central S root and a cycle path with one clear intermediary have capacity eight

Date: October 27, 2026.

**Status: complete force-free hand capacity theorem, submitted for full
root and separate independent review.** The centered-arc prerequisites
are submitted separately. This theorem retains the actual intermediary
square and all three original completion squares.

## 1. Full physical statement

Retain actual interior-disjoint unit squares in the original circle,

    sqrt(17)/2<=R<=sqrt(1105)/16,
    d=sqrt(R^2−1/4)−1,       1<=d<61/60.

Suppose six distinct actual squares are H,L,B_1,B_2,X,B_4, where

    H=[U−1,U] times [V−1,V],
    U>=V>0,       U^2+V^2=d^2,       U<=4/5,
    P=(U,V),       e=P/d,
    L=P+[0,1]e+[-1/2,1/2]Je,                            (1)

and their actual physical contacts include

    H--B_1--B_2--X--B_4--H.                             (2)

The units B_1,B_2,B_4 physically touch the circle. No circle,
force, degree, width, support-normal or orientation premise is
placed on X.

**Theorem.** At most two further arbitrary unit squares can be
added to these six inside the same circle. In particular an
original packing of nine units is impossible.

The internal X position may be reflected: the actual path
H--B_1--X--B_3--B_4--H is covered by reversing its notation.
The theorem does not require a specified root-port order,
a South or Southeast root force, or a new contact between
the two real neighbors of X.

## 2. Actual central clearance and the available inner arcs

Equation (1) gives

    3/5<=V<=U<=4/5.

Thus H contains the closed disk D_(1/5). Every other actual
unit E satisfies

    dist(O,E)>=1/5,       |c_E|>=7/10>2/3.               (3)

The incircle of E proves the second bound. All eight original
nonroot units, including physically clear completion units,
are covered.

By FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md,
each such E meets the radius-9/8 circle in one connected
open interior arc longer than

    delta=2pi/9,

containing the circle point in its actual center direction.

Two more precise physical facts will control a low-center
intermediary. Put

    alpha=atan(2/5),       beta=atan(7/20).

NEAR_CENTER_UNIT_CENTERED_NINE_EIGHTHS_ARC.md proves that,
when an actual unit satisfies (3) and |c_E|<=5/6, its entire
closed centered arc of halfwidth alpha lies inside int(E).

BOUNDARY_UNIT_CENTERED_NINE_EIGHTHS_ARC.md proves that
every actual boundary unit has its entire closed centered
arc of halfwidth beta inside its open interior. Its precise
radius premise holds because a high-radius boundary center
has norm greater than27/20.

The latter source also proves the exact strict comparisons

    alpha+beta>delta,
    atan(6)−alpha−beta<delta.                            (4)

These centered arcs are actual occupied arcs, not symmetric
substitutes for the complete intersections.

## 3. A boundary--X contact excludes every other nonroot center

Fix either real boundary neighbor A of X.

### 3.1. The entire |c_X|>5/6 alternative

MIXED_BOUNDARY_CONTACT_CENTER_GAP.md applies literally.
The actual A--X minor center gap is strictly between pi/6
and pi/2, and contains no other actual center of norm
at least2/3. By (3), this excludes every other nonroot
unit, including the real leaf and both other path units.

### 3.2. The entire |c_X|<=5/6 alternative

Write x=|c_A|>27/20 and y=|c_X| in[7/10,5/6].
Their actual contact gives center distance at most sqrt(2).
Consequently the minor angle theta satisfies

    cos(theta)>[(27/20)^2+(7/10)^2−2]
                       /[2(27/20)(7/10)]
              =125/756>1/sqrt(37),

so

    theta<atan(6)<pi/2.                                (5)

For the unequal-radius comparison, the function
(x^2+y^2−2)/(2xy) increases in x on the stated range.
At x=27/20 it also increases in y, since (27/20)^2<2.
The final squared reserve is

    125^2*37−756^2=6589>0.

The two actual closed centered arcs supplied in Section 2
cannot meet: both lie in the open interiors of distinct
physical squares. Their minor center gap therefore has

    theta>alpha+beta>delta.                             (6)

Suppose a third nonroot center lay on this closed minor
arc. Its actual radius-9/8 center point belongs to its
own open unit. It cannot lie in either of the two closed
occupied centered arcs. It must therefore lie in the
interval remaining between them, of length

    theta−alpha−beta
       <atan(6)−alpha−beta<delta.                        (7)

The third unit's whole connected open arc, longer than
delta, would be trapped in that interval. To leave it,
the arc would have to cross one of the closed occupied
arcs, contradicting disjoint physical interiors.
This proves the same complete center exclusion as in
Section 3.1, including both endpoint rays.

The argument applies to other path bodies and the real
leaf as well as to completion units. It does not assign
a circle load or a boundary-center lower bound to X
or to the third unit.

## 4. The actual path has one direction and spans more than one hundred degrees

For B_1--B_2 use the complete boundary-pair center theorem
BOUNDARY_CONTACT_EXCLUDES_INTERMEDIATE_UNIT_CENTER.md.
For the two contacts involving X use Section 3.
No other nonroot center lies on any of these three
closed minor arcs.

At each internal path vertex its two neighbors must
therefore lie on opposite angular sides: if both were
on the same side, the nearer neighbor direction would
lie in the farther neighbor's forbidden minor arc.
All these arcs are shorter than pi/2. Thus the three
edges continue in a single circular orientation.
Their total length is less than

    2pi/5+pi/2+pi/2<2pi.

The actual leaf center is on none of them. Cut the
center circle at its direction e and orient the path
so its four center lifts are strictly increasing.

The boundary--boundary gap is greater than delta.
When |c_X|>5/6, the other two gaps exceed pi/6, giving
total span greater than

    delta+pi/6+pi/6=5pi/9.                               (8)

When |c_X|<=5/6, both other gaps exceed delta by (6),
so the total span is greater than3delta>5pi/9 as well.

Call the two endpoint lifts gamma_1<gamma_4.
Every other nonroot center, and hence every completion
center, is outside their entire traversed interval.

## 5. The genuine root and leaf give only two completion slots

Both endpoints of (2) physically touch H and the circle.
The complete four-side estimate in Section 3 of
S_LEAF_C5_CENTRAL_ROOT_BOUNDARY_PATH_CAPACITY.md applies
to the actual root (1). It proves that each endpoint
center has minor angle less than5pi/9 from e.

The precise ingredients are |P−p|<21/20 at every actual
root-boundary port, |c_B−P|<9/5, |c_B|>27/20 and d>=1.
They give cos(angle)>−1/6>cos(5pi/9), without a force
or mask assumption at either endpoint.

The two endpoint lifts consequently belong to

    (0,5pi/9) union (13pi/9,2pi).

They cannot both belong to one component, because their
actual path span exceeds5pi/9 by (8). Thus

    gamma_1<5pi/9,       gamma_4>13pi/9.                 (9)

The real leaf's closed radius-9/8 intersection has
halfwidth

    ell=min(arccos(8d/9),arcsin(4/9))>pi/9.

This is its exact physical radial/transverse intersection,
including both genuine circle corners and every arc endpoint.

A completion center before gamma_1 has its whole connected
open inner arc in (ell,gamma_1); one after gamma_4 has its
whole arc in (gamma_4,2pi−ell). Connectedness and the
occupied endpoint center points and leaf arc force this
routing, with all tangencies retained.

By (9), each of those two intervals has length strictly
less than4pi/9=2delta. Each completion contributes a
disjoint open arc longer than delta. Therefore at most
one completion unit fits in either interval, and at most
two further units exist. The required three original
completion units give the contradiction.

## 6. Exact whole high tilted S124 consequence

For the original component

    0--1--2--3--4--0,       0--L,

with genuine S leaf and positive loads exactly1,2,4,
the actual root0 has true degree three and both of
its actual cycle neighbors1,4 are boundary. Body3
keeps its true unloaded degree-two equations, width,
normal, both original applications and actual shape.

Whenever d>=1 and the tilted root has U<=4/5, all
premises (1)--(2) hold, with X=3. The physical theorem
therefore excludes the entire domain. Both possible
root-boundary orders are included; neither is renamed
to manufacture the South-transmitter hypothesis.

The complementary tilted U>4/5 domain is excluded
by the already complete ordered-root theorem
S_LEAF_ROOT_HIGH_COORDINATE_NORTH_SCREEN_EXCLUSION.md,
using the original boundary-edge moment transport
proved in S_LEAF_C5_124_ORDERED_ROOT_DOMAIN.md.

Thus the entire high-radius tilted S124 root is
excluded once this source and its direct centered-arc
prerequisites receive their full reviews. The earlier
central-disk theorem and the same ordered-root
screen already exclude every tilted d<=1 root.
The aligned d>=1 root is separately excluded by
ALIGNED_S_LEAF_ROOT_TWO_BOUNDARY_NEIGHBORS_EXCLUSION.md.

The complete original remainder is still the aligned
strict-low S124 root. Its path contains the actual
unloaded intermediary, so the all-boundary low-radius
path theorem cannot be imported into that remainder.

This theorem preserves all nine original units, all
true degrees, positive forces, actual means, circle
masks and zero individual circle weights. It proves
a physical capacity bound and changes none of these
data. No numerical pose, compilation, CI, shared
metadata edit or remote action is used.

