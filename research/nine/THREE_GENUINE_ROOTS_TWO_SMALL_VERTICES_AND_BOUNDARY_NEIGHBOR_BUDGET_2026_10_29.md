# Three genuine leaf roots have two small vertices and at most one root with two other boundary neighbors

Date: October 29, 2026 UTC. Author: block_forests continuation.

**Status: complete new uniform physical theorem and whole independent-private
six-block exclusion, frozen for full independent review.** The theorem is
independent of the roots' actual positive degrees. It retains all nine
original squares, original forces and torques, original selected normals,
actual singleton applications and complete shared means, physical circle
masks and individual zero circle coefficients.

Keep the common compatible selected certificate in

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Let A,B,C be three distinct genuine leaf roots, with their three actual
distinct genuine positive degree-one leaves. Each root has true positive
degree at least two, and the three genuine leaves are distinct from all
three roots. Other positive forces and the larger actual degrees at these
roots are arbitrary.

**Main theorem.** Every surviving original configuration is in the strict
high-S range d=1+epsilon>1. At least two of A,B,C have an actual vertex
of norm at most 4epsilon. Each root with such a vertex avoids closed O
and has at most two distinct physical boundary neighbors in total,
including its own genuine leaf. Therefore at most one of A,B,C can have
two or more other distinct physical boundary neighbors.

Here a physical boundary neighbor means an actual unit which physically
touches the root and the containing circle. The root-to-neighbor physical
contact need not carry positive stress, and its circle load may be zero.
The theorem counts the actual real leaf among these neighbors. It makes
no claim that a boundary neighbor has degree two or positive circle load.

**Whole six-block consequence.** Suppose the positive component is one
biconnected six-body block Q with three genuine direct leaves at distinct
roots A,B,C. If the other three block vertices are pairwise nonadjacent
in the original positive graph, the whole configuration is impossible.
All positive root-to-root edges, root degrees, private circle masks and
zero-stress physical contacts are retained. In particular this excludes
the entire alternating three-leaf C6, throughout every original radius
and every private load assignment.

## 1. A general small-circle lemma for three actual near units

The following geometric result uses no stress, leaf, containing radius,
shared frame or contact-graph premise.

**Lemma 1.** Let three actual closed unit squares have disjoint open
interiors, and suppose each meets the closed disk D_delta, where

    0<delta<1/10.

Then at least two of the three squares have an actual vertex in the
closed disk D_(4delta).

Set rho=4delta and alpha=acos(1/4). Thus rho<2/5<1/2 and
rho+delta=5delta<1/2. We compare the actual open-square intersections
with the one circle |z|=rho.

### 1.1. Every near square supplies a uniformly sized open arc

Choose any actual point z of a square S with |z|<=delta. In each of
its two perpendicular own-axis directions choose the sign that has
distance at least 1/2 from z to the corresponding far side. Call those
unit vectors u,v. The actual rectangle

    z+[0,1/2]u+[0,1/2]v

is contained in S. The two axes may be positively or negatively oriented;
only the right angle between them matters.

Every point x of |x|=rho satisfying

    x.u>delta,       x.v>delta

lies in int S. Indeed x.u-z.u and x.v-z.v are strictly positive, while
each is at most |x-z|<=rho+delta<1/2. Thus both original square
coordinate inequalities are strict, including when z is a physical
vertex or side endpoint.

On the rho circle these two strict inequalities cut an open first-quadrant
arc of angular length

    beta=pi/2-2 asin(1/4)=2alpha-pi/2.                (1)

Consequently every one of the three squares occupies angular measure at
least beta on that same circle. No connectedness of the full circle
intersection is being assumed.

### 1.2. A near square whose vertices all lie outside the circle supplies a larger arc

Suppose all four actual vertices of S have norm strictly greater than
rho. Then the angular measure of int S on |z|=rho is at least

    2alpha.                                          (2)

This is the complete one-square bound of the unequal-distance angular
budget, with distance bound delta and test radius rho. Its short direct
proof is included to retain every origin-location case.

If O is outside S, its nearest actual point cannot be a vertex, since
the square meets D_delta and delta<rho. Choose an own frame in which

    S=[a,a+1] x [b,b+1],
    0<a<=delta,       b<0<b+1.

Both endpoints of its nearest face are outside the closed rho disk.
Therefore the entire open circle arc x>a lies in int S, of angular
length 2acos(a/rho)>=2alpha. The far face lies beyond the circle
because a+1>rho. If O is on a square side, it is in that side's relative
interior and the same argument with a=0 supplies an open semicircle.

If O is in int S, the diameter 2rho<1 permits at most two faces to
cut the circle, and any two are adjacent. One face removes less than
a semicircle. For two adjacent faces at distances a,b<rho, their actual
common vertex lies outside the circle, so a^2+b^2>rho^2. Thus

    acos(a/rho)+acos(b/rho)<pi/2.

The two removed outside arcs have total angular measure less than pi;
more than pi remains. With no cutting face the full circle remains.
Tangencies remove zero angular measure. Every interior-origin case
therefore gives more than pi, which is stronger than (2).

These three cases exhaust the actual position of O relative to S and
prove (2), with attained distance endpoints included.

### 1.3. Two squares without small vertices are impossible

Suppose two of the three squares had all their vertices outside the
closed rho disk. By (1)--(2), the total angular measure of their three
disjoint open interiors on the same circle would be at least

    2alpha+2alpha+(2alpha-pi/2)=6alpha-pi/2.           (3)

This is strictly greater than 2pi. In fact

    cos(5pi/12)=(sqrt(6)-sqrt(2))/4>1/4,
    alpha=acos(1/4)>5pi/12.

For the exact radical comparison, sqrt(6)>sqrt(2)+1 is equivalent,
after positive squaring, to 3>2sqrt(2), whose square is 9>8.
Equation (3) is consequently greater than
6(5pi/12)-pi/2=2pi, a contradiction.

At most one square can have all its vertices outside the closed rho
disk. This proves Lemma 1, including equality at the vertex radius
4delta. It is an exact continuous angular comparison, with no pose
sample or scalar-angle numerical premise.

## 2. Apply the lemma to the original three genuine roots

The complete accepted high-S reduction applies to three distinct genuine
roots at arbitrary positive degrees. It excludes all D assignments and
all d<=1 alternatives, keeping every original physical square. Thus

    d=1+epsilon>1,       0<epsilon<1/60,

and all three specified genuine leaves are S. Each actual root R_i
contains its original inward radial point

    epsilon e_i,

where e_i is the actual direction of its real S leaf. These three units
meet the same closed D_epsilon. Lemma 1, with delta=epsilon, gives
actual vertices of norm at most 4epsilon in at least two of them.

Every root is physically circle-clear: its epsilon point and its actual
diameter sqrt(2) put the whole square within radius epsilon+sqrt(2),
strictly below R in the present window. In particular the other genuine
roots themselves do not count as physical boundary neighbors below.

## 3. A genuine high S root with a small vertex cannot contain O

Let X be any actual genuine S root in this strict high range, with
an actual vertex W satisfying |W|<=4epsilon. Its real radial application
is P=d e, an actual maximum-e support point of X.

If e is an own side axis of X, the width in that direction is exactly
one. Thus the opposite support is at height d-1=epsilon>0. The entire
X lies strictly on that side of O, and O is outside its closed square.

Otherwise P is a strict actual vertex. It cannot be W, since d>1 while
4epsilon<1/15. It cannot be the vertex opposite W either: their actual
distance would be sqrt(2), whereas

    |P-W|<=d+4epsilon=1+5epsilon<13/12<sqrt(2).

Hence P and W are adjacent actual vertices, at distance one.

Suppose for contradiction that O belongs to closed X. From W choose
the two inward unit own axes u,v, with P=W+u after exchanging them.
The unchanged original origin then has own coordinates a,b in [0,1],
so

    W=-a u-b v,       a,b>=0,
    a^2+b^2=|W|^2<=16epsilon^2.

The actual S support gives

    d^2=|P|^2=1-2a+|W|^2<=1+16epsilon^2.

But

    d^2-(1+16epsilon^2)
      =2epsilon-15epsilon^2
      =epsilon(2-15epsilon)>0,

because epsilon<1/60. This is a contradiction. Therefore O is outside
the full closed X in every original aligned, strict-vertex and endpoint
case. No force or torque equation at X was shortened to reach this result.

## 4. The full actual chart satisfies the accepted one-tenth physical cap

We verify the exact chart needed by the accepted physical cap directly.

For an aligned root, use e as the first own axis. Its interval is
[epsilon,1+epsilon], and its transverse interval contains zero. A small
vertex cannot be on the far face, whose coordinate is greater than one.
Reflect the transverse axis if needed so that the small vertex is
(epsilon,-beta), with 0<=beta<=4epsilon. Thus

    X=[a,1+a] x [-beta,1-beta],
    a=epsilon,       0<=beta<=4epsilon<1/10.

Its real leaf center is (d+1/2,0), exactly the aligned cap hypothesis.

For a nonaligned root, direct both own axes toward the genuine vertex
P=d e. Both its coordinates are positive and have sum of squares d^2.
Since O is outside X, one of these coordinates exceeds one. There is
at most one such coordinate because d<61/60<sqrt(2). Put it first,
then reflect the other coordinate. The actual chart is

    X=[a,1+a] x [-beta,1-beta],
    P=(1+a,-beta),       0<a<=epsilon,
    beta>0,       (1+a)^2+beta^2=d^2.

Here beta^2<d^2-1<121/3600, so beta<11/60. The other near vertex
has transverse magnitude 1-beta>49/60 and the two far vertices have
first coordinate greater than one. The small W must consequently be
(a,-beta), giving beta<=4epsilon<1/10. Its actual leaf center is

    C_L=(1+1/(2d))P,

exactly the tilted cap hypothesis. Every frame endpoint remains in the
aligned or strict-vertex alternative just proved.

The complete physical theorem
ROOTED_GENUINE_S_LEAF_ONE_TENTH_CORNER_BOUNDARY_CAP.md therefore applies
at its literal Sections 1--5 scope. It uses no force equation or positive
degree premise at X. It proves that every actual physical boundary
neighbor other than the real L has its center in one set of diameter
strictly less than one. Since two distinct unit centers have distance
at least one, at most one such other neighbor can exist.

Each root with a vertex in D_(4epsilon) thus has at most two physical
boundary neighbors in total, one of which is its actual genuine leaf.
Section 2 gives at least two such roots among A,B,C. At most one of the
three roots can therefore have two other physical boundary neighbors.
This proves the complete main theorem.

## 5. All three independent private vertices in a six-body block are excluded

Retain the exact positive component stated in the whole six-block
consequence. Let U,V,W be its three nonroot block vertices and suppose
there are no positive edges among them. Their physical zero-weight
contacts remain unrestricted.

Biconnectivity of Q gives each of U,V,W positive block degree at least
two. All its positive neighbors are roots, because the three private
vertices are independent and only the roots have the three outside
positive leaf edges. If a private vertex had all three roots as positive
neighbors, it would be the actual center of the forbidden positive
three-arm tree with those roots as its three ends. The complete accepted
three-arm theorem excludes that possibility with all full stars retained.

Consequently each of U,V,W has true positive degree exactly two, with
two of the three genuine roots as its actual neighbors. None can have
zero total circle load. If, for example, U were unloaded, its actual
two-force equations give a transmitter of width w in {1,sqrt(2)}.
The two root support planes are separated by at least w>=1. Their
actual near points epsilon e_i and epsilon e_j would then have
separation at least one in that normal direction, although their
distance is at most 2epsilon<1. This contradiction forces U loaded.
The same complete argument forces V,W loaded and physically boundary.

Let b_A,b_B,b_C count each root's distinct neighbors among these three
actual boundary private units. There are exactly six original
root-to-private edges, so

    b_A+b_B+b_C=6,       0<=b_i<=3.

If at most one b_i were at least two, their sum would be at most
3+1+1=5. Thus at least two roots have two distinct other physical
boundary neighbors. Their own genuine leaves are additional distinct
boundary neighbors. This contradicts the main theorem.

All root-to-root edges have remained in the original force system. Their
presence changes root degrees but not the exact private-degree proof or
the physical neighbor bound. This proves the entire independent-private
class, including every original private physical mask and all possible
zero total-load candidates before they were excluded.

For the alternating C6, the cyclic graph has roots at every other
vertex and the three private vertices are precisely independent U,V,W.
Thus its complete original three-leaf family is a direct instance.
No contraction to a smaller cyclic core is used.

## 6. Exact consequences for the seven surviving five-body graph families

Use the seven-family graph/root cover in the companion structural source.
The following counts concern other physical boundary neighbors, so the
root's own genuine leaf is not repeated in the table. Circle-clear roots
do not contribute. A private unit with zero load may still contribute if
it physically touches the circle; that only strengthens the main theorem.

| Five-body family | Actual forced private boundary units | Root/private boundary counts forced by those units | New conclusion |
| --- | --- | --- | --- |
| C5, arcs (3,1,1) | At least one of the two private path vertices is loaded | Each path-end root has at most one private neighbor; middle root has none | At least two small root vertices; no whole exit |
| C5, arcs (2,2,1) | Both independent private vertices are loaded | 1,2,1 in the three root roles | The root with two private neighbors has no vertex in D_(4epsilon); the other two roots each have a small vertex and avoid O |
| House ADT | At least one of B,C is loaded | At most one private neighbor at A and D, none at T | At least two small root vertices; no whole exit |
| House ADB | Both T,C are loaded | A:1, D:2, B:1 | A and B each have a small vertex and avoid O; D has no small vertex |
| House ABC | T is loaded; D may have zero load | If D is physically boundary: A:2, B:0, C:1 | In that physical-boundary subdomain B,C each have a small vertex and avoid O; no whole exit |
| Fan H12 | Both private vertices 3,4 are loaded | H:2, 1:0, 2:1 | Roots 1,2 each have a small vertex and avoid O; H has no small vertex |
| Fan H23 | Both private vertices 1,4 are loaded | H:2, 2:1, 3:1 | Roots 2,3 each have a small vertex and avoid O; H has no small vertex |

The forced loads have their actual-degree justifications. A private
path between near roots cannot consist solely of unloaded2 transmitters,
by the original support-width argument in Section 5. A true degree-two
triangle tip cannot be unloaded because its touching neighbors would be
separated by positive transmitter width. In fan H12, private 3 is true
degree three with neighbors H,2,4, and H physically touches both 2 and4;
the complete unloaded diamond-hub theorem therefore forces 3 loaded.
Private4 is a true triangle tip. The other fan's two private units are
both true triangle tips.

In particular the two private units in C5(2,2,1) make only one root have
two other boundary neighbors. This theorem does not mistakenly exclude
that whole family. None of the seven listed five-body families is claimed
closed by the new count alone.

For the six-body structural cover, the entire private-component partition
1+1+1 is now excluded by Section 5. The remaining private-component
partitions are 3 and 2+1. Each component still attaches to exactly one
root pair, as proved in the separate complete structural source. Their
internal degrees, positive loads and full remaining physical geometry
are not supplied by the neighbor count alone.

## 7. Exact frozen inputs and review boundary

| Complete source | SHA256 | Consumed scope |
| --- | --- | --- |
| THREE_GENUINE_LEAF_ROOTS_HIGH_S_REDUCTION.md | 41c6686127871c7c99ab69c84292f04c995a8530eb02cde0235cdacc181ae73f | Whole arbitrary-degree low/critical/D cover and actual epsilon near points |
| UNEQUAL_NEAR_ORIGIN_UNIT_ANGULAR_BUDGET.md | 741ff2415b91fa8d490c601185994b7d947e000003c1ca702e423677eea3684e | Complete one-square angular bound; its full needed argument is reproduced in Section 1.2 |
| ROOTED_GENUINE_S_LEAF_ONE_TENTH_CORNER_BOUNDARY_CAP.md | 31058df9d4e4ac6eaff1194d2b0d59565349fca885795f284c891537a1be820d | Entire force-free physical cap in Sections 1--5, applied after the new chart proof |
| REVIEW_GENUINE_S_LEAF_ONE_TENTH_BOUNDARY_CAP_C6_NEXT_2026_10_27.md | 38f3b928e8b22cefaa6f2cd65272072c74eafafa4eea17082335c5fd5d1428a4 | Existing full independent acceptance of the exact physical cap source |
| THREE_GENUINE_LEAF_ROOTS_POSITIVE_THREE_ARM_TREE_EXCLUSION.md | c9ffa9834fbb5e018122552487256693148e0d45d6b69eef21c68bf577b5cf89 | Whole genuine-root three-arm exclusion, only in Section 5 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original true unloaded2 force/torque transmitter theorem |
| NO_UNLOADED_DIAMOND_HUB.md | 82b546953a927a09d8ccabdefd8ffc10eac3e4efc5d8a122840f1343f80a7e2d | Actual fan private3 load in Section 6 only |
| THREE_GENUINE_ROOTS_BLOCK_TWO_TERMINAL_NETWORK_COVER_AND_DENSE_FIVE_EXCLUSION_2026_10_29.md | 3aed6244d69913b6eecb61ff9b8985688e723da3ec4a57ffaadc8e5d92dd7b66 | Companion graph-only seven-family and six-body component cover; not a premise of the main theorem or Section 5 |

The complete physical cap, complete high-S theorem, complete angular
theorem, complete three-arm theorem and complete diamond theorem were read
directly. The original transmitter proof was checked at its full true2
scope. The cap's existing independent review confirms its exact physical
scope and endpoints. The new angular packing and small-vertex chart
arguments above are separate mathematical contributions and require this
source's own full independent review before adoption.

The main theorem is uniform in every actual root degree and physical
contact pattern. The six-body consequence is a whole graph-domain exit.
The five-body table and remaining six-body partitions are necessary
reductions, with their precise missing physical exits retained. No full
coarse cell, unrestricted lower bound or original equality classification
is declared closed. No original identifier, order, denominator or flag is
edited in this manuscript.

All reasoning is over the whole continuous physical domain. No numerical
pose sample, new packing certificate, physical motion, force deletion,
post-extraction normal change, Lean compilation, CI/workflow dispatch,
remote mutation or merge was performed.
