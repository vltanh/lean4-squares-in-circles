# Physical stress: central bridge cover and two-loaded tree cores

**Status:** proved conditional structure theorems for a physical positive-stress
certificate of a radius-minimizing packing of ten squares. These theorems do not
say that a minimizing certificate has a tree component, that it has only two
loaded bodies, or that either remaining core can be completed to ten squares.
The unrestricted lower bound remains open.

The geometric inputs concerning physical stress come from the n=9 research
branch, rather than from a Lean theorem on the main branch:

- [Physical contact stress](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/PHYSICAL_CONTACT_STRESS.md).
- [Radial bridges and loaded leaves](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/RADIAL_BRIDGE_AND_LEAF_REDUCTION.md).
- [Earlier small-tree classification](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/SMALL_TREE_STRESS_CORES.md).

These source files were read at commit
`901678d95a5197017db81343c7d0182661cc92fc`. We restate the precise inputs
and give the n=10 estimates below. In particular,
we do not import the computational n=8 lower bound used to justify the radius
window of the earlier small-tree manuscript.

## 1. Certificate and radius conventions

Let ten interior-disjoint unit squares lie in the disk of radius R centered at
the origin, and suppose

\[
                         q=R^2\le 9/2.
\]

Area and the elementary bound pi < 22/7 give

\[
             q\ge 10/\pi>35/11>7/4+\sqrt2,
             \qquad R>7/4>\sqrt2.                         \tag{1}
\]

For the comparison in (1), 35/11 - 7/4 = 63/44 > sqrt(2).

A **physical positive-stress certificate** assigns nonnegative weights to
circle vertices and contact forces at actual shared points. On each square,
the contact forces and the radial circle forces balance both force and torque.
A square is **loaded** when its total circle-vertex weight is positive.

Aggregate the contact forces for each body pair to one positive force at an
actual shared point of the two squares. The graph used here is this positive
body-pair graph, not the entire geometric contact graph. A zero-weight square
remains a physical obstacle even if it has no vertex in a selected positive
component.

We use the certificate furnished by the cited physical-stress construction
with the following normal choice: at every point-only vertex/vertex contact
away from the origin, select a supporting normal that is not radial. Such a
normal is available in the open common supporting cone. The construction
therefore has the following consequences.

1. Every positive graph bridge has a radial force line. Summing total torque
   over either component of its deletion leaves only the torque of that bridge;
   radial circle forces have zero torque about the origin.
2. Every bridge cut has a loaded square on both sides. Otherwise force balance
   on the unloaded side leaves one uncancelled nonzero bridge force.
3. An off-origin point-only vertex/vertex positive edge cannot be a bridge.
   This is a property of the selected certificate, not of every possible
   supporting-normal choice.

Existence is an explicit dependency on Sections 2–3 of the pinned physical-
stress source and Section 5 of the pinned radial-bridge source. Their argument
chooses smooth sufficient local separation constraints through the minimizer:
unique support corners at point contacts, and the two actual overlap-endpoint
constraints at side contacts. A global minimizer remains a local minimizer
on that feasible branch. The velocity that dilates all centers, holds angles
fixed, and increases q sufficiently strictly decreases every active constraint;
for a contact its derivative is minus the sum of the two directional
halfwidths, at most -1. This qualification gives normalized nonnegative
Lagrange multipliers with physical force and torque derivatives. The argument
works after the stated nonradial corner/corner normals have been selected,
and does not depend on having nine rather than ten squares. Thus at an
unrestricted global minimizer the cited construction supplies such a
certificate. All conclusions below are conditional on the stated graph
structure of a positive component of that certificate.

## 2. At most four squares cover all positive bridges

Put

\[
                         \delta=\max(R-2,0).
\]

**Bridge-cover theorem.** Every positive bridge has an endpoint square meeting
the closed origin disk of radius delta. All such endpoint squares are
geometrically circle-clear, and there are at most four of them in the packing.

To prove the first assertion, write its radial shared point as p = r e, r >= 0,
and name the incident squares so the inner one supports the line e dot x = r
from below. A unit square has width at least one in every direction. The outer
square therefore has a point with e-coordinate at least r + 1, and containment
in the disk implies r <= R - 1.

At a square support point with unit normal e, the inward segment

\[
                         p-te,\qquad 0\le t\le1,
\]

lies in that square. In its own frame each nonzero coordinate of e points
outward at the support face, and subtracting t times that coordinate changes
it inward by at most one. If r <= 1, this segment contains the origin; if r > 1,
it contains a point at radius r - 1 <= R - 2. This proves the bridge cover.

A square meeting the delta disk cannot also meet the radius-R circle: the
distance between the two meeting points would be at least

\[
                 R-\delta=\min(R,2)>\sqrt2,
\]

larger than the square's diameter.

For the cardinality, each such square's center has norm at most

\[
 \delta+1/\sqrt2\le 2\sqrt2-2<5/6.                         \tag{2}
\]

Distinct square centers have distance at least one because their open
inscribed disks of radius 1/2 are disjoint. Five nonzero centers in the disk
of radius r < 5/6 would have two consecutive polar angles differing by at
most 2 pi / 5. Since cos(2 pi / 5) = (sqrt(5)-1)/4 > 3/10, their squared
distance is at most 7r^2/5 < 35/36 < 1. The bound 7r^2/5 follows by maximizing
a^2 + b^2 - 3ab/5 over 0 <= a,b <= r at the four corners of that rectangle.
If one center is the origin, its distance to every other center is already
less than one. Both alternatives contradict center separation. This proves
the theorem.

## 3. Leaf and transmission formulas

Let

\[
 T=\sqrt{R^2-1/4},\qquad A=T-1,\qquad B=R-\sqrt2.
\]

A loaded graph leaf has one of the following forms, for a radial unit vector e:

| Type | Center | Inward bridge point | Circle load |
| --- | --- | --- | --- |
| S | (T - 1/2)e | Ae | Two equally weighted adjacent vertices |
| D | (R - 1/sqrt(2))e | Be | One vertex |

Here S means a side-normal leaf and D a diagonal leaf. For completeness, if
one circle vertex carries the load, its radial force and the radial bridge
force are opposite. The opposite support point is the opposite square vertex;
their collinearity makes e a diagonal and gives the D row. With two adjacent
circle vertices, write them in the leaf frame as (T, +/-1/2). Their weighted
mean has the form (T,eta). If eta were nonzero, the inward extreme vertex would
have second coordinate opposite in sign to eta and could not be a positive
radial multiple of (T,eta). Thus eta = 0 and the two weights agree, giving S.

Both A and B are positive by (1). A D leaf contacts its neighbor at an
off-origin vertex. By the certificate choice this is in the relative interior
of a neighbor side; the bridge direction is consequently a side normal of
that neighbor.

An unloaded body of degree two has opposite equal forces. Torque balance
makes the two application points collinear along that force direction. If
the force is a side normal, it transmits across opposite sides with width one.
Otherwise the support points are opposite vertices; their collinearity with
the force makes the direction a diagonal, with width sqrt(2).

Any square of center c has maximum squared vertex norm at least

\[
                         \|c\|^2+\|c\|+1/2.
\]

Indeed the exact expression is ||c||^2 + 1/2 plus the sum of the absolute own-
frame coordinates of c, and that sum is at least ||c||. Consequently

\[
                 \|c\|\le (\sqrt{17}-1)/2<25/16.          \tag{3}
\]

For a path of unloaded degree-two transmitters between square endpoints,
the endpoint centers' separation in the common force direction is at least
one plus the sum W of the internal widths. By (3), W < 17/8. Each internal
width is one or sqrt(2), so

\[
                         W\in\{0,1,\sqrt2,2\}.           \tag{4}
\]

In particular two internal bodies must both be side transmitters, and three
internal bodies are impossible.

## 4. Exact two-family reduction for two-loaded tree components

**Two-loaded tree theorem.** If a connected positive component is a tree with
exactly two loaded bodies, it has one of these two forms, after rotating the
entire packing:

1. **S-S:** q = 17/4, with four parallel squares centered at

   \[
   (-3/2,0),\quad(-1/2,\tau_1),\quad(1/2,\tau_2),\quad(3/2,0),
   \qquad |\tau_1|,|\tau_2|\le1/2.                         \tag{5}
   \]

2. **D-S-D:** q = 9/4 + sqrt(2), with two diagonal leaves centered at

   \[
          \left(\pm(1/2+1/\sqrt2),0\right)
   \]

   and one side transmitter centered at (0,tau), where |tau| < 1/2. The
   leaves' diagonals are horizontal and vertical, while the transmitter's
   sides are horizontal and vertical.

Every graph leaf is loaded, since an unloaded one-force body cannot balance.
A finite tree with only two loaded bodies therefore has exactly two leaves
and is a path, with the loaded bodies at its ends. All other bodies on the
path are unloaded degree-two transmitters.

Radial bridge lines and force balance put all application points on one line
through the origin. The two leaves are on opposite rays. Telescoping the
contact points gives

\[
                  W=a_X+a_Y,\qquad a_S=A,\quad a_D=B.       \tag{6}
\]

For S-S, (1) implies W = 2T - 2 > sqrt(2). Thus (4) forces W = 2 and T = 2,
so q = 17/4. Its two internal squares are side transmitters. Their contact
points are (-1,0), (0,0), (1,0), yielding (5). Matching side-contact heights
do not require either transverse center coordinate tau_i to vanish.

For S-D,

\[
                         1<A+B<2.                         \tag{7}
\]

For the lower bound use R > 7/4 and
(7 + 3 sqrt(5))/4 > 2 + sqrt(2). The latter follows by squaring
3 sqrt(5) > 1 + 4 sqrt(2). For the upper bound use R <= 3/sqrt(2), giving

\[
 A+B\le(\sqrt2+\sqrt{17}-2)/2<2.
\]

Thus (4) would force W = sqrt(2), a single diagonal transmitter. At its
contact with the D leaf, both squares contribute a vertex. This is a
point-only contact at the nonzero radius B, contradicting the bridge-normal
choice. S-D is excluded.

For D-D, 0 < W = 2B <= sqrt(2), so W is one or sqrt(2). A value sqrt(2)
again gives a diagonal transmitter with a forbidden off-origin vertex/vertex
bridge. If W = 1, then B = 1/2 and R = sqrt(2) + 1/2. The single internal
body is a side transmitter; its two bridge points are (+/-1/2,0). Its center
is (0,tau), with |tau| <= 1/2. Equality |tau| = 1/2 would turn both contacts
into off-origin vertex/vertex bridges, so |tau| < 1/2. This proves the theorem.

The D-S-D subcase tau = 0 cannot occur in a ten-square packing: the central
transmitter contains the entire open disk of radius 1/2, so the other nine
squares avoid that disk, contradicting
[CENTRAL_DISK_REDUCTION.md](CENTRAL_DISK_REDUCTION.md).
For nonzero tau the transmitter does not contain that entire disk. No such
containment is inferred from its two radial contact points.

## 5. Excluding stars above the lower exceptional radius

**Star theorem.** If R > sqrt(2) + 1/2, a connected positive component cannot
be a star with at least two leaves. A component consisting of a single edge
between two bodies is impossible throughout the radius range (1).

Every leaf is loaded. By the bridge-cover theorem, the hub of a star is
circle-clear and hence unloaded; a one-edge component would instead have
two loaded endpoints, immediately contradicting that theorem.

For the star, use the hub's side axes as coordinates. The leaf contact points
have radius A for S leaves and B for D leaves. The force at each contact is
a positive scalar times its radial vector, with a common choice of sign;
thus hub force balance says a positive combination of those radial vectors
vanishes. The following inequalities hold:

\[
 A^2>1/2,\qquad B>1/2,\qquad A^2-B^2>1/4,
                   \qquad A>\sqrt2 B.                     \tag{8}
\]

The first is precisely the area comparison q > 7/4 + sqrt(2), and the second
is the present radius hypothesis. To check the third, write

\[
 A^2-B^2=2\sqrt2 R-2\sqrt{R^2-1/4}-5/4.
\]

This is strictly increasing for R > sqrt(1/2). At R = 7/4 its being greater
than 1/4 reduces to 7 sqrt(2) - 3 sqrt(5) > 3; squaring reduces this to
22/9 > sqrt(5). Finally

\[
 T^2-(\sqrt2R-1)^2=3/4-B^2\ge1/4>0
\]

because B <= 1/sqrt(2). Hence T > sqrt(2)R - 1 and A > sqrt(2)B.

Each D leaf meets the relative interior of a hub side, so its radial normal
is one of the four hub-axis directions. Two D leaves with the same direction
would coincide. Two opposite D directions would require the hub's width to
be 2B = 1, impossible because B > 1/2. Thus there are at most two D leaves,
and if there are two their directions are adjacent.

If there are no D leaves, all contact points p_j have norm A and a positive
weighted mean equal to zero. After normalizing the weights w_j to sum to one,
the hub center c satisfies

\[
 \sum_j w_j\|p_j-c\|^2=A^2+\|c\|^2>1/2.
\]

This is impossible because every contact point belongs to the hub square and
has distance at most 1/sqrt(2) from its center.

If there is one D leaf, put its contact at (B,0) on the hub's right side. The
hub's horizontal interval is [B-1,B]. Since B > 1/2, every point has |x| <= B.
Every S contact then has |y| >= sqrt(A^2-B^2) > 1/2. The D force has zero
vertical component, so force balance needs S contacts of both vertical signs.
They would be separated vertically by more than one, impossible within a
unit hub square.

If there are two D leaves, put their contacts at (B,0) and (0,B). The hub is
contained in [B-1,B]^2, so all its points have norm at most sqrt(2)B < A. It
contains no S contact. The two remaining positive perpendicular forces cannot
balance. These cases prove the star theorem.

This extension has the explicit strict lower threshold R > sqrt(2) + 1/2.
It does not discard stars at or below that threshold, including the D-S-D
core in Section 4.

## 6. Remaining completion problem

The theorem reduces a specified graph case to two exact geometric families;
it does not show those are the only possible stressed components. The four-
square S-S core still has six unstressed squares to account for, and the
noncentral D-S-D core has seven. Their orientations are unrestricted. The
two parameters in (5), and the nonzero tau in the second family, cannot be
discarded by force or torque balance.

The [sharp exterior-ring theorem](SHARP_EXTERIOR_RING.md) gives an additional
necessary condition in either strictly subcritical family: at least three
of the ten physical squares meet the open disk of radius 1/2. This does not
by itself exclude their completion. Trees with more loaded bodies and
components containing cycles also remain outside this two-family reduction.
