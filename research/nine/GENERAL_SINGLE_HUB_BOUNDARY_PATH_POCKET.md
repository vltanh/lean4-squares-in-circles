# A single unloaded hub and a boundary path have an outer pocket beyond the quarter disk

Date: October 26, 2026.

**Status: accepted complete hand proof after the full-source reviews
REVIEW_SINGLE_HUB_PATH_AND_THREE_FIVE_LOADS_ROOT_2026_10_26.md and
REVIEW_SINGLE_HUB_PATH_THREE_FIVE_LOADS_TRIANGLE_BRIDGES_2026_10_26.md.** This
source strengthens the endpoint argument for the five-spoke fan. It
does not require a spoke from the hub to every internal path body.
Every actual spoke and every actual force is retained.

Write Q=1105/256 and work in 2<=R<=sqrt(Q). Retain the same original
nine-square packing and its selected physical stress. Suppose an entire
positive component has the following form:

    H, B_1,...,B_k, 3<=k<=6;
    B_i B_(i+1), 1<=i<k;
    H B_1, H B_k, and any subset of H B_i for 1<i<k.

H is unloaded, and every B_i has positive total circle load. The actual
outer-face order is H,B_1,...,B_k,H. No body or force outside this
component is removed from the packing. The endpoints B_1,B_k have their
true positive degree two. Internal B_i retain all their actual degrees,
all physical circle masks and individual zero corner weights.

Let p_1,p_k be the original H endpoint applications, n_1,n_k the original
unit normals directed from H into B_1,B_k, and F_i the full circle
resultant on B_i. The *outer H arc* is the boundary arc from p_1 to p_k
which contains no internal positive spoke in the physical exterior-face
order. The exterior pocket is the actual closing circle pocket through H
between B_k and B_1, with all its weak physical contact subdivisions.

**Theorem.** Every whole additional unit in that exterior pocket has
distance strictly greater than 1/4 from the original circle origin.
The claim covers every hub endpoint owner, every original mean, every
internal spoke and positive magnitude, and every physical endpoint mask.

## 1. Complete equations, actual order, and two endpoint moments

The boundary path has no additional physical edge joining nonconsecutive
B_i: it would create a physical boundary cycle on at most k<=6 vertices.
CIRCLE_CONTACT_ANGULAR_ORDER.md, Section 5, excludes every such cycle;
its only cyclic exception is a seven-cycle. This is why the present
standalone statement retains the upper bound k<=6. In particular B_1 and B_k are closed-disjoint and their
H applications are distinct. At an H point at most two B_i occur, and
if two occur they are consecutive on the physical path.

The physical embedding puts every internal hub spoke on the other H
arc, in the order of its actual B_i index. Its outward normals have the
same weak circular order. At distinct points this is the ordinary normal
order of a convex square. At a coincident contact their neighbor tangent
sectors have disjoint interiors, and the normals directed into those
sectors have their physical sector order. Side-owned endpoint means keep
the weak limits; the selected strict convention at free point contacts
keeps their strict normal cones. This is precisely the port-order
argument in CHORDED_HEXAGON_FAN_COMPLETE_EXCLUSION.md, Section 1, and
uses no edge to an omitted internal index.

Write mu_i>0 for every actual hub spoke magnitude, with i ranging only
over the actual spokes I. The complete original hub equations give

    sum_(i in I) mu_i n_i=0,
    sum_(i in I) mu_i det(p_i-c,n_i)=0 for every fixed c.       (1)

Summing all original equations in the component gives

    sum_(i=1)^k F_i=0.                                      (2)

Each boundary force has zero moment about O because its corner forces
are radial. Let g_i be the actual normal directed from B_i to B_(i+1)
and gamma_i>0 its magnitude, at the original mean t_i. The two actual
endpoint torque equations therefore are

    mu_1 det(p_1,n_1)=gamma_1 det(t_1,g_1),
    mu_k det(p_k,n_k)=-gamma_(k-1) det(t_(k-1),g_(k-1)).       (3)

FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Lemma 1.1, is the degree-free
boundary-pair moment theorem: det(t_i,g_i) is strictly positive in the
counterclockwise boundary order and strictly negative in clockwise
order. The actual boundary path has the same circular orientation as
the occupied H arc. Thus, in counterclockwise occupied-arc order,

    det(p_1,n_1)>0, det(p_k,n_k)<0;                           (4)

in clockwise order both signs reverse. No equation at an internal B_i
is used in (3)--(4), and B_2 or B_(k-1) need not touch H.

The true endpoint degree-two proper-concurrence lemma, namely
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, gives

    q_j=tau_j F_j=p_j+ell_j n_j,
    tau_j>0, ell_j>=0, j=1,k.                               (5)

Its required physical boundary neighbor is B_2 or B_(k-1). It includes
two physical circle corners and individual zero weights. The q_j need
not lie in their physical endpoint squares.

Put r=R-sqrt(2). Any point of any B_i satisfies

    |p|>=r>=2-sqrt(2)>1/4,                                  (6)

using one actual circle corner and the unit diameter. Also the unit
lying on the outward side of a hub support gives the useful width bound

    p_j.n_j <= R-1.                                         (7)

Indeed the minimum n_j-projection of B_j is p_j.n_j, its width in that
direction is at least one, and its maximum projection is at most R.

## 2. The occupied-pocket criterion

It suffices to find a vector v!=0 such that

    v.p>0 on the entire outer H arc,
    v.F_1>0, v.F_k>0,
    dist(O, outer H arc)>1/4.                               (8)

Here is the complete geometric join. Replace each endpoint application
only in the barrier construction by the gap-facing extreme a_j of the
actual H--B_j intersection; the original p_j remains in every equation.
The H arc between these extremes is a subarc of the arc in (8). Join
a_j to its gap-facing physical circle corner z_j through the interior
of B_j. The two endpoint paths are disjoint, meet H only at their
contact extremes, and together with that outer H arc make an occupied
crosscut. Its closing circle arc forms an actual Jordan boundary.
The entire boundary misses the closed quarter disk, by (6),(8).

For winding at O, the separate auxiliary homotopy from
CHORDED_HEXAGON_FAN_COMPLETE_EXCLUSION.md, Section 2.2, applies with
exactly these hypotheses. For completeness, every x in B_j satisfies
z.x>=R^2-R sqrt(2)>0 for every physical circle corner z of B_j. Hence
F_j.x>0 throughout B_j, and F_j.q_j>0. Its endpoint path can be homotoped
within that strict half-plane to a_j--q_j--R F_j/|F_j|, avoiding O.
Move the selected circle corner to its resultant direction inside the
body's own angular interval. Distinct physical boundary intervals and
their ordered resultant directions preserve the closing-arc lift.

Every consecutive resultant gap is strictly less than pi: otherwise
the k>=3 distinct directions in (2) lie in a closed semicircle with
at least one in its interior, inconsistent with their positive sum
being zero. Both endpoint resultants lie in v.p>0 by (8), so their
closing gap is their minor arc in that half-plane. After the homotopy,
the entire loop lies in v.p>0 and has winding zero about O. The actual
Jordan boundary consequently also has winding zero about O. It already
misses the whole closed quarter disk, so winding is zero throughout
that connected disk. Its compact boundary has a strict distance margin.
Thus the closed quarter disk, and a slightly larger disk, are outside
the actual bounded pocket. Every whole unit in the pocket has distance
strictly greater than 1/4. Extra zero-weight contacts can subdivide but
cannot enlarge the pocket through the occupied crosscut.

The remaining sections prove (8), or directly contradict the original
equations, for every endpoint normal type.

## 3. Both endpoint normals are H side axes

Choose clockwise occupied-arc order. If both endpoint axes are N, their
ordered normals either make no turn, in which case every actual hub
normal is N and (1) is impossible, or make a full turn. In the latter
case write p_1=(a,h), p_k=(b,h). The full-turn port order gives b<=a,
whereas (4) in clockwise form gives a<0<b. This is impossible.

For adjacent axes, a quarter-turn occupied normal interval would put
all forces in one quadrant, contrary to (1). Rotate and reflect to make
the surviving three-quarter-turn N,E,S,W, with endpoint axes N,W.
Write H=[L,L+1] times [h-1,h]. Equations (4) give

    (p_1)_x<0, (p_k)_y>0,

so L<0<h. Formula (5) places both q_1 and q_k in the strict northwest
quadrant, and therefore both endpoint resultants in that quadrant.
With v=(-1,1)/sqrt(2), the two ports satisfy

    v.p_j >= |p_j|/sqrt(2) >= r/sqrt(2)
           >=sqrt(2)-1>1/4.

The outer arc goes from p_1 through the northwest H vertex to p_k.
Its v-projection on each segment is at least the smaller endpoint
projection. Thus (8) holds. This argument does not require the first
or last internal path body to have a hub spoke.

For opposite axes rotate to endpoints N,S and choose the clockwise
half-turn through E. Write p_1=(a,h), p_k=(b,h-1), with H's left side
x=L. Equation (4) gives a<0 and b<0. Equation (5) therefore puts both
resultants in the strict left half-plane. The whole outer H arc, going
through the two left vertices, has x<=max(a,b)<0. Its horizontal parts
have norms at least those of their endpoint ports, hence at least r.
If the vertical part does not cross y=0, its nearest point is an endpoint,
whose norm is at least the corresponding port norm. If it crosses y=0
and |L|<=1/4, then L<=a,b<0 gives |a|,|b|<=1/4, and (6) implies

    h >= sqrt(r^2-1/16)>1/2,
    1-h >= sqrt(r^2-1/16)>1/2,

a contradiction. The strict comparison follows from
(2-sqrt(2))^2-1/16>1/4, for example using sqrt(2)<91/64.
Thus |L|>1/4 in this last case. The entire outer arc has a strict
quarter-disk margin, and (8) holds with v=(-1,0). No assertion that
adjacent retained spoke neighbors physically touch is needed here.

## 4. One endpoint axis and one oblique endpoint

Reverse the whole path if necessary, rotate to n_1=N, and reflect so
the other endpoint is a left H vertex. Write

    H=[L,L+1] times [h-1,h], p_1=(a,h), L<=a<=L+1.

The oblique endpoint is p_k=(L,h), n_k=(-u,v), or p_k=(L,h-1),
n_k=(-u,-v), where u,v>0. The short occupied arc in the first case
would put every hub normal in the closed upper half-plane, with the
endpoint components strictly positive. In the second case its normal
interval N through W to the strict southwest normal would put every
x-component nonpositive and one strictly negative. Both violate the
full equation (1), including all coincident endpoint sectors.

The occupied arc is therefore the long clockwise arc through the right
and bottom H sides. Equation (4) gives a<0. Equation (5) gives

    (q_1)_x=a<0, (q_k)_x=L-ell_k u<0.

Every point on the outer arc also has negative x-coordinate. If p_k is
the top-left vertex, its whole arc is the horizontal segment extending
left from p_1, with norm at least |p_1|>=r. For the bottom-left vertex,
the outer arc adds a left vertical segment. Its distance argument is
exactly the opposite-axis calculation in Section 3, with the lower
port now at x=L: if that segment crosses y=0 and |L|<=1/4, both actual
port radii require h>1/2 and 1-h>1/2. Otherwise its closest endpoint
already has norm at least r. Thus the outer arc misses the quarter
disk strictly, and (8) holds with v=(-1,0).

## 5. Both endpoint normals are oblique: adjacent H vertices

Both applications are distinct H vertices. First suppose they are
adjacent. Rotate to

    p_1=(x-1/2,h), p_k=(x+1/2,h),
    n_1=(-a,b), n_k=(c,d), a,b,c,d>0,
    a^2+b^2=c^2+d^2=1.

The short top-side occupied arc would put all hub normals in the closed
upper half-plane, impossible by (1). The occupied arc goes around the
other three sides counterclockwise. Its endpoint moment signs (4) give

    b(x-1/2)+a h>0,
    d(x+1/2)-c h<0.                                      (9)

If h<=0 the first inequality forces x>1/2 and the second x<-1/2.
Hence h>0. We next prove |x|<1 without any fan-only center estimate.
If x>=1, put X=x+1/2>=3/2. From (9), h>X d/c, so

    p_k.n_k=Xc+hd > X(c+d^2/c)=X/c>=3/2>R-1,

contradicting (7). The reflected first endpoint excludes x<=-1.
Thus min(|x-1/2|,|x+1/2|)<=1/2. Using (6) at that port gives

    h^2>=r^2-1/4 >=(2-sqrt(2))^2-1/4>9/100.

For the last exact comparison one may use sqrt(2)<283/200.
Therefore h>3/10. The entire outer H arc is the top side at this height;
(5) gives positive y-coordinates for both endpoint resultants. Criterion
(8) holds with v=(0,1).

## 6. Both endpoint normals are oblique: opposite H vertices

Put sigma=1/sqrt(2), rotate the opposite-vertex chord horizontally, and
reflect vertically so the occupied arc is the lower arc. Write

    p_1=(x-sigma,h), p_k=(x+sigma,h), c_H=(x,h).

Group every original positive hub force at p_1 into G_1 and every one
at p_k into G_k. Every other application P is on the intervening lower
arc and satisfies, for its unchanged outward H normal n,

    det(P-p_1,n)<=0, det(P-p_k,n)>=0.                       (10)

On the lower-left side P=p_1+t(sigma,-sigma), n=(-sigma,-sigma),
these determinants are -t and 1-t; the lower-right side gives the
same signs. The bottom vertex has n_y<=-|n_x|, which also gives (10).
The full hub torque about p_k gives (G_1)_y>=0; torque about p_1
gives (G_k)_y>=0. Within the left endpoint group the normal y-component
decreases along the lower-arc order and n_1 is first. In the right
group it increases and n_k is last. Positive weighted group sums
therefore imply

    n_1=(-b_1,a_1), n_k=(b_k,a_k),
    b_j>0, 0<=a_j<=b_j.                                   (11)

This retains every coincident application, positive force and mean.
The lower occupied arc is counterclockwise, so (4) applies.

We claim -sigma<x<sigma, again without a full-fan center bound. If
x>=sigma then X=x+sigma>=sqrt(2), and the last moment sign gives
h>X a_k/b_k. Consequently

    p_k.n_k=Xb_k+h a_k >= X/b_k>=sqrt(2)>R-1.              (12)

When a_k>0 the first inequality is strict; when a_k=0 it is equality,
which is sufficient. Equation (12) contradicts (7). The first endpoint
gives the reflected contradiction if x<=-sigma.

Set X=sigma-x>0 and Y=sigma+x>0. The first moment sign now says

    b_1 h-a_1 X>0,

so h>0. Formula (5) gives positive y-coordinates for q_1,q_k and hence
for both resultants. The whole outer H arc passes through the upper
vertex at height h+sigma and is in y>=h>0. Its upper-left side has
positive support

    (X+h)/sqrt(2)>=sqrt(X^2+h^2)/sqrt(2)
                 =|p_1|/sqrt(2)>=r/sqrt(2)>1/4;

the upper-right side has the identical bound with Y,p_k. Thus its whole
distance exceeds 1/4 and (8) holds with v=(0,1).

## 7. Whole-domain join and limits

Sections 3--6 exhaust the two endpoint normal types. They use the
complete actual hub force and torque equations, the two actual endpoint
equations, degree-free boundary-edge moment signs, and actual physical
port order. They never require an internal path square to touch H, nor
use a degree-two equation at an internal loaded body. Section 2 converts
their signs and actual boundary margins into a whole-pocket exclusion
of the quarter disk, rather than inferring containment from auxiliary
concurrence points.

The conclusion is one uniform exterior-pocket theorem. It does not
assert that the bounded faces of the component are empty. A caller must
prove its complete central and exterior face allocation independently.
It also does not apply when an endpoint has another positive pair force
or when H has a force to an additional body outside the stated path.

No scalar certificate, numerical pose, altered normal, Lean compilation,
CI, remote action, or shared-ledger mutation is used.
