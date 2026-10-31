# Every cyclic block contains a genuine D-leaf root

Date: October 28, 2026 UTC. Author: global_blocks.
Read base: c31ecd109097dde3c8faa1db11a84655575e87ab.

**Status: complete proposed uniform hand theorem, submitted for full root
and independent review. No original fine or coarse checkbox is changed.**

Retain all nine original interior-disjoint closed unit squares, their
unchanged containing circle and one compatible selected positive
certificate, with

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1 <61/60,
    epsilon=max(d-1,0)<1/60,
    sigma=3/125 > sqrt(2)*epsilon.

All actual units, full force and torque equations, true positive degrees,
selected normals, original common applications and side means, physical
circle masks, individual zero weights, additional physical contacts and
arbitrary completing squares remain.

Let E have a genuine positive D leaf L. Then:

> **Every maximal cyclic block of E's positive component contains E.**

In fact the same argument excludes any maximal cyclic block of the whole
selected positive graph that avoids E, whether or not it belongs to E's
connected component. The proof uses E's actual outside-block edge E--L
and full torque cancellation in the block's own component. The following
statement and callers need only the same-component conclusion.

The result is independent of every block's order, chord set, root marks,
load pattern and vertex degrees. It strengthens the prior theorem which
required the separate block to contain another genuine leaf root. It
introduces no computational certificate.

## 1. Physical support facts and a cap occupied by at most one actual unit

Every actual contained unit center c satisfies

    |c| <= d+1/2 < M=91/60.

Every contained unit beyond an actual unit-normal support n.x>=h has
c.n>=h+1/2 and hence h<=d. These follow from the farthest-corner
inequality |c|^2+|c|+1/2<=R^2 and the minimum halfwidth 1/2.

Put C=3501/2440. If a real neighbor has support normal n=(u,v) with

    u>60/61, |v|<11/61, h>1,

then c.n>3/2 and |c.Jn|<sqrt(181)/60<27/120. Thus

    c_x>(3/2)(60/61)-(27/120)(11/61)=C.

The squared diameter of a rectangle containing the cap c_x>C, |c|<M is

    (M-C)^2+4(M^2-C^2)=52124381/53582400<1.

Two distinct actual centers cannot lie in this cap, because the actual
open radius-1/2 incircles are disjoint. This is a geometric statement
about occupied units; using a physical supporting axis in it does not
alter an original selected stress normal.

We also use the following complete contact cap. No actual neighbor can
lie beyond h=p.n with both h>1 and |p|^2>=2. Otherwise

    |p.Jn|>sqrt(3479)/60,
    |c.Jn|<sqrt(181)/60,
    |p-c|>(sqrt(3479)-sqrt(181))/60
           >(58-14)/60=11/15>1/sqrt(2),

contradicting p in that actual unit. All support owners and means are
included. This is the full geometric cap from the degree-free port source.

Finally, if p is a minimum-n support point of an actual unit V, then

    p+[0,1]n is a subset of V.                           (1)

At a vertex, the components of n in the two inward own axes are
nonnegative and at most one. At an owned side, n is the inward own axis
and the unchanged tangent coordinate stays in its interval. This proves
(1) for all side means and endpoints without a degree hypothesis.

## 2. A near square with two far neighbors has nonnegative port order

Let X be an actual square avoiding O and meeting closed D_epsilon.
Let N_-,N_+ be distinct actual contained neighboring units, retaining
original contact points p_-,p_+ and outward X normals n_-,n_+, with

    det(p_-,n_-)<0<det(p_+,n_+),
    dist(O,N_-)>sqrt(2)*epsilon,
    dist(O,N_+)>sqrt(2)*epsilon.                         (2)

The point distances in (2) are conditions on the entire actual neighbor
units, including all boundary points. No force equation, degree, load or
radial-contact premise on X is used.

**Near-unit port lemma.** On the unique angular branch of the origin-free
convex X, the angular advance from p_- to p_+ is nonnegative. Equality
can occur only if both applications are one same far corner q of X,
and q is a radial maximum-support point of X with |q|>1. In particular,

    X lies in {x:q.x<=|q|^2}.                           (3)

The proof includes all own intervals touching zero, all selected normal
owners, full shared-side means and endpoint-valued applications.

### 2.1. Both own intervals miss zero

Reflect and exchange own axes, reversing and relabeling the two moment
signs under a reflection, to write

    X=[a,a+1] x [b,b+1],       a>=b>0.

Because X meets D_epsilon, both a,b<=epsilon. The near vertex (a,b)
cannot be a contact with either neighbor in (2). Its outward normal is
(-u,-v), u,v>=0. By (1) the actual neighbor contains
(a,b)-t(u,v) until the first coordinate reaches zero. That first
parameter is at most sqrt(a^2+b^2)<=epsilon<1; the other coordinate
then lies in [0,max(a,b)]. Thus that neighbor would meet D_epsilon,
contrary to (2). This includes u=0 or v=0 by omitting a zero denominator.

The far corner (a+1,b+1) cannot have any contained neighbor: every
normal in its first-quadrant cone has support greater than one and
its point has squared norm greater than two. Section 1's contact cap
excludes the entire cone, including both axis endpoints.

Use the ray of angle pi/4 as a separator. A negative bottom-side port
(x,b) with angle at least pi/4 has 0<x<=b<=epsilon. Its actual South
neighbor contains (x,0) by (1), contradicting (2). A positive left-side
port (a,y) with angle at most pi/4 similarly has 0<y<=a<=epsilon,
and its actual West neighbor contains (0,y). A negative right-side
port (a+1,y) with angle at least pi/4 has y>=a+1>1, so h=a+1>1
and |p|^2>2, forbidden by the contact cap. The positive top-side
counterpart has x>=b+1>1 and is forbidden in exactly the same way.

Every strict lower-right normal has negative moment and its point
has angle below pi/4. Every strict upper-left normal has positive
moment and its point has angle above pi/4. The near and far vertices
have already been excluded. This is the complete feature cover.
The angular increase is strictly positive throughout this case.

The case epsilon=0 cannot enter this chart, since X avoids O but
meets D_epsilon. It creates no omitted limiting case.

### 2.2. One own interval contains zero

The only remaining origin-free near-unit chart is

    X=[a,A] x [b,c], A=a+1,
    0<a<=epsilon, b<=0<=c, c-b=1.                     (4)

We may preserve orientation after choosing the missing own interval
as the positive first interval. Either sign of the other own axis is
allowed in the calculations below. In particular b=0 and c=0 remain.

All negative ports have height at most zero except possibly these
far features:

- an East-axis port (A,Y) with Y>0;
- the upper-right corner (A,c) with a first-quadrant normal of
  negative moment.

Call these the exceptional negative features. Similarly the only
possible positive ports with negative height are an East-axis port
(A,Y) with Y<0 or a positive-moment lower-right corner. Call those
the exceptional positive features. This classification follows directly
from the normal cones of all four sides and vertices; West moment is
the actual height, North moment the positive x coordinate, and South
moment its negative.

Each exceptional feature puts its actual neighbor in the same cap
of Section 1. The East-axis support is A>1. At an upper-right
negative port with n=(u,v), u,v>=0, its moment inequality is
A*v<c*u. Thus u>0 and

    h=A*u+c*v >= A/u >1/u,

where the strict moment gives a stronger strict first inequality when
v>0, and v=0 is the East endpoint. The actual support bound h<=d
gives u>1/d>60/61 and |v|<11/61, as well as h>1. The lower-right
positive case is its exact vertical reflection. Consequently the
two distinct actual neighbors in (2) cannot provide one exceptional
negative and one exceptional positive port simultaneously.

If neither port is exceptional, p_- has height at most zero and p_+
has height at least zero. Their first coordinates are positive, so
the angular advance is nonnegative. Equality would require both
heights zero. With b<0<c, only a West or East side can have height
zero, and its moment is zero. If c=0, the only nonzero moments at
height zero are positive; if b=0, they are negative. The two sides
cannot both have height zero. Thus equality is impossible in this
nonexceptional case.

Suppose p_- is exceptional. It has the form (A,Y), 0<Y<=c. The
other port cannot be exceptional. Every remaining positive port is
either on the top side, including its two corner applications, or
on the West side at a positive height y.

For a top-side positive port (x,c), a<=x<=A,

    arg(x,c)>=arg(A,c)>=arg(A,Y).

Equality forces x=A and Y=c, so both ports are the one far
upper-right corner q=(A,c), with c>0.

For a West-side positive port (a,y), a counterclockwise advance
which were nonpositive would imply

    0<y<=a*Y/A<=a*c/A<=epsilon,
    |(a,y)|<=sqrt(2)*epsilon.

But this point belongs to the actual N_+, contradicting its full
strict clearance in (2). The angular advance in that alternative
is therefore strictly positive. The case where p_+ is exceptional
is obtained by the whole vertical reflection and exchange of the
moment labels. Its only equality is the coincident far lower-right
corner q=(A,b), b<0.

In either possible equality, |q|>A>1, and q's signs put its radial
direction strictly in the corresponding outward far-corner cone.
Thus q maximizes q.x on X, proving (3). This exhausts (4) and
completes the near-unit port lemma.

## 3. The far-body lemma with its equality clause

For use below, record the exact equality conclusion from the complete
far-body feature proof. Let U be an actual unit with

    dist(O,U)>sqrt(2)*epsilon.

For any two actual opposite-strict-moment ports, the angular advance
is nonnegative, with no distance premise on the actual neighbors.
**If it is zero, their applications are the same unique nearest
point of U to O.**

Here is the complete equality check, in addition to the existing
nonnegative proof. If one own interval contains zero, choose
U=[a,a+1]x[b,c], a>epsilon, b<=0<=c. The East side is impossible
by support a+1>d. A wrong-sign far corner also has support greater
than d. Hence negative ports have height at most zero and positive
ports height at least zero. The height-zero argument in Section2.2
makes the advance strictly positive, including b=0 or c=0.

If both intervals miss zero, reflect and exchange them to obtain
U=[a,a+1]x[b,b+1], a>=b>0 and a>epsilon. The East side is again
impossible. The far corner has no neighbor by Section1's contact cap.
Every negative feature lies at angle at most arg(a,b), and every
positive feature lies at angle at least arg(a,b). The inequalities
are strict away from the near vertex: along the bottom or left
side only that endpoint has the same ratio; the lower-right and
upper-left corners have strict ratios; on the top side the least
ratio (b+1)/(a+1)>=b/a could be equal only when a=b and at the
already forbidden far corner. Thus equality forces both actual
ports to be (a,b), the unique nearest point. Those two charts
exhaust the far-body distance premise.

This does not strengthen any neighbor-avoidance premise. It is an
explicit reconstruction of the existing complete feature proof in
HOUSE_ROOF_AC_D_COMPLETE_MOMENT_EXCLUSION.md, Section1.2.

## 4. The D root supplies one exceptional near unit in every separate block

The genuine D-leaf chart gives O in int E. Every distinct actual
closed square consequently avoids O, including its boundary.
The accepted fixed-disk theorem says at most one such square meets
closed D_sigma, sigma=3/125.

Suppose a maximal cyclic block Q avoids E. The actual E--L edge
lies entirely outside Q, since the genuine degree-one leaf L cannot
belong to a cyclic block. Apply the accepted near-origin boundary-access
theorem at E. It supplies an actual Q unit X meeting D_epsilon.
It is the unique non-E unit meeting D_sigma, and every other actual
unit U different from E,X satisfies

    dist(O,U)>sigma>sqrt(2)*epsilon.                    (5)

The strict second inequality follows from epsilon<1/60 and
sqrt(2)<36/25. Thus every original Q unit other than X has the full
far-body premise, including every point of its boundary. X avoids O.
If epsilon=0, X would contain O, already impossible next to int E.
Hence that entire endpoint is excluded here; the remaining argument
has epsilon>0.

## 5. Every original Q edge has nonzero moment

An edge with both endpoints different from X joins two units avoiding
D_epsilon. If its original selected application and normal were
radial, the missing-own-interval argument in Section2 of the accepted
near-origin transfer source would put its inner endpoint in
D_epsilon: at radial radius t<=d its missing interval has far
coordinate a+1>1, so a<=t-1<=epsilon; two missing intervals would
force t>sqrt(2)>d. This is impossible by (5). An application at O
is also impossible.

If an edge incident to X had zero original moment, its unchanged
compatible selected normal and application would give a radial contact
from X to an actual unit T!=E. Section6 of
ORIGIN_FREE_RADIAL_INNER_UNIT_DEGREE_FREE_PORT_ORDER.md excludes
exactly this situation for the unique near unit of a block outside
a D root. Its premise is the original radial selected data, not a
second geometric normal at a selected nonradial vertex contact.

For completeness, that corollary has no dependency on the new
near-unit lemma proved above. Its argument uses the following older
geometric kernel, proved in Sections1--5 of its source: an
origin-free inner endpoint of any actual radial contact has strict
opposite-moment port order for its contacts to other units, because
the actual radial outer neighbor already occupies the unique cap.
All original nonzero Q moments form a nonempty circulation, since
some edge of a cyclic block has neither endpoint X. A directed
cycle in that circulation cannot use the radial XT edge. At X it
therefore has strict advance from that radial-inner kernel, and at
all its other vertices it has nonnegative advance from (5). A
cycle avoiding X has positive winding by the existing disk-avoiding
cycle theorem. Either cycle traps the actual E and boundary leaf L,
a contradiction. This independently excludes the proposed radial
selected edge without using Section2 or the conclusion of this source.

Consequently every original Q edge has nonzero origin moment. No
physical edge, force term or side mean has been removed or modified.

## 6. Full original torques force a directed cycle

Every component outside a maximal cyclic block attaches at at most
one block vertex. Sum all of its full original origin-torque equations.
Every internal pair cancels at its real common application, and every
circle atom has zero origin torque. Its entire contribution at the
sole attachment therefore has zero moment. Applying this to every
outside component leaves exactly the original Q-edge moment sum
zero at every Q vertex. All other force equations remain unchanged.

Orient each Q edge by the direction in which its unchanged moment
is positive, and retain its positive moment magnitude. This is a
nonempty finite positive circulation. Following outgoing edges from
an incoming edge until the first repeated vertex supplies a directed
simple cycle C. The original graph is simple, so C has at least
three actual distinct vertices.

If C avoids X, every cycle unit avoids D_epsilon. The accepted
complete directed-cycle theorem already gives positive winding
about O, including its coincident-nearest-point equality case.
Suppose C contains X. Its two neighbors are distinct and satisfy
(5), so the complete new near-unit port lemma applies at X. All
other cycle vertices satisfy Section3. Every actual chord between
the two original cycle ports therefore has nonnegative angular
advance on its origin-free unit's branch.

## 7. The all-zero angular-advance case is physically impossible

If all these advances were zero, Section2 would make both ports at
X one far corner q, radial-maximal on X, with |q|>1. Section3 would
make both ports at every other cycle unit its unique nearest point
to O. Neighboring cycle ports share their original common application,
so equality propagates around the connected cycle: every one of
those applications is exactly the same q.

There are at least two actual cycle units other than X. Call two
of them U,V. The nearest-point condition for a convex closed unit
implies

    q.z >= |q|^2 for every z in U and for every z in V.

Indeed, the derivative at zero of |q+t(z-q)|^2 is nonnegative,
since q minimizes squared norm. On X, Section2 gives the opposite
inequality q.x<=|q|^2, with q in X. Consequently U and V are two
distinct actual outward radial neighbors of the origin-free X,
at radial radius |q|>1 and radial normal q/|q|.

That is impossible by Section1's cap, or equivalently the geometric
outward-radial-neighbor uniqueness lemma in Sections2,5 of the
radial-inner source. Explicitly choose a missing own interval
[a,a+1] of X with a>0. Each radial outward support has first
coordinate a+1>1 and radius t<=d, so its normal's first component
is >1/d>60/61. Each actual neighbor center must occupy the same
cap c_x>C, |c|<M, whose diameter is strictly below one. The two
actual unit incircles cannot both fit.

These radial supporting half-planes are used only for physical
center bounds. No original selected force normal is declared radial
or reselected at this step. Thus the equality argument is valid
even if the original two normals at q were different, nonradial
vertex normals.

The all-zero case is excluded. The closed actual contact loop C
has strictly positive total angular advance, an integer multiple
of 2pi, and hence positive winding about O.

## 8. Protected physical boundary access finishes the whole-block theorem

Replace center-to-port strands within each actual cycle unit by its
straight port chord. This is a homotopy in an origin-free convex
square and preserves winding. Choose one sufficiently close
compatible physical embedding of the entire selected graph; finite
positive O clearances preserve C's positive winding and make it a
simple Jordan curve.

The compact segment O--c_E lies in int E and misses all closed
cycle units. Choose the same finite routing neighborhoods smaller
than that clearance as well. E has the same positive winding as O
and lies inside C. The actual E--L edge is entirely outside Q and
cannot cross C in this single compatible embedding. It puts the
actual physical boundary leaf L inside C too. This contradicts
L's protected incidence with the unbounded face.

Thus Q cannot avoid E. Every maximal cyclic block contains the
actual D-leaf root E, as claimed. Every original force, selected
normal, application, mean endpoint, circle mask, zero weight and
physical unit remains throughout the argument.

## 9. Whole original-domain consequences and exact limits

The theorem removes any original attachment with a genuine D leaf
at a vertex omitted from some actual maximal cyclic block. It is
uniform over all marked block graphs and private load masks.
In particular:

1. In the retained non-intact C2.36.b1 family, the genuine leaf is
   at triangle-private A, the actual triangle is H,A,B, and the
   six-block Q shares only H with that triangle. Q avoids A.
   Therefore the *entire D alternative* is excluded, including all
   chorded six-block graphs, every mark and load mask, and all
   actual true degrees at H. Only the genuine S alternative
   remains in this non-intact attachment.
2. The same full D exclusion applies to a triangle-private leaf
   beside a shared five-block in C2.35.b1, and more generally to
   every original cyclic block order allowed by the same nine
   units. The one physical extra in the eight-body case remains
   fixed and arbitrary.
3. Every private-D exclusion in the four retained C2.35.b2
   attachment families follows immediately. Those earlier exits
   are not counted a second time. In the private/common family
   a D leaf at the shared H is not excluded: both actual cyclic
   blocks contain H, so that alternative stays open.
4. If an original positive component has two vertex-disjoint
   maximal cyclic blocks, it has no genuine D leaf anywhere.
   Every proposed D root would have to lie in both disjoint
   vertex sets. The theorem applies without a special bridge
   length, leaf count, side owner or block graph partition.
5. For two blocks sharing exactly H, every genuine D leaf in
   that component must be attached at H. For any collection of
   blocks with empty common vertex intersection, all genuine
   leaves are S. These are direct consequences about actual
   original vertices, without a force-system contraction.

This source does not classify all S attachments, exclude every
component with a D leaf, or assert that every bridge is a direct
leaf at E. The latter statement would require a separate proof;
radial bridge chains have not been deleted here. It does not
change a coarse or fine count. The original larger-block fine
inventory does not isolate the new D/S split as a complete old
fine label. In particular G3.M8.ALL, G3.M9.ALL, C2.35.b1 and
C2.36.b1 remain open with their complete other domains.

The proof adds no numerical pose, angle subdivision, scalar table,
computational exclusion certificate, Lean execution, compilation,
CI, workflow, remote write or shared-ledger edit.

## 10. Operative source pins and dependency boundary

| Source | SHA256 | Exact scope |
| --- | --- | --- |
| ORIGIN_FREE_RADIAL_INNER_UNIT_DEGREE_FREE_PORT_ORDER.md | 7142244039afad69773c04ce9e8d7b798075e6ed638ff9d1493da7cc2cfc91db | Complete radial-inner geometric kernel and Section6, with the unchanged compatible selected radial-contact premise; no dependence on this new source. |
| D_LEAF_ROOT_AT_MOST_ONE_OTHER_UNIT_IN_THREE_125_DISK.md | 34385a647c1889564b3423ecfff03a7a75747275e45f68346c3f8a9f06abfaaf | Entire fixed-disk physical exclusion, arbitrary root degree. |
| NEAR_ORIGIN_BOUNDARY_ACCESS_TRANSFERS_TO_EVERY_CYCLIC_BLOCK.md | 49065116bfd526abf3826ae8bbaa6fd9ad43b7bcdbdc0e0653b959fa84359549 | Entire near transfer from the actual outside E--L boundary path, including epsilon=0. |
| GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md | 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49 | Sections1--3 support/cap facts and existing positive winding for a cycle avoiding X. |
| HOUSE_ROOF_AC_D_COMPLETE_MOMENT_EXCLUSION.md | db795b7a1a287d7e8e422bd80f3ea04e714d9d98af88226e9c16ad757b7e0f5a | Section1.2 full far-body feature proof; its equality clause is reconstructed in Section3 above. |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Single sufficiently close compatible embedding, all weak junctions and physical boundary access. |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine D open-origin geometry and full origin-torque conventions. |
| C2_35_TWO_BRIDGES_AND_C2_36_ONE_BRIDGE_ORIGINAL_ATTACHMENT_REDUCTION.md | 28810d74517a6f6a4a4e5b2972c5359bdf41559957bd7e33bcb5fb4b358685d5 | Only the literal original retained C2.36.b1 non-intact and C2.35.b2 attachment maps in Section9; no smaller-block metric conclusion is transferred. |

All new angular and equality arguments are proved in full above. Earlier
selected-certificate existence and inherited global prerequisite boundaries
remain unchanged. No closure of the unrestricted sharp inequality or
original equality classification is asserted by this structural theorem.
