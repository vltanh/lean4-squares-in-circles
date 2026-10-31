# Circle clearance and outward-support restrictions at an intact root's direct bridge

Date: October 26, 2026.

**Status: accepted complete reusable implications and stated direct-connector
exclusion after full root review in
REVIEW_INTACT_ROOT_DIRECT_BRIDGE_ROOT_2026_10_26.md and separate independent
review in REVIEW_INTACT_ROOT_DIRECT_BRIDGE_ROOTED_BLOCKS_2026_10_26.md.**
No shared ledger is changed. The complete two-triangle bridge cells are
not claimed closed.

Keep the common compatible physical certificate, including its existing
nonradial off-origin point-only vertex/vertex convention, and all actual
units in

    2<=R<=sqrt(1105)/16.

For the nine-square caller the accepted same-nine theorem
`NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md` supplies R>2. Put

    d=sqrt(R^2-1/4)-1<61/60,
    epsilon=max(d-1,0)<1/60,
    |c_T|<=d+1/2<91/60                                  (1)

for every contained actual unit T.

## 1. A negative-center radial interface cannot lead directly to a boundary unit

Let actual units H,K have a positive radial bridge with application
p=r e, r>0, where e is the actual unit normal from H to K. Thus

    H subset {e.x<=r},       K subset {e.x>=r},
    p in H intersect K.

Assume

    c_H.e<0.                                             (2)

**Lemma 1.** K is physically circle-clear.

The actual support equation gives

    r=c_H.e+H_H(e)<H_H(e)<=1/sqrt(2),                     (3)

where H_H is the support halfwidth about H's center.

If e is an actual side axis of K, rotate it east. The actual unit is

    K=[r,r+1] times [l,l+1],        -1<=l<=0,

because it contains p=(r,0). Every corner has squared norm at most

    (r+1)^2+1 < (1+1/sqrt(2))^2+1
                =5/2+sqrt(2)<4<=R^2.

This includes a side-mean endpoint at a K vertex. K is circle-clear.

Otherwise -e strictly exposes a K vertex, so K meets H only at p.
Since p!=O, the selected point-only vertex/vertex convention prevents
p from also being an H vertex: such an edge could not be radial.
Therefore p lies in a relative side interior of H. The unchanged
normal e is an H side axis, so (3) strengthens to r<1/2.
If K touched the circle, every one of its points would have norm at
least R-sqrt(2)>=2-sqrt(2)>1/2, by its diameter. This contradicts
|p|=r<1/2. These two alternatives exhaust K's support face, proving
the lemma for every actual mask, feature, and original mean.

## 2. Intact petals and genuine direct leaves supply the sign in Lemma 1

Suppose H is an intact end-triangle root, so its two true degree-two
tips have positive circle load. The accepted origin theorem puts O
in the open interior of H. Consequently H is physically circle-clear,
every other actual unit avoids O, and every outward radial support of
H has strictly positive height.

Every intact end petal at H has its actual resultant M_j satisfying

    c_H.M_j>0

by the complete arbitrary-root-degree end-triangle pressure theorem.

A genuine direct leaf at H also has strictly positive center pressure.
For an S leaf of direction v, the true support is d v, so

    c_H.v=d-H_H(v)>=d-1/sqrt(2)>0.

Here d>9/10 and 1/sqrt(2)<3/4 suffice. For a D leaf, its application
(R-sqrt(2))v lies in an H side interior, giving

    c_H.v=R-sqrt(2)-1/2>0.

Thus its actual positive force alpha v has positive scalar product
with c_H in either genuine leaf type. No degree assumption at H was
used for this geometric pressure statement.

**Corollary 2.** Suppose all positive H forces except one bridge HK
are the forces of one or more intact end petals and genuine direct
leaves. Then K is physically circle-clear.

Indeed, retain every such actual group in the full H equation:

    beta e + sum_j M_j + sum_i alpha_i v_i=0,
    beta>0,

where e points from H to K. At least one intact petal is present.
Taking scalar product with c_H gives c_H.e<0. The actual radial
application p=r e has r>0 because O is interior to H. Lemma 1 applies.

The corollary does not include a two-edge pendant arm at H: that arm's
actual force can have negative center pressure. It is not silently
replaced by a direct leaf or included in the positive sum.

## 3. A clear outer triangle root has only large outward triangle supports

Let A,B,C be an actual positive triangle. At each body keep its entire
actual external system, and assume each has zero origin moment. At A,
assume the full external system is one inward radial bridge of force
-alpha e_x, alpha>0, with actual application

    p=(rho,0), rho>0,         A subset {x>=rho}.          (4)

In particular A has no circle load or other independent positive force.
The application must be the original one; no interface is reset.

**Lemma 3.** Every actual triangle support at A has height at least
rho+1, unless the whole configuration is already impossible. Hence

    rho<=d-1,                                             (5)

and neither B nor C can meet any disk D_delta with 0<=delta<1.

The last conclusion concerns a neighbor with the stated disk
intersection. It is not a claim that all triangle neighbors always
have that intersection.

The complete external noncollinearity theorem applies to the three
true aggregate equations. If A's cycle pair is nonparallel and the
common triangle moment is nonzero, its actual concurrence is a
positive multiple of -alpha e_x. If the moment is zero, the two
nonparallel force lines both pass through O and their concurrence is
O. Thus in either nonparallel case

    q=(-t,0), t>=0,
    P_i=q+l_i n_i,       l_i>=0                           (6)

at each unchanged proper port.

Suppose first that e_x is not an A side axis. Then p is the unique
minimum-x vertex of A, whose inward axes have strictly positive
x-components. Relative to those axes and p, both coordinates of q
are strictly negative. Every vector P_i-q has both own components
strictly positive. Equation (6) would make both normals strictly
expose the same opposite A vertex. Their nonparallel lines would then
concur at that vertex, contrary to q outside A. This rules out every
tilted minimum-vertex alternative.

Thus A=[rho,rho+1] times [l,l+1], with l<=0<=l+1. In (6), every port
has x>=rho>0 while q_x<=0, so l_i>0 and (n_i)_x>0. The port is on the
right wall. Writing a=rho+1 and P=(a,y), its normal is exactly

    n=(a+t,y)/sqrt((a+t)^2+y^2).

Its support height satisfies

    P.n=(a(a+t)+y^2)/sqrt((a+t)^2+y^2)>=a=rho+1.       (7)

Squaring the positive quantities leaves the nonnegative surplus
y^2(a(a+2t)+y^2). This includes y=0 and every side-axis endpoint.

If the cycle pair at A is parallel, its two outward normals cannot
have opposite signs, because that would separate B and C across A's
positive width. Their full force equation with -alpha e_x therefore
makes both normals e_x. Since A contains p and its width in this
direction is at least one, its support is again at least rho+1.
This parallel case requires no concurrence and no aligned frame.

Every actual contained neighbor beyond a support of height h requires
h<=d, by the sharp center/halfwidth bound. Equations (7) and its
parallel counterpart prove (5). If a neighbor meets D_delta, its
separating support also has h<=delta<1, contradicting h>=rho+1>1.
This proves the whole lemma with arbitrary full external aggregates
at B,C retained.

## 4. A complete direct-connector subfamily of the two-triangle inventory

Use the common minimum-support selection and named small-core joins
of `GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md`. Let the entire
positive component have exactly two cyclic blocks, both triangles,
at most nine bodies, and a single interblock bridge H--A. Suppose:

- H is the root of an intact end triangle;
- every further positive bridge branch at H is a genuine direct leaf;
- A has no bridge branch other than AH.

All attachments at the other triangle's vertices B,C remain present.
Every other actual physical square and every original force remains.

**Corollary 4.** This entire original subfamily is impossible.

The origin theorem makes H the only actual unit containing O. Every
positive unloaded bridge-only body is therefore off-origin and, by
the complete transmitter theorem, has its unique inward neighbor at
H. As a consequence B,C have no nontrivial pendant path or outside
fork: such an internal body would have to be adjacent to H and would
create another interblock route, contrary to the original block tree.
All bridge attachments at B,C are genuine direct leaves.

If both B,C were untouched, A would be a second intact end-triangle
root containing O, already impossible. Thus one, say B, has a direct
leaf and meets D_epsilon. A D leaf at B would overlap H through O;
two distinct leaves at B would also put O in B by the complete
two-leaf-root lemma. Thus the remaining possible attachments have
their true single-S-leaf equations. In particular each full external
system on the A,B,C triangle has zero origin moment.

Corollary 2 makes A physically circle-clear. Its only external pair
edge is AH by hypothesis. Direct its radial bridge inward from A
toward H. Since H contains O openly, the opposite outer endpoint A
has the positive nearest support required by (4). Lemma 3 applies.
Its actual neighbor B meets D_epsilon, with epsilon<1/60<1, giving
the contradiction.

This conclusion does not remove the remaining direct-connector
patterns in which A itself has a genuine leaf, or H has a two-edge
pendant arm. Nor does it remove any no-intact-petal or shared-hub
layout. Those are explicit residual obligations for the full C2.33
bridge cells, not alternative representations discarded by this proof.

No force is deleted, no circle mask is changed, and no mean is chosen
anew. No numerical pose, Lean compilation, CI, remote action, or
shared-ledger edit is used.
