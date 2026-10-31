# Two S leaves on different triangle tips force a clear central hub at high radius

Date: October 27, 2026.

**Status: accepted complete hand reduction after full-source root and
separate independent reviews in
REVIEW_TWO_S_HIGH_RADIUS_HUB_CLEARANCE_ROOT_2026_10_27.md and
REVIEW_TWO_S_TIP_TRIANGLES_HIGH_RADIUS_HUB_CLEARANCE_TRIANGLE_BRIDGES_2026_10_27.md.**
This proves physical clearance and closed origin containment
for the entire high-radius S/S part of the last attachment layout of
C2.33.b2. It is not by itself an exclusion of that layout.

## 1. The original seven-body component and complete aggregates

Keep the same original nine physical units and all original selected
normals, positive magnitudes, shared-side means, physical circle masks
and individual zero corner weights. The exact positive edges are

    HA, AB, BH, HC, CD, DH, AL, CM.

Both L and M are genuine S leaves. The actual degrees are H4, A3,
C3, B2, D2, L1, M1. A and C are physically circle-clear by their
genuine leaves; B and D are loaded, because a true unloaded
degree-two transmitter cannot have touching neighbors. Keep both
arbitrary remaining physical squares in place. Write

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=d-1,
    r=R-sqrt(2).

The present domain is

    d>1,        0<epsilon<1/60,        r>129/200.          (1)

The last bound follows from R>sqrt(17)/2>103/50 and
sqrt(2)<283/200.

Let G_H denote H's whole actual circle resultant, with no assumption
yet that it vanishes. The external systems of the actual triangle
A,B,H have resultants

    F_L,        F_B,        G_H+F_D+F_M.                 (2)

Here F_B,F_D are the original loaded-tip circle resultants, and
F_L,F_M are the genuine leaf resultants. The last identity follows
by summing the full original C,D,M equations. The same sum of their
origin torques shows that the entire external system at H has zero
origin moment. The other two external systems have zero origin
moment directly. Thus the actual triangle external-resultant and
proper-port theorems apply to (2), with all four H forces retained.

**Theorem.** Throughout this full S/S domain H is physically
circle-clear. Moreover the actual closed H contains O.

## 2. An aligned S root already has a small actual H application

This local section also includes d=1, with epsilon=0; the strict
bound r>129/200 still holds at that endpoint. Thus its conclusion
is available throughout 1<=d<61/60 independently of Section 5.

Rotate the leaf L east. If A is aligned with L, its full chart is

    A=[epsilon,d] x [h-1,h],        0<=h<=1.             (3)

At A, a vertical A-owned triangle normal would force the other
triangle normal to have the same weak vertical sign, by the physical
unit-triangle owned-normal lemma. Its own strict vertical component
could not be balanced by the horizontal leaf. A horizontal triangle
normal instead forces the other normal horizontal. Parallel triangle
normals must have the same outward sign, so in this alternative both
point west.

In that parallel alternative both actual applications lie on x=epsilon.
The true A origin torque makes their positive weighted mean have
height zero. Since the AB application belongs to the physically
boundary square B, its absolute height exceeds 16/25: indeed

    |p_AB|>=r,
    (129/200)^2-1/3600>(16/25)^2.                       (4)

The actual AH application has the opposite sign, and the two original
heights lie in the same interval of length one. Hence

    |(p_AH)_y|<9/25,
    |p_AH|^2<1/3600+(9/25)^2<r^2.                     (5)

If the triangle normals at A are nonparallel, neither can be an A
axis by the preceding paragraph. They strictly expose vertices with
opposite vertical signs. Opposite A vertices cannot both be used by
a physical unit triangle. The two right vertices would make the
horizontal force sum strictly positive, as would the east leaf.
The actual applications are therefore the two left vertices.
Their negative horizontal components and the true A torque give
0<h<1. Whichever vertex is used by B satisfies (4); the other is
the actual H application and again satisfies (5).

Every point of a square touching the radius-R circle has norm at
least r, by that square's diameter sqrt(2). Thus (5) proves H
physically clear in every aligned-root alternative. No contact mean
or point normal was changed.

## 3. The tilted S-star concurrence is local to this actual triangle

For a tilted A, reflect in the leaf axis if necessary and write

    A=d e_x+[0,1]u+[0,1]v,
    u=(-a,-b),   v=(-b,a),
    a>=b>0,      a^2+b^2=1.                            (6)

The four A vertices in its coordinates based at d e_x are
0, P=(1,0), Q=(0,1), W=(1,1). In particular the original position
of P is d e_x+u. Let n,m be the actual normals from A toward B,H,
with magnitudes mu,nu. Normalize the leaf magnitude to one, so

    mu n+nu m=-e_x.                                    (7)

Sections 1--2 of TIP_LEAF_BOWTIE_S_TILTED_DOMAIN.md apply to this
actual triangle with its M replaced everywhere by the full third
aggregate in (2). They use only (7), B's genuine loaded degree-two
equations, the arbitrary-degree physical triangle proper-port
statement, and zero origin moment of the full H aggregate. They
use no intact opposite petal and no pressure estimate at H.
Here are the scope-sensitive steps of that transfer.

No third unit can contain d e_x: the tilted A and its real S leaf
leave only sectors strictly narrower than a unit's ninety-degree
local sector. If the two triangle applications at A coincided,
(7) would put them at the unique leftmost vertex W. Torque would
give a=b, and that point has norm sqrt(2)-d<r, impossible for B.
Opposite parallel normals would prevent B and H from touching;
equal parallel normals would give the same excluded W application.
Thus A's two lines are independent, with genuine concurrence

    q_A=q e_x.                                        (8)

Write g for the actual B-to-H normal, gamma>0 its magnitude, and
M_H=G_H+F_D+F_M. The complete equations are

    F_B=mu n-gamma g,       M_H=nu m+gamma g.           (9)

When B is nonparallel, its loaded-tip concurrence is a strictly
positive multiple of F_B. The proof of this conditional part in
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, needs no boundary
neighbor; that separate premise was used only to establish
nonparallelism. Combining its actual proper ports with those of
A and H proves q>0 exactly as in Sections 2.1--2.2 of the tilted
domain source, including the parallel-H alternative g=m. In that
alternative no finite H concurrence is asserted.

For completeness the exceptional parallel-B alternative is retained.
Its only possible sign is g=-n. B is radial S or D and its actual
two means have positive weighted mean r_B n, where r_B=d or r.
Write q_A=tau(mu n+nu m), and let s>=0 be the proper distance
between q_A and the genuine H concurrence along m. The unchanged
weighted-mean equation is

    tau nu(mu+gamma)+gamma s=0.                        (10)

If s>0, then tau<0, hence q>0 by (7). If s=0, all original proper
ports force q_A=q_H=p_AH=O and the two B applications to coincide
at r_B n. A and H share the nondegenerate segment from O to that
point, and A has the actual chart

    [r_B-1,r_B] n+[-1,0] m,        n perpendicular m.   (11)

For radial D, the positive normal n at the resulting singleton
vertex/vertex AB contact is an A-side axis, forbidden by the
original compatible strict point-normal selection. For radial S,
the leaf direction in (7) strictly exposes (d-1)n-m. Its norm d
forces (d-1)^2+1=d^2, hence d=1, outside (1). Thus s=0 is excluded
without replacing either real B mean. This proves q>0 for every
physical B mask and parallel alternative.

The first, purely local paragraph of Section 3 of the tilted domain
source also applies before its later pressure estimate. Set

    sigma=d-q.

An A-owned near-face normal -u or -v is impossible by the physical
unit-triangle owned-normal lemma and the positive own components
(a,b) of the right side of (7). If sigma<0, each adjacent vertex
has the wrong normal sign from q_A, while an owned +u or +v port
would have transverse coordinate sigma b or sigma a outside its
actual A side. Only W would remain for both applications, already
excluded. Consequently

    0<=sigma<d,        0<q<=d.                         (12)

## 4. The unordered local port cover always has a low A feature

The feature enumeration in Section 4 of the same source, before
its high-H exclusions, is also entirely local to A,B,H. Its complete
unordered cover is

    {P,W},       {owned +u,W},       {owned +u,owned +v}.
                                                               (13)

Here P,W mean strict vertex normals; an owned side normal includes
the original side mean and its endpoints. To recall why this is
exhaustive, the leaf vertex and near axes have just been excluded.
Opposite strict vertices P,Q cannot both occur in a unit triangle.
The owned-normal nonobtuse lemma excludes Q with +u and P with +v.
The remaining signed own components exclude Q with +v and P with
+u. For Q,W the positive normal coefficients would require

    lambda_Q=(b-a)/(1-sigma b)<=0,

and the +v,W pair has the same nonpositive +v coefficient. All
coincident-vertex alternatives were excluded before (8). This
leaves precisely (13). The equality a=b only removes possible
members of this list; it adds none.

In every listed pair at least one actual application is either P
or on the owned +u face. The latter's real mean has A coordinates
(1,sigma b), because its actual normal line passes through q_A.
Measured in u,v components from the original circle origin, these
two possible low applications are respectively

    P:             (1-d a,-d b),
    owned +u:      (1-d a,-q b).                       (14)

We do not assign H or B to either member of (13) yet, and do not
use the intact-petal pressure bound that made that assignment in
the earlier bowtie source.

## 5. The distinct actual S root forces the relevant A side near O

Put U=d a and V=d b. The circle origin has A coordinates (U,V),
and U^2+V^2=d^2. Since a>=b>0 and d<61/60, we have

    U>0,             0<V<1.                           (15)

If O is not in the open interior of A, (15) therefore gives U>=1.
Since U<=d=1+epsilon, it follows that U>=1-epsilon.

Suppose instead O is in the open interior of A. The distinct
genuine S root C contains a point x with |x|=epsilon: take its
leaf-axis point epsilon e_M in the full S-root chart. That point
cannot belong to int A, since A and C are distinct interior-disjoint
units. The four distances of O to A's actual sides are

    U, V, 1-U, 1-V.

Three of these exceed epsilon. Indeed U>=d/sqrt(2)>epsilon;
U<1 implies V^2=d^2-U^2>d^2-1=2epsilon+epsilon^2, so V>epsilon;
and V<=d/sqrt(2)<61/84 gives 1-V>23/84>epsilon.
Only the fourth side can prevent the radius-epsilon disk from
lying in int A. Thus 1-U<=epsilon in this case too.

In both alternatives we have proved

    1-epsilon<=U<=1+epsilon,
    |1-U|<=epsilon,
    V^2=d^2-U^2<=4epsilon.                             (16)

By (12), q b<=d b=V. Each actual low application in (14) therefore
satisfies

    |p|^2<=epsilon^2+4epsilon
          <1/3600+1/15=241/3600<r^2.                  (17)

Such a point cannot belong to the actual boundary body B. In
every pair in (13), the low application must consequently be the
original AH application. Equation (17) then proves H physically
circle-clear. Together with Section 2 this covers every possible
S-root frame A, with all original H loads retained until this step.

## 6. Closed origin containment at the same central hub

Physical clearance gives G_H=0. The full original H equation now
makes its actual two triangle-pair resultants opposite. For either
triangle, every full external aggregate at its three actual bodies
has zero origin moment, by the true attached-branch sums used in
Section 1. Apply TRIANGLE_EXTERNAL_RAY_INTERSECTS_BODY.md separately
to A,B,H and C,D,H. The actual closed H meets both opposite
nonnegative rays of its two full external resultants. Convexity
gives

    O belongs to H.                                   (18)

This is closed containment. No origin-interior conclusion or
strict positive-parameter ray intersection is asserted. Those
boundary alternatives remain a separate original S/S obligation.

The proof changes no physical body, contact normal, side mean,
corner weight or graph degree. It adds no generic selection beyond
the original compatible strict point-normal convention and invokes
no numerical certificate, Lean compilation or CI. It closes no
original checklist ID by itself.
