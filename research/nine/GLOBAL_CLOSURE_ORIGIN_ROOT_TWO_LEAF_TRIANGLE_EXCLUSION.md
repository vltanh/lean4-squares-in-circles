# An origin-interior root cannot support a triangle with two leaf-bearing tips

Date: October 26, 2026.

**Status: complete local theorem and original decorated-petal exclusion;
full root and separate independent audits accepted.** The acceptance
records are REVIEW_ORIGIN_ROOT_TWO_LEAF_TRIANGLE_ROOT_2026_10_26.md and
REVIEW_ORIGIN_ROOT_TWO_LEAF_TRIANGLE_ROOTED_BLOCKS_2026_10_26.md.
This is an acceptance-status edit only; no ledger is changed.

Keep all actual physical squares and the common compatible certificate
selection in

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,     epsilon=max(d-1,0)<1/60.

Let H,A,B be an actual positive triangle. Each of A,B has exactly one
further positive pair edge, to its own genuine leaf, and has no other
external pair forces. Every original circle force is retained. H keeps
its arbitrary full external system, assumed to have zero origin moment.
Suppose

    O belongs to int H,
    every vertex of H has norm greater than 1/40.          (1)

**Theorem.** A compatible necessary certificate can be selected so that
this entire local configuration is impossible.

The additional selection below consists only of explicitly nontrivial
finite normal determinants, imposed before multiplier extraction. The
physical pose, all shared-side means, and all other squares stay fixed.
The theorem does not assume a degree-two equation or a single radial
external force at H.

## 1. Full load, origin, and concurrence reductions

The genuine radial leaf theorem makes A and B physically circle-clear.
A D leaf would put O in its root's open interior, contradicting (1).
An S-leaf root contains O when d<=1, again impossible because H contains
O openly. Thus the only remaining domain is

    d=1+epsilon,       0<epsilon<1/60,
    both leaves are S, and A,B each meet D_epsilon.        (2)

Write their actual leaf directions v_A,v_B and positive magnitudes
alpha_A,alpha_B. Their full external resultants are precisely
alpha_A v_A and alpha_B v_B. Their actual outward leaf applications are
d v_A and d v_B. No root load has been dropped: physical circle-clearance
is the original radial-endpoint conclusion.

Apply RADIAL_TRIANGLE_EXTERNAL_RESULTANTS_NONCOLLINEAR.md to the three
full external systems and then
ROOTED_ORIGIN_TRIANGLE_EXTERNAL_RAY_RESTRICTION.md. The triangle's
common directed cycle moment is nonzero. Its three external resultants
are nonzero and noncollinear. At every nonparallel A or B cycle pair,
the genuine concurrence is a positive multiple of its own leaf direction.
All proper-port statements retain nonnegative proper lengths. If m is
the actual outward normal from A or B toward H, then

    h_A(m)<0 or h_B(m)<0, respectively.                   (3)

Moreover A avoids the whole nonpositive v_A ray, and B avoids the whole
nonpositive v_B ray. These statements include parallel cycle pairs,
and no concurrence is assigned to such a pair.

For every original H-to-A or H-to-B normal n,

    0<h_H(n)<=epsilon.                                   (4)

Indeed O is inside H, and the corresponding neighbor contains an actual
point in D_epsilon on the exterior side of that unchanged support.

## 2. Small support directions of H make strictly acute angles

We use the following elementary geometric consequence of (1)--(2).

**Small-support lemma.** All unit directions n satisfying
0<h_H(n)<=epsilon lie within an open angle of pi/4 on either side of
one actual H side axis. In particular any two such directions have
strictly positive scalar product.

Write H in its own axes as [-a,b] times [-c,f], with a,b,c,f>0 and
a+b=c+f=1. A support in any direction is the nonnegative linear
combination of the two corresponding adjacent side heights, with the
absolute direction components as coefficients. If both active side
heights exceeded epsilon, that support would exceed epsilon. Hence a
small support uses at least one actual side of height at most epsilon.

There is at most one such side. Two opposite ones would sum to at most
2epsilon<1. Two adjacent ones would give a vertex of norm at most
sqrt(2)epsilon<1/40, contrary to (1). Call the unique small side axis N,
and its height b_0 in (0,epsilon].

Every small support has positive N-component. If theta is its signed
angle from N, then |theta|<pi/2 and

    h_H(n)=b_0 cos(theta)+t |sin(theta)|,

where t>epsilon is the appropriate adjacent side height. The corresponding
vertex satisfies sqrt(b_0^2+t^2)>1/40. On pi/4<=|theta|<=pi/2 the displayed
positive trigonometric function is concave, so its minimum is at an
endpoint. At those endpoints its values are

    (b_0+t)/sqrt(2)>1/(40sqrt(2))>epsilon,
    t>epsilon.

This excludes the whole interval. Thus |theta|<pi/4, proving the lemma.
The exact strict comparison used here is

    2(1/60)^2=1/1800<1/1600=(1/40)^2.

In particular (4) makes the two actual normals at H strictly acute.

## 3. Radial vertices of an S-leaf root and actual fixed-point selection

### 3.1. The complete radial-vertex facts

Let K be one of A,B and v its genuine S-leaf direction.

If v is a K side axis, the whole root chart is

    K=[epsilon,d] v + [l,l+1] Jv,     -1<=l<=0.          (5)

The only vertices on the positive v ray can be d v and epsilon v;
they occur only when zero is an endpoint of the transverse interval.

If v is not a side axis, d v is a strict supporting vertex and

    K=d v-[0,1]u-[0,1]w,

where u,w are orthonormal and v.u,v.w>0. Neither adjacent vertex is
collinear with v. The opposite vertex is collinear only when
v=(u+w)/sqrt(2), and is then (d-sqrt(2))v on the negative ray. Thus,
using the forbidden nonpositive ray from Section 1, a positive radial
vertex of either root is always its leaf application d v or the
aligned inner vertex epsilon v.

No K-to-H application can equal d v. At that point v and every actual
outward K normal m belong to the same right-angle normal cone, so
v.m>=0 and h_K(m)=d(v.m)>=0, contrary to (3).

Also a free point-only vertex/vertex AB contact cannot equal a leaf
application d v. The genuine S leaf occupies a full tangent half-plane
there. The two distinct units A,B would have to fill the opposite
half-plane by their two right-angle cones. Their frames would then
align and their actual intersection would include a full unit side.
Such an AB contact is not free.

Here and below "free" has exactly the original strict point-normal
meaning: a point-only vertex/vertex interface with an open interval
of allowed normals and no side-axis owner.

### 3.2. A free AB edge has a fixed distinct contact on one root

Suppose AB is free. If both AH and BH were positive-length shared
sides, all three frames would be parallel. Their two actual normals
at H would be side axes. The small-support lemma forces those axes
to be the same. Then A,B have the same normal interval outside that
H side; their interior disjointness and physical contact force a
transverse displacement of one, giving a shared AB side. This
contradicts freedom of AB.

Thus at least one of AH,BH is a singleton. Call that root A. Let p
be its fixed AB point, q its fixed AH point, v=v_A, n its free
AB normal, and m its AH normal.

The points p,q are distinct. If they coincided, torque about p would
give det(p,v)=0. The ray restriction and Section 3.1 leave only the
aligned inner vertex p=epsilon v. The two positive cycle normals
then sum to a negative multiple of v. In the normal cone at that
inner vertex, -v is an extreme ray, so both normals must equal -v.
In particular the AB normal would have an A side owner, contrary
to the assumed free interface.

All the following determinant arguments therefore use actual distinct,
fixed physical points. No variable shared-side mean is fixed.

### 3.3. The AB determinant is nontrivial on its allowed normal domain

The complete A force and moment equations imply the necessary identity

    D(n,m)=det(v,n) det(q,m)-det(v,m) det(p,n)=0.          (6)

If m is parallel to v, positive force balance forces n parallel to v
too. Those at most two directions can be avoided in a free interval.

If det(v,m) is nonzero, regard (6) as det(W,n)=0, where

    W=det(q,m) v-det(v,m) p.                             (7)

Suppose W=0. Then p lies on the v line. The nonpositive ray and leaf
application cases are already excluded, so p=epsilon v in the aligned
chart (5), with p a vertex. Equation (7) would give q-p parallel to m.

This is impossible for the actual H contact. From that inner vertex
write K=p+[0,1]v+[0,1]w, where w is one of the two transverse unit axes.
A nonzero vector q-p parallel to an outward normal at q can only point
toward an adjacent vertex along its positive coordinate axis or toward
the opposite vertex along the diagonal. A negative coefficient is
impossible: any positive coordinate of q-p then contradicts the
support sign on that coordinate. Every remaining possibility has
strictly positive outward support, at least one. This contradicts (3).

Hence W is nonzero. A nonzero determinant det(W,n) cannot vanish on an
open interval of free normals. If m is free too, p and q are distinct
junctions; choosing m nonparallel to v and then n as above proves that
D is not identically zero on the product of their allowed intervals.

Prelist the finitely many physical body/leaf/contact assignments and
impose these finite nontrivial analytic exclusions simultaneously with
the preceding strict, nonradial, matched-junction and generic choices.
Edges sharing A are not an identified opposite pair of a four-junction.
The selection is made before multiplier extraction, and surviving point
normals are unchanged by uncrossing or thinning. Shared-side means remain
unrestricted. This is the same legitimate finite-avoidance mechanism
as GENERAL_FIXED_TIP_NORMAL_SELECTION.md, now with its actual S-root
radial exceptions explicitly resolved.

Consequently AB has an actual side-axis owner in every selected
configuration under consideration. Exchange A,B so that A owns it.

## 4. A nonparallel owner would place H behind a positive support

Rotate so A's outward AB normal is -e_x. By the physical two supports
and the points of A,B in D_epsilon, the AB wall is x=h with

    |h|<=epsilon.

The radius-free UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md gives
(-e_x).m>=0 for the other A cycle normal m toward H, so m_x<=0.
Suppose the A cycle pair is nonparallel. Reflect vertically so its
leaf has positive vertical component. Full force balance then gives
m_y<0, and the actual S-leaf support is the upper-right A vertex:

    A=[h,h+1] times [u-1,u],
    p_L=(h+1,u),         u>0,
    u^2=d^2-(h+1)^2<=4epsilon<1/15,
    u<4/15.                                               (8)

Let the original AB mean be (h,y). Positive radial concurrence and
the actual horizontal AB force line give

    q_A=((h+1)y/u,y),         0<y<=u.                       (9)

If m_x=0, the H support is the bottom A side, of height 1-u>0,
contrary to (3). If m_x<0, the actual AH point is (h,u-1).
Its proper line from (9), with positive proper length, gives

    m=(-a,-b),       a,b>0,
    a/b=(q_Ax-h)/(1-u+y)<=1/(1-u+y).                       (10)

For h<=0 its support -ah+b(1-u) is positive. For h>0,

    h_A(m)/b = 1-u-(a/b)h
              >=1-u-epsilon/(1-u)
              >11/15-(1/60)/(11/15)
              =469/660>0.                                (11)

Again this contradicts (3). Thus the owner A must have parallel cycle
forces. This argument retains every AB mean, zero proper-length
endpoint at AB, and both full leaf-root orientations.

## 5. The entire parallel-owner chart

The two parallel A cycle normals have the same outward sign; opposite
signs would separate the other two triangle bodies. Full force balance
and the A-owned normal therefore give

    v_A=e_x,       n_AB=n_AH=-e_x,
    A=[epsilon,d] times [t-1,t].                          (12)

The nonzero common moment and the full A torque equation put the
two original means at opposite nonzero heights. Reflect if necessary:

    P=(epsilon,Y) on AB,   Q=(epsilon,Z) on AH,
    Y>0>Z,     0<t<1,     Y-Z<=1.                         (13)

B cannot have parallel cycle forces: their same outward sign would
make v_B=-e_x, contradicting the noncollinear full external resultants.
If B had the same frame as A, it would also own AB and Section 4,
applied at its nonparallel pair, would already exclude it.

Thus B is oblique to A, and P is its unique rightmost vertex. Write

    B=P+[0,1]v+[0,1]w,
    v=(-c,s), w=(-s,-c),  c,s>0, c^2+s^2=1.              (14)

Its positive concurrence is on the horizontal AB force line, so it
has height Y>0. The genuine B-leaf direction therefore has positive
vertical component. If k is the actual outward B-to-H normal, full
B balance is

    mu e_x + nu k + beta v_B=0,       mu,nu,beta>0.        (15)

It follows that k_y<0. At H its two normals are e_x and -k.
By (4) and the small-support lemma their scalar product is positive.
Consequently

    k_x<0,     k_y<0,     h_B(k)<0.                       (16)

These signs use the full H geometry and keep its arbitrary external
aggregate.

## 6. The BH edge has a genuine side owner

BH cannot be a positive-length shared side. Such a side would make
B and H parallel. Since both have rightmost support x=epsilon, their
rightmost vertices would be P and Q in (13), separated vertically
by D=Y-Z<=1. Their two frame projections have absolute values Dc,Ds<1.
The two parallel unit squares would overlap in their open interiors.

Suppose BH instead has a free vertex/vertex normal at the fixed point T.
The B radial concurrence is already fixed by the actual AB line and
the actual leaf direction:

    q_B=(Y/(d v_B)_y) d v_B.

This is a positive multiple because (d v_B)_y>0. The B cycle
applications cannot coincide: P on the positive leaf ray would, by
Section 3.1, be d v_B or epsilon v_B, whereas

    epsilon<|P|<sqrt(1+epsilon^2)<d.

The first inequality uses Y>0, and the last uses epsilon>0.
Thus T differs from P and has an independent free-normal parameter.

Nor can T=q_B. Such a T would be a positive radial B vertex.
The leaf application is impossible as an H contact by Section 3.1.
The only other option is epsilon v_B, whose norm is epsilon<1/40.
But a free BH contact would make that point an H vertex, contrary
to (1).

Therefore T-q_B is nonzero. The necessary normal-line condition

    det(T-q_B,k)=0

excludes only finitely many directions in the free BH interval.
Prelist this nontrivial fixed-point condition before multiplier
extraction along with Section 3. It does not involve the AH mean,
the H external aggregate, or an unknown force magnitude. Hence BH
has an actual side-axis owner, either B or H. Its original application
is retained, including every side endpoint.

## 7. Every B-owned BH side is impossible

In the B frame (14), the only side axis with both components negative
is w. Thus a B-owned BH normal must be k=w.

Its negative support in (16) is

    h_B(w)=1-epsilon s-Yc<0.                              (17)

Every point of B has negative w-coordinate. In particular the genuine
radial application d v_B has negative w-coordinate, so v_B.w<0.
Taking the v-component of (15) gives beta(v_B.v)=mu c>0.
Thus the actual S-leaf support is the strict vertex

    d v_B=P+v=(epsilon-c,Y+s).

Its exact radius identity is

    Y^2+2Ys=2epsilon(1+c)<4epsilon<1/15.

Hence Y<4/15. But (17) now satisfies

    h_B(w)>1-1/60-4/15=43/60>0,

a contradiction. The argument includes all possible B side means;
the strict leaf vertex is a consequence of the full force signs,
not an added physical mask.

## 8. Every H-owned BH side is impossible

If H were parallel to A, its axes would be horizontal or vertical,
contrary to the two strict signs of k in (16). Therefore H is oblique,
and its actual AH application Q is its unique rightmost vertex:

    H=Q+[0,1]n+[0,1]m,
    n=(-a,b), m=(-b,-a),  a,b>0, a^2+b^2=1.              (18)

The only H side axis with both components negative is m, so k=m.
The origin's strict interior position in the m coordinate gives

    Q.m=-epsilon b-Za<0,
    |Z|<epsilon b/a.                                     (19)

If a>=b, then |Q|<sqrt(2)epsilon<1/40, contrary to its actual
vertex margin. Consequently

    rho=b/a>1.                                           (20)

Set E=bc-as. The B frame projections on m are

    m.v=E,          m.w=bs+ac>0.

If E=0, B and H have the same frame, already excluded in Section 6.
If E>0, the B maximum-m contact is P+v+w. The H minimum-m face
is Q+[0,1]n. Equality of the x-coordinates of an actual contact gives

    tau a=c+s>1,       0<=tau<=1,

which is impossible.

If E<0, the B maximum-m contact is P+w. Its equality with Q+tau n
gives, with all side endpoints retained,

    tau a=s,
    Y-Z=c+(b/a)s=c+rho s>c+s>1.

This contradicts the original wall span Y-Z<=1 in (13).
These are all H-owned features. Sections 7--8 exhaust every surviving
normal owner, completing the parallel-owner exclusion and the theorem.

## 9. Complete original decorated-petal application

Suppose an actual root H has an intact end triangle and another
triangle H,A,B whose two tips A,B each have one genuine direct leaf
and no other external pair edge. All additional H forces remain.

ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md gives O in int H. Its common
side chart, with actual straddling ports, gives P<39/40. One port has
transverse coordinate of magnitude at most 1/2, so the actual boundary
point bound gives

    P^2>(67/120)^2-1/4=889/14400>1/25.

Thus P>1/5 and 1-P>1/40. Every H vertex has absolute longitudinal
coordinate at least min(P,1-P)>1/40. This proves precisely (1).

The two genuine leaf roots satisfy the full degree and clearance
premises above. The full external H system has zero origin moment:
sum the original private-body moment equations in each attached
branch, retaining every actual circle force and common application.
The theorem therefore excludes the entire two-leaf decorated petal,
including D/S/D leaf alternatives before reduction, all masks, all
actual means, and arbitrary further H branches.

For C2.33.b2 this is the complete shared-hub layout in which both
bridge leaves attach to the two tips of one triangle and the other
triangle is intact. The other original layouts, including a leaf at
H together with one tip leaf and the no-intact-petal layout, are not
declared closed here. No coarse or fine label changes in this source.

No physical square is moved, no positive force is deleted, no mean
is replaced by a midpoint, and no normal is chosen after extraction.
No Lean compilation, CI, numerical pose, remote action, or shared-ledger
edit is used.

