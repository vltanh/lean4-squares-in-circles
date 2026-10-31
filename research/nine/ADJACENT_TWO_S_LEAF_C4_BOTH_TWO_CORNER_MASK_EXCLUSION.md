# Adjacent S leaves: both two-physical-circle-corner boundary masks are impossible

Date: October 27, 2026.

**Status: complete hand exclusion with an explicit compatible initial
point-normal refinement, submitted for full root and separate independent
review.** This closes the entire high domain in which both C and D have
two physical circle corners. It does not close the mixed one-corner /
two-corner mask or the whole LCD.SS gate.

Keep the same nine actual contained, interior-disjoint unit squares and
the original selected component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1.

L,M are the two genuine S leaves at A,B. A,B are physically clear;
C,D have positive total circle load. Work in the strict-high range

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60,       R^2<=1105/256.                 (1)

Every original force, contact owner, actual application mean and physical
circle mask is retained. In particular a physical two-corner mask does
not require both of its individual circle weights to be positive.
All three other original units remain present and arbitrary.

The only new initial convention is in Section 1. It selects a free
normal on the fixed physical pose before the multiplier theorem. No
normal of an obtained certificate is changed.

## 1. The physical radial pair and the initial open normal restriction

A unit square having two physical corners on the containing circle is
an actual radial S square

    S(e)=[d,d+1]e+[-1/2,1/2]Je.                       (2)

For completeness, write the center in its own orthonormal frame. Two
adjacent corners have the same maximal radius only if the transverse
center coordinate is zero. The two outer corners then have coordinates
(d+1,+/-1/2). Opposite maximal corners would force both center
coordinates to vanish, giving radius 1/sqrt(2), contrary to (1).
Thus (2) describes the whole physical two-corner mask.

Suppose two distinct such units C,D touch. Choose the bisector of their
radial directions as the positive horizontal axis, and write the two
directions as angles -theta,+theta, where 0<theta<=pi/2. They are
reflections across that axis. The minimum vertical coordinate of the
upper unit is

    d*sin(theta)-(1/2)*cos(theta).

If this is positive, the two units are separated by a positive vertical
gap. If it is negative, the upper unit has an open interval of interior
points on the horizontal axis; its reflection has the same interval,
giving overlap. Contact therefore forces

    tan(theta)=1/(2d),
    r0=sqrt(d^2+1/4),
    C intersection D={(r0,0)}.                        (3)

The common point is the upper inner corner of C and lower inner corner
of D. The upward bisector normal strictly exposes it in both squares.
The two frames are different modulo quarter turns: 0<2theta<pi/2.
Consequently this point cannot be a four-square junction, since four
right-angle sectors would force one common frame. At most three actual
units meet there.

On the fixed physical pose impose the following convention at every
touching pair of actual radial S units of the form (2): choose its
original point normal in the open strict common-normal interval and
within Euclidean distance 1/1000 of the appropriately oriented
perpendicular bisector normal. The intersection is a nonempty open
interval because that bisector itself is strict.

This is a legitimate initial physical branch in
PHYSICAL_CONTACT_STRESS.md, Section 2.2. The choices are independent of
the matched opposite-pair parameters at four-square junctions, because
(3) is not such a junction. There are only finitely many actual pairs.
Restricting these free parameters to nonempty open subintervals is
compatible with all existing finite strict, nonradial, diagonal and
nonzero-polynomial avoidances: a nonzero analytic polynomial cannot
vanish on a nonempty open parameter set. In particular it is compatible
with the complete unique/unique force-cycle preselection of
ADJACENT_TWO_S_LEAF_C4_HIGH_DOMAIN_AND_SINGLE_CORNER_SELECTION.md,
Section 5, as well as the earlier finite prelists.

Make all these choices before taking multipliers. The original
uncrossing construction of PHYSICAL_BODY_GRAPH_UNCROSSING.md changes
only the two opposite forces at a four-square junction and adds its
already available adjacent side-endpoint atoms. It cannot change or
create the point-only pair (3). Subsequent thinning only deletes atoms,
and aggregation does not alter a surviving point normal. A minimum
positive-atom certificate can be chosen within the same nonempty
admissible class. Thus whenever C,D both have the stated physical mask
in the resulting positive component, their original CD normal obeys
this initial convention.

Use C's own radial coordinates. Then

    C=[d,d+1] times [-1/2,1/2],
    Q_CD=(d,1/2),
    n_CD=(-a,b),       a,b>0,
    a0=1/(2*r0),       b0=d/r0,
    |a-a0|<1/1000,     |b-b0|<1/1000.                 (4)

These are properties of the actual selected force. Section 2 proves a
local consequence using its unchanged equations.

## 2. Local consequence: B must contain the origin openly

Keep the actual C in (4), its true degree two, and its other actual
neighbor B. B is a true degree-three genuine S root, with its real
leaf M and its other actual neighbor A, itself a genuine S root.
The particular actual points epsilon*e_M in B and epsilon*e_L in A
are retained. No force equation at A or D is needed in this section.

Write the original positive BC and CD magnitudes as mu,nu. Circle
moments about the actual origin are zero, so C has the exact moment
equation for these two forces. Its full positive-total circle force is
an arbitrary nonnegative combination of its two actual corners

    z_-=(d+1,-1/2),       z_+=(d+1,1/2).             (5)

### 2.1. The actual BC point lies in a strict radial annulus

Let m be the actual C-to-B normal. Since B contains its actual
epsilon-near point, the genuine common support satisfies

    h_C(m)<=epsilon.

If m_x>=0, then

    h_C(m)=(d+1)*m_x+(1/2)*|m_y|>=1/2>epsilon,

which is impossible. Thus m_x<0. If m_y>0, its C point is Q_CD,
and both original pair moments at C are strictly positive:

    det(Q_CD,m)>0,       det(Q_CD,n_CD)=d*b+a/2>0.

They cannot sum to zero. Hence m_y<=0. For m_y=0 the actual point
is P=(d,y), -1/2<=y<=1/2, and the unchanged torque gives

    mu*y+nu*(d*b+a/2)=0,

so y<0. For m_y<0 the point is P=(d,-1/2). In every case

    d<|P|<=r0.                                          (6)

The whole original inner-side mean is included; it has not been
replaced by a corner before the equation establishes (6).

### 2.2. P cannot be a vertex of a tilted B

If B is tilted relative to its genuine leaf, use its actual shallow
own chart from Section 3 of
ADJACENT_TWO_S_LEAF_C4_HIGH_DOMAIN_AND_SINGLE_CORNER_SELECTION.md:

    B=[U-1,U] times [V-1,V],
    U^2+V^2=d^2,       U>=1-epsilon,       0<V<4/15.

That chart uses only A's genuine epsilon-near point, and retains
origin-interior B. The squared norms of its four actual vertices are

    d^2,
    d^2+1-2U < d^2,
    d^2+2-2(U+V) < d^2,
    d^2+1-2V > d^2+7/15 > d^2+1/4.

Here U+V>d>1. None lies in the annulus (6). Thus P is not a B
vertex.

### 2.3. P cannot be a vertex of an aligned B either

In the aligned case use B's actual genuine-leaf frame:

    B=[epsilon,d] times [h-1,h],       0<=h<=1,
    M is the real radial S leaf in the East direction.

The two left vertices have squared norm at most 1+epsilon^2<d^2.
If a right vertex belongs to (6), its nonzero vertical coordinate has
absolute value at most 1/2. Reflect if needed to put

    P=(d,h),       0<h<=1/2.

Write the original B-to-C normal as (c,s), c,s>=0. The case s=0
would force C to be the same radial S unit as M: the minimum support
of any radial S unit in a unit direction is at most d, with equality
only in its own radial direction. Here that minimum would equal d.
The physical units C and M are distinct, so s>0.

Let alpha>0 be B's genuine East leaf force. Its full true-three-force
equation makes the actual B-to-A force

    (-alpha-mu*c,-mu*s).

Both components are strictly negative. Hence its unchanged point is
the lower-left B vertex (epsilon,h-1). The full origin torque is

    alpha*(1-h)=mu*(s-c),

so s>c. Put w=1-h>=1/2 and k=1-h*c/s. Then w<=k<=1, and the
actual B-to-A unit normal is (-k,-w)/sqrt(k^2+w^2). A's genuine
epsilon-near point gives the necessary support inequality

    w^2<=epsilon*(k+sqrt(k^2+w^2))
        <=epsilon*(1+sqrt(2))<1/24.

This contradicts w^2>=1/4. The case c=0 and both height endpoints
are included. Therefore P cannot be a vertex of an aligned B.

Together Sections 2.2--2.3 prove that P belongs to the relative
interior of an actual B side. B owns the original BC normal.

### 2.4. The West-normal C case is impossible

Suppose m_y=0 in Section 2.1. Then the B-owned B-to-C direction is
East in C's radial frame and its support at B equals d.

For a tilted genuine S root, all four own support heights are
U,V,1-U,1-V, each strictly smaller than d. For an aligned root,
an owned direction is parallel or perpendicular to its genuine leaf.
The perpendicular support heights are at most 1<d, and the opposite
leaf support is -epsilon. The only remaining direction is its own
leaf direction, in which case the actual radial C equals M as above.
Every possibility is excluded.

Consequently the actual BC contact is

    P=(d,-1/2),
    n_BC=(c,s),       c,s>0,       c^2+s^2=1.

Define its actual B support and transverse coordinate by

    H=d*c-s/2,       D0=d*s+c/2>0,
    H^2+D0^2=r0^2.                                     (7)

### 2.5. The two genuine B-frame possibilities

If B is tilted, the force-free normal cover in
SHALLOW_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md applies to
its physical boundary neighbor C. Positive-vertical normals and the
East own normal are excluded there. The remaining owned directions
are West and South. Every point on the West B side has norm below d:
both of its actual endpoints were strictly below d in Section 2.2,
and the squared norm is convex along the side. Thus (6) excludes West.
The actual owned BC side is South, and

    H=1-V.                                               (8)

In particular, if H<49/60, then V>11/60 and

    U^2=d^2-V^2<1+121/3600-121/3600=1.

Since 0<U<1 and 0<V<1, the actual B contains O in its open interior.

For aligned B the actual BC normal n_BC is one of its own axes.
Its real leaf cannot point in that direction, because H<d by (7).
If the leaf pointed in its negative, H=-epsilon, whereas the
transverse coordinate of P would have squared magnitude

    D0^2=r0^2-epsilon^2=5/4+2*epsilon>1.

The actual unit transverse interval contains zero and has length one,
so it cannot contain that point. The leaf is therefore perpendicular
to n_BC. Put u=(s,-c). Since P.u=D0>0, its leaf direction must be
u, not -u. In the actual orthonormal frame (u,n_BC),

    B=[epsilon,d] times [H-1,H],
    0<=H<=1,       epsilon<D0<=d,
    P=(D0,H).

The original positive leaf and BC forces are alpha*u and
mu*n_BC. Their full balancing B-to-A force has both negative own
components, so its point is (epsilon,H-1). Original torque gives

    mu*(D0-epsilon)=alpha*(1-H).                        (9)

Thus w=1-H>0. Put x=D0-epsilon>0. A's real epsilon-near point
again bounds the actual B support, now as

    w^2<=epsilon*(x+sqrt(x^2+w^2)).

Divide by the positive x+sqrt(x^2+w^2), use
w^2=(sqrt(x^2+w^2)-x)*(sqrt(x^2+w^2)+x), and square the resulting
nonnegative inequality. This yields

    w^2<=2*epsilon*D0-epsilon^2
        <=2*epsilon*d-epsilon^2=d^2-1<121/3600.

Every aligned B consequently satisfies

    H>49/60.                                            (10)

This used B's full three-force equation and A's actual near point,
without any boundary assertion or force equation at A.

### 2.6. C's full two-corner force cone forces H<49/60

The exact C torque and force equations, in the original C frame, are

    nu*(d*b+a/2)=mu*D0,
    F_C=mu*(c,s)-nu*(-a,b).                            (11)

The full F_C is a nonnegative combination of the two actual corners
(5). Therefore its lower-cone inequality is

    2*(d+1)*(F_C)_y+(F_C)_x>=0.

Substitute (11) and multiply by the positive d*b+a/2. After exact
cancellation this is

    G:=b*c-(2*d+1)*a*s-a*c<=0.                         (12)

This weak inequality includes either individual circle weight equal
to zero. No unique-corner or concurrence-in-C premise is used.

For the ideal bisector coefficients in (4), the same expression is

    G0=(H-D0)/r0.

If H>=49/60, then by (1) and (7)

    r0^2<4621/3600,
    D0^2<2220/3600<(4/5)^2,
    H-D0>1/60,
    r0<7/6,
    G0>1/70.

The unchanged original normal satisfies the strict error bounds (4),
so

    |G-G0|<(2*c+(2*d+1)*s)/1000
           <151/30000<1/70.

It follows that G>0, contradicting (12). Therefore H<49/60.

This contradicts the entire aligned case (10). The remaining tilted
case has O in int B by (8). The local consequence is proved with
every original mean and both physical circle weights retained.

## 3. Exact both-mask caller

Assume now both C,D have two physical circle corners in the original
high LCD.SS component. Section 1 gives their actual radial pair and
the declared initial compatible CD normal. Section 2, with C's other
neighbor B and B's other genuine root A, gives O in int B.

Reflect the same actual pair and interchange C,D and A,B. The original
reverse CD normal satisfies the same distance bound from the reversed
bisector. The full D2 equation has its own two physical circle corners
and positive total load, and A is the true degree-three genuine root
whose other nonleaf neighbor B has its real epsilon-near point. The
same local proof gives O in int A. The two distinct actual squares
A and B then have overlapping open interiors, a contradiction.

Thus the whole both-two-physical-circle-corner mask is impossible in
the common compatible selected certificate. This is a complete
original-domain exit, including all individual zero circle weights,
all initial point-normal choices within the stated open convention,
all aligned or tilted genuine roots, and all contact-mean endpoints.

The exact remaining high mask frontier is unchanged outside this
subdomain: the unique/unique physical mask has the owner reduction in
the common source; the mixed one-corner / two-corner mask still needs
its own whole proof. This source does not claim the full
M6.B4L2.C4.ADJACENT.LCD.SS gate or any coarse cell.

No selected force is deleted or replaced, no existing normal is
reselected, and no actual neighbor is assigned a false degree-two
equation. The proof uses neither compilation nor numerical poses,
remote actions, or shared-metadata edits.
