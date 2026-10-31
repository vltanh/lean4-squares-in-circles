# A West-leaf root and an owned tilted leaf: the other root contact must be North

Date: October 27, 2026.

**Status: complete hand exclusion of both strict upper-vertex BC
features, submitted for full root and separate independent review.**
The original North-side feature remains. This source does not claim
the whole West-leaf layout or high LCD.SS family closed.

Keep all nine original units and the exact selected component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,

in the strict-high adjacent-S domain

    d=1+epsilon,       0<epsilon<1/60,
    R^2=(2+epsilon)^2+1/4<=1105/256.

The actual AB normal is East, owned by A and not B. Its original
moment is positive, and its point is P=(-epsilon,-k). Assume A's
genuine leaf is its owned West side, and B's genuine leaf is its
owned far-j side from the complete reduction
ADJACENT_S_LEAF_C4_ONE_OWNER_ALL_MASK_LEAF_REDUCTION.md.

The latter source is independently accepted in
REVIEW_ADJACENT_S_ONE_OWNER_ALL_MASK_REDUCTION_ROOTED_BLOCKS_2026_10_27.md.
We keep every original normal, side mean, circle mask and zero weight.

## 1. The exact original chart and the boundary-center order

Write the actual B frame as

    f=(c,s),       j=(s,-c),
    c,s>0,       c^2+s^2=1.

In its positively oriented (j,f) coordinates,

    B=[epsilon,d] times [-w,T],       T=1-w,
    P=(epsilon,-w),       d*e_M=(d,0),
    n_BA=(-s,-c).                                           (1)

The two unchanged coordinate identities are

    -epsilon=epsilon*s-w*c,
    k=epsilon*c+w*s.

The first says wc=epsilon(1+s). Substituting c^2=1-s^2
in the second gives k=w. The accepted physical height bound at
A's other contact therefore gives

    epsilon<w=k<1/5,       T>4/5,                           (2)
    c=2*epsilon*w/(w^2+epsilon^2),
    s=(w^2-epsilon^2)/(w^2+epsilon^2).                       (3)

The strict epsilon<w follows from s>0; no parallel-frame endpoint
has been added to this tilted domain.

The actual AD normal is East. Its real mean is
Q_AD=(-epsilon,y), and the full A3 moment gives

    nu_D*y=mu*w>0,       y>4/5,       y+w<=1.                (4)

Here mu is the original AB magnitude. D is wholly in x>=-epsilon.
Its actual center z_D consequently satisfies

    (z_D)_x>=1/2-epsilon>29/60,
    (z_D)_y>=y-1/2>3/10,
    |z_D|<91/60.                                           (5)

For a minimum-x vertex, the second inequality follows from the two
actual inward axes (a,b),(b,-a), whose center vertical offset is
(b-a)/2>=-1/2. For a side mean it follows from the full unit
vertical interval. Thus (5) includes every orientation and mean.

Let theta_D be its ordinary center angle in (0,pi/2). Then

    cos(theta_D)>29/91>1/sqrt(10),
    theta_D<arctan(3).                                    (6)

The squared reserve for the middle comparison is
10*29^2-91^2=129.

The original common positive cycle moment puts the touching physical
boundary units C,D in counterclockwise minor-center order. This is
Section 1 of
ADJACENT_S_LEAF_C4_UPPER_AND_NEAR_SIDE_OWNER_LEAF_EXCLUSION.md:
it keeps the actual circle spokes and their physical exterior order
L,M,C,D. In particular, if z_C also has positive y coordinate, then

    theta_C<theta_D.                                     (7)

Two center angles in (0,pi) with the opposite inequality could not
have the stated counterclockwise minor order. No choice of a
circle weight is used in (5)--(7).

## 2. The complete BC support cover and the unchanged equations

The full f component at B is positive:

    nu*m_f=mu*c>0.

Thus its only actual BC features are North, strict Northwest or
strict Northeast in the (j,f) frame. The original equations give:

* North at Q=(epsilon+ell,T), 0<=ell<=1:

      c*ell=w*s.                                         (8)

* Strict Northeast at Q=(d,T), m=(a,b), a,b>0:

      nu*T*a=mu*(c-w*s),       nu*b=mu*c.                (9)

* Strict Northwest at Q=(epsilon,T), m=(-a,b), a,b>0:

      nu*T*a=mu*w*s,       nu*b=mu*c.                   (10)

These are the full B3 force and moment equations about P. In
particular no original North mean is set to an endpoint.

At either strict upper vertex the original normal is owned by C
in the compatible necessary certificate. Here is the exact
preselection justification, which does not require the leaf at A
to have a nonparallel force pair.

P is the fixed actual B vertex on AB; its normal is the fixed
actual A own axis. The hypothetical free BC contact has its fixed
actual B vertex Q, distinct from P. The genuine B leaf direction
is e_j, not parallel to the AB normal (-s,-c). Moreover

    det(d*e_j,Q)=d*T>0                                  (11)

in both strict BC features. Apply the complete true-three-force
singleton preselection in
ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md, Section 4.
The necessary determinant for that free normal has a nonzero
coefficient because of (11). Its finitely many exceptional
directions are included in the original finite pose prelist,
simultaneously with the other accepted selections. The distinct
points P,Q prevent a matched-junction parameter identification.
Uncrossing retains point normals and adds only actual shared-side
atoms. Hence a surviving strict B-vertex BC contact must have
C ownership. This argument does not assign a mean or use a C/D
circle mask.

If C is two-corner, the accepted radial-boundary theorem already
forces B-owned North, so both strict features are absent. If D is
two-corner, the accepted all-mask reduction excludes the whole
West-leaf type at A. It therefore suffices below to keep the
original unique/unique mask, with C true degree two and D an
actual physical boundary neighbor.

## 3. The entire strict Northeast BC feature is impossible

Equation (9), with T>0, gives w<c/s. Using (3),

    w^2<2*epsilon+epsilon^2=d^2-1<121/3600,
    T>49/60.                                            (12)

The actual point Q=(d,T) minimizes m on the contained unit C.
Its actual inward unit normal segment gives Q+m in C.
This segment exists for an owned side and also for a vertex:
at a vertex the nonnegative components of the unit inward normal
in the two own inward axes are each at most one.

Since d>T and a+b>=1,

    |Q+m|^2=d^2+T^2+1+2*d*a+2*T*b
             >=d^2+(T+1)^2
             >d^2+(109/60)^2.

But

    R^2=d^2+2*d+5/4
         <d^2+197/60,

and

    (109/60)^2-197/60=61/3600>0.

This actual point would be outside the containing circle.
The proof did not need C ownership, a circle-force weight or a
replacement of its second application.

## 4. Exact notation for the Northwest feature

Suppose (10) holds and put

    r=a/b>0,       E=epsilon,       T=1-w.

The unchanged equations and (3) give the exact relations

    r=w*s/(c*T)=(w^2-E^2)/(2*E*T),
    w^2=2*r*E*(1-w)+E^2,
    c/s=w/(r*T).                                        (13)

In particular all the estimates below concern the actual original
force ratio r. It is not an auxiliary normal chosen for the proof.

C owns the incoming normal m=(-a,b). Let t=(b,a), so m,t are
orthogonal, and retain the entire original side parameter z:

    Q=(E,T),
    C=Q+[0,1]m+[-z,1-z]t,       0<=z<=1.                (14)

Put

    L=|Q|=sqrt(E^2+T^2),
    u=Q.m=(T-r*E)/sqrt(1+r^2),
    v=Q.t=(E+r*T)/sqrt(1+r^2)>0.                        (15)

When 0<r<=1, (2) gives u>0. The full true C2 equations, with
the actual boundary neighbor D, give the proper radial
concurrence

    q=Q+rho*m=lambda*Z_C,       rho>=0,       lambda>0.

All hypotheses are those of Lemma 2.1 of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md. C has its original
unique physical circle corner; no zero weight in a different
mask is being used as uniqueness.

Two exact consequences will be used:

    R<=L+L/u;                                           (16)

and, writing W=sqrt(R^2-(u+1)^2)>0,

    Z_C=(u+1)m+W*t,
    z_C=(u+1/2)m+(W-1/2)t.                              (17)

For (16), the unique corner has normal component u+1,
lambda>=u/(u+1), and its transverse component is v/lambda.
This is the accepted owned boundary-tip radial cap.

For (17), v>0 and lambda>0 make the actual corner's t component
positive. It must be the maximum t corner: the other corner on
the same maximum-m side would otherwise have strictly larger
positive t coordinate and norm. Thus its coordinate is W, and
the actual center is one half-unit back in each own direction.
Equation (17) retains the original side parameter in (14);
it is an equality forced by the actual unique circle corner.

We will exclude 0<r<=1 by (16) or by the center order (7).
The remaining r>=1 has a short physical center bound.

## 5. Small r: the genuine radial cap

Suppose 0<r<=7/20. Write zeta=E/T. Since E<w<1/5 and T>4/5,

    L<T+E^2/(2*T)<T+w/8,
    S=sqrt(1+r^2)<53/50,
    L/u=S*sqrt(1+zeta^2)/(1-r*zeta).

The inequalities sqrt(1+x^2)<=1+x^2/2 and

    r*zeta<7*w/16<7/80,
    zeta^2/2<25*w^2/32<5*w/32

give

    L/u
      <=S+S*(r*zeta+zeta^2/2)/(1-r*zeta)
       <53/50+(1007/1460)*w.

Indeed (53/50)(80/73)(19/32)=1007/1460. Therefore (16)
would give

    R<1+53/50-(541/2920)*w
       <103/50<sqrt(17)/2,

a contradiction. The last squared reserve is
17/4-(103/50)^2=4/625. This closes the entire small-r interval.

## 6. The center-angle test used for the other intervals

Assume 0<r<=1 and c/s<r. In world coordinates the actual normal
m and tangent t have the form

    m=(-sin(delta),cos(delta)),
    t=(cos(delta),sin(delta)),
    tan(delta)=(r-c/s)/(1+r*c/s),
    0<delta<pi/4.                                      (18)

Also c/s<1 gives s>1/sqrt(2)>7/10. The point Q in world
coordinates has height s-w>1/2. From the full mean (14), its
center has height at least Q_y-1/2, and hence

    (z_C)_y>0.                                         (19)

Let q0>0 be a bound with

    W-1/2<q0*(u+1/2).                                  (20)

Because sin(delta)-3*cos(delta)<0, (17) gives

    (z_C)_y-3*(z_C)_x
      >(u+1/2)*[(1-3*q0)*cos(delta)
                         +(3+q0)*sin(delta)].

Consequently

    tan(delta)>(3*q0-1)/(3+q0)                         (21)

implies theta_C>arctan(3), using (19). This contradicts (6)--(7).
This calculation also covers W<=1/2; it did not assume the
center's coefficient along t is positive.

A convenient exact sufficient condition for (20) is

    (u0+1)^2+[1/2+q0*(u0+1/2)]^2>1105/256,
    u>u0>0.                                            (22)

Both terms are increasing in u, so containment and (17) then
give (20). We check (22) with explicit rational reserves below.

## 7. The interval 7/20<=r<=1/2

First suppose w>=3/40. Here T>4/5, E<1/60 give zeta<1/48, so

    (L/u)^2
       <(5/4)*(1+1/48^2)/(1-1/96)^2
        =461/361<(17/15)^2.

The last cross-multiplied reserve is
17^2*361-461*15^2=604. Also L<T+1/5000. Formula (16) gives

    R<1-3/40+1/5000+17/15
       =15439/7500<sqrt(17)/2,

whose squared reserve is 699779/56250000. Thus this whole
height subrange is impossible.

For the remaining w<3/40, (13) gives

    c/s<3/(37*r)<=60/259,
    tan(delta)>613/5600>3/41.                          (23)

The first bound makes c/s<r, and the lower bound for tan(delta)
uses r>=7/20. The final exact reserve in (23) is
8333/229600.

Furthermore

    u>(37/40-1/120)/(sqrt(5)/2)
       >(11/12)/(9/8)=22/27>4/5.

Apply the center test with u0=4/5 and q0=5/12.
Its angle threshold is exactly 3/41, and the reserve in (22) is

    (9/5)^2+(25/24)^2-1105/256=499/57600>0.

Equations (23) and (19)--(22) contradict the original C,D
center order. This closes the entire interval.

## 8. The interval 1/2<=r<=1

First obtain a uniform physical-angle bound from the exact (13).
Put w0=2*r/(7+2*r). The function

    F(x)=x^2-2*r*E*(1-x)-E^2

is strictly increasing for x>=0 and vanishes at x=w.
For 1/2<=r<=1 and E<1/60, its value at w0 is strictly larger
than its value with E=1/60. At that endpoint the numerator is

    3600*(7+2*r)^2*F(w0)
       =12716*r^2-5908*r-49.

This polynomial is increasing for r>=1/2 and equals 176 at
r=1/2. Hence w<w0, and (13) gives

    c/s<2/7.                                           (24)

All remaining bounds can be checked in the following three rational
intervals. In each row r1 is the upper endpoint and w_bar, u0, q0
are the displayed rational constants.

| r interval | w_bar | u0 | lower bound for tan(delta) | q0 |
| --- | --- | --- | --- | --- |
| [1/2,16/25] | 69/500 | 43/60 | 3/16 | 5/9 |
| [16/25,4/5] | 4/25 | 16/25 | 62/207 | 7/10 |
| [4/5,1] | 17/100 | 4/7 | 18/43 | 5/6 |

Here every stated lower bound for tan(delta) is strict by (24).
It is obtained by substituting the interval's lower r endpoint
and 2/7 in (18).

For transparency, the complete exact arithmetic establishing the
remaining bounds is:

| Row | F(w_bar) at r=r1,E=1/60 | (1-w_bar-r1/60)^2-u0^2*(1+r1^2) | reserve in (22) |
| --- | --- | --- | --- |
| 1 | 53/140625 | 22/28125 | 62239/4665600 |
| 2 | 263/90000 | 1636/140625 | 231991/4000000 |
| 3 | 43/45000 | 2329/275625 | 1167/12544 |

F(w_bar) decreases as E and r increase, since w_bar<1.
These positive values imply w<w_bar throughout each row.
Equation (15) then gives

    u>(1-w_bar-r1/60)/sqrt(1+r1^2)>u0,

using the positive middle-column reserves. The last column proves
(22), hence (20).

For the first row, the threshold in (21) is exactly 3/16.
For the other rows the respective thresholds are 11/37 and 9/23;
their strict angular reserves are

    62/207-11/37=17/7659>0,
    18/43-9/23=27/989>0.

Thus every row satisfies the center-angle test and contradicts
(7). This covers the full interval, including all shared
endpoints.

## 9. The remaining interval r>=1

This last interval needs neither concurrence nor a unique corner.
From (13) and w<1/5,

    c/s=w/(r*T)<1/4,
    c<1/sqrt(17),       s>4/sqrt(17).

In world coordinates (14) gives the following upper bound for
the actual center's x coordinate:

    (z_C)_x
       <=-E+c+[(a+b)*c-(a-b)*s]/2
       <=-E+c*(1+1/sqrt(2))
        <5/12.                                         (25)

For the second inequality, write a=r/sqrt(1+r^2),
b=1/sqrt(1+r^2). The bracket is

    [(c-s)*r+(c+s)]/sqrt(1+r^2),

whose derivative is negative for r>=1 because c<s. Its maximum
is sqrt(2)*c at r=1. The final strict rational bound in (25)
follows from sqrt(2)<17/12 and

    (1+1/sqrt(2))^2/17
       <35/204<25/144.

The actual center height is again at least s-w-1/2>0.
A physical boundary unit has center norm greater than 27/20, so

    cos(theta_C)<(5/12)/(27/20)=25/81<29/91
                   <cos(theta_D).

The middle strict comparison is 25*91=2275<2349=29*81.
Both centers have positive height, so theta_C>theta_D.
This contradicts (7) and closes the last interval.

Sections 5,7,8,9 exhaust every r>0. Thus the entire strict
Northwest feature is impossible, at every original C side mean.

## 10. The exact remaining whole feature

Only the actual B-owned North BC contact remains in this
West-A / owned-B-leaf type. Its entire actual mean is retained:

    Q_BC=(epsilon+ell,1-w),
    ell=(w^2-epsilon^2)/(2*epsilon),       0<ell<=1,
    epsilon<w<11/60,
    T>49/60.

The formula for ell follows from (3) and the original (8);
the height bound follows from ell<=1. The original D still
has the full mean (-epsilon,y) with y>4/5 and y+w<=1.
C may be tilted at its North support, and D may be tilted
at its East support. Neither is assigned a degree or alignment
not present in the original system.

The same conclusion holds in a C-two-corner mask directly by
the accepted radial-boundary root theorem; a D-two-corner
mask was already impossible for a West A leaf. The source
therefore gives this exact remaining contact feature in every
one-owner physical mask, without claiming that the feature
itself has been excluded.

No original force or mean is changed, no circle-mask endpoint
is discarded, and no completion unit is removed. No grid,
false triangle, numerical pose, compilation, CI, remote action
or shared-metadata edit is used.
