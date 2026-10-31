# A radial C excludes the owned tilted-root leaf in the one-owner adjacent-S C4

Date: October 27, 2026.

**Status: complete original-domain hand proof, submitted for full root and
separate independent review.** This treats the entire C-two-corner /
D-unique / exactly-one-AB-owner domain with the owned far-j genuine leaf
at the tilted root B. It joins the strict-B-leaf proof to cover this
whole radial placement, but does not claim the other radial placement.

Keep the original nine units and full component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,

with genuine S leaves, clear roots A,B, positive boundary loads C,D and

    d=1+epsilon=sqrt(R^2-1/4)-1,
    0<epsilon<1/60,       R^2<=Q_*=1105/256.

C has two physical circle corners and D one. A is the sole AB side
owner. All individual C weights, actual means and original normal
owners are retained.

## 1. Exact actual roots and the two necessary scalar identities

The complete all-mask leaf reduction and the already proved horizontal
leaf exit leave A's strict outer lower application:

    A=[-X,h] times [-v,1-v],       X=1-h,
    d*e_L=(-X,-v),       X^2+v^2=d^2,
    P_AB=(h,-k),       |h|<=epsilon,       0<k<v<13/50.

At that actual point, B has the inward frame

    f=(c,s),       j=(s,-c),
    c,s>0,       c^2+s^2=1.

In the actual (j,f) coordinates its owned genuine-leaf chart is

    B=[epsilon,d] times [-w,1-w],
    d*e_M=(d,0),
    h=epsilon*s-w*c,       k=epsilon*c+w*s.              (1)

The actual C mask forces B-owned North BC, at its unchanged mean

    Q_BC=(t,1-w),       t=epsilon+ell,       0<ell<1.

The aligned-genuine-root part of
RADIAL_BOUNDARY_UNIT_ADJACENT_GENUINE_ROOT_OWNER_REDUCTION.md,
Section 3.2, gives the entire range

    0<w<11/60,       t>1/2.

The original B3 equations at the real North mean give

    c*ell=w*s,
    t^2+(1-w)^2=d^2+1/4.                               (2)

For example, its f component is nu=mu*c, its genuine leaf magnitude
is mu*s, and its moment about P_AB gives nu*ell=mu*s*w.

The original relative-interior condition k<v supplies another strict
necessary inequality. Since h^2+k^2=epsilon^2+w^2 and
v^2=d^2-(1-h)^2,

    G:=2epsilon(1+s)-w^2-2w*c>0.                       (3)

No scalar parameter in (1)--(3) is changed independently of the pose.

## 2. The exact whole scalar domain gives w<2/15

For this paragraph regard the expressions below as scalar functions on
0<w<11/60, 0<epsilon<=1/60:

    t=sqrt(1/4+2epsilon+epsilon^2+2w-w^2),
    z=t-epsilon,
    r=w/z,
    c=r/sqrt(1+r^2),       s=1/sqrt(1+r^2).

They are precisely the actual quantities in (1)--(2). Throughout this
rectangle z>0 and t<1+epsilon, since
(1+epsilon)^2-t^2=3/4-2w+w^2>0.

At fixed w, z increases with epsilon, so r and c decrease and s
increases. Consequently G in (3) increases strictly with epsilon.
At fixed epsilon, r increases with w: its derivative has the sign of

    z*t-w(1-w)
      =1/4+2epsilon+epsilon^2+w-epsilon*t>0.

Thus c increases and s decreases, so G decreases strictly with w.
These are only scalar comparisons of the necessary formula, not
physical reselections.

If w>=2/15, it follows that
G(w,epsilon)<=G(2/15,1/60). At this endpoint put u=sqrt(213).
A direct substitution gives

    G(2/15,1/60)
      =7/450+(3u-65)/[30sqrt(1982-6u)]<0.               (4)

For an exact verification of the strict sign, both
65-3u and the denominator are positive. Squaring the required
(65-3u)/sqrt(1982-6u)>7/15 gives the positive difference

    1284832-87456sqrt(213)
      >1284832-87456*(73/5)=39872/5>0.

This contradicts (3), proving

    w<2/15.                                             (5)

## 3. The same actual equations give c/s<3/16

Retain z=ell=t-epsilon in (0,1), r=c/s=w/z, and put
S=sqrt(1+r^2). Since t>1/2 and w<11/60,

    0<r<11/29<1/2.

Equation (2) becomes

    S^2*z^2-2r*z-1/4=2epsilon(1-z)>0.                  (6)

Let z0(r) be its left-hand quadratic's positive zero. It is below one
and increases with r on 0<r<1/2: implicit differentiation has positive
numerator 2z0(1-r*z0) and positive denominator 2S^2*z0-2r.
Thus if r>=3/16,

    S>=sqrt(265)/16>50871/50000,
    z>z0(3/16)=8(6+sqrt(301))/265>8811/12500.             (7)

The two rational bounds are exact. Their squared/radical reserves are

    265/256-(50871/50000)^2=1999/156250000,
    301-(173493/10000)^2=178951/100000000,
    8(6+173493/10000)/265-8811/12500=3/662500.

But (3), with w=r*z, is exactly

    epsilon>(S-1)(S*z^2+2z)/2.

Its right side increases with S>1 and z>0. Substituting the rational
bounds in (7) gives

    epsilon>1/60
       +35962769849483/2343750000000000000,

a contradiction. Therefore

    c/s<3/16.                                           (8)

In particular (1),(5) imply the original AB height bound

    k<epsilon*(3/16)+2/15=131/960<3/20.                 (9)

## 4. The actual radial C direction and contact cover

In B's (j,f) frame C's actual radial direction is (s0,c0), with

    s0,c0>0,       s0^2+c0^2=1,
    1-w=d*c0-s0/2,       t=d*s0+c0/2.

This is the actual inner minimum-North corner. If s0<=0 then
t=d*s0+c0/2<=1/2, contrary to t>1/2; also c0<=0 would give
1-w=d*c0-s0/2<=1/2, contrary to 1-w>13/15. Thus both radial
coordinates are strictly positive, with the axis endpoints excluded.

By (5), 1-w>13/15. This forces

    s0<241/1000.

Indeed at s0>=241/1000 one has
c0<=sqrt(941919)/1000<9709/10000, so

    d*c0-s0/2
      <(61/60)(9709/10000)-241/2000
       =13/15-17/200000.

The actual world radial direction e=s0*j+c0*f satisfies

    e_x=(s0+r*sqrt(1-s0^2))/sqrt(1+r^2).

This expression increases in both variables throughout their present
ranges. Using (8) and sqrt(941919)<971,

    0<e_x<6769/[1000sqrt(265)]<5/12.                    (10)

The last squared comparison has numerator reserve 27012016.
Its world vertical component is positive, and therefore

    e_y=sqrt(1-e_x^2)>9/10.

Let J e=(-e_y,e_x). The original CD features are exactly the strict
inner corner

    Q_C=d*e+(1/2)J e,

or the full C-owned transverse side Q_C+z0*e, 0<=z0<=1.
The original D-to-C normal g has g_x>0; in the owned case
g=-J e=(e_y,-e_x). The actual corner obeys

    -1/2<Q_C,x<-19/720<-epsilon,
    1<Q_C,y<17/15.                                      (11)

The horizontal estimate follows from (10). For the lower vertical
bound, e_y>1-e_x^2 and d*e_x<1/2 give
Q_C,y>d+e_x(1/2-d*e_x)>d>1. The upper bound follows from
|Q_C|^2=d^2+1/4<(17/15)^2. Every point on the retained transverse
C side also has height above one.

## 5. Both strict upper AD vertices are impossible

The full A3 vertical component is positive at AD. Thus its complete
support cover is North, strict Northwest, or strict Northeast.

At strict Northwest its actual application is (-X,1-v), and the
original force/torque equations give the normal proportional to

    (-r0,1),       r0=X*(v-k)/[v(1-v+k)].

The complete inward-unit-segment calculation of
ADJACENT_S_C4_MIXED_MASK_PARALLEL_ROOTS_EXCLUSION.md, Section 4,
applies exactly with root width X, depth v, and original mean k.
For v<=43/240 it already gives the circle contradiction. Above that
threshold its only extra premise is k<3/20, which is (9).
The two full bounds are
1361/(60sqrt(641))>107/120 for v<=1/4 and
529/(60sqrt(73))>1 for v>1/4. Thus this whole original feature is
excluded without any D-owner assumption.

At strict Northeast the actual point is (h,1-v). Its projection on
J e is at most epsilon+e_x<13/30<1/2, so D cannot be beyond
C's transverse support. CD must use Q_C. The unchanged D2 proper
rays now give q_D,x>=h at AD but q_D,x<=Q_C,x<-epsilon<=h at CD.
This excludes the whole Northeast feature as well.

## 6. The complete North mean and the D-owned-axis case

The full A3 equations at its actual North contact give

    P_AD=(-X0,H),
    H=1-v>11/15,
    X0=X*k/v,       0<X0<X<61/60.                       (12)

No endpoint is substituted for this genuine derived mean.

If D owns the vertical axis, its actual vertical interval is [H,H+1].
Its unique-corner positive radial concurrence has horizontal coordinate
-X0, so its actual circle corner is upper-left. The original g_x>0
then leaves only East: a negative g_y uses its lower-right corner of
height H<1, whereas every CD point has height above one; a positive
g_y uses its upper-right corner of height H+1>26/15, whereas the
only compatible C feature would be Q_C of height below 17/15.

Thus CD is D-owned East at Q_C. C's actual concurrence is on
Q_BC+rho*f and on the horizontal line through Q_C. Hence

    rho=e_x/s=s0+(c/s)c0<1/4+3/16=7/16.

In C's true radial coordinates it is
(d+rho*c0,-1/2+rho*s0). The complete two-corner circle cone,
including either original zero weight, requires

    rho*[c0+2(d+1)s0]>=1.

But the original bounds give

    rho*[c0+2(d+1)s0]<(7/16)*(241/120)=1687/1920<1.

This is a contradiction. No two-corner concurrence was assumed to lie
inside C.

## 7. A tilted D: its opposite circle corner and the owned C side

Otherwise P_AD is D's strict minimum-y vertex. Reflect the world
vertical coordinate, giving the actual chart

    P=(-X0,-H),
    D=P+[0,1]f_D+[0,1]j_D,
    f_D=(p,-q),       j_D=(-q,-p),
    p,q>0,       p^2+q^2=1.

The genuine unique-corner D2 concurrence lies on the vertical line
below P, inside D, and on its positive actual circle-corner ray.
The complete local proof in Sections 8--10 of
ADJACENT_S_C4_MIXED_MASK_PARALLEL_ROOTS_EXCLUSION.md applies at
this exact physical scope.

In particular P dot j_D>0, so only the adjacent P+j_D or opposite
P+f_D+j_D can be the circle corner. The opposite case gives
R>=sqrt(2)+H>R by the original proper-ray comparison. Thus the
actual circle corner is

    Z_D=P+j_D=(-X0-q,-H-p).

Its other own coordinate is below -1/2. The full original D2 force
then gives g dot f_D>0, so the actual CD mean is on D's far-f_D
side, at distance at least one from P.

If C owns its transverse side, its original normal and actual supports
force D's right vertex. The same retained-mean calculation gives a
positive C-radial increment because

    H-(e_x/e_y)X0
      >11/15-(25/54)(61/60)=851/3240>0.

The tangent increment is positive, and their squared sum is two.
Consequently the actual circle corner has squared norm greater than
R^2+11/30, exactly as in that complete local proof. This excludes
the entire C-owned-side feature, including all of its original means.

## 8. The strict C corner forces an impossible actual D circle radius

It remains that CD uses Q_C. Put

    E=Q_C,x+X0,       F=Q_C,y-H.

By (11)--(12),

    E>-1/2,       0<F<2/5.

If |Q_C-P_AD|<1, the far-side conclusion of Section 7 already gives
a contradiction. Suppose therefore that its squared distance is at
least one.

This first forces v<3/20. For if v>=3/20, (9),(11),(12) imply

    X0<(61/60)(131/960)/(3/20),
    E<7763/8640<9/10,

so the squared distance is below 81/100+4/25=97/100<1.

We now have H>17/20 and

    0<F<2/15+3/20=17/60.

Distance at least one gives
E^2>3311/3600>(23/24)^2. Since E>-1/2, the positive sign is
forced. By (11),

    X0=E-Q_C,x>23/24+19/720=709/720.                    (13)

But the actual adjacent D circle corner found in Section 7 has

    |Z_D|^2=X0^2+H^2+1+2(X0*q+H*p).

Both X0,H exceed 17/20 and p+q>1. Therefore (13) gives

    |Z_D|^2
      >(709/720)^2+(17/20)^2+1+17/10
       =Q_*+491/6480>R^2.

This contradiction excludes the last strict C feature. No original
D orientation, C weight or CD mean was dropped.

## 9. Exact whole-interface join

The owned B leaf is treated throughout its full initial side interval.
The original C mask fixes BC North; the true B3 moment and the two
real root identities produce Sections 1--4. Section 5 excludes both
strict upper AD features, while Sections 6--8 cover its entire original
North mean and every actual D frame and circle feature.

Thus the entire C-two-corner / D-unique / sole-AB-owner-A domain with
B's owned far-j leaf is impossible. Together with the separate strict
B leaf and horizontal A leaf sources, this closes the full C-radial
one-owner placement.

The D-radial one-owner placement is not claimed by this join.
All original forces, true degrees, physical masks and three arbitrary
completion squares remain. No numerical pose, post-extraction change,
compilation, CI, remote action or shared-metadata edit is used.

