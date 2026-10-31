# The entire D-only genuine-West roof is excluded by one actual B point

Date: October 31, 2026 UTC.

**Status: complete original-feature hand proof.** In a same-nine
packing, the physical-two West/strict feature with A-owned strict
roof, genuine West DV singleton, and D-only AD is impossible.
The proof uses the full original A3/D3/V2 equations and containment
of one actual B point. No force or torque equation at B,C,N is
used, and no B/C owner, load, physical circle mask or additional
degree is restricted. The entire original mean and all V circle
coefficient endpoints remain.

This replaces the whole 1667-node generated cover for this feature.
The generated proof tree, its terminal checks and its replay are
not inputs. The argument applies to the original D02.L135 and
D02.L1345 callers alike, since it never treats N as unloaded.
It does not by itself close all original owner/roof features.

## 1. The complete unchanged geometric and force chart

Keep all nine actual interior-disjoint unit squares and the
unchanged origin of their containing circle. The current complete
hand radius-two proof is
`NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`, Sections 1--3,
with its fixed values and derivative supplied analytically by
`NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`, Sections 2--6.
Its accepted dependency join is
`ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`, Section 3.
It assigns mass at least one to every actual open unit under a
nonnegative radial measure of total mass 8997/1000<9. Thus,
for these same nine units, R>2. No historical computational mass
boxes or evaluator is used. With the original radius upper bound,

    2<R<=sqrt(1105)/16<21/10,
    d=sqrt(R^2-1/4)-1, 14/15<d<61/60.          (1)

The strict upper-radius comparison follows, for example, from
110500<112896 after squaring positive quantities. The lower
bound on d follows from 15/4>(29/15)^2.

The actual full positive stars are

    A:{V,D,B}, D:{V,A,C}, V:{A,D},

with unloaded true3 A,D and loaded true2 V. The remaining original
stars are arbitrary and unchanged. The physical-two V and actual
applications are

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,1/2-j), 1/2<j<1,
    h=(c,-s), e=(s,c), c=cos(alpha), s=sin(alpha),
    nD=(C,S), tD=(-S,C), C=cos(beta), S=sin(beta),
    A=P-[0,1]*h+[-ell,1-ell]*e,
    D=Q-[0,1]*nD+[0,1]*tD,
    W=P-ell*e=Q+v*tD.

The complete hand chart reduction in Sections 2--3 of
`PHYSICAL_TWO_WEST_STRICT_D_OWNED_GENUINE_ROOF_COMPLETE_EXCLUSION_2026_10_30.md`
gives the exact necessary domain and identities

    0<alpha<pi/2, pi/4<beta<pi/2,
    pi/2<alpha+beta<3*pi/4,
    H=c*S+s*C, k=s*S-c*C, H>k>0,
    H^2+k^2=1,
    ell=j*S/H in (0,1), v=j*s/H in (0,1),
    y=1-ell, t=1-v, tau=j-1/2,
    K=P-h+y*e.                                (2)

Only that source's printed actual chart and full-star derivation
are imported here; none of its generated exclusion is imported.
The actual positive magnitudes mu,nu,gamma on AV,DV,AD satisfy

    mu*y=gamma*(H-k),
    gamma*t=nu*(S-C),
    nu*tau=mu*B0, B0=d*s+c/2.                 (3)

These are the unchanged full A3,D3,V2 moments, with both V
physical circle corners and the entire nonnegative coefficient
interval retained. Set, only as notation for their actual ratios,

    delta=alpha+beta-pi/2 in (0,pi/4),
    epsilon=pi/2-beta in (0,pi/4),
    alpha=delta+epsilon,
    H=cos(delta), k=sin(delta),
    S=cos(epsilon), C=sin(epsilon),
    p0=H-k>0, g=S-C>0, m=mu/gamma=p0/y.

The two exact scalar consequences used throughout the proof are

    tau*y*t=p0*g*B0,
    m*g*B0=tau*t.                             (4)

The original exterior force at A is

    F_B=-mu*h+gamma*nD
        =gamma*(-(m+k)*h+H*e).

It strictly exposes the actual A corner K. Its unchanged inward
unit direction into B is therefore

    b=(-M*h+e)/sqrt(1+M^2),
    M=(m+k)/H,
    M*y=1-(1-y)*tan(delta)>y.                 (5)

Thus M>1. Put eta=atan(1/M), so 0<eta<pi/4. In ordinary
coordinates b=(-cos(alpha+eta),sin(alpha+eta)).

The actual B contains K+[0,1]*b. This needs no B ownership
assumption: for any unit square, an inward unit support direction
at a support vertex has both nonnegative own components at most
one, and the full unit segment stays in the square. At a supported
side or any original mean on it, that direction is its inward own
axis and the same statement holds. Consequently the actual point
K+b is in the original disk, and its exact ordinary height

    Y=1/2+s+y*c+sin(alpha+eta)                 (6)

satisfies Y<=R<21/10. We will contradict this inequality over
the entire original domain of (2)--(5).

## 2. The full roof cubic gives alpha>atan(5/6)

Suppose alpha<=atan(5/6). Then epsilon<alpha and

    S/H>=S>cos(alpha)>=6/sqrt(61)>23/30.

The last squared comparison has reserve
36*900-529*61=131>0. Since 0<t<1, the left side of the
first equality in (4) is bounded strictly above by

    tau*y*t<(j-1/2)*(1-(23/30)*j)
            <=1369/11040.                    (7)

The last number is the maximum of that concave quadratic, or
(1-(23/30)/2)^2/(4*(23/30)).

On the other side, the exact product identity is

    p0*g=cos(delta-epsilon)-sin(alpha)
          >=cos(alpha)-sin(alpha)=c-s>0.

By d>14/15, the right side of (4) is therefore greater than

    Q(alpha)=(c-s)*((14/15)*s+c/2)
       =-13/60+(43/60)*cos(2*alpha)
                         +(13/60)*sin(2*alpha).

This function is strictly concave on
0<=alpha<=atan(5/6), since its second derivative is negative
and both relevant doubled-angle sine and cosine are nonnegative.
Its endpoint values are 1/2 and 23/183. Hence

    p0*g*B0>23/183>1369/11040,                 (8)

with exact final integer comparison
23*11040=253920>250527=1369*183.
Equations (7)--(8) contradict (4). Thus

    alpha>atan(5/6), s>5/sqrt(61)>16/25.       (9)

The last comparison has squared reserve
25*625-256*61=9>0.

## 3. Actual B containment gives s<4/5 and B0>19/20

First alpha cannot be at least 3*pi/8. On
3*pi/8<=alpha<pi/2, the minimum of sin(alpha+eta) over
0<=eta<=pi/4 is sin(alpha+pi/4). Moreover

    sin(alpha)+sin(alpha+pi/4)
        >=1+1/sqrt(2)>8/5.

The first sum decreases on this interval: its derivative is
2*cos(pi/8)*cos(alpha+pi/8)<=0, so its infimum is at
alpha=pi/2. Equation (6) would give Y>21/10, impossible.

Thus alpha<3*pi/8. On this interval
sin(alpha+pi/4)>=sin(alpha), and concavity of sine on
[alpha,alpha+pi/4] gives sin(alpha+eta)>=sin(alpha).
Because y*c>0, (6) now gives Y>1/2+2*s. Therefore

    s<4/5, c>3/5,
    atan(5/6)<alpha<asin(4/5).                 (10)

The function (14/15)*sin(alpha)+cos(alpha)/2 has derivative
greater than (14/15)*(3/5)-(4/5)/2=4/25 on this interval.
Consequently

    B0>23/(3*sqrt(61))>23/24>19/20,           (11)

using sqrt(61)<8. No B circle equation or endpoint force
condition has been used for these bounds.

## 4. At least one of delta and epsilon is below fifteen degrees

From S>1/sqrt(2)>7/10 and (9),

    (S+s)/H>S+s>67/50>4/3.

By (2), y+t=2-j*(S+s)/H<2-(4/3)*j. The arithmetic-geometric
mean inequality for the two positive original coordinates y,t
therefore gives

    tau*y*t<(j-1/2)*(1-(2/3)*j)^2<=16/243.     (12)

The final cubic has derivative
(1-(2/3)*j)*(5/3-2*j), so its maximum on [1/2,1]
is at j=5/6 and is 16/243. Dividing (12) by the strictly
positive B0 in (11), (4) gives

    p0*g<320/4617<1/10.                       (13)

If both delta and epsilon were at least pi/12, then
|delta-epsilon|<=alpha-pi/6. Hence

    p0*g=cos(delta-epsilon)-s
        >=cos(alpha-pi/6)-s
         =(sqrt(3)*c-s)/2>1/10,               (14)

where (10) and sqrt(3)>5/3 give the last strict bound.
This contradicts (13). Thus the entire remaining domain has

    epsilon<pi/12 or delta<pi/12.              (15)

Since alpha>atan(5/6)>pi/6, both small-angle alternatives cannot
hold simultaneously, though disjointness is not needed below.

## 5. The whole epsilon<pi/12 sector exceeds the circle in height

Put lambda=s/H, so t=1-lambda*j. In this sector

    lambda=tan(alpha)/(cos(epsilon)+tan(alpha)*sin(epsilon)).

For fixed epsilon the expression increases in tan(alpha).
At tan(alpha)=5/6 its denominator increases for
0<=epsilon<=pi/12. The exact rational comparisons

    cos(pi/12)<97/100, sin(pi/12)<13/50

therefore give

    lambda>(5/6)/(97/100+(5/6)*(13/50))
             =125/178>7/10.                  (16)

For the stated trigonometric comparisons, use
cos(pi/12)^2=(2+sqrt(3))/4<15/16<(97/100)^2,
with sqrt(3)<7/4, and
sin(pi/12)^2=(2-sqrt(3))/4<27/400<(13/50)^2,
with sqrt(3)>173/100.

By (16) and the maximum of a concave quadratic,

    tau*t<(j-1/2)*(1-(7/10)*j)<=169/1120.

Here g>cos(pi/12)-sin(pi/12)=1/sqrt(2)>7/10.
The second equality in (4), together with (11), implies

    m<(169/1120)*(200/133)=845/3724<1/4.

As k<H and H>1/sqrt(2), (5) gives

    M<1+sqrt(2)/4<11/8,
    eta>atan(8/11).                            (17)

The whole angle alpha+eta therefore lies between
atan(5/6)+atan(8/11) and asin(4/5)+pi/4. Both sine
endpoint values exceed 24/25:

    sin(atan(5/6)+atan(8/11))=103/sqrt(11285)>24/25,
    sin(asin(4/5)+pi/4)=7/(5*sqrt(2))>24/25.

The respective positive squared reserves are
10609*625-11285*576=130465 and 35^2-2*24^2=73.
Sine is concave on the complete containing interval inside (0,pi),
so sin(alpha+eta)>24/25 throughout it. Equations (6),(9) now give

    Y>1/2+16/25+24/25=21/10,

contradicting actual containment. This excludes the entire first
sector in (15).

## 6. Delta<pi/12 with g>=1/10 is also uniformly too high

Now suppose delta<pi/12 and g>=1/10. Since lambda=s/H>s>16/25,

    tau*t<(j-1/2)*(1-(16/25)*j)<=289/1600.

The global quadratic maximum is a valid upper bound even though
its critical point lies beyond j=1. Equations (4),(11) yield

    m<289/152<2.

Also p0>1/sqrt(2)>7/10, and therefore

    y=p0/m>7/20.

The elementary bounds in this small-delta interval give

    H>cos(pi/12)>24/25,
    k<sin(pi/12)<27/100,
    M<(2+27/100)/(24/25)=227/96<12/5,
    eta>atan(5/12).                            (18)

The new cosine lower bound follows from
cos(pi/12)^2>37/40>(24/25)^2, using sqrt(3)>17/10.
As in Section 5, sine is bounded below by its endpoint values
on the containing interval. Here the lower endpoint is

    sin(atan(5/6)+atan(5/12))=90/(13*sqrt(61))>4/5,

and the same upper endpoint 7/(5*sqrt(2)) is also greater
than 4/5. Thus sin(alpha+eta)>4/5. With (10) and the
strict y bound, the actual point obeys

    Y>1/2+16/25+(3/5)*(7/20)+4/5
       =43/20>21/10.

This excludes the whole second sector.

## 7. Delta<pi/12 with g<1/10: two monotone comparisons

Only

    0<delta<pi/12, 0<g=S-C<1/10                (19)

remains. All original variables continue to satisfy (2)--(11).
Since S+C=sqrt(2-g^2)>7/5 and sqrt(2)<71/50,

    7/10<S<19/25,
    H>24/25, k<27/100,
    r_delta=tan(delta)<1/3.                    (20)

Define the scalar comparison

    y0=1-S/H.

It has the strict bounds

    0<5/24<y0<1-S<3/10,
    y=1-j*S/H>y0,                             (21)

because the original genuine mean satisfies j<1. These comparisons
do not replace that mean by j=1 in a physical configuration.

### 7.1. For fixed original angles, the B-point height increases in y

Identity (5), with the angles fixed only for this scalar comparison,
gives

    eta(y)=atan(y/(1-r_delta+r_delta*y)),
    eta'(y)=(1-r_delta)
             /[y^2+(1-r_delta+r_delta*y)^2],
    0<eta'(y)<3/2, 0<eta(y)<pi/4

for every 0<y<1. By (10), throughout this comparison interval

    cos(alpha+eta(y))
       >cos(asin(4/5)+pi/4)
        =-1/(5*sqrt(2))>-1/5.

Consequently the exact height function from (6) has derivative

    dY/dy=c+cos(alpha+eta(y))*eta'(y)
               >3/5-(1/5)*(3/2)=3/10>0.       (22)

At y0<3/10, (20) further gives

    atan(y0)<eta(y0)<atan(9/20).

Moreover alpha+atan(9/20)<pi/2: by (10), tan(alpha)<4/3,
and (4/3)*(9/20)=3/5<1. Sine is thus increasing on the
whole interval from alpha+atan(y0) to alpha+eta(y0).
Combining this with (21)--(22) gives the strict comparison

    Y>G(delta),
    G(delta)=1/2+sin(alpha)+y0*cos(alpha)
                         +sin(alpha+atan(y0)).       (23)

This step explicitly checks the sine branch; replacing eta by a
smaller angle without that check would not be valid in general.

### 7.2. For fixed epsilon, the comparison G increases in delta

Vary only the scalar delta from 0 to its original value, keeping
epsilon fixed. Along this comparison alpha=epsilon+delta,
H=cos(delta), and y0=1-S/cos(delta). All bounds c>3/5,
s<4/5, 0<y0<3/10 in (10),(20),(21) remain valid: alpha
can only decrease, and H can only increase as delta decreases.

Put

    q0=cos(alpha+atan(y0))
       =(c-s*y0)/sqrt(1+y0^2)>3/10.

Indeed c-s*y0>9/25 and sqrt(1+y0^2)<21/20, so q0>12/35.
The exact derivative and its uniform rational bound are

    y0'=-S*sin(delta)/cos(delta)^2,
    |y0'|<(19/25)*(27/100)/(24/25)^2
             =513/2304<1/4.                  (24)

Differentiate (23), noting alpha'=1:

    G'=c-s*y0+q0
            +y0'*(c+q0/(1+y0^2)).

The bracket is positive and at most two. Hence (24) gives

    G'>3/5-(4/5)*(3/10)+3/10-1/2
        =4/25>0.                              (25)

It follows that G(delta)>G(0). This is a comparison of explicit
functions only; no original square, stress, or mean is moved.

### 7.3. The exact endpoint comparison exceeds 21/10

At delta=0, alpha=epsilon and y0=1-S. Define

    V0=C+S*(1-S)=C+S-S^2.

Then direct trigonometry in (23) gives

    G(0)=1/2+V0+V0/sqrt(1+(1-S)^2).

By (19)--(20),

    V0>7/5-(19/25)^2=514/625,
    sqrt(1+(1-S)^2)<21/20.

Therefore

    G(0)>1/2+(514/625)*(41/21)
          =1/2+21074/13125
           >1/2+8/5=21/10,                   (26)

whose last exact numerator reserve is 21074-21000=74.
Equations (23),(25),(26) contradict Y<=R<21/10. This excludes
the last whole sector, including arbitrarily small positive g and
all original mean values approaching j=1.

## 8. Complete feature conclusion and scope

Sections 2--4 applied to every original chart point before any
case split. The alternatives in (15), followed by the complete
g>=1/10 or g<1/10 split, exhaust that entire domain. Each
contradiction concerns the same actual contained point K+b.
The equality g=1/10 is retained in Section 6; the exact angle
and shared-mean endpoints used in the comparisons were never
silently discarded or substituted into an actual configuration.

The proof therefore excludes the whole stated D-only genuine-West
feature of the same-nine problem. It preserves both individual
zero-coefficient endpoints at V, every B/C circle mask and contact
owner, all actual external degrees and loads, and every unused
original force and torque. No N equation is used. In particular
both original D02.L135 and D02.L1345 satisfy this hand exclusion
at this feature, and larger original positive components do as
well when they belong to the same unchanged nine-square packing
and carry the stated complete A3/D3/V2 stars.

The local inequality is not asserted over the larger comparison
radius range below two without the same-nine analytic radius
input. It is the original nine-unit feature, rather than an isolated
six-unit diagram, that is fully excluded here. No original coarse
row flag is changed by this manuscript.

All displayed bounds are elementary hand inequalities, continuous
derivative comparisons, or two-endpoint concavity bounds. No pose
enumeration, generated parameter certificate, external checker,
normal reselection, shortened positive star, Lean/Lake build or
CI is used.
