# Every actual width-one channel has exterior capacity at most one above radius two

Date: October 26, 2026.
Status: complete hand theorem, accepted after full-source and original-domain
reviews in REVIEW_SIDE_CHANNEL_CAPACITY_AND_FIVE_C6_ROOT_2026_10_26.md and
REVIEW_GENERAL_SIDE_CHANNEL_CAPACITY_GLOBAL_2026_10_26.md. Its complete
five-load consequence closes exactly the existing FIVE.CAP and FIVE labels.

Put Q=1105/256 and r=5/4. Let the entire selected positive component be
an actual simple cycle with at least three positively circle-loaded bodies,
in 2<=R<=sqrt(Q). Let X-U-Y be one original channel, where X and Y have
positive total circle load and U is an actual unloaded degree-two
side-normal transmitter of width one. Keep every original force, physical
circle mask, individual corner weight, actual application mean and slider.

**Theorem.** The whole actual exterior X-U-Y pocket contains at most one
additional physical unit square, of arbitrary orientation.

If either endpoint is physically radial, this is already
RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md. The proof below treats the
complete remaining physical unique/unique mask. It includes both actual
owned-side means and every oblique singleton vertex. It uses no numerical
pose, coefficient packet, sampled sign test, or altered application.

## 1. Actual geometry and the two endpoint applications

The established proper-channel and physical-cap theorems give

    P_X=(-a,h), P_Y=(b,h), a+b=1, h>0,
    X subset {x<=-a}, Y subset {x>=b}.

Their actual centers have nonnegative heights and opposite strict horizontal
signs. The center bound M=91/60 and each projection halfwidth >=1/2 give

    -1/60<a<61/60,       -1/60<b<61/60.

GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md proves h>3/10 and gives each whole
pocket extra one connected open r-circle arc longer than pi/4. Every point
of that open arc lies strictly above y=h.

If h>=r/sqrt(2), the entire upper-circle interval above h has length at
most pi/2 (or is empty). Two extras cannot fit their disjoint arcs there.
It remains to treat

    3/10<h<r/sqrt(2).                                      (1)

All uses of (1) below are therefore under an actual necessary alternative,
not a restriction of the original pocket domain.

### 1.1. Both applications strictly straddle the vertical axis

We claim a,b>0. Suppose a<=0, so b>=1. Consider the right endpoint,
reflected to the left, whose application is (-b,h).

If it is axis aligned, write its actual outer upper circle corner as
(-b-1,B). The nonnegative center height gives B>=1/2, and the actual
side application has h<=B. Hence

    R^2=(b+1)^2+B^2 >=(b+1)^2+h^2.

If it is oblique, write its frame as

    u=(cos t,sin t), v=(-sin t,cos t), 0<t<pi/2,

so the four actual vertices are p, p-u, p+v, p-u+v, with p=(-b,h).
Its center is in the closed upper left quadrant. Thus its own v-coordinate
is positive, and its unique farthest circle corner is either p-u+v or p+v.

For the opposite corner p-u+v, the proper unique concurrence lies on the
positive ray through that same circle corner and inside the square. Its
height is h, so the circle corner's height is at least h. Therefore
cos t>=sin t. Writing A=cos t+sin t>=1 and B=cos t-sin t>=0 gives

    R^2=(b+A)^2+(h+B)^2 >=(b+1)^2+h^2.

For the adjacent corner p+v, put

    k=-b cos t+h sin t,      j=b sin t+h cos t.

The farthest-corner comparison gives k>=1/2. In particular k>=0, so
h sin t>=b cos t and j>=b/sin t>=b. Consequently

    R^2=k^2+(j+1)^2=b^2+h^2+1+2j >=(b+1)^2+h^2.

These actual feature cases exhaust this endpoint. Hence in every case
h^2<=Q-4=81/256. Since -1/60<a<=0, the other unchanged application obeys

    |P_X| <=sqrt((1/60)^2+(9/16)^2)<23/40.

But every point of X is within sqrt(2) of its actual circle corner, so
R<=|P_X|+sqrt(2)<23/40+57/40=2, a contradiction. The last fixed radical
comparison is sqrt(2)<57/40. Reflection excludes b<=0 as well. Thus

    a,b>0,                a+b=1.                           (2)

In particular the whole left endpoint is strictly in x<0 and the whole
right endpoint strictly in x>0.

## 2. Two fixed radical inequalities

For |k|<r put A(k)=sqrt(r^2-k^2), and define

    f(k,j)=((j-k)A(k)+k^2+jk)/r.                            (3)

We will use two elementary inequalities on complete continuous domains:

    -7/8<=k<=1/2,
    j>=sqrt(4-(k-1)^2)-1       => f(k,j)>71/100>1/sqrt(2);  (4)

    1/2<=k<=1,
    j>=sqrt(4-k^2)-1           => f(k,j)>41/50>1/sqrt(2).   (5)

The radical lower bounds in (4) and (5) are well defined. No decimal or
finite sign packet is a premise.

### 2.1. Proof of (4) on -1/2<=k<=1/2

Here A(k)+k>0, so f increases strictly with j. Set

    J(k)=73/100+(29/50)k-k^2/2.

The following exact polynomial identity proves the needed lower bound:

    4-(k-1)^2-(J(k)+1)^2
      =71/10000-(17/2500)k+(246/625)k^2+(29/50)k^3-k^4/4.

On [-1/2,0], its linear term is nonnegative, its cubic term is at least
-(29/100)k^2, and its quartic term is at least -k^2/16. It is therefore
at least 71/10000+(411/10000)k^2>0. On [0,1/2], it is at least
37/10000+((246/625)-1/16)k^2>0. Also J+1>0 on this interval.
Thus sqrt(4-(k-1)^2)-1>J.

Moreover

    A(k)>=5/4-(3/7)k^2,

because the squared reserve equals k^2(1/14-9k^2/49)>=5k^2/196>=0,
and the right-hand side is positive. The polynomial J-k is positive
on [-1/2,1/2]; its minimum is at an endpoint and is at least 79/200.
Consequently the numerator in (3) is strictly greater than

    71/80 + P(k),
    P(k)=1/40+(41/200)k+(899/1400)k^2-(8/25)k^3+(3/14)k^4.

For k>=0, P>=1/40+(41/200)k+(27/56)k^2>0.
For k<=0,

    P>=1/40+(41/200)k+(3/5)k^2
      =(3/5)(k+41/240)^2+719/96000>0.

Dividing by r=5/4 proves f>71/100 throughout this entire interval.

### 2.2. Proof of (4) on -7/8<=k<=-1/2

Put t=-k and s=sqrt(1-16t^2/25). Then

    f=t s+(4/5)t^2+j(s-(4/5)t).                            (6)

The coefficient of j is positive throughout 1/2<=t<=7/8: indeed
s^2-(4t/5)^2>=1/50>0 at the worst endpoint. Thus it suffices to use
j0=sqrt(4-(1+t)^2)-1.

On 1/2<=t<=3/5, we have j0>=1/5, s>7/8, and
s-(4/5)t>79/200. Hence

    f>51/80+79/1000=1433/2000>71/100.

On 3/5<=t<=3/4, we have j0>-1/25, s>=4/5, and
0<s-(4/5)t<=13/25. Therefore

    f>96/125-13/625=467/625>71/100.

On 3/4<=t<=7/8, we have j0>-1/3, s>7/10, and
0<s-(4/5)t<=2/5. Therefore

    f>39/40-2/15=101/120>71/100.

Each radical comparison follows by squaring positive rationals:
s(3/5)>7/8, sqrt(15)/4>24/25, and sqrt(31)/8>2/3,
respectively. These three intervals and Section 2.1 exhaust (4).
Finally 71/100>1/sqrt(2) because 2*71^2>100^2.

### 2.3. Proof of (5)

Again f increases with j. Put s=A(k)/r.
On 1/2<=k<=3/4,

    j>17/20, s>=4/5, j-k>0.

Thus

    f>(4/5)[(17/20)(1+k)+k^2-k]
      =17/25-(3/25)k+(4/5)k^2 >=41/50.

The last polynomial increases for k>=1/2. The bound for j uses
sqrt(55)/4>37/20.

On 3/4<=k<=1, we have j>=sqrt(3)-1>7/10.
If j-k>=0, discard the first term (j-k)s in (3) to obtain
f>(4/5)(3/4)(3/4+7/10)=87/100>41/50.
If j-k<0, use s<=1, obtaining

    f>7/10-(11/25)k+(4/5)k^2 >=41/50.

This polynomial increases for k>=3/4. This proves (5).

## 3. The endpoint quantity for every oblique unique-corner body

Consider X, with application p=(-a,h). Its actual frame and vertices are
as in Section 1.1:

    u=(cos t,sin t), v=(-sin t,cos t),
    p, p-u, p+v, p-u+v,             0<t<pi/2.

Write

    k=p.u=-a cos t+h sin t,
    j=p.v= a sin t+h cos t >0.                             (7)

The actual farthest corner is p-u+v if k<=1/2, and p+v if k>=1/2.
The equality is harmless for the estimates; a physically unique mask
actually avoids the tie. These are the same physical circle corners,
not chosen substitute vertices.

### 3.1. Opposite circle corner

Here R^2=(k-1)^2+(j+1)^2. The proper unique concurrence gives
cos t>=sin t, hence 0<t<=pi/4. In particular, with
C=cos t+sin t>=1 and D=cos t-sin t>=0,

    R^2=a^2+h^2+2+2a C+2h D.                              (8)

The application p lies strictly inside the r-circle. If a<=1/2, use
(1) to get a^2+h^2<1/4+r^2/2=33/32<r^2. If a>=1/2, (8) gives
a^2+h^2<=Q-3=337/256<r^2.

Also j+1>r. Otherwise the circle equation and k<=1/2 give
k<=1-sqrt(4-r^2)<-1/2. Then h=k sin t+j cos t<=j<=r-1=1/4,
contrary to (1).

Since j>0 and R^2<=Q, we have

    k>1-sqrt(Q-1)>-7/8,             k<=1/2.                (9)

The final radical bound is sqrt(Q-1)<15/8. Thus the circle equation
and R>=2 put (k,j) within the complete domain (4).

### 3.2. Adjacent circle corner

Here R^2=k^2+(j+1)^2 and k>=1/2. From (7) and a>0,

    1/2<=k<h<r/sqrt(2)<1.

Moreover k>=0 gives j>=a, exactly as in Section 1.1.
The application again lies inside the r-circle. Otherwise
a^2+h^2>=r^2 and h^2<r^2/2 would imply a>r/sqrt(2), and then

    R^2=a^2+h^2+1+2j
       >=a^2+h^2+1+2a
       >r^2+1+sqrt(2)r>Q,

a contradiction. The last fixed comparison is
41/16+5sqrt(2)/4>1105/256, or 320sqrt(2)>449,
which follows by squaring.

Finally j+1=sqrt(R^2-k^2)>sqrt(3)>r. The original circle equation
and R>=2 put (k,j) in the complete domain (5).

### 3.3. The actual gap-facing inner-circle endpoint

In both cases p is strictly inside the r-circle and j+1>r. Therefore
the segment p+[0,1]v crosses that circle at exactly

    P=k u+A(k)v,

with 0<A(k)-j<1. This is on the actual square edge adjoining p.
Its height is above h, and its angle alpha is in (pi/2,pi), because
the whole square lies in x<=-a<0. The upper v-face j+1 is outside
the inner circle; thus this is precisely the gap-facing endpoint of
X's upper inner-circle interval. Its angle satisfies

    alpha=t+arccos(k/r)=pi/2+phi,
    phi=t-arcsin(k/r),                  0<phi<pi/2.

Rotating (7) by this angle gives the exact identity

    a(sin phi+cos phi)+h(cos phi-sin phi)=f(k,j).            (10)

For example, if p's components along the radial direction of P and its
clockwise tangent are U0 and V0, then
U0=(k^2+j A(k))/r, V0=k(A(k)-j)/r; the left side of (10) is U0-V0.
This also verifies the signs in (10) directly.

By (4) and (5), every original oblique unique endpoint satisfies

    F_X:=a(sin phi+cos phi)+h(cos phi-sin phi)>1/sqrt(2).   (11)

## 4. Every original owned-side mean has the same strict endpoint bound

Suppose X owns the horizontal support, so its actual square is axis aligned.
Write

    X=[-a-1,-a] times [B-1,B],
    R^2=(a+1)^2+B^2, B>=1/2, B-1<=h<=B.

Physical uniqueness makes B>1/2, but the weak endpoint is harmless here.
Its gap-facing inner-circle endpoint P is on either the right face x=-a
or the upper face y=B, with a face join allowed. Write its angle as
pi/2+phi, 0<phi<pi/2. We prove (11) with the original h, not a selected
new mean. The endpoint comparisons below are inequalities in that same h.

### 4.1. Right face, phi<=pi/4

Here a=r sin phi. If a>=3/5, then sin phi>=12/25 and cos phi>=1/sqrt(2)>7/10.
Since cos phi-sin phi>=0 and h>0,

    F_X>=a(sin phi+cos phi)> (3/5)(59/50)=177/250>1/sqrt(2).

The last squared comparison is 2*177^2>250^2.

If a<=3/5, use h>=B-1 and cos phi-sin phi>=0. The virtual endpoint
(-a,B-1) gives a lower bound on F_X; it is not substituted in the
physical channel. In the frame t=0 this lower bound is f(k,j), with
k=-a in [-3/5,0] and j=B-1. The original circle equation gives
j=sqrt(R^2-(k-1)^2)-1>=sqrt(4-(k-1)^2)-1. The actual right-face
endpoint P has own coordinates (k,A(k)), so the identity (10) holds
for this lower bound. Inequality (4) proves (11).

### 4.2. Upper face, phi<=pi/4

Now B=r cos phi<=r, and R>=2 yields

    a=sqrt(R^2-B^2)-1>=sqrt(4-r^2)-1>1/2.

Using h>3/10 and cos phi-sin phi>=0 gives

    F_X>(4/5)cos phi+(1/5)sin phi >=1/sqrt(2).

The trigonometric expression is concave on [0,pi/4]; its endpoint
values are 4/5 and 1/sqrt(2), so its minimum is the latter.
The first inequality remains strict at phi=pi/4 because a>1/2.

### 4.3. Upper face, phi>=pi/4

Here B=r cos phi<=r/sqrt(2)<1, while B>=1/2. Since
cos phi-sin phi<=0 and h<=B, the virtual top endpoint (-a,B) gives
a lower bound on F_X. In the frame t=pi/2 it has k=B in [1/2,1]
and j=a, and the original circle equation is R^2=k^2+(j+1)^2.
The actual upper-face point P has own coordinates (k,A(k)).
Thus (10) identifies this lower bound with f(k,j), and (5) proves (11).

### 4.4. Right face, phi>=pi/4

Here a=r sin phi>=r/sqrt(2). By (1),

    F_X>=a(sin phi+cos phi)+(r/sqrt(2))(cos phi-sin phi)
       >=sqrt(2)r cos phi=sqrt(2)*sqrt(r^2-a^2)>1/sqrt(2).

For the last inequality use a<1 from (2), so r^2-a^2>r^2-1=9/16>1/4.

The four cases cover both actual active faces, all endpoints of the
original side-mean interval, and the face join. Thus (11) holds for
every owned-side endpoint without changing its application.

## 5. The actual free endpoint interval is shorter than pi/2

Reflect the right endpoint. Its same complete feature analysis gives
an angle psi in (0,pi/2) and

    F_Y:=b(sin psi+cos psi)+h(cos psi-sin psi)>1/sqrt(2).

The left gap-facing endpoint has angle pi/2+phi. The right endpoint
has angle pi/2-psi. Their intervening actual free interval therefore
has length Delta=phi+psi.

Suppose Delta>=pi/2. Put delta=phi-pi/4, epsilon=psi-pi/4. Then

    delta,epsilon in [-pi/4,pi/4], delta+epsilon>=0,
    sin delta+sin epsilon
      =2sin((delta+epsilon)/2)cos((delta-epsilon)/2)>=0.

Using a,b>0 and a+b=1,

    F_X+F_Y
      =sqrt(2)[a cos delta+b cos epsilon
                -h(sin delta+sin epsilon)]
      <=sqrt(2)(a+b)=sqrt(2).

This contradicts F_X,F_Y>1/sqrt(2). Therefore

    Delta<pi/2.                                           (12)

## 6. Full pocket routing and capacity

For completeness, (12) is used with the actual occupied crosscut
z_X-P_X-P_Y-z_Y and its outward outer-circle arc, as in
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md. The boundary endpoint units meet
|p|=r in connected closed arcs containing their radial-center points
in their relative interiors, by ANNULAR_CENTER_ARC_AT_23_25.md.
Their upper restrictions are intervals; here X lies in x<0 and Y in
x>0. The actual gap-facing endpoints of those intervals are exactly
the P points used in Sections 3 and 4.

The left radial-center point is strictly left of x=-a and the right
one strictly right of x=b. Monotonicity of cosine on the upper
semicircle shows that every intersection of the middle crosscut segment
with that circle lies between the two center directions. The other
two crosscut segments lie in their corresponding closed endpoint units.

An inner-circle point in the open interior of a pocket extra cannot lie
outside these two center directions. Otherwise follow the upper circle
toward angle zero or pi, avoiding both closed endpoint intervals and
the middle segment, then escape to infinity along the horizontal ray
below h. This contradicts the point's bounded-pocket label. Avoiding
the two closed endpoint arcs therefore places every such point in the
single intervening free interval of length (12).

This is the unchanged physical crosscut argument; no sector containment
of a square or its center is assumed. The established compact-interior
routing convention retains every weak junction, extra zero-weight contact
and original mean endpoint. Additional contacts may subdivide the pocket
but cannot enlarge its free inner-circle interval or move an extra
through its occupied boundary.

GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md supplies each whole extra one
connected open r-circle arc longer than pi/4. Two interior-disjoint
extras have disjoint arcs with combined length greater than pi/2,
contradicting (12). The high-height alternative was already excluded
in Section 1. Thus every original unique/unique side-channel pocket
has capacity at most one.

Together with the existing physical-radial endpoint theorem, this proves
the stated complete width-one theorem, including every actual mask and
all genuine side means. No other exterior pocket or central region is
assigned a new capacity by this local theorem.

## 7. Accepted complete five-load C6 consequence

In the original five-load bare cycle U-S1-S2-S3-S4-S5-U, the accepted
SIX_CYCLE_FIVE_LOAD_CENTRAL_CAPACITY_ONE.md gives at most one extra in the
whole central region and routes every other original extra into the sole
S5-U-S1 exterior cap. The same-nine-square lower bound supplies R>2.

The diagonal-width family has cap capacity one by
DIAGONAL_CHANNEL_EXTERIOR_CAPACITY_ONE.md. The width-one family has
cap capacity one by the present theorem. The full original force,
mask and width cover is exhaustive, so at most two of the three actual
extras can be placed. The entire five-load bare-C6 orbit is impossible.

The full-source root and separate independent reviews named above accept
this entire original family and its unchanged physical parent scope.
Exactly M6.B6.C6.FIVE.CAP and M6.B6.C6.FIVE close. Both four-load parents,
C6.ALL and the coarse cell retain their separate obligations.
No Lean compilation or CI has been run.
