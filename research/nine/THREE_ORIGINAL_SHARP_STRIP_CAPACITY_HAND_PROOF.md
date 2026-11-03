# A sharper shared three-original strip inequality

November 3, 2026. Complete hand proof of a local physical implication.
This improves the previously accepted three-original strip theorem without
adding an orientation split to its callers. It does not by itself close an
original cell or a whole mask. No Lean, Lake or CI.

## 1. Statement and rational row used by the existing pipeline

Let three distinct physical unit squares L, M, U have pairwise disjoint
open interiors. Their frames are independent. Suppose their unchanged
centers satisfy

    y_L <= y_M <= y_U,
    max(x_L,x_M,x_U)-min(x_L,x_M,x_U) <= W,
    0 <= W <= 7/10.

Put V=y_U-y_L and Delta=x_U-x_L. Then

    V+(13/50)Delta^2 >= min(2,2sqrt(2)-2W).             (1)

In particular the entirely rational consequence is

    V+(13/50)Delta^2 >= min(2,280/99-2W),               (2)

because 140^2=19600<19602=2*99^2. If the same complete original
parent proves Delta in [l,u], the row

    V+(13/50)((l+u)Delta-lu) >= min(2,280/99-2W)         (3)

follows from (Delta-l)(Delta-u)<=0. All width,
projection, order and endpoint secant guards are unchanged from
[the preceding strip theorem](THREE_ORIGINAL_NARROW_STRIP_CAPACITY_HAND_PROOF.md).
Every signed original and physical contact boundary is retained. The
quadratic coefficient is improved from 5/14 to 13/50 as well as the
right side. The new secant row is therefore at least as strong: its
secant value is nonnegative wherever Delta lies in [l,u].

For comparison, the old right side is min(2,208/75-(29/15)W).
The new rational right side equals it for W<=2/5 and is strictly
larger for 2/5<W<=7/10. Where both affine branches apply their
difference is

    280/99-208/75-W/15 = 136/2475-W/15
      >= 41/4950 > 0.

On 2/5<W<=41/99 the new right side is 2 while the old one is less
than 2. Thus (3) is a valid uniform replacement, not a numerical cut.

## 2. The sharper universal square-plus-disk slice

Let S be any physical unit square centered at the origin, B the closed
disk of radius 1/2, and K=S+B. The local geometric assertion is

    length(K intersect {x=d}) >= min(2,2sqrt(2)-2d)
                      for 0<=d<=1/sqrt(2).            (4)

Let P be the vertical Steiner symmetrization of S: replace every
vertical interval slice by the centered interval of the same length.
The elementary interval-sum argument in Section 3 of the preceding
theorem gives

    Steiner_y(S+B) contains P+B.                      (5)

In detail, for x=x_1+x_2, the Minkowski sum of the S-slice at x_1
and the B-slice at x_2 lies in the K-slice at x. Its length is the
sum of the two lengths. Centering produces exactly the corresponding
sum of centered slices; the centered intervals for all decompositions
of x are nested. This proves (5).

A square's quarter-turn symmetry and reflection permit side components
alpha>=beta>=0, alpha^2+beta^2=1. Write

    t=beta/alpha in [0,1], r=sqrt(1+t^2),
    alpha=1/r, beta=t/r,
    k=(alpha-beta)/2, h=(alpha+beta)/2, A=r/2.

The upper half-length of P's vertical slice is A for |x|<=k,
and (h-|x|)/(2alpha beta) for k<=|x|<=h. The latter branch is
omitted at beta=0. Thus P has the upper corner (k,A), the right
vertex (h,0), and the segment joining them. Also P contains B:
the original square contains B, and centering a slice cannot shrink
its length below the centered disk slice.

Put a=sqrt(2)-1. We prove the exact critical inclusion

    (a,1) belongs to P+B.                             (6)

Both P and B are symmetric in both coordinate axes. Once (6) is
known, convexity gives (d,1) in P+B for 0<=d<=a. The inclusion
B+B in P+B supplies (1/sqrt(2),1/sqrt(2)). The line segment from
(a,1) to that disk point has equation y=sqrt(2)-x. Reflecting in y
therefore proves (4) by (5).

## 3. Small and intermediate original slopes

For 0<=t<=3/20, monotonicity of k gives

    k >= 17/(2sqrt(409)) > 21/50 > a.

The nontrivial square comparison here is
425^2=180625>180369=21^2*409. Since A>=1/2, the point (a,A)
of P is within distance 1/2 of (a,1). This proves (6).

For 3/20<=t<=1/6, use the corner (k,A). We have

    2/5<k<17/40,  41/100<a<21/50,
    A>=sqrt(409)/40>101/200.

The last comparison follows from 25*409=10225>10201=101^2.
The k lower bound follows from 625>592 as in the preceding proof.
Consequently |a-k|<1/50 and 0<1-A<99/200, giving

    (a-k)^2+(1-A)^2 < 9817/40000 < 1/4.               (7)

For 1/6<=t<=9/10 set

    F_a(t)=(a-(1-t)/(2r))^2+(1-r/2)^2.

We will prove F_a convex. Its value at 1/6 is bounded by (7).
At 9/10, k=1/(2sqrt(181)), A=sqrt(181)/20, and the rational
bounds

    a<829/2000, k>37/1000, A>269/400

give 0<a-k<151/400 and 0<1-A<131/400. Their elementary square
checks are

    2829^2=8003241>8000000=2*2000^2,
    181*37^2=247789<250000=500^2,
    269^2=72361<72400=181*20^2.

Thus

    F_a(9/10) < (151^2+131^2)/400^2
               =39962/160000 < 1/4.                 (8)

Convexity and (7)-(8) prove (6) throughout [1/6,9/10]. Here is
its exact verification. For a general fixed x, differentiation gives

    F_x''(t)=x(1-3t-2t^2)/r^5
                +t(3-t^2)/r^6+1/2-1/r^3.

The preceding strip proof established, for x=2/5,

    10r^6 F_(2/5)''(t) >= p(t),
    p(t)=-1+18t-6t^2-16t^3+6t^4+5t^6.

For completeness its exact Bernstein coefficients on [1/6,1],
with t=(1+5z)/6, are

| i | b_i |
|---:|---:|
| 0 | 82301/46656 |
| 1 | 29681/7776 |
| 2 | 253/48 |
| 3 | 139/24 |
| 4 | 191/36 |
| 5 | 13/3 |
| 6 | 6 |

That is p((1+5z)/6)=sum b_i binom(6,i)z^i(1-z)^(6-i).
All basis weights are nonnegative and sum to one, and every b_i is
at least 82301/46656>6/5. Now 0<a-2/5<1/50, r<3/2, and
1-3t-2t^2>=-4 on [1/6,1]. Therefore

    10r^6(F_a''-F_(2/5)'')
       =10(a-2/5)r(1-3t-2t^2) > -6/5.

It follows that F_a''>0 on that entire interval, proving the required
convexity without sampled angles.

## 4. Large original slopes: use the side, not just its corner

For 9/10<=t<=1, the nearest point to (a,1) on the sloping side of
P lies in that side's interior. To check both guards explicitly,
write its initial point as z=(k,A) and its terminal point as w=(h,0).
The vector w-z is (beta,-A). The bounds

    beta>=9/sqrt(181)>2/3,
    a>33/80, k<=1/(2sqrt(181))<3/80

give

    ((a,1)-z) dot (w-z)
       =beta(a-k)-A(1-A)>1/4-A(1-A)>=0.              (9)

Their positive-square comparisons are respectively 729>724,
12800>12769, and 1629>1600. At the other endpoint,

    ((a,1)-w) dot (z-w)=beta(h-a)+A>0,               (10)

because h>=1/2>a. Equations (9)-(10) put the perpendicular foot
strictly between z and w.

The side line is x+2alpha beta y=h. Put s=alpha+beta, so
1<=s<=sqrt(2), h=s/2, and 2alpha beta=s^2-1. The squared distance
from (a,1) to this line is

    (s^2-s/2+sqrt(2)-2)^2 / (1+(s^2-1)^2).           (11)

The following exact factorization proves that (11) is at most 1/4:

    1+(s^2-1)^2-4(s^2-s/2+sqrt(2)-2)^2
       =(sqrt(2)-s) q(s),

    q(s)=3s^3+(3sqrt(2)-4)s^2+(4sqrt(2)-7)s
                    +16-11sqrt(2)
        =3s(s^2-1)+(3sqrt(2)-4)s^2+(4sqrt(2)-4)s
                    +16-11sqrt(2)>0.

Every summand in the last line is nonnegative, and the last three
are positive: sqrt(2)>4/3 and sqrt(2)<16/11 follow by squaring.
Also sqrt(2)-s>=0. The actual foot belongs to P by (9)-(10), so
distance at most 1/2 proves (6), including t=1 and its equality.

This completes the universal inclusion and the slice proof (4).
The scalar slice bound itself is sharp: an aligned square realizes
length 2 for d<=a; a square at 45 degrees realizes
2sqrt(2)-2d for a<=d<=1/sqrt(2). No optimality claim for three
physical squares follows from these square-plus-endpoint-disk examples.

## 5. Return to the original three squares

The endpoint squares contain their concentric open radius-1/2 disks.
Their disjointness from M implies that their centers lie outside the
interior of M+B. Let D=|c_U-c_L| and let d be the distance of c_M
from the endpoint line. All the guards are direct consequences of
the original hypotheses, as in Section 7 of the preceding theorem:

    y_M-y_L, y_U-y_M >= sqrt(1-W^2)>7/10,
    V>7/5,
    (c_M-c_L) dot (c_U-c_L) >=2-3W^2>=53/100>0,
    (c_M-c_U) dot (c_L-c_U) >=2-3W^2>=53/100>0,
    0<=d<=W<=7/10<1/sqrt(2).

The dot inequalities put the middle center's projection between the
endpoints. Rotation to the endpoint frame and (4) therefore give

    D>=min(2,2sqrt(2)-2d)>=min(2,2sqrt(2)-2W).

The improved coefficient requires retaining the sharper geometric bound

    d <= WV/D.                                       (12)

Indeed let lambda=(y_M-y_L)/V in [0,1]. At height y_M the endpoint
line has x-coordinate (1-lambda)x_L+lambda x_U. Its horizontal
separation from M is at most W. The perpendicular component of this
horizontal segment is exactly V/D times its length, proving (12).

There are two exhaustive cases.

**Case D>=2.** Since |Delta|<=W<=7/10,

    V^2=D^2-Delta^2 >=351/100 > (24/13)^2,
    351*169-576*100=1719>0.

Thus D+V>50/13 and

    D-V=Delta^2/(D+V) <= (13/50)Delta^2.

It follows that V+(13/50)Delta^2>=D>=2, proving (1).

**Case D<2.** The slice inequality forces
D>=2sqrt(2)-2d: otherwise it would violate the minimum of this
quantity and 2. Set V_0=2sqrt(2)-2W. By (12),

    D^2+2WV >=2sqrt(2)D.

Using D^2=V^2+Delta^2 and D-V=Delta^2/(D+V) gives

    V(V_0-V) <= Delta^2(1-2sqrt(2)/(D+V)).             (13)

If V>=V_0 the desired inequality is immediate. If V<V_0, use
D+V<4, sqrt(2)>7/5, and V>7/5 in (13) to obtain

    V_0-V <= (3/14)Delta^2 <= (13/50)Delta^2.

The scalar comparisons are 2>49/25 and 150<182. This proves
V+(13/50)Delta^2>=V_0, and hence (1), in the second case too.
All equality boundaries are assigned to one of these two cases.

This proves (1), and hence (2)-(3). Only original physical squares,
their proven coordinate intervals and a common rigid rotation were
used. No shared original orientation or unproved separating axis was
assumed. Applications must separately prove every whole-parent guard
and their complete terminal contradiction before updating any cell,
mask, positional-root or roadmap ledger.
