# Full side columns of an actual cone four-chain: a complete hand closure

Complete hand proof, independently reviewed, 5 November 2026. This theorem retains all nine original
physical squares. It uses the fully hand-proved five-square cap and the
hand lemmas explicitly identified below. There is no coefficient table,
numerical exclusion, or certificate input.

Put

    Q=1105/256, r=sqrt(Q), rho=91/60,
    l=29/60, u=13/12, zeta=2211/4000,
    J=23/150, A_0=18911/59520.

For every original square, let h be its coordinate projection halfwidth
and g=1/(4h) the halfwidth of its contained aligned square. Its side-axis
absolute components are a>=b>=0, with a^2+b^2=1, h=(a+b)/2,
k=(a-b)/2. In particular h+g>=1 and g>=1/(2sqrt(2))>1/3.

## 1. The exact theorem and its existing hand inputs

**Theorem.** Nine original interior-disjoint unit squares in a centered
disk of squared radius q<Q cannot have all of the following properties:

1. Four of them form an actual horizontal projection chain
   M0<_x M1<_x M2<_x M3.
2. Every consecutive center comparison in this same chain is horizontal
   cone: |y_(i+1)-y_i|<=x_(i+1)-x_i.
3. Their five outsiders have column counts (L,C,R)=(2,1,2), using the
   columns x<=-l, |x|<l, x>=l.

The cone condition is part of the theorem. The conclusion does not
claim to close every actual four-chain or every nine-square packing.

The following previously proved hand lemmas are used in their stated
original-square domains:

- The actual-four outsider strip, endpoint budget and inner bands, in
  [UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md).
- The actual-four side markers and their order under closed-disjoint
  normalization, in [UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md).
- Inner clearances greater than 97/100 in a main's horizontal half-plane,
  and greater than 59/60 for a central outsider in that half-plane, in
  [UNRESTRICTED_ACTUAL_FOUR_CHAIN_INNER_CLEARANCE_HAND_PROOF.md](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_INNER_CLEARANCE_HAND_PROOF.md).
- The middle-main bound |y_M|<7/20, in
  [UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md).
- The oriented asymmetric side-pair cap, Section 2 of
  [ORIENTED_SIDE_PAIR_CAP_AND_LOW_OUTSIDER_BAND_HAND_PROOF.md](sources/ORIENTED_SIDE_PAIR_CAP_AND_LOW_OUTSIDER_BAND_HAND_PROOF.md).
- The near-main clearance in Section 2 and the extreme-main theorem
  |y_M|>3/5 in Sections 3--4 of
  [FULL_SIDE_EXTREME_MAIN_THREE_FIFTHS_HAND_PROOF.md](sources/FULL_SIDE_EXTREME_MAIN_THREE_FIFTHS_HAND_PROOF.md).
  The latter theorem's side-pair height input is supplied by Section 2
  below, with the stronger 7/16 bound. This is an acyclic dependency:
  the side-pair proof below uses the asymmetric source's Section 2 and
  its own positive-normal proof; it uses neither the extreme-main
  theorem nor a caller that depends on that theorem.
- The central adjacent-proxy whole-square barrier, in
  [ADJACENT_PROXY_BARRIER_HAND_PROOF.md](sources/ADJACENT_PROXY_BARRIER_HAND_PROOF.md).
- The completed widened five-square cap, in [FIVE_SQUARE_CAP.md](FIVE_SQUARE_CAP.md).

All uses below are spelled out. The three extra geometric inputs that
the full-side caller needs are proved in Sections 2--4.

### 1.1. Normalize the strict counterexample

Expand all centers by one common factor greater than one, retaining
every original frame, until the largest squared corner norm is Q. A
physical separator initially has positive support sum; multiplying its
center gap makes its separating inequality strict. Thus the normalized
closed squares are pairwise disjoint. Actual projection comparisons and
the homogeneous cone comparisons persist.

The endpoint span of the normalized chain satisfies

    D=x3-x0-h0-h3>2.                                  (1)

The four side outsiders stay in their original side columns. The central
outsider cannot enter a side column during normalization: at Q that
would give three side outsiders plus the corresponding inner main, all
closed-disjoint, contradicting the three fixed side markers. Therefore
the same (2,1,2) occupancy persists, with a single outsider F satisfying
|x_F|<l.

For each full side, its inner main and two outsiders occupy its three
distinct markers in actual center-height order. The available main
ranges are

    bottom: y_M<-3/5,
    middle: |y_M|<7/20,
    top: y_M>3/5.                                    (2)

The inner cone comparison gives |y2-y1|<31/30, so the two mains cannot
be at opposite extremes. Horizontal and vertical reflection leave the
three possibilities

    (middle,middle), (bottom,bottom), (bottom,middle).  (3)

In each pattern we will find three distinct original outsiders L,F,R
such that

    -u<x_L<=0<=x_R<u, |x_F|<l,
    y_L,y_R>=3/5, y_F-h_F>=1/10.                      (4)

The actual outer endpoints satisfy the other hypotheses of the widened
five-square cap: x3 in (89/60,91/60), x0 in (-91/60,-89/60), their
halfwidths are less than 8/15, and |y0|,|y3|<=1/8. That cap gives D<=2,
contradicting (1).

### 1.2. Quantitative facts used repeatedly

The actual chain gives

    -31/60<x1<-29/60, 29/60<x2<31/60,
    1/2<=h1,h2<31/60, g1,g2>15/31,
    x1>h1-61/60, x2<61/60-h2,
    x2>h2-1/60.

Every center has norm less than rho; every outsider has |x|<u.
For the right endpoint E its inset obeys

    x_E-g_E<503/480, x_E+g_E>937/480,
    g_E>=15/32, g_E-|y_E|>221/600.                    (5)

In particular the fixed rectangle

    [503/480,937/480] x [-221/600,221/600]             (6)

is contained in E. The left-endpoint facts are the horizontal reflections.
The main cone comparisons and |y0|,|y3|<=1/8 also give

    |y1|,|y2|<139/120.                               (7)

For example x1-x0<31/30, so |y1|<=|y0|+(x1-x0)<139/120.

## 2. A complete signed side-pair cap at height 7/16

In the presence of the actual four-chain, among original units with
l<=x<=u there is at most one whose center height is at least 7/16.
Both coordinate reflections are valid. The inner main may be one of
the two units. We first prove the positive-normal half of this statement
without any endpoint assumption, then use the endpoint for the other sign.

### 2.1. The positive-normal half

Suppose two physical squares U,V in the Q-disk satisfy

    l<=x_U,x_V<=u, 7/16<=y_U<=y_V,

and have a separating unit normal from U to V of the form n=(a,b),
a>=0, b>0, a^2+b^2=1. This is impossible.

The exact two-vector support minimum is

    H_S(w)+H_S(z)>=1/2[K+(|w.z|+|det(w,z)|)/K],
    K=max(|w|,|z|).

It follows by minimizing between support sign changes: the minimum is
at an alignment with one of the two vectors, and alignment with the
longer vector is no worse. Its full derivation appears in
[TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md](sources/TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md) Section 2.

Put eta=7/16, t=1/2, m=(t,b), L=|m|=sqrt(5/4-a^2).
Also H_U(n)>=1/2 and r<25/12.

For 0<=a<=1/2, both coefficients in
a x_U+(t-a)x_V are nonnegative; use the lower endpoint l. Combining
the physical separator, containment of V in direction m, and the
two-vector minimum gives

    r>=F(a):=1/2+A/L+[t(a+b)+b^2-ab]/(2L^2),
    A=89/120+eta b.

Write f(b)=(b-t)/(b^2+t^2) and G=(t-a)f(b)/2. Then F=1+A/L+G.
On sqrt(3)/2<=b<=1, direct differentiation gives

    0<f<=2/5, 0<f'<3/8, b>6/7,
    G'>-1/5-7/512>-7/32.

For clarity f'=(-b^2+b+1/4)/(b^2+1/4)^2. Its numerator is positive
and less than 3/8, its denominator is at least one, and f increases
to f(1)=2/5. In differentiating G, use a(1/2-a)<=1/16.

Furthermore

    (A/L)'=a[89/120-eta/(4b)]/L^3 >=(2/5)a,

because L^3<3/2 and

    (2/3)[89/120-49/384]=131/320>2/5.

Integration and completion of the square give

    F(a)>=F(0)-(7/32)a+a^2/5>=F(0)-245/4096.

Using sqrt(5)<9/4,

    F(0)=11/10+283/(120sqrt(5))>58/27,
    58/27-245/4096-25/12=553/110592>0.

This excludes the first normal range.

For 1/2<=a<1, the coefficient t-a is nonpositive; use x_U>=l and
x_V<=u. Now L<=1, and the same support calculation yields

    rL>=N:=37/24-(7/20)a+(3/16)b+ab/2+b^2/2.         (8)

For b<=7/10 the coefficient b/2-7/20 of a is nonpositive. Use
a<=1-b^2/2 to obtain

    N>=143/120+(11/16)b+(27/40)b^2-b^3/4.

On 0<=b<=1/4, use L<=1/2+b^2. It gives

    N-(25/12)L
      >=3/20+(11/16)b-(169/120)b^2-b^3/4
      >=3/20+(307/960)b>0.

On 1/4<=b<=7/10, use the tangent bound L<=5/8+b^2/2. The resulting
lower bound is

    P1(b)=-53/480+(11/16)b-(11/30)b^2-b^3/4.

It is concave, with P1(1/4)=133/3840 and P1(7/10)=253/2400,
both positive.

For 7/10<=b<=sqrt(3)/2, the coefficient of a in (8) is nonnegative.
The chord bound a>=1-(2/3)b^2 and the same tangent bound on L give

    N-(25/12)L>=P2(b)
       :=-53/480+(11/16)b-(37/120)b^2-b^3/3.

This polynomial is concave on the larger interval [7/10,7/8], and
P2(7/10)=253/2400, P2(7/8)=61/1920 are positive. These intervals
cover the entire second normal range and contradict (8). The
positive-normal half is proved for every physical orientation and owner.

### 2.2. The endpoint supplies the other horizontal sign directly

Suppose U,V are two side units with 7/16<=y_U<=y_V. Their horizontal
gap is at most 3/5. The two contained half-unit disks give
y_V-y_U>=4/5; since y_V<rho, we have y_U<43/60.

If U is the inner main, x_U<31/60<4/5. If U is an outsider, retain
the actual right endpoint E and set D_E=x_E-x_U>0,
V_E=|y_U-y_E|. From (5),

    V_E-g_E<43/60-221/600=209/600<3/8.

Its half-unit disk avoids E's aligned inset. The exact distance to that
inset therefore gives

    D_E-g_E>sqrt(1/4-(3/8)^2)=sqrt(7)/8>1/4.

Consequently

    x_U<503/480-1/4=383/480<4/5.                     (9)

There is no reversed-horizontal-center case here: x_E>89/60>u>=x_U.
Also 4/5-383/480=1/480>0, so the final comparison is strict.

Every genuine separating unit normal from U to V has positive vertical
component. Otherwise its projection of the center difference is at most
3/5, while the two supports sum to at least one. A normal with
nonpositive horizontal component is excluded by the established
oriented asymmetric cap: (9) supplies x_U<4/5 and y_U>=7/16>37/100.
A normal with positive horizontal component is excluded by Section 2.1.
Thus all signed normals are covered and the 7/16 side-pair cap follows.

This proof uses no 9/16 side cap. Conversely it supplies that weaker
bound whenever it is invoked in the extreme-main proof: the lower
member of any two side units has height less than 7/16, hence less than
9/16. The low-center band theorem itself only assumes |y|<=9/16 and
is independent of any pair cap. This explicitly resolves the dependency.

## 3. The lower outsider of a bottom full side

Suppose a full side's inner main is at its bottom marker. Write U for
its lower outsider and H for its higher outsider. Then

    -113/600<y_U<7/16, l<=|x_U|<zeta,
    |x_U|-g_U<J, y_U+g_U>A_0,
    y_H>367/600>3/5.                                 (10)

All these refer to the original U, including its single physical frame.

### 3.1. A uniform low-side center and inner-edge bound

First let U be any right outsider with l<=x_U<u and |y_U|<7/16.
Put A=503/480, c=221/600, e=7/16-c=83/1200. For the right endpoint
inset, D=x_E-x_U>0 and V=|y_E-y_U| satisfy V-g_E<e. The half-unit
disk of U gives

    D-g_E>sqrt(1/4-e^2),
    x_U<A-sqrt(1/4-e^2)<zeta.

The last comparison has exact squared reserve

    A-zeta=2971/6000>0,
    1/4-e^2-(2971/6000)^2=934/36000000>0.             (11)

Retain U's actual side components a>=b>=0. A coordinate vertical
separator from the endpoint inset is impossible, since V<9/16<g_E+h_U.
A horizontal separator requires D-g_E>=h_U. Any U-owned side separator,
after taking absolute components, requires one of

    a(D-g_E)+b(V-g_E)>=1/2,
    b(D-g_E)+a(V-g_E)>=1/2.

For b>0 the first yields the smaller necessary horizontal gap, because

    (1/2-ea)/b-(1/2-eb)/a
      =(a-b)[1/2-e(a+b)]/(ab)>=0.

The case b=0 is covered by the coordinate axes. Thus every separator
implies x_U<A-m, where

    m=min(h_U,(1/2-eb)/a).

We claim m+g_U>2147/2400. The h_U branch follows from h_U+g_U>=1.
For the other branch, put t=b/a in [0,1]. Its sum with g_U is

    (t+2)sqrt(1+t^2)/(2(t+1))-(83/1200)t.

Moving the linear term, multiplying and squaring positive quantities
reduces the claim to positivity of

    P(t)=1440000(t+2)^2(1+t^2)-(t+1)^2(2147+166t)^2
        =1412444t^4+4992084t^3+1137227t^2
                    -4172022t+1150391.

Its curvature and one rational anchor are

    P''(t)=16949328t^2+29952504t+2274454>2000000,
    P(3/7)=28507100/2401>10000,
    P'(3/7)=-610980/343, |P'(3/7)|<2000.

The tangent quadratic gives P(t)>=P(3/7)-P'(3/7)^2/4000000>9999
for every t in [0,1]. Therefore

    x_U-g_U<A-2147/2400=23/150=J.                    (12)

Reflection gives the identical bounds on the left side.

### 3.2. Its height and proxy top

The main cone bound (7) and same-half-plane clearance give
y_U>y_M+97/100>-113/600. The side-pair cap in Section 2 gives y_U<7/16,
so Section 3.1 applies. Since zeta<47/80, the horizontal gap to its
near-aligned inner main is less than 5/48. That main's inset satisfies

    g_M-D>15/31-5/48>3/8.

The established near-main physical clearance yields
y_U-y_M>=g_M+h_U-1/128. Using h_U+g_U>=1,

    y_U+g_U>1-139/120+15/31-1/128
             =18911/59520=A_0>3/10.

This last conclusion has the following stronger local contract, useful
outside the full-side pattern: if an original side outsider S is above
its corresponding inner main and y_S<7/16, the actual-and-cone chain
already gives y_S>-113/600. Thus |y_S|<7/16, and Section 3.1 and this
same near-main calculation give

    |x_S|<zeta, |x_S|-g_S<J, y_S+g_S>A_0.

No second outsider on that side is needed for this implication. In the
full-side application only, Section 2 supplies the premise y_U<7/16.

Finally U,H have horizontal gap less than u-l=3/5, so their half-unit
disks give y_H-y_U>4/5. Thus y_H>367/600. This proves (10).

## 4. A lower central outsider is impossible in the mixed pattern

Suppose y1<-3/5, y2<7/20, and a right outsider T satisfies
l<=x_T<u, y_T<y2. There is no central outsider F with |x_F|<=l
and y_F<y1. These are the exact conditions used later for the
(bottom,middle) main pattern.

### 4.1. Such an F would have x_F>1/3

Reflect vertically. Write (X,Y) for F and (x1,Z) for M1, so
Y>Z>3/5. Put g=g1>15/31. Suppose X<=1/3. Since X>=-l>x1,
the center gaps D=X-x1>0 and V=Y-Z>0 satisfy

    D-g<17/20-15/31=227/620<11/30,
    V-g<133/64-3/5-15/31-h<1-h.

The respective rational margins are 1/1860 and 57/9920. The coordinate
axes cannot separate F from the aligned main inset, because h>=1/2.
With F's side components a>=b>=0, a side separator would require

    a(D-g)+b(V-g)>=1/2 or b(D-g)+a(V-g)>=1/2.         (13)

For the first alternative, use a<=1-b^2/2 and h>=1/2+(2/7)b. The
latter follows by squaring a>=1-3b/7: the difference is
b(42-58b)/49>=0 for b<=1/sqrt(2)<21/29. Therefore

    a(D-g)+b(V-g)
      <11/30+b/2-(197/420)b^2
      <=11/30+105/788=1/2-1/11820.

For the other alternative, first suppose a>=3/4. Then

    (11/30)b+a(1-h)
      =a-1/2+b^2/2+b(11/30-a/2)<=1/2,

using a+b^2/2<=1 and 11/30-a/2<=-1/120. If a<=3/4, then
a+b>7/5, so h>7/10, and b<5/7 gives

    (11/30)b+a(1-h)<11/42+9/40=409/840<1/2.

In both cases the original strict gap bounds make the second expression
in (13) less than 1/2. All separating axes fail, a contradiction.
Thus X>1/3.

The correlated main band also gives D-g<X+1/60<=1/2 even without
the contrary X<=1/3 assumption. The half-unit disk of F therefore
forces V>g. We have proved

    1/3<X<=l, 3/5+15/31<Y<rho.                      (14)

### 4.2. The right lower outsider gives a circular profile

In the reflected frame write (s,t) for T. Its actual clearance from M2
gives l<=s<u and t>97/100-7/20=31/50. Its half-unit disk avoids the
fixed endpoint rectangle (6), so, writing A=503/480 and c=221/600,

    max(A-s,0)^2+(t-c)^2>=1/4.

Here s<u<937/480 and t>c. Put

    s0=A-sqrt(1/4-(31/50-c)^2).

Then l<s0<A<u and s0<37/60; the latter positive-root comparison has
reserve

    1/4-(31/50-c)^2-(A-37/60)^2=3959/5760000>0.

Consequently t>=L(s), where

    L(s)=31/50                              for l<=s<=s0,
    L(s)=c+sqrt(1/4-(A-s)^2)                 for s0<=s<=A,
    L(s)=c+1/2                              for A<=s<=u.

If t>=Y, the original centers have horizontal gap less than 3/4 and
vertical gap less than rho-3/5-15/31=161/372<1/2. Their squared
distance is therefore less than 13/16<1, impossible for their two
contained half-unit disks.

If t<=Y, their squared distance is at most

    f(s)=(s-X)^2+(Y-L(s))^2.

On the first and last profile intervals f increases with s. On the
middle interval its exact expansion is

    f(s)=2(A-X)s+X^2-A^2+(Y-c)^2+1/4
           -2(Y-c)sqrt(1/4-(A-s)^2).

It is convex there, since Y>c and the radical is concave. The maximum
over the whole strip is therefore at s0 or u. Using (14),

    f(s0)<(17/60)^2+(269/300)^2
           <(3/10)^2+(9/10)^2=9/10<1,
    f(u)<(3/4)^2+(389/600)^2
           <(3/4)^2+(13/20)^2=197/200<1.

Again the two half-unit disks overlap. This proves the mixed
lower-central exclusion with every physical frame and separator retained.

## 5. Route the unique central outsider

The original F is either above both inner main centers or below both.
To prove this, set p=x_F-x1>0 and q=x2-x_F>0. The correlated main
bands and h_i+g_i>=1 give p-g1<1/2, q-g2<1/2. The half-unit disk
of F therefore has vertical center gap greater than g_i from each
main inset.

Also p+q=x2-x1<31/30, so one of p,q is less than 31/60. For that
inset its horizontal residual is less than 1/30, and its vertical
center gap is greater than g_i+49/100, using
1/4-1/900>(49/100)^2. If F were between the two main heights, their
difference would exceed

    g1+g2+49/100>30/31+49/100>31/30,

contradicting their cone comparison. Equality with either main height
is already excluded by its positive gap.

## 6. Both inner mains in the middle

Reflect vertically so F is above both. The adjacent-proxy barrier gives

    y_F-h_F>min(y1,y2)+869/1860
              >-7/20+869/1860=109/930>1/10.

Choose the upper outsider from each full side as L,R. Their
same-half-plane clearances give y_L,y_R>-7/20+97/100=31/50>3/5.
Thus (4) holds, and the widened five-square cap contradicts (1).

## 7. Both inner mains at the bottom

Write U_L,U_R for the lower outsiders in the full sides, and H_L,H_R
for the higher ones. Section 3 gives every bound in (10) for both sides.
F cannot be below both mains: its same-half-plane clearance would give
y_F<-3/5-97/100<-rho. Therefore it is above both. Its stronger
central clearance and (7) give y_F>-7/40.

Choose U on F's own side. The horizontal gap is less than zeta, and

    11/36-zeta^2=3311/144000000>0.

Their half-unit disks give |y_F-y_U|>5/6. If F were below U, then
y_F<7/16-5/6=-19/48, contrary to y_F>-7/40. Hence

    y_F>y_U+5/6>-113/600+5/6=129/200.                (15)

Suppose T=y_F-h_F<=1/10. At the height v=3/10 the section of F has
depth d=v-T>=1/5 above a bottom vertex, with 0<d<h_F. For side
components a>=b>0 its section length is d/(ab) for d<=b and 1/a
for b<=d<=h_F. The aligned case has length one. Thus the section
length is at least min(2d,1)>=2/5.

At that same height both zero insets have full horizontal sections in
their interiors: their tops exceed A_0>3/10, while their bottoms are
below 7/16-g_U<5/48<3/10. The horizontal gap between them is less
than 2J=23/75<2/5. Thus F's section cannot fit in the middle gap.

It cannot fit to the left of both insets either. In the bottom-right
vertex orientation its right endpoint is at least x_F>=-l. In the
bottom-left orientation its right endpoint exceeds x_F if d>=b; if
d<=b it is at least x_F-k+d>=-l-1/2+1/5=-47/60. The left inset's
outer endpoint is less than -l-1/3=-49/60. In all cases F's right
endpoint lies to the right of that outer endpoint. The aligned case is
immediate. Reflection excludes the exterior right component.

Consequently F's section intersects the interior of a zero inset, a
physical interior overlap. We have proved y_F-h_F>1/10. Taking
L=H_L and R=H_R gives their heights greater than 367/600>3/5.
Again (4) and the five-square cap contradict (1).

## 8. One inner main at the bottom, the other in the middle

Take the left main at bottom and the right at middle. Let U be the
lower left outsider, H_L its higher companion, and H_R,B_R the right
upper and lower outsiders. Section 4, using the original B_R, excludes
F below both mains. Section 5 therefore places F above both.
The high shoulders already satisfy

    y_H_L>367/600>3/5, y_H_R>-7/20+97/100=31/50>3/5.

It remains to prove y_F-h_F>1/10, using both original U and M2.

### 8.1. The two proxy tops and their inner edges

Write U's center (-Z,y_U). Section 3 gives

    l<=Z<zeta, |y_U|<7/16,
    Z-g_U<J, y_U+g_U>A_0.

For M2, the correlated main bands and h2+g2>=1 give

    x2-g2<1/60, x2+g2>59/60,
    y2+g2>B_0:=83/620.

Suppose T=y_F-h_F<=1/10, and put

    c_L=A_0-1/10=12959/59520>1/6,
    c_R=B_0-1/10=21/620>0.

Their exact comparison is

    4c_L c_R-(17/100)^2=45993/76880000>0.            (16)

Write F's center (X,Y), and retain its one original frame a>=b>=0,
h=(a+b)/2, k=(a-b)/2 throughout both pairs.

### 8.2. The right proxy forces an upward-left F-owned axis

Put D_R=x2-X>0, V_R=Y-y2>0. Then

    D_R-g2<1/60-X<=1/2,
    V_R-g2<h-c_R.                                   (17)

Both coordinate separators fail. Any remaining separator is F-owned,
and F's support in its unit side direction is exactly one half. Its
vertical component must be positive: otherwise its adjusted projection
is at most |n_x|(D_R-g2)<1/2.

An upward axis pointing right also fails. With absolute components
(a,b), its adjusted projection is less than bh<=1/2. With components
(b,a), it is less than

    ah-b(D_R+g2)=1/2+b[k-(D_R+g2)]<=1/2,

because D_R+g2>59/60-l=1/2>=k. Thus the axis points strictly up
and left. An aligned F would have no such side direction, so b>0.
Put t=b/a in (0,1]. The possibilities (-a,b),(-b,a), using (17),
give respectively

    X<1/60-k-tc_R or X<1/60+k-c_R/t.                (18)

In either case X<4/15. For the second bound use k<=(1-t)/2 and
t/2+c_R/t>=sqrt(2c_R)>1/4; the last squared reserve is 13/2480.

### 8.3. F lies above the left zero unit as well

The half-unit disk of F and (17) give V_R>g2, hence Y>B_0. If
Y<=y_U, their center gaps would satisfy

    0<=X+Z<4/15+zeta<5/6,
    0<=y_U-Y<7/16-B_0<1/3.

Their squared distance would be less than 29/36<1, a contradiction.
The horizontal comparison uses zeta<17/30; the vertical one uses
B_0>5/48. Hence Y>y_U.

Now put D_L=X+Z>=0, V_L=Y-y_U>0. The bounds become

    D_L-g_U<X+J<21/50<1/2,
    V_L-g_U<h-c_L.                                  (19)

Both coordinate axes again fail, and every F-owned separator has
positive vertical component. Its horizontal component must be positive.
An inward axis with vertical component b has adjusted projection below
bh<=1/2. One with vertical component a has adjusted projection below

    1/2+b(k-D_L-g_U)-a c_L<1/2,

since g_U>1/3, D_L>=0, k<=1/2, and
t(k-D_L-g_U)<1/6<c_L. Thus the left separator points up and right.

### 8.4. The single original F frame makes the two inequalities incompatible

The left upward-right axis and right upward-left axis are the two
different orthogonal side axes of F. For the assignment (a,b),(-b,a),
their necessary inequalities from (17),(19) imply

    D_L-g_U>k+t c_L, D_R-g2>-k+c_R/t.

For the other assignment they imply

    D_L-g_U>-k+c_L/t, D_R-g2>k+t c_R.

In either case their sum is strictly greater than
2sqrt(c_L c_R)>17/100, by (16). But the actual inner edges satisfy

    D_L+D_R-g_U-g2=Z-g_U+x2-g2<J+1/60=17/100.

This contradiction proves y_F-h_F>1/10. Taking L=H_L,R=H_R now
supplies (4), and the five-square cap contradicts (1).

## 9. Conclusion and exact boundary of the result

The three patterns (3) are exhaustive under the actual-and-cone chain
hypothesis, and Sections 6--8 close each of them. Therefore the original
strict counterexample with outsider occupancy (2,1,2) does not exist.

All five outsiders are retained. In the mixed pattern, B_R excludes the
lower central placement and U forces the central whole floor. In the
equal-bottom pattern, both lower outsiders force that floor while both
higher outsiders are the shoulders. Every use of an aligned inset keeps
it centered in its original physical square. The two-pair argument in
Section 8 uses one actual F frame, not independently chosen orientations.

This proves the full stated nine-original occupancy theorem. It leaves
the other outsider counts and actual four-chains without the retained
cone comparisons as separate domains. No unrestricted G3 closure or
global equality classification is asserted here.
