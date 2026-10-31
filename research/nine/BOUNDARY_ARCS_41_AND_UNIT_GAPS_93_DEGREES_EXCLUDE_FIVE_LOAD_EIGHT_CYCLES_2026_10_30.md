# Forty-one-degree boundary arcs and ninety-three-degree unit gaps

**Date:** October 30, 2026 UTC. **Status:** complete proposed continuous
geometric proof and marked-cycle consequences, awaiting independent full
review. Every earlier frozen angular source remains unchanged.

The new geometric bounds are strict: two physical boundary squares have
center separation greater than 41 degrees, and a set gap of at least one
between two such squares forces center separation greater than 93
degrees. The whole closed interior arcs used below are proved directly.
These bounds exclude the entire eight-body five-mark family, including
all side-normal singleton runs. Together with the earlier long/diagonal
angles, they restrict every compatible eight-body cycle to at least six
marks; with exactly six marks, both singleton runs must be side-normal
in a full force-and-torque caller.

## 1. Radius window and two radial profiles

Let actual unit squares have pairwise disjoint open interiors and lie
in the disk centered at O with radius

    79/40<=R<=sqrt(Q), Q=1105/256.

A boundary square physically touches this containing circle, regardless
of its selected load or which physical corner weights vanish. For a
boundary square with center C, put r=|C| and e=C/r. Let Je be a
perpendicular unit direction. We will prove the following two profiles:

| Profile | A | B | rho^2=A^2+B^2 |
| --- | --- | --- | --- |
| Boundary separation | 117/100 | 439/1000 | 1561621/1000000 |
| Unit-gap separation | 103/100 | 9/25 | 2381/2000 |

For either profile put `rho=sqrt(A^2+B^2)` and `alpha=atan(B/A)`.

**Theorem 1 (two complete interior-arc profiles).** For each profile,
the entire closed arc

    {rho*(cos(theta)*e+sin(theta)*Je): |theta|<=alpha}     (1)

lies in the original square's open interior. In particular its two
angular endpoints `A*e+-B*Je` are actual interior points.

Both listed values of rho are less than 5/4. For the first profile
the exact squared reserve is `879/1000000`; for the second it is
`93/250`. The arc proof will use the radial and transverse bounds
for every theta in (1), rather than infer arc containment merely
from its two endpoints.

## 2. A tighter exact radial bound

Every contained unit center satisfies

    |C|<M=91/60,                                         (2)

by the farthest-corner lower bound `|C|^2+|C|+1/2` and its strict
excess `31/57600` over Q at M. For a physical boundary square,

    r>=R-1/sqrt(2)>5/4,                                 (3)

using `1/sqrt(2)<29/40`. In particular r>rho>A for both profiles.

Reflect and exchange the square's own axes so that its center
direction has components c,s with

    c>=s>=0, c^2+s^2=1, 0<=s<=1/sqrt(2).

Actual physical circle contact gives

    r^2+r(s+c)+1/2=R^2.

Consequently

    r+(s+c)/2=sqrt(R^2-1/4+(s*c)/2)
             <=sqrt(Q-1/4+(s*c)/2).

The square-root tangent at s*c=3/8 has value 33/16. Equivalently,
apply `sqrt(t)<=(t+w^2)/(2*w)` with w=33/16. This gives the exact
uniform inequality

    r <= 355/176+(4/33)*s*c-(s+c)/2.                    (4)

This includes the tangent equality case and all actual orientation
endpoints. No numerical fitting is involved.

## 3. Uniform own-coordinate bounds for every point of either arc

For every point P on (1), its radial and transverse displacement
from C has the form `(-K,L')`, where

    0<K=r-rho*cos(theta)<=r-A,
    |L'|<=B.                                            (5)

The positivity uses r>rho; the two upper bounds use the entire
closed interval `|theta|<=atan(B/A)`. Thus both own-coordinate
absolute deviations of P are bounded by

    F_1=(r-A)*s+B*c,
    F_2=(r-A)*c+B*s.                                    (6)

Put `E=355/176-A`. The radial tangent (4) gives

    F_1<=E*s-s^2/2+c*(B-s/2+(4/33)*s^2).

The coefficient multiplying c is positive for both profiles.
Indeed B>=9/25, and the function `B-s/2+(4/33)*s^2` decreases on
`[0,3/4]`; at 3/4 its value is at least `117/2200>0`.
The actual interval has `s<=1/sqrt(2)<3/4`. Using
`c<=1-s^2/2`, we obtain

    F_1<=G_(A,B)(s)
       :=B+(E-1/2)*s+(4/33-1/2-B/2)*s^2
          +(1/4)*s^3-(2/33)*s^4.                       (7)

We now certify G<1/2 for each profile and check its second
own-coordinate bound.

### 3.1 Boundary-separation profile

For A=117/100 and B=439/1000, let D(s)=1/2-G_(A,B)(s). Then

    D(s)=61/1000-(1527/4400)*s+(39487/66000)*s^2
          -(1/4)*s^3+(2/33)*s^4.

Set z=s-9/25. Exact expansion gives

    D(s)=50801/17187500-(5961/2750000)*z
          +(123887/330000-(179/1100)*z+(2/33)*z^2)*z^2.
                                                               (8)

Since s<3/4, we have z<39/100. The coefficient multiplying z^2
is at least

    123887/330000-(179/1100)*(39/100)
       =6434/20625>0.

The linear term is bounded below using this same upper bound on z;
negative z only improves it. Therefore

    D(s)>=50801/17187500-(5961/2750000)*(39/100)
         =580337/275000000>0.                           (9)

For this profile `A+B=1609/1000>M`, so (2) gives

    F_1-F_2=(c-s)*(A+B-r)>=0.

Equations (7)--(9) thus make both deviations in (6) strictly below
one half throughout the complete arc (1).

### 3.2 Unit-gap profile: the first own coordinate

For A=103/100 and B=9/25, the corresponding difference is

    D(s)=7/50-(2143/4400)*s+(461/825)*s^2
          -(1/4)*s^3+(2/33)*s^4.

Set z=s-2/3. Its exact expansion is

    D(s)=829/534600-(1247/356400)*z
          +(1091/4950-(35/396)*z+(2/33)*z^2)*z^2.       (10)

Here z<1/12. The quadratic coefficient is at least

    1091/4950-(35/396)*(1/12)=25309/118800>0.

As before, this holds for every negative z as well. Hence

    D(s)>=829/534600-(1247/356400)*(1/12)
         =359/285120>0.                                 (11)

Thus F_1<1/2 on the whole interval.

### 3.3 Unit-gap profile: the second own coordinate

When 0<=s<=1/2, rewrite the radial tangent bound for F_2 as

    F_2<=(E-s/2)*c-1/2+s^2/2+(B+4/33)*s-(4/33)*s^3.

Here `E=4343/4400` and E-s/2 is positive. Using `c<=1-s^2/2`
therefore gives

    F_2<=U(s):=2143/4400-(31/1650)*s
                   +(57/8800)*s^2+(17/132)*s^3.

The polynomial U is convex on [0,1/2], since U'' is positive
there. Its maximum on that interval is at an endpoint, and

    U(0)=2143/4400=1/2-57/4400,
    U(1/2)=17437/35200=1/2-163/35200.                   (12)

This proves F_2<1/2 for the first interval.

For 1/2<=s<=1/sqrt(2), the quantity s+c is increasing and obeys

    s+c>=(1+sqrt(3))/2>34/25.

The strict rational comparison follows from `sqrt(3)/2>43/50`.
If r>=139/100=A+B, the boundary equation would imply

    R^2=r^2+r(s+c)+1/2
         >(139/100)^2+(34/25)*(139/100)+1/2
         =Q+39/6400>Q,

which is impossible. Therefore r<A+B and
`F_1-F_2=(c-s)*(A+B-r)>=0` on this second interval. The first-
coordinate bound (11) now also proves F_2<1/2.

All points of both full closed arcs have both own-coordinate
deviations strictly below one half. This proves Theorem 1.

## 4. Exact elementary trigonometric comparisons

For clarity, all angle comparisons used next have rational
certificates. The classical inequality pi<22/7 follows, for
example, from the exact positive integral

    22/7-pi=int_0^1 x^4*(1-x)^4/(1+x^2) dx>0.

Polynomial division of the integrand gives
`x^6-4*x^5+5*x^4-4*x^2+4-4/(1+x^2)`, verifying the identity.

Put beta=pi/9, or twenty degrees. Triple-angle monotonicity gives

    cos(beta)>31/33,
    cos(beta)<47/50,
    sin(beta)<137/400.                                  (13)

For the two cosine comparisons, the increasing polynomial
`4*x^3-3*x` on x>1/2 has test values

    17887/35937=1/2-163/71874 at x=31/33,
    7849/15625=1/2+73/31250 at x=47/50.

For the sine comparison, `3*x-4*x^3` is increasing on [0,1/2].
At 137/400 it equals

    13/15+5941/48000000>13/15>sqrt(3)/2,

where the last positive square comparison is `169/225>3/4`.

Let h=11/1260. Since `pi/360<h`, the addition formulas, (13),
`cos(t)>=1-t^2/2` and `sin(t)<t` give

    cos(41*pi/360)>C_0
       :=(31/33)*(1-h^2/2)-(137/400)*h
        =981141437/1047816000>0,

    sin(41*pi/360)<S_0
       :=137/400+(47/50)*h
        =44189/126000.

The exact comparison

    3*C_0-8*S_0=1206173/349272000>0

therefore proves

    tan(41*pi/360)<3/8<439/1170,
    439/1170-3/8=1/4680>0.                              (14)

For the later ninety-three-degree comparison, put delta=pi/120.
Then delta<11/420, and

    67*cos(delta)+139*sin(delta)
       <67+139*(11/420)=29669/420
       <707/10<50*sqrt(2).                              (15)

The two final strict comparisons use the rational reserve `5/84`
and `sqrt(2)>707/500`, respectively. All quantities compared
through squaring are positive.

## 5. The new physical boundary-angle and unit-gap theorems

**Theorem 2 (forty-one-degree boundary separation).** Two distinct
physical boundary squares have minor center angle strictly greater
than 41*pi/180.

**Proof.** For the boundary-separation profile, its full closed
interior arc has halfwidth

    alpha=atan((439/1000)/(117/100))=atan(439/1170)
          >41*pi/360

by (14). If two boundary centers had minor separation at most
41*pi/180, the midpoint direction of that minor arc would belong
to both closed interior-arc intervals. The same point of their
common radius rho would lie in both open square interiors. This
contradicts physical disjointness. QED.

**Theorem 3 (ninety-three-degree unit-gap separation).** If physical
boundary squares S,T have `dist(S,T)>=1`, their minor center angle
is strictly greater than 31*pi/60, or ninety-three degrees.

**Proof.** Suppose their minor angle theta is at most 31*pi/60.
Use the unit-gap profile A=103/100,B=9/25 and rotate the disk frame
so the two center directions have angles -theta/2 and theta/2.
Take the two facing interior points

    P=A*e_S+B*Je_S, Q=A*e_T-B*Je_T.

As in the right-angle comparison, their distance is

    |P-Q|=2*|A*sin(theta/2)-B*cos(theta/2)|.               (16)

The function inside the absolute value is strictly increasing on
`0<=theta/2<=pi/4+pi/120`, since its derivative
`A*cos(t)+B*sin(t)` is positive there. Its initial value is -B,
whose magnitude is less than one half. Its final value is

    ((A-B)*cos(delta)+(A+B)*sin(delta))/sqrt(2)
       =(67*cos(delta)+139*sin(delta))/(100*sqrt(2))
       <1/2

by (15). Thus the distance in (16) is strictly below one. Theorem
1 puts P and Q inside their respective actual squares, contradicting
the set-gap hypothesis. QED.

These two theorems are entirely force-free. A geometric set gap is
used for Theorem 3, not a guessed center gap. Both actual squares
must physically touch the circle; no selected positive load is
required for the geometry.

## 6. A combined bound for every compatible marked cycle

Use the exact marked-cycle setting and physical order join of

`UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md`,

frozen SHA256
`b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be`.

There is a simple cycle of m actual bodies, at least two marked
physical boundary bodies, one common signed actual support normal
along each marked-to-marked run, and a compatible physical embedding
of that same actual graph preserving its marked circle spokes.
Its consecutive positive center angular gaps sum to 360 degrees.

Let k_0 count direct runs, k_1 count all singleton runs, d count
singleton runs whose actual internal support width is sqrt(2),
and ell count two-internal-body runs. Every run has at most two
internal bodies by support telescoping and the center diameter.
Thus

    m=k_0+2*k_1+3*ell,
    t=k_0+k_1+ell=m-k_1-2*ell                           (17)

is the mark count.

A common-normal run with at least one internal unit gives set
distance at least one between its endpoint squares: projecting
any two actual endpoint points onto the signed normal leaves the
sum of the positive internal support widths. Theorem 3 therefore
applies to every singleton run, with arbitrary internal orientation.
Theorem 2 applies to the direct runs.

For diagonal-width singleton and long runs, retain respectively
the greater-than-105-degree and greater-than-175-degree estimates
of

`SHARP_LONG_AND_DIAGONAL_RUN_ANGLE_BUDGET_2026_10_30.md`,

frozen SHA256
`614382093c6c976e7767855c5234419fe3a3c477bafc8c4465e46d86446e56fc`.

The four run classes thus have consecutive positive gaps strictly
greater than 41, 93, 105 and 175 degrees. Summing gives

    360>41*k_0+93*(k_1-d)+105*d+175*ell
       =41*m+11*k_1+12*d+52*ell.

**Theorem 4 (strengthened exact cycle budget).**

    41*m+11*k_1+12*d+52*ell<=359.                        (18)

No angle is replaced by an unproved force-polygon turn: the actual
marked cyclic order is the frozen physical annular-order conclusion.

## 7. Whole eight-body five-mark closure and precise remaining scope

If m=8, equation (18) implies ell=0, because `328+52>359`.
It then reads

    11*k_1+12*d<=31,
    k_1=8-t.                                            (19)

In particular k_1<=2 and hence t>=6. The precise remaining
eight-body count table is:

| Marked physical boundary bodies t | Singleton runs k_1 | Diagonal-width singletons d |
| --- | --- | --- |
| 6 | 2 | 0 |
| 7 | 1 | at most 1 |
| 8 | 0 | 0 |

The six-mark d=0 assertion follows because `22+12>31`.
The table is a necessary condition, not a realization claim.

**Corollary 5 (entire eight-body five-mark family excluded).** A
compatible eight-body cycle with exactly five marked physical
boundary bodies is impossible. After long runs are excluded, it
would have three singleton and two direct runs. Their actual
angular gaps would sum to more than

    3*93+2*41=361 degrees,

contradicting one full turn. This covers every cyclic placement
and every orientation of the three internal bodies, including
the entire all-side family left by the previous budget.

The earlier whole four-mark eight-body exclusion is retained and
also follows from (19). An eight-body six-mark cycle with either
singleton of diagonal width is likewise impossible; its angle
sum is already greater than `4*41+93+105=362` degrees.

## 8. Complete full-force callers and preserved seven-body record

For a physical translational stress, require every unmarked cycle
body to be unloaded of true positive degree two in the same full
retained graph. Its complete two-force equation supplies the common
signed support normals. Every original marked-body force, chord
or attachment is retained, and its degree may be arbitrary.

The geometric budget (18) reads d directly from actual support
widths and needs no torque. For a retained full force-and-torque
certificate, the original zero-moment equation at a singleton
transmitter gives the exact side-width-one or diagonal-width-sqrt(2)
classification proved in the frozen diagonal source. In that caller,
the six-mark row of (19) has two actual side-normal transmitters.
It does not assert that independently selected certificates have
the same degrees or classifications.

An entire compatible simple positive component with four or five
positively circle-loaded bodies therefore has at most seven total
bodies: the base or (18) excludes nine and more, and (19) excludes
eight. Every actual completing square and physical circle mask is
retained. Arbitrary marked zero-load physical boundary bodies are
also allowed in the geometric version.

The seven-body side-short record orbit `(2,0,1,0)` remains. It has
`m=7`, `k_1=1`, `d=0`, `ell=1`, giving left side 350 in (18).
This source does not exclude the six-, seven- or eight-mark rows
of (19), every seven-body block, or chorded blocks with additional
positive forces at circle-clear cycle vertices. It does not assign
an original coarse-row closure automatically.

## 9. Verification boundary

Both complete closed interior arcs are proved over their full
continuous intervals, with exact quartic certificates and an
explicit second-coordinate split. Every trigonometric comparison
has rational reserves and elementary positive squaring. All
displayed expansions and exact fractions were independently
recomputed during derivation.

The geometric part is self-contained; only the cycle order and
the stronger long/diagonal angles use the two literal frozen
inputs identified above. There is no numerical pose search,
finite table, unproved endpoint alignment, altered contact mean,
Lean compilation, CI run, original ledger edit, metadata change,
or remote publication asserted here.
