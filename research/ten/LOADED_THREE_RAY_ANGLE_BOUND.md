# A shared angular bound for three circle-loaded squares

**Status:** reviewed exact hand theorem with a 24-row rational certificate;
root and independent full mathematical reviews passed on 2026-10-31.
The table was independently checked by exact radical elimination and by
separate dyadic rational brackets. Section 6 excludes the whole fixed
case `C20-M08-L07-B01-T02`.
The squares need not touch or carry any specified contact forces.

Let three interior-disjoint unit squares be contained in the centered
disk of radius `79/40<=R<=3/sqrt(2)`, and let each have a vertex on the
containing circle. List their center rays in order on an angular interval,
with the middle ray between the other two. Let the two intervening angles
be delta_1, delta_2, with positive sum at most `2pi`.

Put

```text
delta_* = 2 atan(1/(sqrt(14)-1)),
delta_0 = atan(9/10).
```

**Theorem.**

```text
delta_1+delta_2 > delta_*+delta_0
                    > pi/2-atan(15/104).                 (1)
```

The last constant is sufficient, together with the reviewed D-path cap
bound, to exclude the whole seven-loaded, one-D cycle. The proof below
is shared by every triple of geometrically circle-loaded squares; it
does not classify the three bodies' contact ownership.

## 1. One side of a loaded center ray has a forbidden angular interval

The pair theorem in
[LOADED_PAIR_ANGLE_BOUND.md](LOADED_PAIR_ANGLE_BOUND.md) gives minor
center-ray separation at least delta_*. It also proves that a separating
line at absolute offset at least `1/2` forces separation at least `pi/4`.

Rotate the middle center ray to the positive horizontal axis. Choose a
square-frame angle modulo `pi/2`, and reflect vertically if necessary,
so this frame has angle `0<=alpha<=pi/4`. We prove that **no other
circle-loaded square can have center ray at angle `-delta`, with
`0<delta<=delta_0`**.

Suppose such a square exists and take a separating line. Orient its unit
normal n toward the middle square. Because `delta_0<pi/4`, the cited
pair theorem makes the line's offset a satisfy `|a|<1/2`. Every square
has directional halfwidth at least `1/2`, so the two center projections
on n have strictly opposite signs. Consequently

```text
n=(sin(beta),cos(beta)),       0<beta<delta,
gamma=delta-beta>0.                                      (2)
```

Both squares may now be moved radially outward, preserving their center
rays and frames, until they touch the circle of radius `3/sqrt(2)`.
This preserves containment in that larger disk: the greatest squared
vertex radius of a square with center `r e` is

```text
r^2+r w+1/2,        1<=w<=sqrt(2),
```

which is strictly increasing in r. It also preserves the chosen
separation: the positive center projection increases and the negative
one decreases, while both directional halfwidths remain fixed. Thus
it suffices to treat the common radius `R=3/sqrt(2)`. The original
separating line, still with `|a|<1/2`, remains available.

## 2. The middle square's frame reduces to two endpoint orientations

At this radius, the middle center is `(r(alpha),0)`, where

```text
w=cos(alpha)+sin(alpha),
r^2+w r=4,
r(alpha)=[sqrt(w^2+16)-w]/2.
```

Since `0<beta<delta_0<pi/4` and `0<=alpha<=pi/4`, the square's halfwidth
in direction n is

```text
h(alpha,beta)=[sin(beta+alpha)+cos(beta+alpha)]/2.
```

Its least projection on n is

```text
A(alpha,beta)=r(alpha)sin(beta)-h(alpha,beta).             (3)
```

This is strictly convex as a function of alpha. Indeed, put
`d=cos(alpha)-sin(alpha)` and `L=2r+w`. Implicit differentiation gives

```text
r'=-r d/L,
r''=[r w+2r d^2(L-r)/L^2]/L >0,
A''=r'' sin(beta)+h(alpha,beta)>0.                       (4)
```

Therefore its maximum on `[0,pi/4]` occurs at an endpoint:

```text
A(alpha,beta)<=max(A_0(beta),A_45(beta)),

A_0(beta)=(sqrt(17)/2-1)sin(beta)-cos(beta)/2,
A_45(beta)=sqrt(2)sin(beta)-cos(beta)/sqrt(2).             (5)
```

Both functions in (5) are strictly increasing for
`0<=beta<=delta_0`.

## 3. The other square's orientation is bounded by the reviewed cap lemma

Take positive coordinates along `-n` and along its rightward
perpendicular. The other center ray then has components
`(sin(gamma),cos(gamma))`. The square lies in the half-plane whose
first coordinate is at least `-a>-1/2`.

The cap-orientation theorem in Section 1 of the cited pair bound says
that if this square exists, then the axis-parallel square on the same
center ray whose first center coordinate is `-a+1/2` fits in the disk.
The maximum possible first center coordinate for such an axis-parallel
square is `r_axis(gamma)sin(gamma)`, where

```text
r_axis(gamma)^2
 +(sin(gamma)+cos(gamma))r_axis(gamma)=4.
```

It follows that

```text
-a <= B(gamma):=r_axis(gamma)sin(gamma)-1/2.
```

The middle square has least projection A at least a. Therefore the
necessary condition for the two squares is

```text
0<=A(alpha,beta)+B(gamma).                              (6)
```

The function B is strictly increasing for `0<=gamma<=pi/4`.
For example, differentiating the displayed equation for r_axis gives

```text
d[r_axis sin(gamma)]/d gamma
 =r_axis[2r_axis cos(gamma)+1]
      /[2r_axis+sin(gamma)+cos(gamma)] >0.
```

As `gamma=delta-beta<=delta_0-beta`, equations (5)--(6) would require

```text
max(A_0(beta),A_45(beta))+B(delta_0-beta)>=0.              (7)
```

## 4. A 24-row rational certificate contradicts that condition

Set `t=tan(beta)`, so `0<=t<=9/10`, and write

```text
z(t)=tan(delta_0-beta)=(9-10t)/(10+9t),

a_0(t)=[(sqrt(17)-2)t-1]/[2sqrt(1+t^2)],
a_45(t)=(2t-1)/sqrt(2+2t^2),
b(z)=z[sqrt(17z^2+2z+17)-1-z]/[2(1+z^2)]-1/2.
```

Here a_0 and a_45 are increasing, b is increasing, and z is decreasing.
For each row `i=0,...,23`, use the closed interval

```text
l_i=3i/80 <= t <= u_i=3(i+1)/80.
```

The three integers in that row certify

```text
a_0(u_i)<=U_0/10000,
a_45(u_i)<=U_45/10000,
b(z(l_i))<=U_B/10000.
```

Thus the final column divided by 10000 bounds the left side of (7)
throughout the entire interval. All entries are negative.

| i | U_0 | U_45 | U_B | max(U_0,U_45)+U_B |
| --- | ---: | ---: | ---: | ---: |
| 0 | -4598 | -6536 | 4465 | -133 |
| 1 | -4192 | -5993 | 4073 | -119 |
| 2 | -3781 | -5445 | 3672 | -109 |
| 3 | -3369 | -4894 | 3264 | -105 |
| 4 | -2958 | -4343 | 2850 | -108 |
| 5 | -2547 | -3794 | 2431 | -116 |
| 6 | -2140 | -3248 | 2010 | -130 |
| 7 | -1738 | -2709 | 1586 | -152 |
| 8 | -1342 | -2177 | 1161 | -181 |
| 9 | -954 | -1655 | 737 | -217 |
| 10 | -574 | -1143 | 314 | -260 |
| 11 | -203 | -644 | -106 | -309 |
| 12 | 158 | -158 | -522 | -364 |
| 13 | 508 | 314 | -934 | -426 |
| 14 | 847 | 771 | -1341 | -494 |
| 15 | 1175 | 1213 | -1742 | -529 |
| 16 | 1491 | 1640 | -2136 | -496 |
| 17 | 1795 | 2052 | -2522 | -470 |
| 18 | 2088 | 2448 | -2901 | -453 |
| 19 | 2370 | 2829 | -3272 | -443 |
| 20 | 2640 | 3195 | -3635 | -440 |
| 21 | 2899 | 3546 | -3989 | -443 |
| 22 | 3148 | 3883 | -4335 | -452 |
| 23 | 3385 | 4205 | -4672 | -467 |

These are rational upper bounds, not rounded numerical evaluations.
One exact way to verify every row is to bracket each positive radical
`sqrt(v)` between `k/10^8` and `(k+1)/10^8`, checking

```text
k^2 <= 10^16 v < (k+1)^2.
```

Use the upper radical in every positive numerator, and the lower
denominator for a nonnegative numerator or the upper denominator for
a negative numerator. Round the resulting rational upper bound upward
to a multiple of `1/10000`. This produces the displayed table. The
companion [exact verifier](check_loaded_three_ray_angle_bound.py) performs
only rational arithmetic and integer square checks, and also checks that
all printed rows agree with its recomputation. In particular the largest
certified bound is `-105/10000=-21/2000<0`.

The 24 intervals cover `[0,9/10]`, including every shared endpoint.
Consequently (7) is impossible. This proves the one-sided angular
exclusion, including `delta=delta_0`.

## 5. The three-ray bound

If either intervening angle is at least pi, their sum already exceeds
the right side of (1). Otherwise both are minor angles and the pair
theorem bounds each below by delta_*.

If both were at most delta_0, rotate to the middle center ray and make
the frame reflection used in Section 1. One neighbor is then on its
forbidden negative-angle side, a contradiction. Thus at least one
intervening angle is strictly larger than delta_0, and their sum exceeds
`delta_*+delta_0`.

For the convenient second bound in (1), the exact tangent identity is

```text
tan(delta_*)=(7+6sqrt(14))/35 >5/6,
```

since `sqrt(14)>133/36` (square both positive sides). Both angles are
in `(0,pi/2)`, so `delta_*>atan(5/6)`. The tangent addition identity gives

```text
atan(5/6)+atan(9/10)=pi/2-atan(15/104),
```

proving (1).

## 6. Consequence for the seven-loaded, one-D whole cycle

Consider the fixed word `LLLLLLLD`, ID `C20-M08-L07-B01-T02`, under the
selected-certificate and radial-order hypotheses of the reviewed cycle
classification. Its seven loaded rays occur in their cycle order. The
six direct loaded gaps form three consecutive pairs; apply (1) to each.
The remaining D gap exceeds

```text
pi-2atan(17/27),
```

by the exact D-cap comparison proved in
[STRONG_DIRECT_CYCLE_BUDGET.md](STRONG_DIRECT_CYCLE_BUDGET.md).

Put `x=atan(15/104)` and `y=atan(17/27)`. The sum of all seven angular
gaps therefore exceeds

```text
3(pi/2-x)+pi-2y=5pi/2-(3x+2y).
```

Here `0<3x<pi/2` and `0<2y<pi/2`: for the first, use
`atan(15/104)<15/104` and `45/104<1<pi/2`; the second follows from
`17/27<1`. Their tangent product is exactly

```text
tan(3x)tan(2y)
 = (483345/1054664)(459/220)
 = 44371071/46405216 <1.
```

Because both angles lie in `(0,pi/2)`, this implies `3x+2y<pi/2`.
The gap sum would exceed `2pi`, contradicting the circular order.
Thus this whole cycle is excluded.
No radial endpoint, load split, square orientation, or contact-slide
parameter has been omitted: the triple estimate uses only containment,
geometric circle loading, and interior disjointness.
