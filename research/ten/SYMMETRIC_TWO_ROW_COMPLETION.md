# Symmetric two-row cores with two small centers have capacity at most nine

Put

```text
Q=9/2, R=3/sqrt(2), r=sqrt(1+1/sqrt(2)).
```

Suppose a packing in the origin-centered disk of squared radius Q contains
four axis-parallel unit squares centered at

```text
(-1/2,-t), (1/2,-t), (-b,1-t), (b,1-t),
0<t<=sqrt(69)/20,
b>=1/2,
b^2+(1-t)^2<=1.
```

The lower centers therefore have norm at most `13/20`; the upper centers
have norm at most one. Then at most five additional squares fit, with
arbitrary independent orientations. This extends the smaller parameter
rectangle in [TWO_ROW_CORE_COMPLETION.md](TWO_ROW_CORE_COMPLETION.md).

These are hypotheses on a particular four-square core. No assertion is
made that every four-inner-center configuration has this form.

## 1. Preliminary geometry

The parameter bounds give `0<t<1/2` and `1/2<=b<1`. The lower squares fill

```text
[-1,1] x [-t-1/2,1/2-t],
```

and the upper squares have horizontal intervals
`[-b-1/2,-b+1/2]`, `[b-1/2,b+1/2]` and vertical interval
`[1/2-t,3/2-t]`. Write `z=3/2-t>1`.

Every point of the closed unit disk has distance strictly less than `1/2`
from the core. Below height `1/2-t`, its distance from the lower rectangle
is at most `1/2-t<1/2`. Above that height, its distance from the two upper
rectangles is at most `b-1/2<1/2`. Thus the inscribed radius-`1/2` disk of
an additional square excludes every additional center from the closed unit
disk.

Every additional center also has norm at most

```text
A=(sqrt(17)-1)/2<25/16.
```

By [CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md), each additional
square has one connected test-circle arc of angle at least `pi/4`.

The upper-right core square has a nonempty first-quadrant arc
`[alpha,beta]`, with

```text
0<alpha<pi/4<beta<=pi/2.                            (1)
```

Indeed its inward corner is inside the test circle and its outward corner
outside. Its lower endpoint is determined by `y=1/2-t` or `x=b+1/2`;
the former has angle below `pi/8`, while the latter, when active, has angle
at most `acos(1/r)<pi/4`. Its upper endpoint is determined by `y=z>1` or
`x=b-1/2<1/2`; either gives angle greater than `pi/4`.
The upper-left trace is `[pi-beta,pi-alpha]`.

## 2. If the lower squares cross the circle, five arcs are the maximum

Put `gamma=acos(1/r)`, so `pi/8<gamma<pi/4`.
If `1+(t+1/2)^2>r^2`, the right lower square has the fourth-quadrant arc

```text
[2pi-delta,2pi-gamma],
delta=asin((t+1/2)/r)>gamma.
```

The left lower trace is its reflection. The four complementary gaps have
angles

```text
pi-2beta,   alpha+gamma,   pi-2delta,   alpha+gamma.
```

By (1), the first, second, and fourth gaps are each strictly shorter than
`pi/2`, and the third is strictly shorter than `3pi/4`. They can therefore
hold at most `1+1+2+1=5` connected arcs of angle at least `pi/4`.

It remains to treat

```text
t<=2^(-1/4)-1/2,
z>=z_0=2-2^(-1/4).                                 (2)
```

Here the lower squares lie inside the test circle. Any isolated tangencies
can be ignored to enlarge the available gaps.

## 3. Six additional arcs force a small upper gap

There are now only two relevant gaps, with angles

```text
G_top=pi-2beta<pi/2,
G_bottom=pi+2alpha<3pi/2.
```

If six additional squares existed, exactly one arc would have to use the
upper gap and five the lower. In particular

```text
beta<=3pi/8,
alpha>=pi/8.                                       (3)
```

The lower endpoint cannot be determined by `y=1/2-t`, whose angle is
strictly below `pi/8`. Therefore (3) implies

```text
b+1/2<=r cos(pi/8),
b<=1/sqrt(2).                                      (4)
```

The upper endpoint cannot be determined by `x=b-1/2`: since `b<1`, that
angle is strictly greater than `acos((1/2)/r)=3pi/8`. Consequently

```text
z<=H=(1+sqrt(2))/2,
beta=asin(z/r).                                    (5)
```

We exclude every physical square using this upper gap under (2), (4),
and (5).

## 4. Such a square has a horizontal chord longer than 43/100

Let S be an additional square using the upper gap, with center `(x_c,y_c)`
and norm u. As in Section 3 of
[TWO_ROW_CORE_COMPLETION.md](TWO_ROW_CORE_COMPLETION.md), the radial point
`r(x_c,y_c)/u` is strictly inside S, because `1<u<25/16` gives
`|r-u|<1/2`. Thus its center's polar angle belongs to the same gap, and

```text
y_c>=z/r,
|x_c|<=A sqrt(1-z^2/r^2).                           (6)
```

The following elementary rational bounds provide convenient strict
horizontal control:

```text
A<25/16,
r^2<239/140,
z>=z_0>1159/1000,
sqrt(2)/2<177/250.
```

For the second bound use `1/sqrt(2)<99/140`; for the third use
`841^4=500246412961>500000000000`, so `2^(-1/4)<841/1000`.
Equation (6) then gives

```text
x_c^2 < (25/16)^2[1-(1159/1000)^2/(239/140)]
      = 2547033/4894720
      < (361/500)^2.
```

The difference in the last comparison is
`14081939/15296000000>0`. Adding the unit square's horizontal half-width
shows that its entire horizontal extent lies strictly inside

```text
(-143/100,143/100).                                (7)
```

Let m and M be its minimum and maximum heights, and let `w=c+s` be its
vertical width, with `c>=s>=0` and `c^2+s^2=1`. Since `m<=R-1<9/8<z`,
the horizontal line at height z is above its bottom. From (5)--(6),

```text
2(M-z) >= 2(y_c+1/2-z)
       > 1-2z(1-1/r)
      >= 1-2H(1-1/r)
       = sqrt(2+sqrt(2))-sqrt(2)
       > 43/100.                                  (8)
```

The first strict inequality uses `u>1` in the radial center estimate.
For the last one, squaring positive sides reduces it to
`(7/50)sqrt(2)>1849/10000`, which follows from `sqrt(2)>7/5`.
In particular `M>z`, so the line crosses the square's interior.

Also `z>23/20` and `R<17/8` give

```text
z-m>=z-R+w>w-39/40>(43/100)cs.                     (9)
```

The last inequality holds for all `1<=w<=sqrt(2)`: after subtraction,
using `cs=(w^2-1)/2`, it is a concave quadratic in w whose endpoint values
are `1/40` and `sqrt(2)-119/100`, both positive.

For a non-axis square the horizontal chord length at height z is

```text
min(1/c, (z-m)/(cs), (M-z)/(cs)).
```

Its first term is at least one; the second exceeds `43/100` by (9), and
the third does so by (8) and `cs<=1/2`. The axis-parallel chord has length
one. Thus in every case this chord has length strictly greater than
`43/100`.

At height z the upper core edges occupy
`[-b-1/2,-b+1/2]` and `[b-1/2,b+1/2]`. Inside the interval in (7), each
outer free component has length at most `43/100`, since `b>=1/2`. The
middle component has length

```text
2b-1<=sqrt(2)-1<43/100
```

by (4). None can contain the chord just proved. An interior point of S on
a core boundary would force overlapping square interiors locally, so S
cannot cross either core edge instead. This contradiction excludes S.

Six additional squares are therefore impossible in the case (2) as well.
Together with Section 2, this proves total capacity at most nine over the
whole stated symmetric two-row family.
