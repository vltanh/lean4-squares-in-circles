# A cap bound sharpens every transmission angle

**Status:** exact hand theorem; two independent full mathematical reviews
passed on 2026-10-29, including arbitrary orientations, negative cap offsets,
boundary cases, and all exact inequalities. Numerical exploration suggested
the bound but is not a premise of the argument below. Its finite-cycle
consequence is recorded in
[SHARP_TRANSMISSION_CYCLE_BUDGET.md](SHARP_TRANSMISSION_CYCLE_BUDGET.md).

Let two unit squares lie in the centered disk of radius R, where
`79/40<=R<=3/sqrt(2)`. Suppose parallel supporting lines separate them by
a distance `W>=1`. Let delta be the minor angle between their center rays.
Then

```text
delta >= pi-2 atan((sqrt(R^2-(W+2)^2/4)-1/2)/((W+1)/2)).       (1)
```

Existence of the two squares implies that the radical is defined and its
displayed numerator is nonnegative. In particular, for the three possible
transmission widths, a strictly subcritical packing satisfies

```text
S (W=1):       delta>pi/2,
D (W=sqrt(2)): delta>3pi/5,
SS (W=2):      delta>9pi/10.                             (2)
```

This theorem needs containment and the separating strip, not positive
circle loads. Transmission paths supply the strip by the distance theorem
in [CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md).

## 1. Reducing one cap to an axis-parallel square

Consider a unit square K contained in the disk and in `x>=a`, where
`a>=-1/8`. Its center has first coordinate at least `a+1/2>=3/8`.
Reflect in the horizontal axis if needed so its center is `(x,t x)`,
with `t>=0`. We claim

```text
t <= [sqrt(R^2-(a+1)^2)-1/2]/(a+1/2).                  (3)
```

The universal center bound `|center|<25/16` gives `t<25/6`.
If `a<0` and `t<=1`, the axis-parallel square centered at
`(a+1/2,t(a+1/2))` has farthest squared vertex norm at most
`2(a+1)^2<=2<R^2`, proving (3) immediately. We may henceforth assume
either `a>=0`, or `a<0` and `1<t<25/6`.

Write an unsigned square-frame angle as `0<=theta<=pi/4` and put

```text
c=cos(theta), s=sin(theta), w=c+s, d=c-s,
rho=sqrt(1+t^2), h=w/2.
```

The horizontal halfwidth is h. The smallest possible farthest squared
vertex norm on this fixed center ray is obtained at `x=a+h`, since the
farthest norm increases with positive x. Of the two frame chiralities,
the smaller farthest norm is

```text
F(theta)=rho^2(a+h)^2+1/2+(a+h) ell(theta),             (4)
```

where the explicit support-function calculation gives

```text
t>=1:
  ell=w+t d,   0<=theta<=atan(1/t),
  ell=t w-d,   atan(1/t)<=theta<=pi/4;

0<=t<=1:
  ell=t w+d,   0<=theta<=atan(t),
  ell=w-t d,   atan(t)<=theta<=pi/4.                   (5)
```

For example, the two possible unscaled support sums are
`|c+t s|+|t c-s|` and `|c-t s|+|t c+s|`; taking their minimum gives (5).

After the switch angle in (5), both h and ell are nondecreasing, with
ell strictly increasing for t>0. Thus F cannot have a smaller value
there than at the switch. Before the switch, direct differentiation gives

```text
t>=1:
F''=-a[(t^2+2)w+t d]-(t^2+3)sin(2theta)-2t cos(2theta);

0<=t<=1:
F''=-a[(t^2+t+1)w+d]-(t+1)^2 sin(2theta)-2cos(2theta). (6)
```

These are negative when `a>=0` except for harmless endpoint limits.
For `-1/8<=a<0` only the first row is needed. The positive function

```text
G(theta)=(t^2+3)sin(2theta)+2t cos(2theta)
```

is concave on the interval from zero to `atan(1/t)`, and its endpoint
values are `2t` and `4t`; hence `G>=2t`. Using `w<=sqrt(2)<3/2`,
`d<=1`, and `1<=t<=25/6`, the first row of (6) gives

```text
F'' <= [(3/2)(t^2+2)+t]/8-2t < 0.
```

Indeed `t+2/t<=25/6+2=37/6`, so
`(3/2)(t^2+2)<=37t/4<15t`. Thus F is concave before the switch in
every needed case; its minimum occurs at zero or at the switch.

At zero the square is axis-parallel. At the switch, its center ray is
normal to a side. Subtracting the two values gives

```text
F(switch)-F(0)=a B_t+t/2,
B_t=rho(t+2)-(t^2+t+2).                              (7)
```

For `t>0`, one has `0<B_t<t`. Both comparisons follow by squaring
positive sides:

```text
rho^2(t+2)^2-(t^2+t+2)^2=2t^3>0,
(t^2+2t+2)^2-rho^2(t+2)^2=3t^2+4t>0.
```

Since `a>=-1/8`, equation (7) is positive. The case t=0 has its switch
at zero. Consequently `F(theta)>=F(0)` for every orientation.

The actual square is contained in the disk, so the axis-parallel square
centered at `(a+1/2,t(a+1/2))` is contained too. Its farthest vertex gives

```text
(a+1)^2+[t(a+1/2)+1/2]^2<=R^2,
```

which proves (3), including nonnegativity of its right-hand numerator.

## 2. The cap's maximum center angle is concave in its offset

Define

```text
Theta(a)=atan(y/x),
x=a+1/2,       y=sqrt(R^2-(a+1)^2)-1/2.
```

Its relevant domain has `x>0,y>=0`. Write

```text
U=x+1/2, V=y+1/2, r^2=x^2+y^2,
N=r^2+(x+y)/2.
```

The boundary point `(U,V)` has norm R, so
`r>=R-1/sqrt(2)>1`; in particular `r^2>1/2`.
Differentiation with respect to x (equivalently a) gives

```text
y'=-U/V,
(r^2)'=(x-y)/V,
N'=(x-y)/(2V),
Theta'=-N/(V r^2).
```

The sign of `Theta''` is the sign of

```text
H=(V/2)(x-y)(r^2+x+y)-N U r^2.                       (8)
```

If `x<=y`, this is negative. If `x>=y`, use `V<=U` to obtain

```text
H <= (U/2)[-2y r^2+(x^2-y^2)-2r^4]
  <= (U/2)r^2(1-2r^2)<0.
```

Thus Theta is strictly concave on its relevant domain.

## 3. Apply the cap lemma to the two endpoint squares

Orient the common support normal horizontally. The two squares lie in

```text
x>=a,       x<=-b,       a+b=W.
```

Every unit square has projection width at least one. Disk containment
therefore gives `a,b<=R-1`, hence

```text
a,b>=W+1-R>=2-R>-1/8,
```

using `R<=3/sqrt(2)<17/8`.
Their centers have opposite nonzero horizontal coordinates. After
independently reflecting their vertical coordinates for the purpose of
bounding angles, Section 1 bounds the angular heights above their
respective horizontal rays by `Theta(a)` and `Theta(b)`.

The minor angle between the two actual center rays is at least
`pi-Theta(a)-Theta(b)`, whether their vertical coordinates have the same
or opposite signs. By concavity and `a+b=W`,

```text
delta >= pi-Theta(a)-Theta(b)
      >= pi-2Theta(W/2).
```

This is (1). Existence of the squares puts both a,b in the interval where
Theta is defined with nonnegative y, and hence puts their midpoint there
too. This justifies all radicals in (1).

## 4. Simple exact bounds for the three transmitter types

The right side of (1) decreases as R increases. For W=1 at
`R=3/sqrt(2)`, the midpoint cap center is `(1,1)`, so the right side is
exactly `pi/2`; it is strictly larger when R is smaller.

For W=sqrt(2), the midpoint cap center at the largest radius is

```text
x=(1+sqrt(2))/2,       y=sqrt(3-sqrt(2))-1/2.
```

Here `y/x<2/3`: after squaring positive sides the inequality reduces
to `75/56<sqrt(2)`, which follows from `sqrt(2)>7/5`.
Also `tan(pi/5)>2/3`, since

```text
tan(pi/5)^2=(5-sqrt(5))/(3+sqrt(5))>4/9
```

is equivalent to `33>13sqrt(5)`, whose squared check is `1089>845`.
Thus `Theta(W/2)<pi/5`, giving `delta>3pi/5`.

For W=2, the midpoint cap center at the largest radius is

```text
x=3/2,       y=(sqrt(2)-1)/2,
y/x=(sqrt(2)-1)/3<3/20<pi/20.
```

The rational comparison uses `sqrt(2)<29/20`; the last uses `pi>3`.
Since `atan(z)<z` for z>0, one has `Theta(W/2)<pi/20`, hence
`delta>9pi/10`. This proves (2).

These improved transmission bounds give the reviewed
[234-case radial-order cycle budget](SHARP_TRANSMISSION_CYCLE_BUDGET.md).
No claim about an ordinary direct-contact gap exceeding 45 degrees is made:
that stronger assertion is false even for parallel loaded squares.
