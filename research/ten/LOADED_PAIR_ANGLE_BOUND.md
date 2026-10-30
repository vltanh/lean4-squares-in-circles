# A stronger angular separation for any two loaded squares

**Status:** hand theorem; root and independent full mathematical reviews
passed on 2026-10-29, including the unbounded slope range, strict cap
offset boundary, and larger-offset loaded-center argument. No finite
case status is changed by this manuscript alone.

Let two interior-disjoint unit squares lie in the centered disk of radius
`79/40<=R<=3/sqrt(2)`, with each square having a vertex on the circle.
Let delta be the minor angle between their center rays.

**Theorem.**

```text
delta >= delta_* := 2 atan(1/(sqrt(14)-1)) > acos(7/9).
```

The explicit constant is approximately forty degrees; no numerical value
is used below. The proof improves the orientation reduction in
[TRANSMISSION_CAP_ANGLE_BOUND.md](TRANSMISSION_CAP_ANGLE_BOUND.md) to every
cap offset strictly above `-1/2`. Separators at larger absolute offsets
are treated separately using the loaded-center lower bound.

## 1. Extend the single-cap orientation reduction to a>-1/2

Suppose a unit square K is contained in the disk and in `x>=a`, where
`a>-1/2`. Its center has positive first coordinate, since every unit
square has horizontal halfwidth at least one half. After reflection,
write the center ray as `(1,t)` with `t>=0`.

We claim exactly the same cap inequality as before:

```text
t <= [sqrt(R^2-(a+1)^2)-1/2]/(a+1/2).                 (1)
```

In particular, existence implies that the radical is defined and its
numerator is nonnegative. For `a>=0`, the proof in Section 1 of the cited
cap theorem already applies, without using its lower-offset estimates.
It remains to prove (1) for `-1/2<a<0`.

If `0<=t<=1`, the axis-parallel square centered at
`(a+1/2,t(a+1/2))` has farthest squared vertex norm at most
`2(a+1)^2<=2<R^2`. It is therefore contained in the disk, which gives
(1) directly. Hence assume t>1.

Use the support-function formulas from the earlier cap proof:

```text
0<=theta<=pi/4,
c=cos(theta), s=sin(theta), w=c+s, d=c-s,
rho=sqrt(1+t^2), h=w/2, x=a+h>0.
```

For this orientation, the least possible squared farthest-vertex radius
on the specified center ray, taking the better of its two chiralities,
is

```text
F(theta)=rho^2 x^2+1/2+x ell(theta),

ell=w+t d,       0<=theta<=theta_0:=atan(1/t),
ell=t w-d,       theta_0<=theta<=pi/4.                (2)
```

The actual center can lie farther along the ray, which only increases
the farthest squared radius because x>0 and ell>0. After theta_0, both
h and ell increase, so F is nondecreasing there. We show that the
minimum before theta_0 is attained at zero.

### 1a. All t>=2: F increases before the switch

Differentiating the first branch of (2) gives

```text
F'=x[(t^2+2)d-t w]+d ell/2.                           (3)
```

For `0<=theta<=atan(1/t)`,

```text
(t^2+2)d-t w
 =c[(t^2-t+2)-(t^2+t+2)tan(theta)]
 >=c[(t-1)^2-2/t] >=0,
```

since the last bracket is zero at t=2 and increases thereafter.
Every other factor in (3) is nonnegative, so F is nondecreasing.
Thus its minimum is F(0). This proof is uniform for arbitrarily large
t; no bound depending on `1/(a+1/2)` is used.

### 1b. The compact range 1<t<2: F is concave before the switch

The differentiated expression from the cap proof is

```text
F''=-a D-G,
D=(t^2+2)w+t d>0,
G=(t^2+3)sin(2theta)+2t cos(2theta).
```

We prove `G/D>=1/2`. Put `z=tan(theta)`, so `0<=z<=1/t`, and write

```text
G/D=2[-t z^2+(t^2+3)z+t]
       /[sqrt(1+z^2)((t^2+t+2)+(t^2-t+2)z)].           (4)
```

The sign of the derivative in z is the sign of

```text
N(z)=t^4+6t^2+t+6
     -3t(t^2+t+2)z
     -3t(t^2-t+2)z^2
     -(t^4+6t^2-t+6)z^3.                             (5)
```

All three nonconstant coefficients are negative for t>=1, and the
constant is positive. Therefore N is strictly decreasing for z>=0.
The ratio (4) either increases throughout the interval or first
increases and then decreases. Its minimum is consequently at an
endpoint. At those endpoints its values are

```text
2t/(t^2+t+2) >= 1/2,
4t/[(t+2)sqrt(t^2+1)] > 1/2.                         (6)
```

The first inequality is equivalent to `(t-1)(t-2)<=0`. For the second,
use `sqrt(t^2+1)<t+1` and
`(t+2)(t+1)<8t` on `[1,2]`; the latter is the elementary inequality
`t^2-5t+2<0`, whose convex quadratic has negative values at both
endpoints. This proves `G/D>=1/2`.

Because `-a<1/2`, it follows that `F''<0`. Its minimum on the first
branch is therefore at zero or theta_0. The already expanded endpoint
identity is

```text
F(theta_0)-F(0)=a B_t+t/2,
B_t=sqrt(1+t^2)(t+2)-(t^2+t+2),
0<B_t<t.                                             (7)
```

For completeness, the two strict comparisons in (7) follow by squaring
positive quantities:

```text
(1+t^2)(t+2)^2-(t^2+t+2)^2=2t^3>0,
(t^2+2t+2)^2-(1+t^2)(t+2)^2=3t^2+4t>0.
```

Thus `a B_t+t/2>(t-B_t)/2>0`. The minimum is again F(0).

All cases are covered. Consequently the axis-parallel square centered
at `(a+1/2,t(a+1/2))` is contained in the disk whenever K is. Its farthest
vertex gives

```text
(a+1)^2+[t(a+1/2)+1/2]^2<=R^2,
```

which proves (1). The argument uses only the strict domain a>-1/2;
the boundary a=-1/2 is not obtained by dividing by a vanishing quantity.

## 2. Separators with absolute offset below one half

Take any separating line for the two squares and rotate it to `x=a`,
with one square in `x<=a` and the other in `x>=a`. Such a line exists by
convex separation, whether or not the squares touch. Suppose first that
`|a|<1/2`. Their centers have strictly opposite horizontal coordinates.

Define, on its relevant domain,

```text
Theta_R(b)=atan([sqrt(R^2-(b+1)^2)-1/2]/(b+1/2)),
b>-1/2,
sqrt(R^2-(b+1)^2)-1/2>=0.
```

Section 2 of the earlier cap theorem proves that this function is
strictly concave on precisely this domain: its proof uses only
`x=b+1/2>0`, `y>=0`, and
`x^2+y^2>1/2`, the last following from `R-1/sqrt(2)>1`.
It places no additional lower bound on b. Thus that concavity applies
to the enlarged interval of Section 1.

The two cap inequalities give angular deviations from the negative and
positive horizontal rays at most `Theta_R(-a)` and `Theta_R(a)`.
Irrespective of the signs of their vertical coordinates,

```text
delta >= pi-Theta_R(-a)-Theta_R(a)
      >= pi-2Theta_R(0)
      =2 atan(1/(2sqrt(R^2-1)-1))
      >=2 atan(1/(sqrt(14)-1))=delta_*.                (8)
```

Existence of the two squares places both endpoints of the Jensen
comparison in the relevant interval; its midpoint zero is there as
well. The last inequality in (8) uses `R^2<=9/2`.

## 3. Separators farther from zero force at least forty-five degrees

Now `|a|>=1/2`. Reflect horizontally if necessary so `a>=1/2`.
Every unit square has horizontal width at least one, so containment of
the square in `x>=a` gives `a<=R-1<9/8`. Put

```text
z=a-1/2,       0<=z<5/8.
```

The left center has first coordinate at most z. Since that square is
loaded, its center norm exceeds `5/4`, as proved in
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md), Section 1.
Its minor angular distance beta from the positive horizontal ray
therefore satisfies

```text
beta >= acos(4z/5)=pi/2-asin(4z/5).                   (9)
```

This remains true if its horizontal coordinate is negative.
The right center's minor angular distance alpha from that ray is at most
`Theta_R(a)`. This is no larger than `Theta_{3/sqrt(2)}(a)`, because its
formula increases with R. At b=1/2 the latter function has value pi/4
and derivative -1. Its concavity therefore supplies the tangent bound

```text
alpha <= pi/4-z.                                     (10)
```

The circular angular triangle inequality gives `delta>=beta-alpha`.
Combining (9)--(10),

```text
delta >= pi/4+z-asin(4z/5) >= pi/4.                   (11)
```

For the last comparison, the function `z-asin(4z/5)` is zero at zero
and has positive derivative on `[0,5/8]`, since

```text
(4/5)/sqrt(1-16z^2/25) <= 8/(5sqrt(3)) < 1,
64<75.
```

Finally `delta_*<pi/4`: this is equivalent to
`sqrt(14)>2+sqrt(2)`, whose square reduces to `2>sqrt(2)`.
Thus (11) is stronger than the required bound. It also covers
`a=1/2` exactly, so no boundary case was omitted in Section 2.

## 4. A convenient exact comparison

The cosine of the proved constant is

```text
cos(delta_*)=(7-sqrt(14))/(8-sqrt(14))<7/9.
```

The strict comparison is equivalent to `7<2sqrt(14)`, with squared
check `49<56`. Since cosine decreases on `[0,pi]`,
`delta>=delta_*>acos(7/9)`, completing the theorem.

The proof requires loading only for the left-center lower bound in
Section 3. It does not claim the same separation for arbitrary two
squares whose centers are inside the unit disk, and it does not assume
parallel square frames or any restriction on the contact ownership.
