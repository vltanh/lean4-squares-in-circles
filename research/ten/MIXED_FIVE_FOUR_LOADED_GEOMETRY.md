# The diagonal transmitter in a four-loaded five-cycle contains zero

Independent mathematical review passed on 2026-10-29; this is not Lean verification.

Consider the physical positive component

```text
U-A_1-A_2-A_3-A_4-U,
```

with precisely the four A bodies circle-loaded. Use the radius window
`5/2+sqrt(2)<R^2<=9/2` and its explicitly imported n=8 dependency as in
[MIXED_FIVE_FOUR_LOADED.md](MIXED_FIVE_FOUR_LOADED.md). That theorem
already forces U to be a diagonal transmitter.

**Theorem.** The origin lies in the interior of U. Its center moreover
satisfies

```text
|c_U|^2 < [1-(R-sqrt(2))^2]/2 < 9/25.
```

This localizes the one remaining transmitter in this component type.
It does not exclude the component or bound the capacity of its complement.

## 1. A positive transmission chord completes one angular turn

Use the cyclic loaded-center lifts from Section 2 of
[MIXED_FIVE_FOUR_LOADED.md](MIXED_FIVE_FOUR_LOADED.md):

```text
phi_1<phi_2<phi_3<phi_4<phi_1+2pi,
pi/5<phi_(i+1)-phi_i<2pi/5,
3pi/5<phi_4-phi_1<6pi/5.
```

Let `q_0` be the actual pair-force application point U--A_1, let `q_4`
be A_4--U, and let `q_i` be A_i--A_(i+1), for `i=1,2,3`.
Every point of a loaded square has angular deviation less than `pi/5`
from its center ray, by Section 3 of
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md).
Thus the loaded-loaded contacts have lifts

```text
phi_i<arg(q_i)<phi_(i+1).                              (1)
```

Orient each force `f_i` in the cycle direction U,A_1,A_2,A_3,A_4,U.
Circle forces have zero torque about zero, so torque balance on every
body gives the common value

```text
tau=q_i cross f_i       (i=0,...,4).                    (2)
```

This value is positive. At a loaded-loaded contact, put
`e=q_i/|q_i|`, let t be its counterclockwise unit tangent, and set
`D=c_(i+1)-c_i`. Equation (1) gives `t dot D>0`. The two radial center
projections lie in `(1,25/16)`: their radii exceed `5/4` and their
angular deviations are below `pi/5`, whose cosine exceeds `4/5`.
Hence `|e dot D|<9/16`. The actual supporting normal
`n_i=f_i/|f_i|` satisfies `n_i dot D>=1`, since unit-square halfwidths
are at least `1/2`. If `t dot n_i<=0`, the radial-tangential decomposition
would instead give `n_i dot D<9/16`. Thus `q_i cross n_i>0`, proving
the strict sign in (2). This is the local argument of Section 1 of
[SEVEN_RING_FORCE_CIRCULATION.md](SEVEN_RING_FORCE_CIRCULATION.md);
no all-loaded-component hypothesis is needed for that individual edge.

U's opposite equal forces give `f_4=f_0=mu*n`, with `mu>0`, and the
diagonal transmission formula is

```text
q_0-q_4=sqrt(2)*n.
```

The straight chord from `q_4` to `q_0` has positive origin torque by
(2). Its continuous angular increment is therefore some
`gamma in (0,pi)`.

Lift `arg(q_0)` within `pi/5` of `phi_1` and `arg(q_4)` within `pi/5`
of `phi_4`. The lifts at the intervening shared contacts agree by (1).
The polygonal path `q_0,q_1,q_2,q_3,q_4` lies successively in the four
loaded squares and has net angular increment

```text
Delta=arg(q_4)-arg(q_0),       pi/5<Delta<8pi/5.
```

Each segment avoids zero and stays within its loaded square's angular
interval. Since `0<Delta<2pi`, the positive closing increment satisfies
`gamma=2pi-Delta`.

Every loaded square has viewing width strictly less than `pi/3`, by
Section 5 of [ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md).
Each of the four path increments has absolute value below that width.
Consequently

```text
Delta<4pi/3,
2pi/3<gamma<pi.                                       (3)
```

This proves the angular statement without assuming that a physical
Jordan ring avoids or surrounds zero.

## 2. The center is within radius three fifths

Let the radii of the two chord endpoints be r,s. Each point belongs to
a loaded square, and comparison with that square's circle vertex gives

```text
r,s>=R-sqrt(2).
```

The diagonal transmitter's center is their midpoint. Since the chord
length is `sqrt(2)`, elementary midpoint and cosine identities give

```text
|c_U|^2=1/2+r*s*cos(gamma)
       <1/2-r*s/2
       <=[1-(R-sqrt(2))^2]/2,
```

using (3). The older radius window `R>=79/40` and `sqrt(2)<57/40`
give `R-sqrt(2)>11/20`. Thus

```text
|c_U|^2<1/2-(11/20)^2/2=279/800<9/25.
```

## 3. Zero cannot be outside or on the transmitter

Use coordinates along and perpendicular to the transmission direction.
Write `c_U=(m,h)`, put `a=|m|`, `b=|h|`, and put `k=1/sqrt(2)`.
The transmitter's vertices are `c_U+(-k,0)`, `c_U+(k,0)`, and
`c_U+(0,+-k)`. Its interior contains zero exactly when

```text
a+b<k.
```

The chord has positive torque, so `b>0`. Its endpoint dot product is
`a^2+b^2-k^2`, and the absolute cross product is `2*k*b`. By (3),
the chord's angle has cotangent less than `-1/sqrt(3)`. Hence

```text
a^2+b^2+(2*k/sqrt(3))*b<k^2.                           (4)
```

Suppose instead `a+b>=k`. Equation (4) gives `b<k`, so `a>=k-b`.
Substituting that lower bound into (4) yields

```text
0<b<ell:=k*(1-1/sqrt(3)).                              (5)
```

The nearer of the two transmission endpoints has squared norm
`(a-k)^2+b^2`. Using (4) and `a>=k-b`,

```text
(a-k)^2+b^2
 <2*k^2-(2*k/sqrt(3))*b-2*k*a
 <=2*k*(1-1/sqrt(3))*b
 =2*ell*b
 <2*ell^2=(1-1/sqrt(3))^2<1/4.
```

It would therefore have norm less than `1/2`. But it belongs to a loaded
square, whose every point has norm at least `R-sqrt(2)>11/20`.
This contradiction proves `a+b<k`, so zero is strictly inside U.

The theorem is a hand consequence of the stated local geometric and
physical-stress lemmas. Lean formalization and kernel verification have
not been performed. The remaining diagonal component still requires an
exclusion or a completion-capacity bound.
