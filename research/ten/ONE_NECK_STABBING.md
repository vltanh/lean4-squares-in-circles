# Two interior stabbing points for the one-unit neck

**Status:** complete hand proof, with independently audited geometric and
algebraic branches. No Lean verification is claimed.

Let `D` be the origin-centered disk of squared radius `17/4`. A candidate
square is a closed unit square contained in `D` and in `y>=0`, and
interior-disjoint from the three axis-parallel squares centered at

```text
(-3/2,0), (-1/2,0), (3/2,0).
```

The stabbing points are

```text
P = (27/64,255/256),       Q = (-27/64,5/4).
```

**Interior-stabbing theorem.** Every candidate square contains `P` or `Q`
in its **interior**. Consequently at most two candidate squares can be
mutually interior-disjoint. This proves the smaller upper-region capacity
bound used in
[STAGGERED_CHAIN_REDUCTION.md](STAGGERED_CHAIN_REDUCTION.md).

## The neck below height one half

At every height strictly between `0` and `1/2`, the obstacles occupy
`[-2,0]` and `[1,2]`. Their outer corners `(+-2,1/2)` lie on the containing
circle. The two side caps `x>2` and `x<-2` are separate components of the
free region, each of horizontal width less than one. A candidate square
cannot have its connected interior in either cap. Consequently every part
of its interior below `y=1/2` lies in the neck `0<x<1`.

A non-axis square cannot have a maximal horizontal chord at any height
strictly between `0` and `1/2`: that chord has length greater than one.
This includes the limiting possibility that the chord is at the endpoint
of its maximal-chord interval. Thus, if a non-axis candidate has minimum
height `m<1/2`, only its lowest corner lies below that line. Its chord at
`y=1/2` lies in `[0,1]`.

For positive tilt, write its orthonormal side directions as

```text
u = (c,s),       v = (-s,c),
0 < s <= c,     c^2+s^2 = 1.
```

Let its lowest vertex be `B=(b,m)`, and put `d=1/2-m>0`. The square is
`B+[0,1]u+[0,1]v`. At height `1/2`, the chord endpoints are

```text
b-(s/c)d,       b+(c/s)d.
```

The neck condition therefore gives

```text
(s/c)d <= b <= 1-(c/s)d,        0<d<=cs.             (1)
```

The condition `m>=0` additionally gives `d<=1/2`, already implied by
`d<=cs`. In center coordinates, with `h=(c+s)/2` and `t=(c-s)/2`, this is

```text
y = 1/2+h-d,
t+(s/c)d <= x <= 1+t-(c/s)d.
```

For negative tilt the reflected formulas are

```text
y = 1/2+h-d,
-t+(c/s)d <= x <= 1-t-(s/c)d,
0<d<=cs.
```

These formulas retain the original disk center; reflection of the neck
about `x=1/2` is not a symmetry of that disk.

## Low axis-parallel squares contain P

If an axis-parallel candidate has minimum height `0<=m<1/2`, its unit
horizontal chord below `1/2` must fill the neck. It is therefore exactly

```text
[0,1] x [m,m+1].
```

Both coordinates of `P` lie strictly between the corresponding endpoints,
so `P` belongs to its interior.

## Low positive-tilt squares contain P

Put

```text
p=27/64,       r=255/256,       e=r-1/2=127/256.
```

The own-frame coordinates of `P-B` are

```text
alpha = c(p-b)+s(e+d),
beta  = -s(p-b)+c(e+d).
```

Membership in the square's interior is equivalent to
`0<alpha<1` and `0<beta<1`. Three of these inequalities follow directly
from (1):

```text
alpha <= cp+se < (c+s)/2 < 1,
beta >= ce-sp+d/c >= c(e-p) > 0,
beta <= s(1-p)+ce <= sqrt((1-p)^2+e^2) < 1.
```

Here `c>=s`, `e>p`, and the last squared radical is `38033/65536<1`.
The strict bound `(c+s)/2<1` follows from `c+s<=sqrt(2)`.

Suppose the remaining inequality failed, so `alpha<=0`. Let `V=B+u+v`
be the opposite, highest vertex. Then

```text
u dot V >= 1+u dot P = 1+pc+rs.                    (2)
```

The right endpoint condition in (1) also implies

```text
v dot B = -sb+c(1/2-d) >= c/2-s.
```

Geometrically this is the supporting-edge inequality imposed by the
right obstacle corner `(1,1/2)`. Consequently

```text
v dot V >= 1+c/2-s.                               (3)
```

Both right sides in (2)–(3) are positive. Orthogonality gives

```text
|V|^2 >= (1+pc+rs)^2+(1+c/2-s)^2 > 17/4,           (4)
```

contradicting containment in `D`. Here is a complete exact check of the
strict inequality in (4). Set `z=tan(theta/2)`, so

```text
c=(1-z^2)/(1+z^2),   s=2z/(1+z^2),
0<z<=sqrt(2)-1<1/2.
```

Direct expansion gives

```text
(1+pc+rs)^2+(1+c/2-s)^2-17/4
  = [356-5484z+42809z^2+4972z^3-60060z^4]
      / [16384(1+z^2)^2].
```

Since `0<=z<=1/2`, its numerator is at least

```text
356-5484z+27794z^2.
```

This quadratic is strictly positive on the whole real line: its leading
coefficient is positive and

```text
4*356*27794-5484^2 = 9504400 > 0.
```

Thus `alpha>0`, completing the proof that every low positive-tilt candidate
contains `P` in its interior. The rational expansion is an algebraic
identity; no numerical optimization is a premise of the argument.

## Low negative-tilt squares contain P or Q

The complete proof is in
[ONE_NECK_NEGATIVE_TILT.md](ONE_NECK_NEGATIVE_TILT.md). It uses exactly the
reflected neck inequalities above, together with the same containing disk.
It proves strict interior membership in one of `P,Q`; boundary membership
is not used as a substitute. That argument has received an independent
line-by-line mathematical audit.

## Squares wholly in the upper cap

The complete proof for a square wholly in `y>=1/2` is in
[ONE_NECK_CAP_STABBING.md](ONE_NECK_CAP_STABBING.md), with its two auxiliary
side-face estimates in
[ONE_NECK_CAP_SIDE_FACES.md](ONE_NECK_CAP_SIDE_FACES.md). It allows either
tilt sign and proves strict interior membership in `P` or `Q`. The
six-region case split, the geometric inequalities, and the displayed
positive-polynomial certificates have each received an independent audit.

These cases cover every candidate square: either its minimum height is at
least `1/2`, or it is a low axis-parallel square, or it is a low tilted
square of one of the two signs. Every case supplies an interior stabbing
point. Three mutually interior-disjoint candidates would assign two of
their interiors to the same one of the two points, a contradiction. This
proves the stated capacity bound.

## Consequence for a staggered chain

Consider the four-square chain with parameters `t1,t2` from the linked
staggered-chain note. If `t1>=0`, the left inner square contains
`[-1,0] x [0,1/2]`. Every additional upper square is consequently a
candidate for the present theorem, and there are at most two of them.
Horizontal reflection gives the same conclusion if `t2>=0`.

Thus three or more additional upper squares require `t1<0` and `t2<0`.
Vertical reflection shows that three or more additional lower squares
require `t1>0` and `t2>0`. The completed
[wide-neck three-point theorem](WIDE_NECK_THREE_POINT_STABBING.md) separately
bounds both groups by three, excluding `4+2` and `2+4` splits. The sign
conditions exclude the remaining `3+3` possibility. Equivalently, the sign
of `t1` makes one group have capacity two and the other capacity three.
Every staggered four-square chain therefore has total capacity at most
nine, for all parameter choices and arbitrary orientations of the
additional squares.
