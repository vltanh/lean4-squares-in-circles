# Exact angular restrictions for radial-side double-diagonal transmitters

**Status:** independently reviewed exact necessary conditions (2026-10-29).

Use the physical positive component `A-U-C-V-B-A` and radius window from
[RADIAL_SIDE_MIXED_TRANSMISSIONS.md](RADIAL_SIDE_MIXED_TRANSMISSIONS.md).
Both U and V are diagonal transmitters. This note proves exact necessary
angular restrictions; **the double-diagonal case remains open**.

Assume the radial-side setup, reflected so that
`C=[-L-1,-L] x [-1/2,1/2]`. Its two DD contacts have coordinates
`P=(-L,h)` and `Q=(-L,-k)`, where `0<h,k<=1/2`. Set `d=h+k`.
Their outgoing unit directions are `(p,q)=(cos(theta),sin(theta))`
and `(r,-s)=(cos(eta),-sin(eta))`, respectively, with all coordinates
nonnegative. If `h<1/2`, then `theta=0`; if `k<1/2`, then `eta=0`,
because a relative-interior side contact has the horizontal normal.

## Angle range forced by the endpoint square

Any unit square supported at a point T with inward unit normal `(p,q)`,
`p,q>=0`, has a point of height at least `T_y+q`. For vertex support,
write the two inward orthonormal edge vectors as `u,v` and
`(p,q)=a u+b v`, where `a,b>=0` and `a^2+b^2=1`. Its upper height
relative to T is `max(u_y,0)+max(v_y,0)`, which is at least
`a u_y+b v_y=q`. For side support, its inward edge is `(p,q)` and
its tangent is `(-q,p)`; a translate of the contact by the inward edge
already gives a point of height `T_y+q`.

The upper endpoint A is supported at
`T=(-L+sqrt(2)p,h+sqrt(2)q)`. Thus its maximum height is at least
`h+(sqrt(2)+1)q`. If the transmission starts at the corner and
`theta>=pi/4`, this is at least
`1/2+(sqrt(2)+1)/sqrt(2)=3/2+1/sqrt(2)>3/sqrt(2)`, impossible.
A side-interior contact already has `theta=0`. Consequently
`0<=theta<pi/4`; reflection gives `0<=eta<pi/4`.

## Exact separating-axis calculation

Put `delta=theta+eta`, so `0<=delta<pi/2`. The upper and lower
transmitter centers differ by

```
D=((p-r)/sqrt(2), d+(q+s)/sqrt(2)).
```

The four possible separating axes can be represented by these upward
unit normals:

```
a_U=(p-q,p+q)/sqrt(2), b_U=(-p-q,p-q)/sqrt(2),
a_V=(-r+s,r+s)/sqrt(2), b_V=(r+s,r-s)/sqrt(2).
```

On each of these axes the sum of the two square half-widths is
`H=(1+cos(delta)+sin(delta))/2`. Direct multiplication gives

```
D.a_U=(1-cos(delta)+sin(delta))/2+d(p+q)/sqrt(2),
D.b_U=(-1+cos(delta)+sin(delta))/2+d(p-q)/sqrt(2),
D.a_V=(1-cos(delta)+sin(delta))/2+d(r+s)/sqrt(2),
D.b_V=(-1+cos(delta)+sin(delta))/2+d(r-s)/sqrt(2).
```

All four projections are nonnegative, since `cos(delta)+sin(delta)>=1`
and `p>q,r>s`. Therefore the separating-axis criterion for disjoint
interiors is that at least one of these projections is at least H.
The b-axes would respectively require `d(p-q)>=sqrt(2)` or
`d(r-s)>=sqrt(2)`, impossible because `d<=1` and `p-q,r-s<=1`.
Thus the exact condition is

```
d max(p+q,r+s) >= sqrt(2) cos(theta+eta).                 (1)
```

This includes boundary contact equality and the cases with one horizontal
transmission. It uses the actual oriented unit-square transmitters.

## Consequences

After exchanging upper and lower, assume `theta>=eta`. The function
`cos(t)+sin(t)` increases on `[0,pi/4)`, so (1) reads

```
d cos(pi/4-theta) >= cos(theta+eta).
```

Since `d<=1` and cosine is decreasing on `[0,pi/2]`, it follows that

```
2 theta+eta >= pi/4,                                    (2)
```

with strict inequality if `d<1`. In particular, the larger angle is at
least `pi/12`. If the lower contact is in the relative side interior,
then `eta=0,d<1`, so the upper angle obeys `theta>pi/8`.

Independently, any supported unit square with inward normal `(p,q)`
can extend down from its support point by at most p. For vertex support,
at most one incident edge points down and its vertical component has
magnitude at most p; for side support the full tangent side has vertical
length p. Hence

```
min_y A >= h+sqrt(2)q-p,
max_y B <= -k-sqrt(2)s+r.
```

The physical A--B contact requires these vertical projections to overlap,
so necessarily

```
d <= p+r-sqrt(2)(q+s).                                  (3)
```

Combining (1) and (3) gives a further necessary angular inequality.
These conditions do not themselves exclude the DD pattern: for example,
`theta=eta=pi/12,d=1` satisfies both (1) and (3).


## A further radius constraint

A unit square supported at a point T with inward unit normal n contains
T+n. At a vertex, write n=a u+b v in its two inward unit edge directions;
then 0<=a,b<=1, so T+n belongs to the square. At a side point, translation
by the unit inward normal maps the support side to its opposite side.

For an upper-corner transmission this forces

```
(-L+(sqrt(2)+1)p)^2+(1/2+(sqrt(2)+1)q)^2 <= R^2
 = (L+1)^2+1/4.
```

Expansion gives the exact necessary inequality

```
L >= [2+2sqrt(2)+(sqrt(2)+1)q] / [2((sqrt(2)+1)p+1)].
```

The denominator is positive. Reflection gives the same statement for a
lower-corner transmission. This condition uses containment only, and
should not be read as a loadedness or stress-sufficiency criterion.
