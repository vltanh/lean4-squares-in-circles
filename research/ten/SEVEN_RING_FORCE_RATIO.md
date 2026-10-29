# A uniform ratio bound for loaded-ring contact forces

**Status:** independently reviewed hand proof (2026-10-29).

Use the entirely loaded physical ring in the radius window
`79/40<=R<=3/sqrt(2)`. Let `f_i=mu_i n_i`, where `mu_i>0` and
`|n_i|=1`, be its original pair forces, and let `tau>0` be their common
origin torque. The concurrence theorem gives the convex polygon

```text
Q={x : x cross f_i<=tau for every i},
```

with zero in its strict interior and every boundary edge covered by its
two incident loaded squares. See
[SEVEN_RING_INTERNAL_CONCURRENCE.md](SEVEN_RING_INTERNAL_CONCURRENCE.md),
Section 8. This note derives necessary inequalities, not a ring exclusion.

## 1. A larger disk inside the concurrence polygon

Put `d=R-sqrt(2)>0`. Every point `x` of every loaded square satisfies
`|x|>=d`: its circle vertex `w` obeys `|w|=R`, and the square's diameter
gives `|w-x|<=sqrt(2)`. The triangle inequality proves the claim.

The boundary of `Q` therefore avoids the open disk `B(0,d)`. Since `Q`
contains zero in its strict interior, it contains this whole disk. For
example, if a point of the disk were outside `Q`, the segment from zero
to that point would first meet the boundary at norm less than `d`, a
contradiction. Taking closures proves

```text
D_d subset Q.
```

In particular, the distance `h_i=tau/mu_i` of each supporting force line
from zero satisfies `h_i>=d`.

On the other hand, the actual contact point `p_i` satisfies
`p_i cross n_i=h_i`, so `h_i<=|p_i|<R`. Strictness follows because two
packed unit squares cannot share a point of the containing circle, as
proved in Section 1 of the concurrence manuscript. Thus

```text
R-sqrt(2) <= tau/mu_i < R.                          (1)
```

## 2. Every pair of positive magnitudes is comparable

Dividing (1) for any two edges gives

```text
(R-sqrt(2))/R < mu_i/mu_j < R/(R-sqrt(2)).           (2)
```

Both inequalities are strict because the upper support-distance bound is
strict. In particular the smaller-to-larger ratio is greater than `9/32`
throughout the working window. Indeed

```text
(R-sqrt(2))/R >= 1-40sqrt(2)/79 > 9/32,
```

where the last comparison reduces to `1817>1280sqrt(2)` and follows
from `1817^2-2*1280^2=24689>0`.

No one-chirality or unique-circle-vertex assumption is needed for (1)--(2).

## 3. A side-contact parameter cannot tend to zero at a small frame turn

Under the additional one-chirality hypotheses of
[SEVEN_RING_ONE_CHIRALITY.md](SEVEN_RING_ONE_CHIRALITY.md), the exact
torque relation is

```text
lambda_i mu_i = mu_(i-1) cos(delta_i),
0<delta_i<pi/2.
```

Hence (2) yields

```text
lambda_i > ((R-sqrt(2))/R) cos(delta_i)
         > (9/32) cos(delta_i).                    (3)
```

The index is essential: `delta_i` is the turn *into* body `i`, whereas
`lambda_i` is its outgoing side parameter. In the local spike coordinates
of [SEVEN_RING_SPIKE_REDUCTION.md](SEVEN_RING_SPIKE_REDUCTION.md), the
displayed turn is `delta_(i+1)`. Inequality (3) must not be imposed using
that outgoing turn in place of `delta_i`.

## 4. Every loaded vertex has own-frame horizontal coordinate greater than one

A supported unit square contains `p+n` whenever `p` is a point on a
support face and `n` is its inward unit normal. At a vertex, write
`n=a e+b f` in the two inward orthonormal edge directions. Then
`a,b>=0`, `a^2+b^2=1`, so `0<=a,b<=1` and `p+n` belongs to the square.
At a side point, translation by the inward unit normal maps that side
onto its opposite side. These cases exhaust support points.

Use the one-chirality coordinates

```text
w_i=R(cos(alpha_i) u_i-sin(alpha_i) v_i),
p_(i-1)=w_i-u_i,
v_(i-1)=sin(delta_i) u_i+cos(delta_i) v_i.
```

The neighbor at the incoming contact has inward supporting unit normal
`-v_(i-1)`. It therefore contains

```text
p_(i-1)-v_(i-1)
 =w_i-(1+sin(delta_i))u_i-cos(delta_i)v_i.
```

Its disk containment and `|w_i|^2=R^2` imply, after expansion,

```text
2(1+sin(delta_i))
 <=2R[(1+sin(delta_i))cos(alpha_i)
       -cos(delta_i)sin(alpha_i)].
```

Dividing by the positive factor gives the exact necessary inequality

```text
R cos(alpha_i)
 - R sin(alpha_i) cos(delta_i)/(1+sin(delta_i)) >= 1. (4)
```

Because `0<delta_i<pi/2` and `R sin(alpha_i)>1/2`, it follows that

```text
R cos(alpha_i)>1.                                  (5)
```

This is stronger than the original farthest-vertex condition
`R cos(alpha_i)>1/2`. It uses the physical neighbor, so it need not hold
for a solution of the scalar action equations alone.

For a local spike defined by bodies `i` and `i+1`, (5) applies to both
bodies in a complete physical ring. The limiting witness in the spike
note has `R cos(alpha_i)=sqrt(2)-1/2<1`, and hence cannot be approached
by complete physical rings with this pattern. This conclusion follows
from (5), independently of the indexing issue in (3).

The ratio bound is a hand consequence of the established concurrence
polygon. It does not prove global uniformity or a bound on the hole's
capacity. No Lean verification is claimed.
