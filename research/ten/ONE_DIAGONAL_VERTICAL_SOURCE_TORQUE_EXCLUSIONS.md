# Further torque exclusions when one D endpoint has a vertical S path

**Status:** exact conditional hand proofs; root and independent full
mathematical reviews of the assembled note passed on 2026-10-31. These
prune support rows within LSLSLD and do not close the whole signature.
The final radial-C row described below was subsequently excluded by
[RADIAL_VERTICAL_SOURCE_EXCLUSION.md](RADIAL_VERTICAL_SOURCE_EXCLUSION.md).

Use the both-unique-D-endpoint branch and the common-edge classification
of [ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md](ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md).
Assume A's S direction is vertical, `n_A=(0,1)`, while
`n_B=(−r,s)` with `0<r<s` and `r²+s²=1`. Let sigma_A,sigma_B>0 be the
two S magnitudes. At C the outgoing forces are `−sigma_A*n_A` and
`−sigma_B*n_B`, and its outward circle-load resultant is

```text
g=sigma_A*n_A+sigma_B*n_B.
```

All endpoint top-side contact positions remain those of the common-edge
note; none is assumed to be a strict corner contact at A.

## 1. A radial loaded square has no side-normal S path to a loaded square

This observation is valid throughout `79/40<=R<=3/sqrt(2)` and does not
depend on the surrounding graph. Put a radial loaded square in the frame

```text
C=[L,L+1]×[−1/2,1/2],
L=sqrt(R²−1/4)−1,       9/10<L<17/16.
```

Suppose a single S path from C ends at another loaded square. A
side-normal contact on the top or bottom side, including a corner with
that normal, puts the endpoint square's unit normal step at height
`±5/2`, outside the containing disk. An outward normal on the outer
vertical side similarly puts that step at horizontal coordinate L+3.
The remaining side-normal direction is inward, from a point `(L,h)`
with `|h|<=1/2`. Its far contact is

```text
Q=(L−1,h),       |L−1|<1/10,
|Q|²<1/100+1/4<(21/40)².
```

Every point of the endpoint square is within sqrt(2) of Q. Thus every
such point has norm strictly below

```text
21/40+sqrt(2)<21/40+57/40=39/20<79/40<=R.
```

The endpoint cannot be loaded. This excludes all side-normal S paths
from a radial loaded square to another loaded square, with both
geometric circle vertices and all load splits retained.

## 2. Row E_B is impossible for every circle feature at C

In row E_B, put

```text
e=(s,r),       m=n_B=(−r,s),
Q_B=Q_A+ell*e,       0<ell<=1,
C=Q_A+[0,1]*e+[0,1]*m.
```

The circle resultant has strictly positive components in this frame:

```text
g dot e=sigma_A*r>0,
g dot m=sigma_A*s+sigma_B>0.
```

If C has a unique geometric circle vertex, it is therefore
`W=Q_A+e+m`. Indeed the farthest vertex in a square frame takes the
signs of the center's frame coordinates, and the unique circle vector
has those same signs; positivity of the two components selects this
corner.

Torque about W eliminates its circle force. The two outgoing S torques
are exactly

```text
sigma_A*(s−r)>0,
sigma_B*(1−ell)>=0.
```

They cannot sum to zero. If C instead has two geometric circle vertices,
Section 1 excludes its side-normal S path to B. Thus row E_B is
impossible in every case, including ell=1 and a zero coefficient at one
of two geometric circle vertices.

## 3. Row V_V is impossible when C has a unique circle vertex

Write

```text
e=(a,b)=Q_B−Q_A,       m=(−b,a),
a²+b²=1,       a>0,
C=Q_A+[0,1]*e+[0,1]*m.
```

The strict V_V support inequalities give

```text
b>0,       r*a−s*b>0,
0<b/a<r/s<1.
```

In particular a>b. Also

```text
g dot m=sigma_A*a+sigma_B*(r*b+s*a)>0.
```

If C has a unique circle vertex, it must consequently be one of the two
upper vertices in the m direction. If it is `W=Q_A+e+m`, the outgoing
torques about W sum to

```text
sigma_A*(a−b)+sigma_B*(r*a−s*b)>0.
```

If it is `W=Q_A+m`, the torque sum is

```text
−sigma_A*b−sigma_B*((s−r)*a+(r+s)*b)<0.
```

Neither is zero, so neither unique-circle case is possible.

## 4. Exact remaining scope

Together with
[ONE_DIAGONAL_VERTICAL_SOURCE_SIDE_EXCLUSION.md](ONE_DIAGONAL_VERTICAL_SOURCE_SIDE_EXCLUSION.md),
these arguments exclude vertical A in row E_A, vertical A in row E_B,
and vertical A in row V_V with a unique geometric circle vertex at C.
Horizontal reflection gives the corresponding statements for vertical B.

The only remaining vertical-endpoint source case is row V_V with two
geometric circle vertices at C. Its contacts are strict vertices, so the
side-normal clearance lemma does not apply. The two radial circle loads
must remain free, including a possible zero coefficient. No exclusion
of that remaining row is claimed here.

## Completion of the vertical-endpoint classification

The [complete radial-source certificate](RADIAL_VERTICAL_SOURCE_EXCLUSION.md)
now excludes the last V_V/radial-C form. Consequently both S contacts at
the D endpoints are strict inner-corner contacts throughout the whole
both-unique-D-endpoint branch. This does not remove radial D endpoints
or prove completion capacity for the remaining strict/strict forms.
