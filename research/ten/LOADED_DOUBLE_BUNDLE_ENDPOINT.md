# A loaded endpoint of a double bundle forces a radial side geometry

**Status:** reviewed hand argument; root and independent mathematical
reviews passed on 2026-10-30.
This is a structural restriction for arbitrary retained loaded and unloaded
counts. It does not change a catalog, close the branching case, or assert
a ten-square completion bound.

Work in `79/40<=R<=3/sqrt(2)` with the selected physical stress and the
suppressed skeleton of
[BRANCHING_COMPONENT_SKELETON_DRAFT.md](BRANCHING_COMPONENT_SKELETON_DRAFT.md).
Let C be loaded and have exactly one distinct retained neighbor B. Suppose
their connection is a double-S or double-SS bundle. Write W=1 or W=2,
respectively, for the width of each path.

**Theorem.** After rotation, the endpoint C and an effective point Q in B
have the exact form

```text
L=sqrt(R^2-1/4)-1,
C=[-L-1,-L] x [-1/2,1/2],
Q=(W-L,0) in B.                                     (1)
```

For a double-S bundle, B is geometrically circle-clear. In particular,
a loaded endpoint with no other retained neighbor cannot be joined by
double-S to another loaded body. For a double-SS bundle, containment
forces `L>=1`, equivalently `R^2>=17/4`.

These statements concern the physical endpoint B, regardless of its
degree or additional contacts. The weighted point is used to infer
geometry; it is not a replacement force or a new stress certificate.

## 1. Aggregate the two path forces without changing their displacement

The reviewed double-bundle reduction fixes side support at both endpoints,
with frames parallel to all the side transmitters. Rotate so the paths
leave C in direction d=(1,0). Their positive magnitudes are mu_1,mu_2.
Write the endpoint application points as P_j in C and Q_j in B. The
transmission equations give

```text
Q_j-P_j=W*d,       j=1,2.
```

Taking the same positive weighted average at both ends gives

```text
P=(mu_1*P_1+mu_2*P_2)/(mu_1+mu_2) in C,
Q=(mu_1*Q_1+mu_2*Q_2)/(mu_1+mu_2) in B,
Q-P=W*d.                                            (2)
```

Both averages remain on the respective supporting sides. C has no other
positive body-pair forces, since it has no other retained neighbor.
In the gradient sign convention, its two contact vectors point right.
Their aggregate is a nonzero horizontal vector acting at P. Every circle force has zero torque about
the original origin. Torque balance on C makes `P_y=0`.

Force balance makes the positive circle-load resultant on C horizontal
and directed left. Because C's frame is axis-parallel, a unique farthest
circle corner cannot have vertical coordinate zero: the other vertex on
the same vertical side would have larger absolute vertical coordinate.
The geometric circle contact must consequently consist of the two
vertices of C's outer left side, at heights -1/2 and +1/2. Both have to
carry positive weight to make their positive resultant horizontal.
The center has vertical coordinate zero, and the outer left coordinate
is `-sqrt(R^2-1/4)=-L-1`.

The inward supporting side is therefore `x=-L`. With `P_y=0`, this gives
`P=(-L,0)` and then exactly (1) by (2). The two circle weights in fact
are equal, though that additional conclusion is not needed below.

For completeness, C cannot instead have its horizontal center coordinate
zero: an axis-parallel square with center on the vertical axis has all
its farthest vertices in one strict vertical half-plane in this radius
window, so no positive combination of those vertices is horizontal.
Likewise its horizontal center cannot be positive, since then all circle
vertices have positive horizontal coordinate. This justifies the left
outer side used above without an implicit symmetry assumption.

## 2. A double-S partner contains a point very close to the origin

The radius window gives

```text
9/10<L<9/8.
```

The lower comparison follows from
`R^2-1/4>=5841/1600>361/100=(19/10)^2`; the upper comparison follows
from `R^2-1/4<=17/4<289/64=(17/8)^2`.
For W=1, (1) therefore gives

```text
|Q|=|1-L|<1/8.
```

Every point z of the unit square B is at distance at most its diameter
sqrt(2) from Q. Hence

```text
|z|<=|Q|+sqrt(2)<1/8+3/2=13/8<79/40<=R.             (3)
```

All of B is strictly inside the containing circle. B is thus circle-clear
and in particular unloaded. This proves the double-S assertion without
using any restrictions on B's other neighbors.

## 3. A double-SS partner forces the cardinal lower radius

For W=2 the side-support frame at B is parallel, and its horizontal
interval is `[2-L,3-L]`. Since L<9/8, its farthest horizontal coordinate
is the positive number `3-L`. Every unit vertical interval has an
endpoint of absolute value at least 1/2. Containment of that endpoint's
vertex in B therefore requires

```text
(3-L)^2+1/4<=R^2=(L+1)^2+1/4.
```

Subtracting the two sides gives `8(L-1)>=0`. Thus L>=1 and
`R^2=(L+1)^2+1/4>=17/4`, as claimed.

The double-SS configuration is not excluded by this inequality. Nor does
Section 2 exclude double-S bundles whose two loaded endpoints both have
additional retained neighbors: their extra forces invalidate the single
aggregate-force premise. Those two situations remain genuine obligations
for a universal branching or shared completion argument.
