# Diagonal transmission paths form disjoint paths after suppression

**Status:** hand theorem; root and independent full mathematical reviews
passed on 2026-10-29, including the even-cycle matching moment.

Select the physical certificate by
[GENERIC_CONTACT_NORMAL_SELECTION.md](GENERIC_CONTACT_NORMAL_SELECTION.md)
before classifying its positive graph. Work in the usual ten-square
radius window `79/40<=R<=3/sqrt(2)`.

Suppress unloaded bodies of degree two in the whole positive component,
as in [BRANCHING_COMPONENT_SKELETON_DRAFT.md](BRANCHING_COMPONENT_SKELETON_DRAFT.md).
Form the **D graph** on the retained bodies, keeping exactly the skeleton
edges that consist of one diagonal transmitter. Retained endpoints can
be loaded or unloaded branching bodies. The argument also applies to a
whole simple cycle, retaining its loaded bodies.

**Theorem.** The D graph is a disjoint union of paths and isolated vertices.
At any retained body there are at most two incident D paths; if there
are two, their outgoing directions are perpendicular. All square frames
in a connected D graph are parallel, and the directions of successive
D edges alternate between their two common axes.

These are necessary conditions on the graph of the selected certificate.
They do not exclude geometric contacts carrying zero stress or preserve
the graph of a differently chosen certificate.

## 1. Each D edge transfers a common square frame

The generic normal-selection theorem makes each D transmitter contact
both neighboring bodies in relative side interiors. Its diagonal force
direction is therefore a side normal of both endpoints. Their square
frames are parallel, with the transmitter's frame rotated by 45 degrees.

Let d be the unit direction from an endpoint H to the other endpoint K.
The exact width is sqrt(2), and each endpoint has directional halfwidth
1/2 in that frame. Consequently their centers satisfy

```text
d dot (c_K-c_H)=1+sqrt(2)=:ell.                        (1)
```

This is an equality, not merely a lower bound. Transverse positions of
the two side-interior contacts are unrestricted within their sides.

## 2. Two D paths cannot leave the same side

Suppose two distinct D paths leave one retained body C along the same
outward normal. Rotate so that normal is horizontal. Both contact points
lie in the relative interior of the same unit side of C, so their
vertical coordinates differ by strictly less than one.

Each diagonal transmitter has its horizontal diagonal as its force line.
Its center is the contact point shifted horizontally by `1/sqrt(2)`.
The two transmitter centers therefore have equal horizontal coordinates
and vertical separation less than one. At their common center abscissa,
the interiors of both diamonds have vertical halfwidth `1/sqrt(2)`.
Disjoint interiors would require their vertical center separation to be
at least sqrt(2), a contradiction.

In particular, parallel copies of a D edge are impossible.

## 3. Two D paths cannot leave opposite sides

Suppose the outgoing directions at C are d and -d, with endpoint bodies
A and B. The two support faces of C differ by one in the d coordinate.
Each path adds width sqrt(2), and the endpoint center is another 1/2
beyond its support. Hence

```text
d dot(c_A-c_B)=2+2sqrt(2).                            (2)
```

If the two endpoint bodies were the same, (2) would immediately be
impossible. Otherwise the universal center bound from
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md), Section 2,
gives

```text
|c_A-c_B|<25/8,
```

contrary to (2), since `2+2sqrt(2)>4>25/8`.

All D directions at C belong to its two pairs of opposite side normals.
Sections 2--3 allow at most one path from each such pair. Thus its D
degree is at most two, and a degree-two vertex uses perpendicular
directions. Frame propagation from Section 1 makes these two axis labels
consistent throughout any connected D graph.

## 4. Odd and even D cycles are both impossible

On a D cycle, each vertex is incident to one edge of each common axis.
The edge labels alternate, so the cycle is even. This already excludes
every odd cycle.

Suppose an even cycle has r vertices. Use the two common square axes as
coordinates, with the disk center still as origin. Its horizontal edges
form a perfect matching, and each obeys `|x_i-x_j|=ell` by (1).
The elementary inequality

```text
x_i^2+x_j^2 >= (x_i-x_j)^2/2=ell^2/2
```

therefore gives

```text
sum_i x_i^2 >= r*ell^2/4.
```

The vertical edges form another perfect matching, yielding the same
bound for `sum_i y_i^2`. Adding them gives

```text
sum_i |c_i|^2 >= r*ell^2/2.
```

But every center has norm below 25/16, whereas

```text
ell^2/2=(3+2sqrt(2))/2>5/2>625/256.
```

This contradicts the sum of the individual center bounds. No D cycle
exists. Together with degree at most two, this proves that the D graph
is a disjoint union of paths and isolated vertices.

## 5. Consequences for the fixed finite ledgers

The alternating three-loaded/three-diagonal six-cycle

```text
C20-M06-L03-B02-T04: LDLDLD
```

would produce a triangle in the D graph. It is therefore excluded in
the selected-certificate lower-bound reduction. No additional physical
ownership cases remain for that stable signature: the side-interior
conditions come from the certificate selected before classification.

For the branching catalog, every digit-4 subgraph must be acyclic with
maximum degree two. A code violating either condition is excluded by
this hand theorem, for both the cataloged b=0 subclass and any later
catalog allowing unloaded retained branching vertices. A surviving
code is only a necessary graph candidate, not a physical realization.
