# Width-two transmission paths cannot cross another transmission path

**Status:** independently reviewed exact hand proof, including the topological
argument, all four-body junction cases, and the finite-case IDs.

Consider a ten-square packing in the radius window

```text
79/40 <= R <= 3/sqrt(2).
```

Use its physical positive-stress body-pair graph. Let P and Q be two
**vertex-disjoint nonempty transmission paths**: their endpoints are loaded,
all internal bodies are unloaded and have degree two in the whole positive
graph. Suppose P consists of two side transmitters, so its width is two.
Then their four loaded endpoints cannot alternate in circular order.

The circular order here can be read from loaded center rays or from chosen
circle vertices of those bodies. The proof does not assume that body-pair
edges form a planar graph. It explicitly treats every possible transverse
four-body contact junction.

## 1. A corner-extension obstruction

Suppose `x>0`, `y<=0`, and `x+y>0`. Put `q=(x,y)` and

```text
R^2=x^2+(y-1)^2.                                    (1)
```

No unit square contained in this disk can contain q while lying wholly
in the half-plane `X>=x`.

For an axis-parallel square, its left side must have coordinate x, with q
on that side. Its bottom height is at most y and is nonpositive. Its
bottom-right vertex therefore has squared norm at least

```text
(x+1)^2+y^2 = R^2+2(x+y)>R^2.
```

For a non-axis square, q is its unique leftmost vertex. Its two outgoing
edge vectors can be written `(c,s)` and `(s,-c)`, with `c,s>0` and
`c^2+s^2=1`. The latter endpoint has squared norm exceeding (1) by

```text
2[xs+y(1-c)] > 2x[s-(1-c)] = 2x(c+s-1)>0.
```

The first strict inequality uses `y>-x` and `1-c>0`; the second uses
`c+s>1`. This proves the obstruction, including side and vertex contacts.
Reflections and rotations give its other coordinate versions.

## 2. Alternating loaded endpoints force a transverse four-body junction

A loaded square's circle vertices deviate from its center ray by at most
`beta=asin(1/(2R))<pi/10`. For the strict bound, use
`1/(2R)<=20/79<3/10<sin(pi/10)`, where
`sin(pi/10)=(sqrt(5)-1)/4>3/10` follows from `sqrt(5)>11/5`.
Loaded center rays are pairwise more than `pi/5` apart. Thus choosing one
circle vertex for every loaded endpoint preserves their circular order.

For either transmission path, join successive body centers to their actual
contact points, and extend each endpoint inside its loaded square from its
center to the chosen circle vertex. This is a simple arc in the containing
disk, with only its two ends on the circle. Center-to-boundary segments lie
in the square's open interior except at their boundary endpoints. All
nonadjacent bodies within a transmission path have positive distance:
the intervening unloaded subpath realizes a positive width. Its contact
points are distinct. These facts rule out self-intersections of the arc.
Contact points between two squares cannot lie on the containing circle,
by the circle-point lemma in
[SEVEN_RING_INTERNAL_CONCURRENCE.md](SEVEN_RING_INTERNAL_CONCURRENCE.md).

Two such simple arcs with alternating boundary ends cannot be disjoint.
They intersect only at finitely many shared contact points: an interior
point of a path segment lies in the interior of its body, so cannot belong
to the other path. At any intersection, four distinct squares meet, two
from each path. Their four interior angular sectors each have angle at
least `pi/2` and are disjoint. Hence all four have angle exactly `pi/2`,
and the squares tile a solid axis-parallel two-by-two block after rotation.

At least one intersection is a transverse junction: the two paths pair
opposite quadrants of this block. To justify this last topological step,
if every intersection paired adjacent quadrants, each could be removed
by a local perturbation of the two arcs in a small disk around the
junction. The finitely many disks can be chosen disjoint. This would
produce disjoint arcs with the same alternating boundary ends, contrary
to the Jordan separation theorem. This perturbation is used only for the
topological contradiction; it is not a motion of any square or force.

Write the resulting block as

```text
p+[-1,1]^2,              p=(u,v).                    (2)
```

The path connections use the two pairs of opposite quarter-squares.
Every transmission path contains at most two unloaded bodies, by
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md). Each pair at
this junction therefore consists of either two unloaded S bodies, or a
loaded endpoint and its neighboring transmitter. There are zero, one,
or two loaded bodies among these four quarter-squares.

## 3. One loaded quarter-square

In this case one path meets the junction internally, as its two S
transmitters. The other path supplies the loaded quarter-square. Choose
coordinates so the S transmission line is horizontal and that loaded
square is the southeast quarter of (2). The loaded square's circle vertex
must be the southeast corner of the whole block, since the entire block
is contained in the disk. Therefore

```text
u>=0, v<=0,             R^2=(u+1)^2+(v-1)^2.          (3)
```

Put `q=(u+1,v)`, `x=u+1>=1`, and `y=v<=0`. If `x+y<=0`, (3) would give

```text
R^2 >= x^2+(x+1)^2 >=5>9/2.
```

Thus `x+y>0`. The horizontal SS path has its right endpoint contact at q,
and its loaded endpoint square lies wholly in `X>=u+1`. Section 1
forbids that square. This excludes the junction.

The normalization is valid for either horizontal or vertical S-force
direction by exchanging coordinates, then reflecting axes. It uses the
side transmitter's actual force line, not the center/contact arc direction.

## 4. Two loaded quarter-squares

The two loaded squares come from different paths, so they are adjacent
quarters of (2). Rotate so they are the two lower squares. Their circle
vertices are the two bottom outer corners of the block. Equality of their
squared norms gives u=0, and

```text
R^2=1+(v-1)^2,          -7/8<v<0.                    (4)
```

Here v is nonpositive because the bottom corners are farthest, and is
strictly negative since `R>sqrt(2)`. Also
`(1-v)^2<=7/2<(15/8)^2`, giving the lower bound in (4).

Choose the SS path P. At this junction it joins one lower loaded square
to the opposite upper S transmitter. Reflect horizontally to make this
the lower-left and upper-right pair. Starting from `p=(0,v)`, its side
transmission direction is either rightward or upward.

If rightward, the next S square starts at `q=(1,v)` and lies wholly in
`X>=1`. Section 1 applies because `1+v>0` and (4) is its containing-circle
identity. Such a square cannot fit.

If upward, the two side transmitters take the force line from p to
`p+(0,2)`. The loaded endpoint beyond them has center height at least

```text
v+2+1/2 > 13/8 > 25/16,
```

contrary to the universal square-center bound. Both possibilities are
excluded.

## 5. No loaded quarter-square

Both paths meet the junction internally, so both consist of two side
transmitters. Their force lines pass through p and are each parallel to
one coordinate axis of the block.

If they are parallel, rotate to make both horizontal. Their two distinct
loaded left endpoints contain `p-(1,0)` and lie in `X<=u-1`. Two disjoint
unit-square sectors, each of angle at least `pi/2`, fit at that point in
the left half-plane only by filling its two quadrants. Thus these loaded
squares are exactly the two axis-parallel squares tiling

```text
[u-2,u-1] x [v-1,v+1].
```

The same argument places the two right endpoints in the column
`[u+1,u+2] x [v-1,v+1]`. Along with the four middle squares they fill the
rectangle `p+[-2,2] x [-1,1]`. Its opposite corners have distance
`2sqrt(5)>2R`, impossible in the disk.

If the force lines are perpendicular, their four loaded endpoint contacts
are `p+(+-1,0)` and `p+(0,+-1)`. The endpoint center projections are at
least another half-unit outward. Since all center norms are less than
`25/16`,

```text
|u|<1/16,           |v|<1/16.
```

The four middle-square centers consequently have squared norms less than

```text
2(1/2+1/16)^2=81/128<1.
```

The [general translated-block theorem](GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md)
then bounds the whole packing by nine squares, contradicting the stipulated
ten squares. This last branch uses a completion theorem rather than
excluding the eight-body contact configuration in isolation.

All junction cases are excluded, proving the no-alternating-endpoints
statement.

## 6. Consequence for exactly two nonempty runs

Suppose a whole mixed simple-cycle component has `k>=4` loaded bodies,
exactly two nonempty unloaded runs, and at least one run is SS. Then both
transmission endpoint pairs are adjacent in the radial loaded-center order.

For runs sharing a loaded endpoint this is already the direct-path argument
in [SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md](SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md).
Otherwise the direct loaded contacts form two disjoint nontrivial paths
covering all k loaded vertices. They are a subgraph of the radial k-cycle
H with exactly `k-2` edges, so they are precisely the two paths obtained
by deleting two edges of H.

There are only two ways for the two transmission paths to reconnect their
four ends into the given single cycle: use the two missing H-edges, or
use the opposite matching whose endpoint pairs alternate around the circle.
The second is excluded by the theorem because one path is SS. Hence the
first is forced, establishing the claimed radial adjacency.

Therefore the first three rows of the shared-endpoint angular-budget theorem
extend to **all** two-run components, without the shared-endpoint assumption:

```text
SS-SS: k>=4;        SS-S: k>=6;        SS-D: k>=5.
```

The one-S/one-D and D-D rows with no SS run are not extended by this argument.

## 7. Thirteen further cases

The preceding extension closes these additional fixed-inventory entries:

| Stable ID | Canonical word |
| --- | --- |
| `C20-M08-L04-B04-T01` | `LLSSLLSS` |
| `C20-M08-L05-B02-T02` | `LLLDLLSS` |
| `C20-M09-L05-B04-T01` | `LLLSSLLSS` |
| `C20-M09-L06-B02-T01` | `LLLLSLLSS` |
| `C20-M09-L06-B02-T02` | `LLLLDLLSS` |
| `C20-M09-L06-B04-T01` | `LLLSLLLSS` |
| `C20-M09-L06-B04-T02` | `LLLDLLLSS` |
| `C20-M10-L06-B04-T01` | `LLLLSSLLSS` |
| `C20-M10-L06-B09-T01` | `LLLSSLLLSS` |
| `C20-M10-L07-B02-T01` | `LLLLLSLLSS` |
| `C20-M10-L07-B02-T02` | `LLLLLDLLSS` |
| `C20-M10-L07-B04-T01` | `LLLLSLLLSS` |
| `C20-M10-L07-B04-T02` | `LLLLDLLLSS` |

Their hand exclusions are recorded in [cycle_progress.json](cycle_progress.json).
