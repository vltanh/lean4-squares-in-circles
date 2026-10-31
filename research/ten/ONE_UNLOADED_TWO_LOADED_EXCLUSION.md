# One unloaded branch vertex with two loaded endpoints is impossible

**Status:** complete hand exclusion; independent and integrated mathematical
reviews passed on 2026-10-29. This excludes the `k=2,b=1` part of C05, including every
orientation of every other square in the ten-square packing. It does not
exclude the other branching strata.

Use the selected physical stress of a hypothetical strictly subcritical
ten-square packing in the reviewed radius window

```text
79/40 <= R < 3/sqrt(2).
```

Suppress only unloaded bodies of whole-graph degree two. Suppose the
remaining skeleton has two loaded vertices A,B and exactly one unloaded
branch vertex H. Every other body in this positive component is an
internal transmitter on a skeleton edge. The remaining squares of the
packing, including unstressed squares, stay present as physical obstacles.

## 1. The unloaded branch has a direct edge and a double-S bundle

The [reviewed skeleton reduction](BRANCHING_COMPONENT_SKELETON_DRAFT.md)
excludes loops and unloaded sets with only one outside body-neighbor.
Thus H has exactly the two distinct retained neighbors A,B. Its degree
is at least three. Section 4 of that reduction gives the only possibility:
a direct edge to A and a double-S bundle to B, with H an effective side
transmitter. Exchange A and B if needed.

Write the two distinct side transmitters in the double bundle as V1,V2.
The bundle fixes the frames of H,B,V1,V2 parallel. Its common direction
from H to B is a side direction d. At H, aggregate the two bundle forces
with their positive magnitudes as weights. Force balance makes their
resultant opposite to the force at the direct A--H contact, with the
same magnitude. Torque balance makes the direct contact and the weighted
bundle contact differ by d, the width of H.

Taking the same weighted average on B adds the bundle width one. Hence
there are actual support points `p_A in A`, `p_B in B` with

```text
p_B-p_A=2d,
A lies in {x : d dot x <= d dot p_A},
B lies in {x : d dot x >= d dot p_B}.
```

The point p_A is the actual A--H contact; p_B is a convex weighted average
of points on B's support side. Both belong to their squares. These support
identities prove `dist(A,B)=2` with unique closest-displacement vector 2d.
They do not replace any physical square or erase V1,V2.

## 2. There is no additional skeleton edge between A and B

A direct A--B edge is impossible because their distance is two. Any
nonempty A--B transmission path realizes that same distance, so the
reviewed transmission-distance theorem forces its width to be two and
its direction to be d. It would therefore be an SS path; the per-pair
alphabet permits one or two such parallel paths.

Even one is impossible. Look at the first S body on that path starting
from B. It has the same longitudinal unit interval as V1 and V2 and the
same parallel frame. These are three distinct squares: the maximal
suppressed paths have disjoint internal bodies. Their unit transverse
intervals must have pairwise disjoint interiors.

Each of the three intervals overlaps B's unit support interval in
positive length. Otherwise the contact would be a point-only
vertex/vertex contact carrying a side normal, forbidden by the selected
strict-normal convention. But three unit intervals with disjoint
interiors cannot all overlap one unit interval in positive length. In
increasing order, the third left endpoint is at least two beyond the
first left endpoint; points in their first and third positive overlaps
would consequently be more than one apart.

Thus there is no A--B skeleton edge. The whole positive component consists
of exactly the five bodies A,H,V1,V2,B.

## 3. Both loaded endpoints are radial side bodies at squared radius 17/4

A is a loaded leaf. Its direct edge to H is radial, and the
[loaded-leaf classification](PHYSICAL_TREE_REDUCTIONS.md) gives one of the
two radial contact distances

```text
D: R-sqrt(2),
S: T-1,          T=sqrt(R^2-1/4).
```

The aggregate points through H and the bundle stay on that same radial
line, so p_B is radial too. Aggregating B's two parallel forces produces
one force at its support point p_B, preserving both force and torque.
The same loaded-leaf argument applies to that resultant: it uses only
one supporting force and the circle forces, not the combinatorial degree
of B. This is the aggregate-endpoint argument used in Section 3 of
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md).

B's frame is parallel to d, so B must have the side form S. For clarity,
the orientation of the radial line is fixed by A's loaded-leaf geometry:
A lies on the outer side in direction -d, so `p_A=-r_A*d`, where r_A is
its positive S or D contact distance. Both listed contact distances are
less than two. The support identity from Section 1 therefore gives
`p_B=(2-r_A)*d` on the opposite positive ray. Thus the two positive radial
contact distances sum to two; no opposite-ray assumption is needed.

A cannot have the D form. At the largest permitted radius,

```text
R-sqrt(2) <= 1/sqrt(2) < 3/4,
T-1 < 17/16,
```

where `T<=sqrt(17)/2<33/16` follows from `1088<1089`.
The two contact distances would sum to less than `29/16<2`.
Therefore A also has the S form. Their distances give

```text
2(T-1)=2,       T=2,       R^2=17/4.
```

Rotate coordinates so the centers of A and B are `(-3/2,0)` and
`(3/2,0)`. The direct radial contact A--H is `(-1,0)`. The five bodies
have the forms

```text
A = [-2,-1] x [-1/2,1/2],
H = [-1,0]  x I_H,                 0 in I_H,
V1= [0,1]   x I_1,
V2= [0,1]   x I_2,
B = [1,2]   x [-1/2,1/2],
```

where each I is a closed unit interval and `I_1,I_2` have disjoint
interiors. Each of `I_1,I_2` overlaps both `I_H` and `[-1/2,1/2]` in
positive length by the same strict-normal argument as above. The weighted
B contact has transverse coordinate zero, so zero belongs to the convex
hull of `I_1 union I_2`.

## 4. The middle gap is a sealed cavity that cannot hold a unit square

Order the two middle intervals as

```text
I_1=[l,l+1],       I_2=[u,u+1],       u>=l+1.
```

If u=l+1 there is no gap. Otherwise let `g=u-(l+1)>0`. Positive overlap
of both intervals with `[-1/2,1/2]` gives

```text
-1/2 < l+1 < u < 1/2,       0<g<1.
```

Likewise positive overlap of both intervals with I_H puts the entire
closed gap `[l+1,u]` in the relative interior of I_H. Consequently the
open rectangle

```text
C=(0,1) x (l+1,u)
```

is a sealed component of the complement of the five core squares. Its
left and right boundary segments belong to H and B, and its bottom and
top segments belong to V1,V2. Its closure lies strictly inside the
containing disk since `|x|<=1, |y|<1/2` there.

The interior of any additional square is connected and disjoint from
the closed core: touching the core at an interior point would cause
interior overlap. If it met C, its entire interior would lie in that
component. This is impossible because C has vertical width g<1, whereas
every unit square has vertical projection width at least one, irrespective
of orientation.

It is therefore legitimate to fill the cavity for the purpose of
separating the additional squares. This is only an auxiliary obstacle;
no square is inserted and no assumption on an additional square's
orientation is made.

## 5. The filled barrier and the capacity count

After filling the possible gap, the middle column is
`[0,1] x [l,u+1]`, whose vertical interval contains zero. For every
`-2<x<2`, the vertical section of the filled core is a nonempty interval
containing zero. At the interfaces x=-1,0,1, the neighboring intervals
intersect, so their union is still an interval containing zero.

At x=+-2 the open disk of squared radius 17/4 has `|y|<1/2`, and the
corresponding outer anchor covers the entire section. Exactly the
barrier argument of
[STAGGERED_CHAIN_REDUCTION.md](STAGGERED_CHAIN_REDUCTION.md) now applies:
any additional square lies wholly in the closed upper or closed lower
half-plane, unless it lies in a side cap. A side cap has horizontal width
`sqrt(17)/2-2<1` and cannot hold a unit square. The sealed cavity was
already excluded in Section 4.

Write the center height of H as t, so `-1/2<=t<=1/2`. If t>=0, H contains
`[-1,0] x [0,1/2]`; the reviewed
[one-neck theorem](ONE_NECK_STABBING.md) bounds the upper candidates
avoiding A,H,B by two. The
[wide-neck theorem](WIDE_NECK_THREE_POINT_STABBING.md) bounds the lower
candidates avoiding A,B by three. If t<=0, reflection interchanges the
two bounds. Thus the combined capacity of these two half-plane classes
is at most five.

At least one of V1,V2 already lies wholly in one of the two closed
half-planes. Indeed, if both unit vertical intervals straddled zero in
their interiors, they would overlap in their interiors. That existing
middle square avoids A,H,B and therefore consumes at least one place
in the combined capacity-five bound. Every additional square consumes
one of the other places. There are consequently at most four additional
squares, and the total packing has at most

```text
5+4=9
```

squares. This contradicts the stipulated ten-square packing.

The proof uses the selected strict-normal convention, the reviewed
skeleton and transmitter reductions, and the complete hand capacity
theorems at squared radius 17/4. It does not use planarity or a numerical
optimization result, and it makes no claim about other C05 strata.
