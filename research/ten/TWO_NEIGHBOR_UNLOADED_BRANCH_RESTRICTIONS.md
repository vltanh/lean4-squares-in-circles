# Restrictions on unloaded branch vertices with two neighbors

**Status:** hand restrictions; Sections 1--5 received root and independent
full mathematical reviews on 2026-10-29. The stronger matching and
`r<=1` consequences in Sections 6--7 passed both reviews on 2026-10-30. These
apply to every C05 skeleton in the ten-square radius window, including
unloaded retained endpoints. They do not exclude the whole branching
family and do not change any fixed raw catalog.

Work in `79/40<=R<=3/sqrt(2)`. Use the selected strict/nonradial physical stress, and suppress only
unloaded bodies of degree two in the whole positive graph. Let k denote
the loaded retained count, b the unloaded retained count, and r the number
of unloaded retained vertices having exactly two distinct retained
neighbors. Degrees still count parallel paths.

**Theorem.** For every such vertex H with neighbors A,B:

1. Its incident symbols are direct and double-S. It is an effective side
   transmitter, and `dist(A,B)=2` with a fixed closest-displacement vector.
2. There is no skeleton edge between A and B.
3. No two of the r vertices are adjacent in the skeleton.
4. No two of them have the same unordered neighbor pair {A,B}.
5. Their internal double-S paths are disjoint, and `k+b+2r<=10`.
6. The unordered endpoint pairs of all width-two relations form a
   matching, after repetitions of the same pair are ignored. This includes
   both actual SS paths and the effective connections in item 1. In
   particular, the r exceptional vertices have disjoint neighbor pairs.
7. If the stress is chosen with the jointly compatible planar selection
   of [PLANAR_SELECTED_PHYSICAL_STRESS.md](PLANAR_SELECTED_PHYSICAL_STRESS.md),
   then `r<=1`, for every number b of unloaded retained vertices.

Whenever A and B are loaded, the cap-angle theorem additionally makes
both arcs between their center rays greater than 162 degrees. This angle
restriction is valid even though there is no skeleton edge A--B.

## 1. The effective width-two connection

Section 4 of the reviewed
[skeleton reduction](BRANCHING_COMPONENT_SKELETON_DRAFT.md) gives exactly
one direct edge and one double-S bundle at H, and makes H an effective
S body after aggregating the two bundle forces. Name A the direct
neighbor and B the double-S neighbor, and write V1,V2 for the two distinct
internal side transmitters.

Their common direction from H toward B is a side normal d of H, B,
V1, and V2. Force balance on H makes its direct force opposite to the
sum of its two positive bundle forces. Weighted averaging by those two
forces preserves their support-face application points. Torque balance
on H gives an effective displacement d across H, and the two single-S
paths add another d. Thus there are support points p_A in A and p_B in B
with

```text
p_B-p_A=2d,
d dot x <= d dot p_A       for x in A,
d dot x >= d dot p_B       for x in B.
```

The first point is the actual direct A--H contact; the second is a
weighted average on B's support face. These equations give
`dist(A,B)=2`, attained by p_A,p_B. The closest-displacement vector is
unique by strict convexity of squared norm on the convex difference set.
No force is assigned to a fictitious square, and the three physical
unloaded bodies H,V1,V2 are retained as obstacles.

This is the local argument in Sections 1--2 of
[ONE_UNLOADED_TWO_LOADED_EXCLUSION.md](ONE_UNLOADED_TWO_LOADED_EXCLUSION.md).
It does not require A or B to be loaded or to have no other contacts.

## 2. No additional A--B edge can coexist

A direct A--B edge would contradict their positive distance. Any nonempty
suppressed transmission path between them must realize the same distance and closest-displacement
vector, so it would be an SS path in direction d.

At B, its first side transmitter and the two bodies V1,V2 have the same
longitudinal unit interval and parallel frames. They are distinct because
different maximal suppressed paths have disjoint internal bodies. Their
unit transverse intervals have pairwise disjoint interiors. Each overlaps
B's unit support interval in positive length. For a new SS path, a
singleton overlap would be a point-only vertex/vertex contact with a side
normal, forbidden by the selected strict-normal convention; the bundle
already has positive overlaps by the same argument.

Three disjoint unit intervals cannot each overlap a fixed unit interval
in positive length. Therefore even one additional SS path is impossible.
This proves that the A--B symbol is zero.

The support strip in Section 1 also permits direct application of
[TRANSMISSION_CAP_ANGLE_BOUND.md](TRANSMISSION_CAP_ANGLE_BOUND.md) with
W=2. The endpoint bodies' degrees and loads are irrelevant to that local
theorem. In a strictly subcritical packing their minor center angle is
greater than 162 degrees. For two loaded endpoints this gives the stated
two-arc condition in their circular loaded order.

## 3. Two such unloaded vertices cannot be adjacent

Suppose H1 and H2 are adjacent and each has exactly two distinct retained
neighbors. Their common symbol can only be direct or double-S, because
these are their two allowed incident symbols.

If it is direct, each vertex's other connection is a double-S bundle.
Aggregate the bundles. The outer support points are linked through widths

```text
1 (first bundle) + 1 (H1) + 1 (H2) + 1 (second bundle) = 4.
```

If their common symbol is double-S, each other connection is direct.
The outer support points are then linked through widths

```text
1 (H1) + 1 (common bundle) + 1 (H2) = 3.
```

In each case force balance fixes one common direction and equal aggregate
magnitudes, while torque balance preserves the effective support-point
displacements through both vertices. This is exactly the weighted-point
projection argument already used in the skeleton reduction. If W is the
sum just displayed, the two outer endpoint centers have directed
projection difference at least `1+W`: each endpoint contributes a
directional halfwidth of at least one half.

The two outer endpoints have not been assumed distinct. If they are the
same body, the projection difference is zero, contradicting `1+W>0`.
If they are distinct, both center norms are below 25/16, so the difference
is less than 25/8, whereas `1+W>=4`. Both alternatives are impossible.

Thus the r exceptional vertices form an independent set in the skeleton.

## 4. Two such vertices cannot have the same neighbor pair

Suppose H and H' both have neighbor set {A,B}. By Section 1 both give
width two between the same convex endpoint squares, so their directions
are the same closest-displacement direction, up to reversing A,B.

Choose B to be the double-S endpoint of H. Its two first transmitters
V1,V2 occupy one longitudinal unit interval next to B's support side.
The connection through H' leaves B on this same side. If B is the
double-S endpoint for H', it supplies two further first side transmitters. If B
is the direct endpoint for H', its first body is H' itself, which has a side
frame in the common direction by its effective-S property. In either
case there is at least one further unit square with the same longitudinal
interval and parallel frame.

That further square is distinct from V1,V2. The vertices H,H' are retained,
whereas V1,V2 are internal; and a suppressed-path internal body cannot
belong to two paths. Its overlap with B's unit side is positive: otherwise
their point-only vertex/vertex side-normal contact would violate the
selected normal convention. Together with V1,V2 it again gives three
disjoint unit transverse intervals each overlapping B's unit interval
positively, which is impossible.

Hence each unordered retained-neighbor pair supports at most one such H.

## 5. The body budget and finite-classification use

Each of the r vertices contributes two internal S bodies in its double
bundle, in addition to its own retained body. Two such double bundles
could share an internal S body only if that body's two retained endpoints
were the two exceptional vertices themselves. That would make them
adjacent, excluded by Section 3. Thus all 2r internal bodies are distinct.
There are already k+b retained bodies, so

```text
k+b+2r<=10,
r<=floor((10-k-b)/2),
3r<=10-k.
```

In particular r is at most two, and it is at most one when k>=5.

For a `b=1` raw record whose unique unloaded retained vertex has two
neighbors, Sections 1--2 give two new finite tests: their
loaded-loaded pair code must be zero, and their loaded angular separation
has the same lower bound as an SS connection. These are additional
necessary predicates, to be recorded as exclusions against the unchanged
raw catalog. For `b>=2`, the independent-set and distinct-neighbor-pair
conditions constrain the entire remaining finite family.

Contracting one of these configurations to an effective width-two
relation is only geometric bookkeeping. It changes graph degrees and
cycle counts, and it is not asserted to produce a new physical stress
with fewer square bodies.

## 6. Every width-two relation belongs to one matching

Call an unordered pair of distinct retained bodies a width-two relation
when their parallel supporting lines are separated by two. An actual SS
path supplies such a relation, as does Section 1 at an exceptional vertex.
The assertion below is geometric: it does not require either endpoint
to be loaded or require the relation to be a skeleton edge.

If A,B form a width-two relation, their center separation is at least
three, since each square contributes directional halfwidth at least one
half. The universal center bound therefore gives

```text
|c_A| >= 3-|c_B| > 23/16 > 5/4,
|c_B| > 23/16 > 5/4.
```

Any two distinct bodies occurring as endpoints of width-two relations
thus have center norms in `(5/4,25/16)` and center separation at least
one. Their center rays are more than 36 degrees apart. For completeness,
if their minor angle were at most `pi/5`, then
`cos(pi/5)>4/5` would bound their squared distance strictly above by

```text
f(x,y)=x^2+y^2-(8/5)xy.
```

Separate convexity puts the maximum over `[5/4,25/16]^2` at a corner.
The three different corner values are `5/8`, `225/256`, and `125/128`,
all less than one, a contradiction. This uses the annular-center
calculation from [ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md),
Section 1, with its lower-radius hypothesis now supplied by the
width-two relation instead of loading.

Suppose A has width-two relations with two different bodies B,C.
The W=2 cap theorem gives both minor angles A--B and A--C greater than
162 degrees. Thus the rays of B and C are each less than 18 degrees
from the antipodal ray to A. Their mutual minor angle is less than
36 degrees by the circular triangle inequality. This contradicts the
preceding annular-center bound. Consequently no endpoint has two
different width-two partners, proving the matching assertion.

Section 4 already excludes two exceptional vertices with the same
unordered neighbor pair. Therefore their neighbor pairs are pairwise
disjoint. Moreover neither member of such a pair can be incident to an
actual SS path: a different SS partner would contradict the matching
property, while its own partner is excluded by Section 2. Multiple
actual SS paths with the same endpoint pair are not excluded by the
matching statement alone.

## 7. At most one unloaded retained vertex has two neighbors

Use the jointly selected planar certificate. Sections 1--6 hold for that
same certificate, because its selection preserves the strict point-only
VV normal convention before the graph is classified.

Section 5 gives `r<=2`. Suppose equality, and name the exceptional
vertices H,H', with neighbor pairs {A,B} and {C,D}. The pairs are disjoint
by Section 6. Neither H nor H' belongs to either pair, by Section 3.
These are therefore six distinct retained bodies. The body budget gives

```text
6 <= k+b <= 10-2r = 6.
```

Thus these are all retained bodies, and the four distinct internal S
bodies of the two double bundles exhaust the remaining body budget.
Every other skeleton edge is direct: every nonempty suppressed path
would require at least one additional physical square.

Consider one endpoint, say A. It cannot be joined to B by Section 2.
It cannot be joined to H', whose two neighbors are exactly C,D. Apart
from its own connection to H, its possible neighbors are therefore C,D,
and those possible edges are direct. It cannot touch both C and D:
two touching unit squares have center distance at most `sqrt(2)`, so
the triangle inequality through A would give

```text
|c_C-c_D| <= |c_C-c_A|+|c_A-c_D| <= 2sqrt(2) < 3,
```

contrary to the width-two relation C--D. Hence A has at most two
distinct retained neighbors. The same argument applies to B,C,D.

If any of these endpoints were unloaded, it would have multigraph
degree at least three. The per-pair bundle multiplicity is at most two,
so it cannot have only one distinct neighbor. Having exactly two would
make it a third exceptional vertex, contrary to `r<=2`. All four
endpoints are consequently loaded, and `k=4,b=2`.

Their four successive circular center-ray gaps are each greater than
36 degrees. If the two disjoint pairs {A,B} and {C,D} did not alternate
in this order, both pairs would be adjacent boundary pairs. One of the
four successive gaps would then run directly from A to B, and a
different gap directly from C to D. Each of these two gaps is greater
than 162 degrees by Section 6 and the W=2 cap theorem: both circular
arcs between a width-two pair have this lower bound. The other two gaps
are greater than 36 degrees. Their sum would exceed
`162+162+36+36=396` degrees, contradicting 360 degrees. The two pairs
must therefore alternate in loaded circular order.

Choose one of the two S bodies in each double bundle. They give actual
positive-graph paths from A to B through H and its chosen S body, and
from C to D through H' and its chosen S body. The order of H and S on
its path depends on which endpoint is direct, but the two paths are
vertex-disjoint in either case. All their internal bodies are unloaded.
The planar selection theorem places the four loaded endpoints on the
disk boundary in their center-ray circular order. Two vertex-disjoint
paths with alternating boundary endpoints cannot be drawn in a disk:
one path, completed along a boundary arc, separates the endpoints of the
other. This contradicts that theorem's disk embedding.

Thus r cannot be two, and `r<=1`. This restriction holds across the
entire branching family, with arbitrary allowed k,b. It needs no new
catalog and changes none of the existing raw denominators or exclusion
counts by itself.
