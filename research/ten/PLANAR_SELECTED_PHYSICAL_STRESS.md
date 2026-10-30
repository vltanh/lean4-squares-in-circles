# A planar positive body-pair graph can be selected

**Status:** independently reviewed hand selection theorem (2026-10-29),
including joint compatibility with the loaded-VV polynomial selection.
This is a new choice of physical stress at a minimizing packing,
not a claim that an arbitrary physical body-pair stress graph is planar.
It is separate from, and unnecessary for, the diagonal-normal selection
used in the four-loaded five-cycle exclusion.

## 1. Statement and order of operations

At an unrestricted minimizing packing of unit squares, a normalized
physical force-and-torque stress can be chosen so that:

1. Every point-only vertex/vertex positive contact normal is strict,
   avoids both incident square diagonals, and is nonradial off the origin.
2. Its simple positive body-pair graph is planar.
3. All loaded vertices of that graph are incident to the exterior face; their
   exposure paths to their chosen circle vertices are mutually disjoint.

Here a graph vertex denotes a square. No claim is made that a graph edge
must be drawn as the straight segment between square centers or through
its final aggregated force application point. The planar embedding is
used only as a graph embedding; all force points and wrenches remain the
physical ones supplied by the construction below.

Choose the initial normals, obtain the stress, perform the local
replacements below, aggregate positive forces by body pair, and only then
classify its components and suppress unloaded degree-two bodies. Earlier
component identities or degrees need not survive these operations.

## 2. Coherent generic normal choices at four-square points

If four interior-disjoint squares contain one point p, each contributes
an interior angular sector of at least 90 degrees. Their sectors therefore
all have angle exactly 90 degrees and tile the full angle. After rotation,
the four squares are the NE, NW, SW, and SE quarters of the unit 2-by-2
block centered at p. Adjacent quarters share a full unit side; opposite
quarters intersect only at p.

At such a point choose positive numbers a,b with `a^2+b^2=1`. For the
opposite pairs choose the directions

```text
u=(a,b)       toward NE from SW,
v=(-a,b)      toward NW from SE.
```

Require `a!=b` and, when p is off the origin, choose their ratio so neither
direction is parallel to p. This excludes finitely many ratios from the
positive real interval, so a choice exists. Both directions are strictly
inside the appropriate common vertex normal cones and avoid the diagonals
of all four square frames.

At other point-only vertex/vertex contacts use
[generic normal selection](GENERIC_CONTACT_NORMAL_SELECTION.md). Each
such body pair has only its one shared point, so choices made at different
four-square points do not conflict. Choose all normals before the smooth
local constraints and multiplier argument. The unchanged strict
center-dilation qualification supplies a normalized physical stress.

This coherent choice can also retain the joint polynomial exclusions of
[LOADED_VV_GENERIC_RESTRICTION.md](LOADED_VV_GENERIC_RESTRICTION.md).
The compatibility must be checked because the two opposite-pair normals
at one four-square point are no longer independent variables. Use the
unnormalized chart `u=(1,t), v=(-1,t)` with t in a positive open interval;
normalize only after making all choices. Each individual direction is
still an affine function spanning the plane as t varies.

At a four-square point, each incident square belongs to exactly one
point-only VV pair, namely its opposite-quarter pair. Its other two
pairs there share positive-length sides. Consequently a concurrence
polynomial involving two VV pairs incident to one body never involves
both coupled opposite-pair normals at this point. If its other contact
is VV, that contact has an independent parameter: at another four-way
point, or at a separately parametrized non-four-way contact. If its
other contact is a fixed-normal point or a shared-side endpoint, its
normal is fixed as before. Thus every nonzero concurrence polynomial in
the linked selection remains nonzero after this parametrization, by
exactly its one- or two-variable argument. All diagonal and radial
avoidance factors remain nonzero too. The finite product therefore can
be kept nonzero on the open parameter box. The coherent and polynomial
selections are jointly possible, not merely separately possible.

In the n=10 radius window this also permits the additional open-interval
choices in
[SEVEN_RING_ALL_INNER_FACE_CAPACITY.md](SEVEN_RING_ALL_INNER_FACE_CAPACITY.md).
The opposite-corner midpoint intervals in
[LOADED_OUTER_VV_NORMAL_EXCLUSION.md](LOADED_OUTER_VV_NORMAL_EXCLUSION.md)
also satisfy the compatibility argument below. They concern disjoint VV
pairs from the earlier circle-adjacent intervals and impose one common
open interval that works for either endpoint's possible outer-body role.
The enlarged candidate range in
[LOADED_OUTER_CORNER_CLEARANCE.md](LOADED_OUTER_CORNER_CLEARANCE.md),
Section 2, uses that same midpoint prescription on the old candidates.
It is compatible for the same reason and is the range used in the
complete seven-ring exclusion.
Those choices concern only point-only VV pairs whose two incident squares
both have geometric circle vertices (and in the restricted cases have
unique circle vertices adjacent to the pair contact). Such a pair cannot
be an opposite pair at a four-square point when `R>sqrt(2)`.

Indeed the four squares fill `p+[-1,1]^2`. Only its outer corners can lie
on the containing circle: every other point lies in a nontrivial convex
combination of corners, and strict convexity of squared norm puts it
strictly inside the disk. If opposite quarters are both circle-loaded,
their opposite outer corners are both global farthest corners of this
block. Comparing either one with the two other outer corners forces both
coordinates of p to be zero. Their circle radius would then be sqrt(2),
contrary to the window.

Thus every contact subject to the additional VV interval restriction is
outside the four-way junctions. Its normal parameter remains independent
of the coherent four-way ratios. First shrink these non-four-way open
intervals as required by the capacity theorem, then apply the same
nonzero-polynomial product argument on the resulting open parameter box.
All these selections can therefore be imposed on one certificate.

## 3. Remove one crossing opposite-pair force at each four-way point

Work before aggregation, so side-contact endpoint atoms are retained.
Suppose both opposite pairs at p carry positive forces. Write their
repulsive forces on NE and NW as `lambda*u` and `mu*v`, respectively,
where lambda and mu are positive. Let `t=min(lambda,mu)`.

Subtract t from both opposite-pair coefficients. Add side-contact forces
of magnitude `t*a` to the top and bottom horizontal pair contacts, and
of magnitude `t*b` to the left and right vertical pair contacts, all
acting at the same physical point p. These are allowed forces at an
endpoint of each actual positive-length shared unit side.
In fact these endpoint atoms are among the side-contact rows already
present in the initial sufficient local branch; no new contact geometry
or unsupported gradient is introduced.

The added resultant on each quarter is:

| Square | Added resultant |
| --- | --- |
| NE | `(t*a,t*b)` |
| NW | `(-t*a,t*b)` |
| SW | `(-t*a,-t*b)` |
| SE | `(t*a,-t*b)` |

These are exactly the resultants removed from the two opposite-pair
forces. All contributions act at p, so each square's torque about any
origin is also unchanged. Circle forces and their normalization are
unchanged. Every remaining and added coefficient is nonnegative, and
at least one of the two opposite-pair coefficients becomes zero.

Do this at every four-square point with two positive opposite pairs.
The process is finite. It cannot recreate an eliminated opposite pair
elsewhere: that pair has singleton intersection {p}, whereas all added
pairs share positive-length sides. A pair with singleton intersection has
only its original chosen normal, so the generic strict/nonradial choices
remain true for every surviving point-only positive pair.

Finally aggregate the parallel side-contact atoms of each body pair at
their weighted-average point in their actual shared segment. This
preserves each force and torque and creates no new body-pair edge.
The resulting positive pair graph has at most one opposite-pair edge at
every four-square point.

The replacements may increase the number of positive contact atoms.
No bound of 30 atoms, or any other sparse-atom bound, is asserted or used
for this selected stress. The later skeleton bounds use the physical
number of square bodies and geometric degrees instead.

The polynomial selection just discussed remains available for the final
stress: surviving point-only VV normals have not changed, and all the
point-contact and shared-side-endpoint candidates in those polynomials
were fixed from the geometric packing before any stress was selected.
If the final graph has a loaded seven-ring, its restriction is therefore
derived anew from those unchanged nonvanishing polynomials and its
physical equilibrium equations. No old component is transferred through
the replacements.

## 4. Construct a planar embedding of the resulting pair graph

Temporarily retain the physical contact atoms before aggregation. Draw
the incidence segments from square centers to their contact points.
Except for a contact endpoint, each segment lies in its square's open
interior. Segments from different squares cannot intersect there, and
segments inside one square meet only at its center unless they have the
same contact endpoint. Thus this is a planar incidence network, with
contact junction degree at most four, as in Section 4 of the pinned
[physical-stress source](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/PHYSICAL_CONTACT_STRESS.md).

Take disjoint small disks around the distinct contact points, avoiding
all square centers. At each contact, replace its incidence junction by
local arcs joining the square-sector ports for the positive body pairs:

* Two ports require at most one connection.
* Three ports require a subgraph of the triangle, which is drawable
  without crossings with those ports in their circular order.
* Four ports occur in quarter-square order. The available edges are a
  subgraph of the four perimeter pairs plus at most one diagonal, by
  Section 3. This is drawable without crossings in that circular order.

If several edges use the same incidence segment, separate their nearby
tracks inside a narrow neighborhood of that segment and inside the
corresponding square. The tracks can fan out at the square-center graph
vertex and reach their contact ports in the prescribed order. Distinct
incidence segments have disjoint such neighborhoods away from their
shared center. This gives a planar drawing of the contact-atom multigraph
on square vertices. Delete parallel copies of the same pair to obtain
the simple positive body-pair graph; deletion preserves planarity.

This construction does not move a force application or a square. A graph
edge's auxiliary drawing may differ from the physical force line and
from the averaged application point after aggregation.

## 5. Loaded vertices remain exposed to the exterior

Choose one circle vertex w of each loaded square. A point of the containing
circle cannot belong to two packed squares, by the reviewed circle-point
lemma. The segment from that square's center to w has its nonendpoint
portion in the square's open interior and meets the incidence drawing
only at its center. Different chosen exposure segments lie in different
square interiors and are disjoint.

The contact points are strictly inside the containing disk and distinct
from every chosen circle vertex. The local contact disks and the narrow
edge-track neighborhoods in Section 4 can therefore be chosen to avoid
all these exposure segments except at their own square centers. Extend
each exposure segment outward past w. This supplies a path from the
loaded graph vertex to the unbounded face without crossing any graph
edge or other exposure path. Hence every loaded vertex is incident to
the exterior face.

In the n=10 radius window, every chosen circle vertex deviates from its
loaded center ray by at most `beta=asin(1/(2R))`, by Section 4 of
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md). In fact
`beta<pi/12`: the window gives `1/(2R)<=20/79`, while

```text
sin(pi/12)^2=(2-sqrt(3))/4 > 1/15 > (20/79)^2.
```

Here `sqrt(3)<26/15` follows from `675<676`, and the last comparison is
`6000<6241`. Distinct loaded center rays have minor separation greater
than `pi/5`, by Section 1 of
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md).
Their open `pi/12` neighborhoods are therefore pairwise disjoint because
`2(pi/12)=pi/6<pi/5`. Choosing one circle vertex in each such neighborhood
preserves the cyclic center-ray order.

The embedding can
equivalently be regarded as a disk drawing with the loaded vertices on
its boundary in that prescribed circular order and all other retained
vertices inside. Suppressing unloaded degree-two paths preserves this
planar disk drawing and can create parallel edges, but not loops by the
earlier unloaded-set lemma.

## 6. Classification consequence and boundary

For `b=0`, the selected skeleton has an outerplanar drawing with its
loaded circular order fixed. No two skeleton edges with four distinct
alternating loaded endpoints can occur, including a D-D pair. The older
raw catalog that allowed D-D alternation is still a finite covering
catalog; the additional selected-certificate condition can exclude such
records without changing their stable IDs.

For `b>0`, the appropriate finite records are planar disk multigraphs
with k prescribed boundary loaded vertices and b unlabeled interior
retained vertices, together with the already reviewed seven-symbol edge
alphabet, body costs, degrees, and loaded-cut conditions. This theorem
does not itself enumerate those records or exclude their geometrically
realizable completions. No atom-count refinement or Lean verification is
claimed.
