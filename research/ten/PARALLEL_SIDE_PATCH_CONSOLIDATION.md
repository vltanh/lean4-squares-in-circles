# A two-column side patch can be consolidated to one side-side path

**Status:** reviewed hand normalization; root and independent full
mathematical reviews passed on 2026-10-30, including the open-center-chord
cavity proof, all interval endpoint choices, motions, wrenches, and stable
certificate properties. This supplies a different minimizing packing and physical stress.
It does not exclude the original realization, preserve its raw case ID,
or change any fixed-family closure status.

Suppose an unloaded set U has precisely two outside body-neighbors A,B,
all its positive contact forces are parallel, and its physical geometry
consists of one or two side bodies in each of two consecutive unit-width
columns. Every first-column body has positive contact to A and to the
second column; every second-column body contacts B and the first column.
All positive contacts with an endpoint in U belong to this patch. The
strict point-only VV convention is in force.

These are the local W=2 hypotheses supplied for arbitrary-terminal
connected patches by
[TWO_TERMINAL_UNLOADED_PATCH_REDUCTION.md](TWO_TERMINAL_UNLOADED_PATCH_REDUCTION.md).
They also hold for a double-SS bundle, whose two two-body paths give a
possibly disconnected U. Parallelism is an explicit hypothesis here;
this note does not establish it for an arbitrary two-terminal region.

**Local theorem.** If U has three or four bodies, move at most one body
in each column and replace the whole patch stress by one SS path through
two of its physical bodies. The other one or two bodies stay in the
packing, entirely unstressed. The radius, all forces outside the patch,
the aggregate force and torque at each terminal, and all circle loads
remain unchanged. The stable certificate properties listed in
[DOUBLE_SIDE_BUNDLE_CONSOLIDATION.md](DOUBLE_SIDE_BUNDLE_CONSOLIDATION.md)
are preserved. For connected U, at most one body needs to move.

## 1. Three bodies reduce by the double-S theorem

If one column has two bodies and the other has one, each body in the
double column has exactly two positive neighbors: its adjacent terminal
and the body in the single column. These are a double-S bundle. Its
reviewed consolidation removes one active body and preserves the entire
wrench at the body in the single column. That body now has exactly two
opposite horizontal forces, at the same height by torque balance. Thus
the surviving patch is an SS path. Reflection covers the other column
order.

It remains to treat two bodies in each column.

## 2. Ordered intervals force the two straight intercolumn contacts

Use translated local coordinates with columns `[0,1]` and `[1,2]`.
Name the lower and upper bodies in the first column L1,L2, and in the
second R1,R2. Their vertical intervals are

```text
I_1=[a,a+1],       I_2=[b,b+1],       b>=a+1,
J_1=[c,c+1],       J_2=[d,d+1],       d>=c+1.
```

Two bodies at each terminal force parallel side support there, by the
reviewed bundle argument. Therefore

```text
A=[-1,0] x I_A,       B=[2,3] x I_B,
```

where I_A,I_B have length one. Every positive horizontal pair contact has
positive-length interval overlap. A singleton would be a point-only VV
contact carrying a side normal, contrary to the selected convention.

There are no positive within-column contacts: the positive force direction
is horizontal, and its oriented endpoint-center projection strictly
increases. The two crossing intercolumn pairs L1--R2 and L2--R1 cannot
both have positive-length overlap. They would require

```text
d<a+1<=b<c+1<=d,
```

a contradiction. Since each column body has an intercolumn positive
neighbor, both straight positive edges L1--R1 and L2--R2 are necessary.
Indeed, omitting either straight edge would require both crossing edges
to supply neighbors for its two endpoints.

Thus the intercolumn positive graph has the two straight edges and at
most one crossing edge. If U is connected, it has exactly three edges
and is a four-vertex alternating path.

## 3. The possibly stepped gap contains no other physical square

Let the open gap intervals in the columns be

```text
K_L=(a+1,b),       K_R=(c+1,d).
```

Either may be empty. Their lengths are below one, because both column
intervals overlap their common terminal unit interval positively.
The positive straight overlaps imply

```text
c<a+1<=b<d+1,
a<c+1<=d<b+1.                                      (1)
```

Consequently the entire left gap lies inside the right column's convex
vertical span `[c,d+1]`, and the entire right gap lies inside the left
column's span `[a,b+1]`.

Define the open free set between the two rows by

```text
F=((0,1) x K_L) union ((1,2) x K_R)
  union ({1} x (K_L intersection K_R)).              (2)
```

The last term makes this set open at the common column interface. The
outer vertical boundary is occupied by A and B; the top and bottom of
each gap cell are occupied by its column bodies. At the interface x=1,
(1) ensures that a gap point not in the opposite gap belongs to a body
of the opposite column. Hence every boundary point of F is in one of
A,B,L1,L2,R1,R2. F may have two components or no component at all.

No other unit square meets F. Otherwise its connected interior, disjoint
from the six closed obstacle bodies, would meet one component and be
unable to leave it across the occupied boundary. The entire square would
lie in that component's closure. Its center is an interior point and
therefore lies in F. But the vertical section of F at any first-coordinate
has length below one: it is K_L, K_R, or their intersection.

The open vertical chord through the square's center lies in its interior
and therefore in the same component of F. Its length is at least one:
for a frame at angle theta it is
`1/max(|cos(theta)|,|sin(theta)|)>=1`. This contradicts the section of
the open set F having length below one at that first-coordinate. Using
the interior here avoids any assumption about a section of the closure
at the column interface. The contradiction excludes an intersection of
interiors, and closure then excludes even a boundary-only intersection
with the open set F.

For a connected four-body patch there is a simpler description. Suppose
the third positive edge is L1--R2. Then

```text
a<c+1<=d<a+1<=b<d+1.
```

The right gap is strictly inside L1, and the left gap is strictly inside
R2. Each gap rectangle is separately sealed by its terminal, its two
column bodies, and one body of the opposite column. Their height ranges
are disjoint. The reflected third-edge case has the same property.

## 4. The whole patch determines one aggregate height

Summing the original force equations over U shows that the total positive
horizontal force magnitude F_0 entering from A equals that leaving to B,
and F_0>0. Let m_A,m_B be the force-weighted mean contact heights at these
two interfaces. Summing the original torque equations over U about the
original disk center cancels every internal contact wrench and gives

```text
F_0*(m_A-m_B)=0.
```

Thus `m_A=m_B=:m`. One horizontal path with magnitude F_0 at height m
will preserve both aggregate endpoint resultants and torques.

Moreover m lies in the relative interior of each terminal unit interval.
At A both first-column bodies carry positive incoming force. If their
weighted mean were an endpoint of I_A, every contributing height would
equal that endpoint. Both disjoint column intervals would contain it and
would meet there. One would then overlap I_A only at that point, contrary
to the positive-length overlap. The argument at B is identical. Also m
lies strictly between the bottom of the lower body and the top of the
upper body in each column: both bodies carry positive force, and their
contact heights belong to the two ordered, interior-disjoint unit
intervals. Thus an outer endpoint of the whole column span cannot be m.

## 5. Choose one physical side body at height m in each column

Consider a column in which m belongs to a positive-height gap. Translate
its lower body upward until its top has passed m by a sufficiently small
positive amount, while remaining below the original upper body's bottom.
Then m belongs to the moved body's side interior. At an endpoint of a
positive-height gap, an arbitrarily small translation of the appropriate
bordering body into the gap has the same effect.

These motions are exactly the motions proved in the double-S theorem.
The newly occupied strip is inside that column's empty gap cell, so there
is no overlap with any unchanged physical square. Its points lie in
convex combinations of corresponding points of the two original column
bodies, so the moved square stays in the containing disk. If both columns
need a motion, they are still interior-disjoint because their open
horizontal column intervals are disjoint. A motion in one column cannot
occupy the interior of the other column's gap cell.

In a column where no such motion is needed, choose an existing body
containing m. If either chosen interval contains m in its interior, the
two chosen intervals have positive-length overlap. The only ambiguity
comes from a zero-height gap at m. Either bordering body may then be
chosen. Choose the body on the same side of m as the other column's
chosen body; if both columns have zero-height gaps at m, choose both
lower bodies. The two selected intervals again have positive overlap.
Their terminal intersections have positive overlap as well, because m
lies in the interior of I_A and I_B.

Thus the chosen bodies give a physical SS path at height m, with no
point-only VV side-normal contact. At most one body in each column has
moved. For connected U, the gap height ranges are disjoint by Section 3,
so at most one column can require a motion. Its opposite-column sealing
body already contains m in its interior and can be used unchanged.

## 6. Concentrate the forces on that path

Set all old forces with an endpoint in U to zero. On the selected path
put opposite horizontal forces of magnitude F_0 at the common height m.
Each selected side body has zero resultant and torque. Section 4 proves
that the aggregate wrench on A and on B is exactly its previous one.
Keep all other forces and all circle weights unchanged. The unused patch
bodies remain present as entirely unstressed physical obstacles.

Every changed positive incidence is SS. All positive point-only VV pairs
outside the patch, with their geometric positions and chosen normals,
remain unchanged. At a new four-square junction, a moved body has no
positive opposite-quarter VV pair, so at most the other opposite pair
is positive. At old junctions no added positive VV edge occurs. Thus the
at-most-one-positive-opposite-pair condition remains valid, permitting
reconstruction of physical planar routing with its force-normal order.

The patch still connects A to B and has no other outside neighbor.
Therefore connectivity of the full positive component is preserved,
after removing unused active vertices. Every loaded body and its circle
load stays fixed. A mixed component remains mixed because two unloaded
side bodies remain on the replacement path. Other components are
unchanged. In particular no entirely loaded positive component is created.

In the disconnected double-SS case, the selected intercolumn contact may
have carried zero force before consolidation. The proof does not claim
that the new positive graph is always a subgraph of the old one. It uses
the preserved physical junction condition to reconstruct planarity;
all new positive contacts have positive-length shared sides. Component
connectivity and the loaded boundary order are unchanged nonetheless.

## 7. The normalized structural consequence and its exact scope

Use the minimum-active-body normalization class of the double-S theorem:
physical nonnegative equilibrium at the same minimizing radius, all ten
squares retained, strict/nonradial/nondiagonal positive point-only VV
normals, physical four-junction planarity and loaded boundary order, and
no entirely loaded positive component. This class is preserved by the
operation above. A minimum member cannot contain a three- or four-body
patch of the stated kind, because consolidation reduces its number of
active bodies. In particular it has no double-SS bundle either.

Together with double-S consolidation and the original exclusion of
parallel diagonal paths, its suppressed skeleton is simple. Every
unloaded retained vertex has at least three distinct retained neighbors.
The reviewed arbitrary-terminal parallel-force theorem now supplies the
needed scope: every unloaded connected component obtained after deleting
two terminal bodies reduces to S, D, or SS, with no retained unloaded
branching vertex inside it.

This remains a choice of minimizing representative, not an exclusion of
the original realization. The old generic-selection polynomials for
unused geometric contacts are not asserted to survive motion. A proof
using this normalization must use the stable properties just listed,
or separately establish compatibility with any stronger convention.
No raw family is declared closed solely because its representatives can
be moved to a different graph. Regions with three or more outside
body-neighbors remain a separate structural and completion problem.
