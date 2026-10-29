# The selected loaded ring must use an outer edge at a weak opposite-corner body

**Status:** hand extension; two independent full mathematical reviews
passed on 2026-10-29, including the U8/U9 degenerate triangles and the
unchanged cap, normal-selection and boundary hypotheses.

Use the radius minimizer and the selected physical stress of
[SEVEN_RING_ALL_INNER_FACE_CAPACITY.md](SEVEN_RING_ALL_INNER_FACE_CAPACITY.md).
All its normal choices, including the finite-polynomial and dangerous-VV
open-interval restrictions, remain unchanged.

**Theorem.** Every entirely loaded positive seven-ring of this selected
stress contains a unique-circle body of type U4 or U5.

Thus the only remaining local obstruction in C04 is an outer-edge/opposite-
corner mixed body. Radial-side bodies, unique-circle U8/U9 bodies, and all
pair-contact types can be included in the inner-face capacity argument
when U4/U5 are absent. This is a necessary condition, not a proof excluding
U4/U5 or an unrestricted n=10 proof.

## 1. The two additional vertex/vertex body rows have a core contact

The all-pair theorem already handles unique-circle rows U1,U6,U7,U10.
Rows U2/U3 are impossible by the independent incident mixed exclusion.
To prove the theorem it remains to allow U8 and U9 in the capacity proof.
Keep the square labels of the ownership alphabet:

```text
W=(1,1) is the unique circle vertex,
A=(0,0) is the opposite corner,
B=(1,0), C=(0,1) are the adjacent noncircle corners.
```

The two additional rows are

```text
U8: B -> A,       U9: A -> C.                         (1)
```

Choose the same core corner A as for every unique-circle body. On U8,
the within-body inner path is the single side from B to A. On U9 it is
the single side from A to C. These paths have the same counterclockwise
hole orientation as the corresponding portions of the U10 path B->A->C.
They are simple and have distinct endpoints.

At each strict V incidence at A, the contact equals the body's core.
The associated contact triangle is therefore degenerate and contained
in the segment joining the two incident core corners. It contributes
zero to the oriented triangle identity. At the other V incidence, the
contact is adjacent to W and its unit segment to A is exactly the old
inner-side geometry. No change to the core-radius bound is needed.

## 2. Every nondegenerate triangle retains a reviewed bound

The new rows have no S incidence, so every S body still has one of the
source or inner mixed patterns already handled by the proper cap and
shared-side theorems. All the geometric and force hypotheses of those
local S-body estimates are unchanged.

For an SV/VS pair whose V contact is A, its triangle was just removed as
degenerate. Otherwise the V contact is adjacent to the chosen circle
vertex, so the nondegenerate triangle has exactly the local form used in
the reviewed cap theorem, including the acute frame angle and the unit
core edge. That theorem does not constrain the V body's other contact.
It applies without change to the nondegenerate V incidence of U8/U9.

For a VV pair, the generic VV restriction actually prevents U8/U9 from
being its unique-circle endpoint: such an endpoint would need an S other
pair, while these bodies have two strict V incidences. Thus every
nondegenerate VV triangle in the extended scope is already included in
the all-pair theorem. Even without this shortcut, an opposite-core
incidence would make its triangle zero, and all remaining V incidences
would have the same circle-adjacent geometry.

Consequently every nondegenerate contact triangle still puts each
inner-square vertex in the centered disk of squared radius `83/50`.
Degenerate triangles lie in the core hull, whose squared radius is below
`36/25`.

## 3. The global boundary proof remains valid

Use the same geometric contact choices as before: the inner endpoint of
a shared-side overlap for SS pairs, and the actual single point for all
other pairs. The U8/U9 paths of Section 1 meet their neighbors only at
those contacts, and nonneighbors do not touch. If a core already equals
a contact, remove the resulting zero-length segment. The full boundary
is still simple and winds once about the origin; the same body-path
homotopy and connected-interior argument encloses all three inner squares.

Its oriented chain still equals the core polygon plus the sum of its
counterclockwise or degenerate contact triangles. Every triangle made
degenerate by (1) has its contact at a core endpoint, so it cannot
contribute a point outside the core convex hull. The winding-number
containment argument and all strict radius estimates therefore survive.

All three inner squares would lie in the centered disk of squared radius
`83/50`, contradicting `425/256-83/50=1/6400>0`. This excludes the enlarged
set U1,U6,U7,U8,U9,U10, with arbitrary radial bodies and pair ownership.
After U2/U3 have been excluded, only U4/U5 remain, proving the theorem.

The U4/U5 restriction is geometric: their S support is on the outer edge
not incident to the opposite V corner. It does not identify the circle-
load weights, frames, or contact positions, and it does not assert that
either row has a realization in a complete seven-ring.
