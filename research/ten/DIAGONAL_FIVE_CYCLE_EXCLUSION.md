# Excluding the four-loaded diagonal five-cycle in the chosen certificate

**Status:** reviewed hand exclusion for the strengthened certificate choice
(2026-10-29); the generic selection and nearer-endpoint exclusion have
independent mathematical reviews. No assertion is made that every possible
physical stress on every packing avoids this component.

Use the physical stress certificate selected in
[GENERIC_CONTACT_NORMAL_SELECTION.md](GENERIC_CONTACT_NORMAL_SELECTION.md).
At each point-only vertex/vertex contact, its fixed normal is strictly
inside both supporting cones and avoids every diagonal direction of both
incident squares. The choices also retain the earlier nonradial condition
at contacts away from zero. The physical-stress construction supplies a
certificate after these choices are made; no existing stress is perturbed.

Work in the explicitly imported ten-square radius window

```text
5/2+sqrt(2) < R^2 < 9/2.
```

**Theorem.** No whole positive component of this selected certificate is a
five-cycle with precisely four loaded bodies. Thus the C19 diagonal branch
is excluded for the certificate used in the unrestricted lower-bound
reduction. Together with the existing side-transmitter exclusion C18, this
closes the four-loaded five-cycle family in that reduction.

## 1. A diagonal transmitter has side-supported endpoint neighbors

An unloaded degree-two square has equal opposite forces. Torque balance
makes their actual application points collinear in the force direction.
The existing transmission classification gives either a side transmitter
or a diagonal transmitter.

In the diagonal case, the two application points are opposite vertices,
and the force direction is a diagonal of the transmitter. That normal is
strictly inside its vertex's supporting cone, so the corresponding
supporting line meets the transmitter only at that vertex. Its geometric
intersection with its neighbor is consequently a singleton.

If the application point were also a geometric vertex of the neighbor,
this would be a point-only vertex/vertex contact. The selected normal at
such a contact avoids the transmitter's diagonal, a contradiction.
Therefore each neighbor is contacted in the relative interior of a side.
In particular, its support feature there is S.

This conclusion uses the selected certificate. It does not replace the
force direction of a pre-existing diagonal transmitter or claim that
arbitrary physical stresses satisfy the same restriction.

## 2. The nearer endpoint cannot have side support

Suppose a component were

```text
U-A1-A2-A3-A4-U,
```

with exactly the four A bodies loaded. The
[four-loaded five-cycle theorem](MIXED_FIVE_FOUR_LOADED.md) already excludes
a side transmitter, so U must be diagonal.

Choose the loaded endpoint at U's contact nearer the disk center. Sections
1--4 of
[DIAGONAL_FIVE_CYCLE_NEAR_ENDPOINT.md](DIAGONAL_FIVE_CYCLE_NEAR_ENDPOINT.md)
prove, in precisely the same radius window, that this endpoint cannot have
support feature S. This includes support-edge application at either
endpoint; the result is stronger than the relative-interior exclusion
needed here. Its feature must instead be a strict vertex, and the opposite
vertex is its unique circle vertex.

Section 1 of the present note makes that same endpoint a side-interior
contact. The contradiction excludes the component.

The extra concurrence conclusion in Section 5 of the nearer-endpoint note
is not needed for this exclusion. The proof uses no completion-capacity
estimate, numerical search, or claim that a mixed component inherits the
all-loaded ring's convex enclosure theorem.

## 3. Scope of the progress update

The finite stress roadmap starts by choosing one certificate furnished by
the physical-stress construction. It may choose the strengthened version
above because the normal choices occur before the multiplier theorem.
All earlier reductions retain their premises: original physical contact
points, positive forces, strict supporting cones at point-only corner
contacts, and the earlier off-origin nonradial normal choice.

The generic-selection lemma and Sections 1--4 of the nearer-endpoint proof
have passed root and independent reviews. Accordingly C19 is hand-closed. This is an exclusion of
C19 in the selected-certificate route to the ten-square lower bound.
The unrestricted lower bound remains open while other roadmap families
remain unresolved, and no Lean theorem is supplied by this manuscript.
