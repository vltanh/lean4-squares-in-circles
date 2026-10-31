# The three-loaded six-cycle with an SS path and a diagonal path is impossible

**Status:** complete hand proof; two integrated mathematical reviews passed
on 2026-10-29, including the exhaustive contact classification.

Choose the physical certificate using
[GENERIC_CONTACT_NORMAL_SELECTION.md](GENERIC_CONTACT_NORMAL_SELECTION.md)
at the minimizing packing, before classifying its positive components.
Suppose a whole positive component has three loaded bodies A,B,C, a
direct A--B edge, an SS path from C to A, and a single D transmitter
from C to B. Its stable inventory entry is

```text
C20-M06-L03-B01-T02: LLDLSS.
```

Work in `79/40<=R<=3/sqrt(2)`, with the imported lower-radius dependency
stated in [CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md).

**Theorem.** No such component can occur in the selected certificate.
This entire signature is excluded in the selected-certificate lower-bound
reduction for a strictly subcritical ten-square packing.

## 1. Transmission geometry and the first two branches

All internal path bodies have degree two in the whole positive component.
Their force and torque equations therefore produce straight paths of
widths two and `sqrt(2)`. The endpoint squares are supported at their
corresponding far contacts, and A,B touch by their positive edge.

If the two outgoing directions at C are parallel, the reviewed
[width-two parallel exclusion](SS_PATH_PARALLEL_EXCLUSION.md) applies.
It covers both equal and opposite directions.

Otherwise distinguish C's geometric circle contacts. A loaded square
has either one or two circle vertices in this radius window; three would
put its center at the disk center with radius `1/sqrt(2)`.
If C has two circle vertices, the
[radial-side SS/D exclusion](SS_PATH_RADIAL_SIDE_DIAGONAL_EXCLUSION.md)
applies. It uses the generic normal selection explicitly to make the D
contact a relative side-interior point on both of its loaded neighbors.
It proves that the D endpoint is strictly circle-clear.

## 2. The unique-circle-vertex branch is exhaustive

Suppose C has a unique circle vertex. Every path contact lies on its
boundary and is either a vertex or a relative side-interior point. A
circle vertex cannot be a pair contact, by the common-circle-point
lemma in [VERTEX_CONTACT_MIXED_FIVE_CYCLE.md](VERTEX_CONTACT_MIXED_FIVE_CYCLE.md).

If the two contacts coincide at a vertex, Section 1 of
[SS_PATH_VERTEX_SUPPORT_EXCLUSIONS.md](SS_PATH_VERTEX_SUPPORT_EXCLUSIONS.md)
excludes them. Coincidence in a side interior would make both directions
parallel, already excluded.

If both distinct contacts are vertices, Section 2 of that same note
excludes every pair. Its only additional width-two equality case has
`W1=1,W2=2` and is explicitly circle-clear; thus no five-cycle width
restriction is silently retained.

If both forces are side normals, their nonparallel directions are
perpendicular. The projection argument in Section 3 of that note forces
both widths to be one, contradicting the SS path. This also excludes a
vertex contact whose selected normal is on the boundary of its normal
cone.

The only remaining possibility has one strict vertex support and one
relative side-interior support. Section 3 of the same note checks that
the earlier nonincident support exclusion and force-balance signs use
only path widths at least one. They therefore put these contacts in the
incident opposite-corner/inner-side normal form.

The [incident width-two exclusion](SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md)
then applies, regardless of which contact starts the SS path. Its
vertex-starting case violates the containing disk's diameter; its
side-starting case places a unit normal step of the far endpoint outside
the disk by an explicit positive polynomial identity.

Every branch is excluded. This proves the theorem for the entire stable
entry `C20-M06-L03-B01-T02`.

The companion word `LLSLSS` requires a separate radial-side SS/S argument;
it is not closed by this theorem. No claim about the remaining larger
cycle signatures, branching components, or global n=10 optimality is
made here.
