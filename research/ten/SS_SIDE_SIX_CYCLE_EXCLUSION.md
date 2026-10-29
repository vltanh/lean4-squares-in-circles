# The three-loaded six-cycle with SS and S paths is impossible

**Status:** hand proof; root and independent integrated mathematical
reviews passed on 2026-10-29, including every radial-side case.

At a minimizing packing, choose the physical certificate with the
strict contact normals specified in
[GENERIC_CONTACT_NORMAL_SELECTION.md](GENERIC_CONTACT_NORMAL_SELECTION.md)
before classifying its positive components. Suppose a whole positive
component has three loaded bodies A,B,C, a direct A--B edge, an SS path
from C to A, and a single S transmitter from C to B. Its fixed signature
is

```text
C20-M06-L03-B01-T01: LLSLSS.
```

Work in `79/40<=R<=3/sqrt(2)`, with the imported radius dependencies
unchanged from [CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md).

**Theorem.** This component is impossible in the selected certificate.
The entire signature is excluded in the selected-certificate lower-bound
reduction for a strictly subcritical ten-square packing.

## 1. Parallel directions and a radial-side central body

If the outgoing transmission directions at C are parallel, apply
[SS_PATH_PARALLEL_EXCLUSION.md](SS_PATH_PARALLEL_EXCLUSION.md), which covers
equal and opposite directions and both possible short-path types.

Otherwise, if C has two geometric circle vertices, apply
[SS_PATH_RADIAL_SIDE_SIDE_EXCLUSION.md](SS_PATH_RADIAL_SIDE_SIDE_EXCLUSION.md).
Its proof first obtains L>=1 from the SS endpoint. The
[side-endpoint height bound](RADIAL_SIDE_S_HEIGHT_BOUND.md) separates the
two loaded endpoints when the SS contact is a corner. For a side-interior
SS contact, a hypothetical A--B contact gives a strict force triangle
around zero; its positive radial concurrence contradicts the horizontal
SS force line. This treats all geometric support types of A and B and
all circle-load splits on the radial-side central body.

## 2. A unique-circle central body

C has at most two circle vertices in the radius window. It remains to
consider one circle vertex and nonparallel outgoing directions.

Each path contact is a vertex or a relative side-interior point. A
circle vertex cannot be shared with another square. The following tests
are exhaustive:

1. Coincident vertex contacts are excluded by Section 1 of
   [SS_PATH_VERTEX_SUPPORT_EXCLUSIONS.md](SS_PATH_VERTEX_SUPPORT_EXCLUSIONS.md).
   A coincident side-interior contact would make the directions parallel.
2. Two distinct vertex contacts are excluded by Section 2 of that note,
   including the width-two equality case in the old projection argument.
3. If both selected directions are side normals of C, they are
   perpendicular in the present nonparallel branch. Section 3 of that
   note shows that endpoint contact would force both path widths to be
   one, contradicting the SS path. A boundary normal at a vertex belongs
   to this test too.
4. The remaining strict-vertex/relative-side-interior pair is reduced by
   the same section to the incident opposite-corner/inner-side normal
   form. The reduction uses only path widths at least one.
   [SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md](SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md)
   excludes that form whether the SS path starts at the vertex or side.

Every case is impossible. This closes the whole stable entry
`C20-M06-L03-B01-T01` in the selected-certificate reduction. It does not
close the other larger-cycle signatures or the unrestricted n=10 theorem.
