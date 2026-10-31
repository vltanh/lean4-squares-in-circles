# Independent review: the full-star four-neighbor common-corner chain exclusion

Date: October 28, 2026 UTC. Reviewer: review_resume continuation.

## 1. Exact reviewed source and verdict

**PASS.** I read the entire frozen source
`UNLOADED_COMMON_CORNER_FOUR_NEIGHBOR_CONTACT_CHAIN_EXCLUSION.md`
and independently rederived its support geometry, complete normal-sign
cover, and full-star force contradiction. I also read the complete
operative input `UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md`, including its
self-contained proof of the support-span statement. No source edit is
needed. I did not contribute to the discovery of this theorem.

The reviewed source is exactly 6,964 bytes, SHA-256

`96ab1fde361d3967d035b080f6c00dcfb2163b03538b878889a9c4e291d94115`,

with Git blob `3bf230c868f215dcfd342c9538b8868cfc69c233`.

Its sole direct input matches exactly:

| Input | SHA-256 | Checked role |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete degree-free support span and owned-axis triangle restriction |

The separately frozen three-neighbor/common-corner forcing theorem is
not a dependency of this source. I read it as context, but the present
four-neighbor result has its own full sign argument and does not inherit
a verdict merely from that earlier review.

## 2. Literal physical domain and arbitrary positive degree

The actual unloaded U retains its entire positive neighbor set. Four
distinct actual neighbors A,B,C,D have the physical contacts AB, BC and
CD. Those three contacts need not themselves carry a selected positive
force. Original U-to-A and U-to-D normals strictly expose the same
actual U vertex. Every remaining original force, except those toward
the displayed four neighbors, lies in that vertex's closed outward
normal cone.

All original positive pair magnitudes remain. An extra vector on a cone
axis may apply anywhere on its own actual support side. The proof uses
only its vector components and never relocates that side mean to the
vertex. The original torque equation remains available but is not a
premise needed for the contradiction. No circle, boundary mask, neighbor
degree, neighbor force equation, or preselected free-normal condition is
assumed.

Thus the theorem genuinely permits any positive degree for U, provided
the printed sign premise covers every additional original force. It
does not obtain a degree-four equation by omitting extra neighbors.

## 3. Complete minimum-support reach, including side means

I independently checked the strict reach statement used in the source.
If Q is an actual minimum-n point of a unit and n dot e<0 for a unit
direction e, its entire e-reach from Q is strictly less than one.

At a vertex Q, write the actual inward orthonormal axes as r,s. Their
n components are nonnegative. Both e components cannot be positive:
resolving e in this basis would make n dot e nonnegative. Only one
positive component can contribute to the maximum, and it cannot equal
one, since equality would make e that inward axis and again give
n dot e>=0. The zero-component possibilities satisfy the same strict
bound. If neither e component is positive, the maximum reach is zero.

At a side-interior support, the inward normal axis has strictly negative
e component. Only the actual tangent interval can contribute positively.
Its length is at most one, and its projected unit component has absolute
value strictly below one because n dot e is nonzero. This proof retains
the original tangent parameter and both possible closed endpoints.
The latter endpoints also have the already checked vertex proof.

No hypothesis about the other unit at the support is needed for this
whole-unit bound.

## 4. Both physical consequences have the required strictness

In the actual chart U=[0,1]^2, a strict Southwest neighbor at (0,0)
lies wholly in x<1 and y<1 by the preceding reach bound. A strict
Northeast neighbor at (1,1) lies wholly in x>0 and y>0. Any common
point would therefore lie in the open interior of U. A point of a
different full closed square in int U is itself impossible: arbitrarily
close interior points of that square remain inside int U. Thus the two
opposite strict-corner neighbors are closed-disjoint. Reflection gives
the other diagonal pair. This is stronger than an assertion only about
their open interiors or selected applications.

For the owned-axis triangle restriction, normalize the U-to-V normal
to East. The whole actual V lies in x>=1, with every original side mean
permitted. If the U-to-W normal had negative x component, its actual
U support would lie on x=0. The same support point on W is minimum for
that normal, so W lies wholly in x<1. Physical contact VW would be
impossible. Therefore the two original normals have nonnegative dot
product. The zero-dot endpoint is correctly retained.

Both arguments use actual full units. They do not assert that arbitrary
strict-corner neighbors occupy a prescribed quadrant, only the precise
whole-unit coordinate bounds needed to make a common point impossible.

## 5. Exhaustive force-sign cover and the full equation

Normalize the common strict vertex of A and D to P=(0,0). Their actual
positive force vectors have strictly negative x and y components. Each
additional original vector covered by the closed-cone premise has both
components nonpositive.

The AB contact rules out a B vector with both components positive by
the opposite-corner result. It also rules out East and North B normals:
each is an owned U axis whose dot product with the strict Southwest A
normal is negative. Consequently a positive x component of B forces a
strictly negative y component, while a positive y component forces a
strictly negative x component. These implications include the zero
coordinate alternatives through their explicit axis exclusions.

Exactly the same complete argument using CD and the strict Southwest D
normal gives the two corresponding implications for C. No constraint
on the degrees or loads of A or D is used to obtain them.

The entire original force equation, with all extra vectors retained,
then gives

    (F_B)_x+(F_C)_x>0,
    (F_B)_y+(F_C)_y>0.

The strictness comes from the two actual end vectors, not from a
genericity condition. One of B,C has positive x component. Relabeling
the whole chain by reversing A,B,C,D if necessary makes this B. Its y
component is strictly negative, so the second full-coordinate equation
forces C's y component strictly positive. C's x component is therefore
strictly negative. The unchanged B and C forces strictly expose the
opposite Southeast and Northwest U vertices. Their actual BC contact
contradicts the already proved whole-unit separation.

This covers the full force-normal circle, including every original own
axis and every possible support mean. The only labels reversed are
the complete physical chain; no force or contact is replaced.

## 6. Exact export and verification boundary

For a true unloaded H4 whose entire neighborhood is A,B,C,D and whose
physical rim contains AB,BC,CD, the extra-force premise is vacuous.
HA and HD therefore cannot strictly expose the same H vertex. Either
normal may be externally side-owned or free; the premise is its actual
strict exposure on H. A hub-owned axis is outside that strict premise
unless a separate argument puts it in another covered case.

The result is radius-free and needs no torque equation. It is a complete
local full-star theorem, not by itself a whole original graph/load
closure. All original force, contact, mean, mask and true-degree data
remain. The current source and its input were not changed. This review
creates only a new review record and performs no metadata or flag edit,
numerical pose search, geometric computation certificate, Lean build,
CI, workflow, commit, remote write, or merge.
