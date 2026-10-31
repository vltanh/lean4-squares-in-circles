# Independent full review of the physical side-gap exclusion

Date: October 28, 2026 UTC. Reviewer: thin_d, independently of the
source author and the root co-derivation.

**Result: PASS at the exact stated geometric and original H4 interface
scope. No change to the reviewed source is requested.**

## 1. Frozen source and complete review scope

I read the entire manuscript
PHYSICAL_SIDE_GAP_CLOSED_BY_TOUCHING_NEIGHBORS_EXCLUDES_UNIT.md at
SHA256

    f209207b7aed6ae2bbf8c6fb92dc81d855721173c88060f08a00fb69fdf81492

and independently reconstructed every part of its physical localization,
normal criterion, feature partition and literal H4 consequence. I also
checked its actual dependent scopes against the full shared-end source
and the already independently reviewed full opposite-return H4 source.

## 2. The force-free physical theorem

The closed-body observation is valid even at side endpoints and multiple
physical junctions: if a point of one closed square belonged to another
square's open interior, an open neighborhood of that point would meet
the first square's open interior. Thus open-interior disjointness indeed
implies that the whole boundary of the proposed contact triangle avoids
the open interior of D.

The three sides of the triangle are actual closed body segments by
convexity: its base is in H, and the other two sides are in B and C.
At any point P in the relative interior of the base, a sufficiently
small move toward an arbitrary interior point of D is strictly inside
the triangle. This uses only that D lies on the triangle's exterior
side of H and that its interior has height greater than the base;
there is no assumption on the horizontal coordinate of the apex.
The same point is in int(D). Since int(D) is connected and avoids the
triangle boundary, all of int(D) lies in the triangle interior.
Taking closures gives the asserted inclusion of the entire actual D.

The area bound is exact: the apex and one base endpoint are points of
one actual unit square, so the height is at most its diameter sqrt(2).
The triangle therefore has area at most sqrt(2)/2, strictly below the
unit area of D. No strict diameter estimate, preferred planar graph
embedding, circle assumption or positive multiplier is used.

This covers a vertex or side application at P, including every
endpoint-valued mean compatible with 0<p<1. Contacts of zero force
and extra physical junctions are retained.

## 3. Normal criterion and complete H4 application

I checked the two support inequalities directly. If the BC contact
height were at most the H top height, the first inequality would force
its horizontal coordinate to be at most the left endpoint, and the
second would force it to be at least the right endpoint. The two
requirements are incompatible. The proof includes v=0 and s=0; it
does not silently turn an arbitrary mean into a corner.

In the actual H-owned-HD, strict-NE-HC chart, HA is strict SW and the
actual exterior D meets the relative interior of the H top. The strict
NE and strict SW choices for HB are respectively excluded by the
actual AB and BC opposite-corner obstructions. East and North are
excluded using their negative dot products with HA; West and South
are excluded using their negative dot products with HC. Thus the
stated two strict remaining HB quadrants exhaust the full normal
circle, including every axis and shared-side mean. In the NW case,
the actual HB and HC applications are the two true top endpoints,
so the physical theorem applies literally and excludes that branch.

The source consequently proves that HB is strict SE in this entire
interface. It preserves H's true degree four, D's true unloaded degree
three, every force and moment, all other degrees and loads, and all
nine physical units. The substitutions for H4_D0.L124 and
H4_D0.L0124 retain the actual unloaded end. The separate East-HC
mean case and the strict-SE residue are correctly left open.

## 4. Exact dependency check and limits

The following current source pins agree with the reviewed manuscript:

| Source | SHA256 |
| --- | --- |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b |
| INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md | bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c |
| INNER_PENTAGON_FOUR_SPOKE_SHARED_UNLOADED_END_EXCLUSION.md | ab1882057cc4d5bc0be2929c0c926543a92fbbbc4f8f74598c2238707d17f9f6 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |

Sections 1--2 of the reviewed source are self-contained; the contact
triangle source is correctly recorded as provenance rather than a new
unstated premise. The H4 dependencies are used only at their literal
physical and degree scopes. This review accepts a uniform physical
theorem and the declared necessary-domain reduction. It does not
close either H4 family, change a gate count, or assert a Lean proof.
