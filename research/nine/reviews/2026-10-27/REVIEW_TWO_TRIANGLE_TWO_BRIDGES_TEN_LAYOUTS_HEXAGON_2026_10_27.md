# Independent review: the complete two-triangle, two-bridge inventory

Date: October 27, 2026.
Reviewer: separate hexagon proof worker.
Source reviewed: TWO_TRIANGLE_TWO_BRIDGES_TEN_LAYOUT_REDUCTION.md,
in its updated nine-closed-types / one-remaining-type form.

**Verdict: accepted as a complete finite graph cover and as the nine
stated whole-type joins.** The original coarse cell C2.33.b2 remains
open with precisely the one original attachment described in Section 4.
This is an inventory and source-scope review; it is not a new proof of
that final attachment or of the whole coarse cell.

## 1. The ten graph types are exhaustive and nonduplicated

The component has two triangular cyclic blocks and two bridges, hence
seven bodies. Distinct cyclic blocks share either no vertex or one
articulation; sharing more would make them part of one block. Their
block-cut incidence graph is a tree.

If the triangles share H, their union has five bodies and the other
two bodies occur in bridge trees attached to that bowtie. The two
bridges are either a single length-two pendant path or two genuine
leaves. The bowtie automorphism group has exactly two vertex orbits,
H and its four private tips, giving two path attachments. Its unordered
pairs of attachment vertices with repetition have exactly five orbits:
(H,H), (H,A), (A,A), distinct tips (A,B) on one triangle, and tips
(A,C) on different triangles. Equality of the two vertices, being H,
and belonging to the same triangle distinguish these orbits completely.
Thus there are exactly seven shared-H types.

For disjoint triangles, their six bodies leave one further body. The
unique interblock route uses either both bridges and that body as its
internal vertex, or one direct bridge. In the latter case the other
bridge is a genuine leaf at either a connector endpoint or a private
tip, the two vertex orbits of the resulting symmetric graph. This gives
exactly three more types. A second interblock route would make its edges
nonbridges and is outside the original block profile, so it is not an
omitted case.

Every original load set, physical circle mask, actual normal and mean,
S/D leaf choice and completion-square position remains within its graph
type. The cover is structural and does not select a geometric pose.

## 2. All seven shared-H joins have the exact required scope

| Original attachment | Checked complete consequence |
| --- | --- |
| Length-two path at H | Both triangles remain intact at H; the accepted two-intact-petal theorem applies to the whole all-triangle block tree, including the actual arm. |
| Length-two path at private A | The other triangle is intact at H. The all-bridge internal U is truly unloaded by exact articulation splitting; its off-origin transmitter theorem forces an actual inward neighbor containing O. That neighbor must be H, but the unchanged neighbors are A and L. |
| Two genuine leaves at H | Both triangles remain intact; the same complete two-intact-petal theorem permits both real leaves and the full root degree. |
| One genuine leaf at H and one at A | The intact petal at H plus its genuine S or D leaf gives strict D_epsilon containment for both full leaf types. The distinct genuine root A must meet that disk, forcing overlap. |
| Two genuine leaves at A | The other triangle is intact at H. The complete two-leaf-root geometry puts O in A for every radius, including its boundary-vertex exception at d=1, so the closed A meets int H. |
| One leaf at each tip A,B of one triangle | The other triangle is intact at H. The complete origin-root two-leaf triangle theorem applies with the actual H external system and the true degree-three A,B equations. |
| One leaf at A and one at C of different triangles | This is the sole remaining no-intact attachment. No exclusion is inferred from the preceding distinct layouts. |

I checked the potentially sensitive premises in these joins. The
off-origin bridge theorem concerns the real all-bridge body U and
keeps both applications; it does not reattach its path to H. The
two-leaf-root lemma is geometric with arbitrary additional neighbors,
so the extra triangle at A does not change its scope. The S/D central
disk theorems likewise retain all actual H forces and apply at its
true degree five in the root-and-tip leaf layout.

For the two-private-tip-leaf theorem, the intact petal gives precisely
the additional H-vertex norm premise. Its actual common-side height
has 1/5<P<39/40, so every H vertex has longitudinal absolute coordinate
greater than 1/40. The intact petal's full external origin moment is
zero by summing its private-tip equations. Thus the arbitrary-full-H
external-system hypothesis is satisfied; no degree-two or single-radial
external-force equation is imposed at H.

All uses of exact articulation splitting retain the common selected
radius/Phi-minimizer pose and its named small-core prerequisites. The
new inventory does not export those joins to an arbitrary unselected
packing or a reselected normal system.

## 3. The three disjoint-block joins are complete

With a length-two connector, both actual triangle roots have two
untouched true degree-two loaded tips. Each contains O openly, which
contradicts disjoint interiors. A direct connector with its extra leaf
at an endpoint has the same two intact roots; the leaf changes only
one root's full degree, allowed by the origin theorem.

For a direct connector with the extra leaf at a private tip, the
far intact root has exactly its intact petal and the actual connector
as its full positive system. The opposite connector root has no
other bridge. These are exactly the premises of Corollary 4 in
GLOBAL_CLOSURE_INTACT_ROOT_DIRECT_BRIDGE_REDUCTION.md. Its full root
pressure argument first proves physical circle clearance of the far
endpoint; the original possible circle load is not simply omitted.
The actual leaf-bearing neighbor meets D_epsilon, contradicting the
resulting outward support greater than one. The explicit R>=2 premise
is supplied by the retained same-nine R<=2 exit, with its arithmetic
dependency declared in the cover.

## 4. The single remaining type retains its entire physical domain

The remaining actual edges are

    HA,AB,BH, HC,CD,DH, AL,CM.

The root H has true degree four, A and C true degree three, and B,D
true loaded degree two. Genuine leaves make A,C physically circle-clear;
no such assertion is made about H. Its original circle resultant is
retained. D/D is geometrically impossible because the distinct actual
roots A,C would both contain O openly. The remaining genuine type
orbits are the whole S/S and S/D domains, with D/S represented by the
actual graph symmetry exchanging the triangles.

Both arbitrary extra physical squares remain. A six-body one-leaf
bowtie theorem cannot be applied by deleting either positive leaf
force, and the cover explicitly declines that invalid reduction.
Accordingly its count is exactly nine complete graph types excluded
out of ten, with one original type still open; it creates no new fine
gates and claims no closed coarse cell.

No sampled pose, numerical enumeration, new scalar certificate, Lean
compilation, CI, remote action, or shared-ledger mutation was used in
this independent review.
