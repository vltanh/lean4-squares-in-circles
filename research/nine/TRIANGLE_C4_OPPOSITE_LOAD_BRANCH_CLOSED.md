# The entire opposite-load C4 with an attached end triangle is closed

**Status: complete whole-orbit hand assembly; root and separate independent
full assembly audits passed.** Every complete source used below has also
passed its root and separate independent full hand reviews.

Choose the common nine-square radius minimizer which also minimizes
the sum of squared center norms among radius minimizers. Work in the
inherited declared window
\[
                    \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
The entire selected positive component has the exact graph
\[
                     H-A-U-C-H,\qquad H-X-Y-H,
\tag{2}
\]
with exact positive block-load set A,C. Thus the true positive degrees
are four at H and two at each of A,U,C,X,Y. The tips X,Y are loaded,
H is physically circle-clear, and U has zero circle load. All three
remaining physical squares stay arbitrary and present.

**Theorem.** No compatible selected certificate at this canonical
minimizer has the whole opposite-load orbit (2). This closes
M6.TB4.C4.LAC of TRIANGLE_FOUR_BODY_BLOCK_LOAD_COVER.md.

## 1. Exact load domain and the intact triangle

The complete graph/load cover gives the true unloaded transmitter U,
with actual unit bypass H and reserve one. This uses no degree-two
equation at H. Its extra two forces are precisely the genuine X,Y
triangle forces throughout the argument.

Write M=F_X+F_Y. The complete end-triangle pressure theorem and the
whole-component force sum give
\[
                      c_H\cdot M>0,\qquad M+F_A+F_C=0.
\tag{3}
\]
Every physical radial-S neighbor of H has positive c_H projection
at both of its circle corners. Nonnegative original corner weights,
including a zero individual weight, preserve that strict positivity.
Consequently END_TRIANGLE_RADIAL_NEIGHBOR_OBSTRUCTION.md gives:

* The entire mask in which A and C both have two physical circle
  corners is impossible.
* Otherwise some actual unique corner has negative c_H projection.
* If exactly one tip has a unique physical corner, it is that tip
  whose corner has negative projection.

These statements concern the physical masks. A radial body with one
zero corner multiplier remains in the two-physical-corner mask.

## 2. The complete canonical physical contact reduction

FOUR_CYCLE_PARALLEL_BYPASS_GENERAL_EXCLUSION.md first excludes the
whole frame domain H parallel to U. Its proof retains arbitrary
additional H forces and uses the original common channel mean in
both tip torque equations. It does not import a radial-leaf equation.

TRIANGLE_C4_OPPOSITE_LOAD_CANONICAL_CONTACT.md then gives actual HU
contact, with H oblique to U and singleton HA and HC intersections.
The actual HU contact is allowed to have zero stress. No positive
HU edge is added to (2).

For completeness, the canonical packing is chosen before normal
preselection and stress extraction. For any subsequently selected
candidate (2), equation (3) bounds the
whole H center by |c_H|^2<9/2-R^2. The complete four-cycle hole is
empty: an inner unit would force the aligned cross, incompatible
with U's selected exact unloaded degree-two transmission. A positive
transverse HU gap is therefore an empty strip through which U can
move inward, preserving X,Y and every other actual square, while
strictly decreasing the sum of squared center norms. A positive gap
therefore contradicts the already fixed packing's secondary minimality.
This proves genuine zero-gap contact without changing either that
packing or its selected certificate. All original physical tip masks and
all possible final channel means remain in the subsequent cover.

Thus no original completion body or occupied region is discarded
in obtaining the canonical domain.

## 3. Every physical circle-mask pair is excluded

A contained circle-touching unit has either one physical circle
corner or two. Up to the reflection exchanging A and C, the complete
mask list and its full exits are:

| Physical A/C masks | Complete exclusion |
| --- | --- |
| Both have two circle corners | END_TRIANGLE_RADIAL_NEIGHBOR_OBSTRUCTION.md, Section 2 |
| Both have one circle corner | TRIANGLE_C4_OPPOSITE_UNIQUE_TIPS_EXCLUSION.md |
| A has one and C has two | TRIANGLE_C4_OPPOSITE_MIXED_TIPS_EXCLUSION.md |

The unique/unique source removes every free root interface with its
actual fixed or shared transmitter contact before covering all side
owners. Its final two-H-owned alternative uses the intact triangle
pressure in (3); it assigns no fictitious leaf force to H.

The mixed source covers the complete physical domain as follows:

| Whole mixed-domain alternative | Full exit |
| --- | --- |
| C parallel to U, with any of its four physical radial axes | The actual channel point on A is too central for any boundary unit |
| Free unique HA, with A oblique or parallel to U | Fixed-tip or A+U shared-block virtual work, with the actual AU mean retained |
| A owns HA | Actual H-contact diameter, or the complete two-tip-owned theorem |
| H owns HA and A is oblique to U | Actual H-contact diameter, including every HC owner and radial-C mean |
| H owns HA and A is parallel to U | C4_MIXED_PARALLEL_TIP_SCALAR_BOUND.md, applied to the true force, torque and application equations |

In the oblique-A case no ordering of A's two circle-coordinate
magnitudes is assumed. The complete contact calculation forces
d>1/2, then v<1/10 and sigma>9/10 in its stated frames; two actual
points of H would have vertical separation greater than 29/20,
which exceeds its diameter. The parallel-A case instead keeps the
actual shared mean ell in (0,1] and obtains the strict opposite
pressure c_H.z_A>3233/2408000>0. Both contradict the corresponding
physical premises, with no normalization of either tip's frame.

The mixed reflection covers the fourth ordered mask. This is the
entire physical mask cover, including all zero individual radial
corner weights and all side-mean endpoints.

## 4. One compatible certificate and the exact conclusion

Choose the canonical packing once. Before the physical multiplier
theorem, prelist every finite graph labeling, transmitter direction,
physical mask, unique corner and fixed/free contact-star or shared
block candidate used by the sources. Impose their compatible strict,
nonradial, matched-junction and generic conditions simultaneously.
No source selects a normal after seeing its multiplier or changes an
actual shared-side mean. The relevant virtual-work coefficients are
nonzero independently of those means and of radial corner weights.

Uncrossing preserves surviving point normals and introduces only
genuine shared interfaces already included in the physical cover;
thinning deletes atoms. Thus the proof uses one common selected
certificate, not separately chosen certificates for the rows above.
All original physical zero-weight contacts remain available, most
notably the actual HU contact.

The lower-window bound 79/40, the canonical minimizer and the selected
component construction are inherited prerequisites. The previously
proved one-/two-load restrictions used in the global frontier are
not reproved or weakened here. Inside that declared domain, all
three physical mask pairs in Section 3 are excluded, so the entire
opposite-load C4 attachment is closed with all three extra squares
retained.

The conclusion is at the canonical lower-bound scope. It is not an
assertion that every noncanonical stressed core of this graph is
geometrically impossible, and it does not classify equality packings.
Adding further positive edges at A,U,C,X or Y would change the exact
degrees used here and is outside this theorem. The whole ABC orbit,
the diamond-hub attachment and the rest of C2.34.b0 require their
own complete exits. No numerical premise, angle boxes, Lean
compilation or CI enters this assembly.
