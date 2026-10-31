# Independent review: short-diameter contact rings and the five-load C6 join

Date: October 26, 2026.

Reviewer: independent C6 completion agent.

**Result: PASS for both complete current sources, with precisely the stated
scope.** This is a fresh review of
SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md and
SIX_CYCLE_FIVE_LOAD_CENTRAL_CAPACITY_ONE.md. It does not close the original
five-load gate. The review includes the new winding and nonconvex extraction
arguments, each transferred continuous branch, and the complete original
five-load routing and fifteen-pair metric join.

## 1. The new topological and metric argument

I checked the statement for an arbitrary finite physical contact ring,
including the distinction between a polygonal center chain and a convex
polygon. No convexity, radial order, number of ring bodies, force, or
boundary-circle equality is used implicitly in the new proof.

An extra interior avoids each closed ring square. Its distance from every
ring center is at least one half, while a true contact gives a center edge
of length at most \(\sqrt2\). Section 2 of
C7_CENTER_POLYGON_LOCALIZATION.md is indeed a local chord statement with
these inputs; it does not use that source's separate convex C7 construction.
Consequently every center edge avoids the extra interior.

The two physical spokes and their replacement center edge bound a triangle
whose entire boundary avoids the connected extra interior. That interior
must be wholly inside or wholly outside the triangle. The first option
would place area one in a triangle of area at most one quarter and is
impossible. Degenerate replacements have zero winding directly. Thus each
replacement preserves the winding about every extra interior point.
This argument works separately for every proposed extra and does not
require the resulting center chain to be simple.

The compact-interior weak-junction convention is sufficient: the limiting
occupied curve has positive distance from each compact subset of an extra
interior, so winding is stable. A ray from that interior to infinity must
meet the actual occupied ring. Hence every later ray witness is an actual
square, with its actual corners and frame.

I separately reconstructed the missing-face-zone extraction. In the local
coordinates \(T=[-1,0]\times[-1/2,1/2]\), nonzero winding forces an edge to
meet the left ray at \(x\le-1\). Clearance and the absence of a center in
the closed middle zone rule out a vertex encounter or a horizontal edge.
The short-edge and clearance alternatives force both endpoint first
coordinates strictly below \(-1\), and their second coordinates strictly
above \(1/2\) and below \(-1/2\), respectively. Thus the displayed
\((u,v),(w,z)\) excesses and all four strict/weak inequalities are valid,
including \(u,w>1/4\). These endpoints are actual ring centers.

This is precisely the missing hypothesis needed in the parallel-pair
argument. All three zone-occupancy alternatives in
PARALLEL_INNER_PAIR_DIAMETER_EXTRACTION.md then use only the extracted
actual endpoints, their clearance, and the actual diameter. Arbitrary
stagger is retained. No convex-hull edge is substituted for a true edge.

## 2. Full nonparallel dependency audit

I read the relevant complete proofs, including their original hypotheses,
in:

- CENTER_COVER_PIERCING.md, Sections 1--4;
- C7_INNER_SIDE_CORNER_RESTRICTIONS.md;
- C7_INNER_OUTSIDE_FACE_CORNER_EXCLUSION.md;
- C7_INNER_PAIR_FAR_FACE_CENTERS.md;
- C7_SHARP_BALANCED_RADIAL_TAIL.md;
- C7_OUTSIDE_INNER_RAY_WITNESS.md, in particular scalar estimate (3);
- C7_RIGHT_OUTSIDE_INNER_EXCLUSION.md;
- C7_LEFT_OUTSIDE_INNER_EXCLUSION.md.

The side-coordinate, vertex, outside-face and initial angle restrictions
need only the true outgoing witness and the uniform ring-center bound.
The balanced radial-tail lemma is a two-square statement covering both SAT
owners and every normal sign on its stated whole domain. The imported
scalar estimate from the outside-witness manuscript requires only its
displayed scalar interval.

The far-face proof's only polygon-containment input is the missing-zone
endpoint extraction. Its replacement in the current source is sufficient.
The mean-square lower bound \(F_X(V)\), its monotonicity in \(X\), and its
concavity in \(V\) use no other polygon property. Returning to the fixed
disk origin before applying center norms is correctly stated. The
extracted far-face centers are distinct actual centers; the exact
horizontal gap and the strict diameter therefore supply the required
signed lower bound for their transverse parameter.

The outside-coordinate cover retains the original owned separator. It
does not interchange the two inner squares after selecting a separator.
The branches \(\xi\ge1/2\) and \(\xi<1/2,\alpha>1/2\) exhaust every
nonparallel case, including the equality in the first branch.

I checked the right-branch witness localization and uniqueness against
the actual far-face center. The witness-frame estimate uses containment
\(\rho^2+\rho(\cos\psi+\sin\psi)+1/2\le Q\), not circle equality.
The subsequent signed bounds and concave endpoint comparison therefore
transfer unchanged.

I also checked the entire asymmetric left branch, including its balanced
and unbalanced secondary-coordinate alternatives, shallow and steep
radial normals, all square-owned normal signs, the mixed-down witness
rectangle, and the last tangent comparison. Its difficult upward-owned
case contradicts an actual corner's containment in the disk. It does not
require that corner to be a loaded circle corner. In every surviving
normal case, center separation identifies the witness with the same
actual far-face square before the two transverse bounds are combined.
There is no use of a fictitious independently positioned witness.

Thus the stated general ring theorem is proved. It is a capacity-one
theorem, not a claim that a set of diameter below three has a covering
disk of radius three halves.

## 3. Exact arithmetic reconstructed

I recomputed the fixed comparisons with independent rational arithmetic.
Among the resulting reserves are

\[
\begin{array}{c|c}
\text{comparison}&\text{positive reserve}\\ \hline
M^2+M+1/2-Q&31/57600\\
941/400-M^2&47/900\\
11529/5000-M^2&497/90000\\
91/10-9&1/10\\
f(3/16)&4109/5581500\\
f(3/8)&136499/2232600\\
3/40-(43/10)e&197/72000\\
(581/125)^2/5-Q&87491/20000000\\
58/25-M^2&71/3600\\
1/4-\bigl(M^2-(36/25)^2\bigr)&2099/90000\\
1-\bigl((11/60)^2+(7/8)^2\bigr)&2891/14400 .
\end{array}
\]

The three fixed radical comparisons at the far-face endpoint also follow
with positive reserves after squaring. These checks verify displayed
whole-domain estimates; they are not a parameter grid or a new finite
certificate packet.

## 4. The original five-load C6 join

The actual component is exactly
\(U-S_1-S_2-S_3-S_4-S_5-U\), with all five loaded bodies, the original
unloaded degree-two transmitter, and all three further physical squares.
Properness and routing use the entire selected positive cycle. Direct
loaded-loaded exterior pockets are empty, while all other exterior
extras lie in the one actual \(S_5-U-S_1\) cap.

The original contact-ring area bound first gives \(n_{\rm in}\le2\).
Since there are three extras, it supplies an actual occupied-cap extra
before the transmitter-radius theorem is invoked. Hence there is no
circular dependency on the subsequently proved central capacity.

I checked the full fifteen-pair cover against the unchanged actual paths.
The occupied-cap theorem bounds the transmitter center by \(89/60\),
so its five distances to centers bounded by \(91/60\) are strictly below
three. The four one-edge and three two-edge loaded pairs use actual
contacts. The two three-edge pairs use actual four-boundary-body paths.
The remaining pair \(S_1,S_5\) uses its real two-contact path through
\(U\), not an inadmissible mixed three-edge inference.

The actual central routing gives exactly the winding hypothesis of the
new generic theorem. Extra physical contacts may split regions but do
not remove any extra from the counted union. Consequently
\(n_{\rm in}\le1\), and the exact remaining allocations are
\((n_{\rm in},n_{\rm cap})=(0,3),(1,2)\).

For an actual width-one channel with at least one physical radial
endpoint, RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md applies with the
true degree-two transmitter and the entire positive simple cycle. It
permits either zero individual radial weight, every true support owner
and mean, and arbitrary masks on the other three loaded bodies. Its cap
capacity one contradicts both remaining allocations. The both-radial
empty-cap conclusion is consistent with, and stronger than, this join.

The two-unique side-channel family and every remaining diagonal-mask
family are expressly retained. In particular, the diagonal radial
restriction \(R^2<17/4\) is not contradicted just by the same-nine lower
bound \(R>2\). The original M6.B6.C6.FIVE.CAP gate therefore remains
open, exactly as the source states.

All twelve direct manuscript references in the generic source and all
nine in the physical join were present when this review was saved.
No source correction, ledger change, Lean run, or CI run was needed.
