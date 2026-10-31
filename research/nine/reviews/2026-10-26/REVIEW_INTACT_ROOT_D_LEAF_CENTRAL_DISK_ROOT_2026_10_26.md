# Root review: an intact-petal D-leaf root excludes its entire triangle block tree

Date: October 26, 2026.

**Decision: ACCEPT the complete contact barrier, central-disk theorem and
whole all-triangle block-tree exclusion, at their stated hypotheses.**
No original bridged coarse cell closes by this subfamily theorem alone.

Reviewed source:
`GLOBAL_CLOSURE_INTACT_ROOT_D_LEAF_CENTRAL_DISK_EXCLUSION.md`.
Exact mathematical source pin before status-only acceptance edits:

    a6145b31a2688a851ec35fa4d6eefe751af396a429b9da664ee6d2de835f49fc

I read the entire source and checked its inheritance from the true S/D
radial-leaf geometry, the complete intact-triangle origin theorem, and
the minimum-support articulation/off-origin bridge classification.

## 1. Complete common-side contact barrier

The two actual root ports strictly straddle the side-interior point p.
For an actual mutual tip contact Q left of the root side, choose the
oppositely signed root port: its segment toward Q enters the open root
interior even when the initial port is a root vertex. If Q is on the
side line but differs from p, one tip contains a side segment with p in
its relative interior. Disjointness from the root makes that tip occupy
the right local half-plane, where it overlaps any distinct positive-area
unit W with p on its boundary. If Q=p, three right-angle-or-larger tangent
cones cannot fit interior-disjointly into the right semicircle.

For Q strictly right of the side, the physical tips and root contain the
entire boundary of triangle P_-P_+Q. Some W interior points near its
base-interior point p lie inside this triangle. The connected (indeed
convex) W interior cannot cross its occupied boundary. Its whole unit
area would be enclosed. The base is at most one and the height at most
sqrt(2), because Q and each corresponding base port belong to one unit.
Area at most sqrt(2)/2<1 is impossible. All choices of actual means,
coincident contacts and side endpoints are thus covered geometrically.

## 2. Strict containment of the whole closed central disk

For the real D leaf, the root is [-s,r] times [l,l+1], with r=R-sqrt(2),
s=1-r and -1<l<0. This uses the actual side-interior radial application
of the D theorem, not a freely placed replacement contact. The intact
petal supplies origin interior and an actual common side of height
1/5<P<39/40, with strict transverse port straddling.

If epsilon=0, the conclusion is precisely origin interior. Otherwise
both horizontal margins exceed epsilon. Reflect a failing transverse
margin to the top, with 0<eta<=epsilon. The top and bottom sides have
heights at most epsilon and at least 1-epsilon and violate the petal
height interval. The right side is excluded by the complete contact
barrier applied to the actual D leaf. On the left side the upper actual
petal port has height in (0,epsilon], so its squared norm is at most
s^2+epsilon^2. But

    r^2-s^2=2r-1>7/60>epsilon^2,

with strict reserve at least 419/3600 after using epsilon<1/60. A physical
boundary tip has no point of norm less than r, giving the fourth and
last contradiction. Consequently all four margins exceed epsilon,
placing the entire closed D_epsilon in the open root interior.

## 3. Every original bridge branch is retained in the next reduction

Every genuine leaf root meets D_epsilon. For D this follows from its
strict origin containment. For S its actual inward radial unit segment
contains (d-1)v if d>1 and O if d<=1. Neither conclusion restricts other
forces at that root. Since D_epsilon is now wholly inside H's open
interior, no distinct physical unit can meet it. Thus every genuine
leaf root must be H.

A positive unloaded bridge-only body is off-origin because H contains
O openly. Its full selected classification gives an actual application
in D_epsilon, again impossible. Loaded bridge-only bodies are genuine
leaves by the accepted articulation split. Hence there are no bridge-
only internal vertices; no arm is shortened by assumption.

## 4. The whole all-triangle block-tree conclusion

Use the exact block-cut tree rooted at H, with bridges as two-body
blocks. A terminal triangle has two private true degree-two vertices;
their touching-neighbor obstruction makes them loaded. Its root must
therefore be H, by uniqueness of the origin-interior intact-petal root.
A terminal bridge has a genuine positive degree-one loaded endpoint,
so its root is also H by Section 3. Any branch that continues beyond a
block incident to H has a farthest terminal block whose articulation is
not H, contradiction. Thus all cyclic blocks and leaf bridges are actual
direct blocks at H. This exhausts separated triangles, shared roots and
all original bridge lengths without treating an isolated unstressed extra
as part of the positive block tree.

H is physically circle-clear. The final root equation contains every
intact-petal resultant and every direct S/D leaf force. All have strictly
positive c_H pressure, so the full equation cannot vanish. This proves
the entire declared all-triangle family containing an intact-petal root
with a genuine D leaf.

## 5. Limits and verification

The theorem does not cover an S leaf at the intact root, a graph without
an intact petal, or a larger terminal cyclic block. It does not reassign
tip equations, masks, normals or shared means. Exact Fraction checks
verified the side-height reserves and r^2-s^2 comparison; every physical
case is handled continuously in the proof. No Lean compilation, CI,
numerical pose, remote action or shared-ledger edit was performed.
