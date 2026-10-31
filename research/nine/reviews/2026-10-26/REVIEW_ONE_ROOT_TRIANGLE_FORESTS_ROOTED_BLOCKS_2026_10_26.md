# Independent full review: all bridge forests attached to one triangle root

Date: October 26, 2026.
Reviewer: rooted-blocks independent agent.

**Verdict: ACCEPT the complete stated selected-certificate theorem.**
The theorem excludes every positive component whose sole cyclic block is a
triangle and whose entire bridge forest is attached to one triangle vertex,
after the explicitly proved minimum-support selection at the common
radius/Phi-minimizer pose. It includes all branching forests, all original
circle weights and physical masks, the critical radius, and all nine
physical bodies. It does not close the corresponding coarse cells when
bridges attach at several triangle vertices.

The primary source reviewed in full is
`GLOBAL_CLOSURE_ONE_ROOT_TRIANGLE_FORESTS_EXCLUDED.md`, SHA-256
`49df3f67592455fc79afff55a88598c6214fac5486d8081705b87fd8240241a8`.
Its complete direct selection prerequisite,
`GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md`, was also read and checked;
its SHA-256 is
`39aa9e31a6de4ecdff535a8136f5c3330e6bb653903951fde812ee522d128d4a`.
Status-only updates after this review do not change its mathematical target.

## 1. Original certificate and the new minimum-support selection

I checked the branch operations rather than inferring permission to discard
an old force from the new graph. Every component V_j of G minus an actual
articulation A has positive private circle mass a_j. The proof is exactly
CY.LOAD.1 of `CYCLIC_BLOCK_INVENTORY.md`: dot each unloaded body's force
equation with its center relative to c_A and sum. Every internal or boundary
pair contributes minus its positive magnitude times the sum of the two
positive supporting half-widths. Thus an all-unloaded branch is impossible.
This establishes a_j>0 independently of the branch-moment identity.

Summing all original origin-moment equations in one branch gives zero total
moment at A. Consequently scaling the whole branch preserves all its
equations and retains zero moment at A. The operation scales both endpoint
atoms of every shared-side interaction equally, so its actual mean is
unchanged. The physical bodies and zero-weight contacts remain in place.

The vectors (f_j,a_j) and (2 lambda_z z,lambda_z) used in the source have
strictly positive last coordinates and sum to the normalized vector
(0,0,1). Any linear dependence therefore has coefficients of both signs.
Replacing the old coefficient 1 by

    1 - beta_i / max_h beta_h

is nonnegative, preserves force balance and normalization, and removes at
least one positive original atom. The branch origin moments already vanish,
so the angular equation at A is preserved as well. This is a complete new
stress, not an equation formed by deleting a positive term. All surviving
forces use the original normal system, and its graph remains planar.

This proves k+ell<=3 at every articulation of the selected stress. At an
unloaded articulation with three branches, collinear f_j put the three
vectors (f_j,a_j) in a space of dimension at most two. The identical
dependence argument removes a positive branch. Hence the source's extra
noncollinearity conclusion is valid even if an individual branch resultant
were zero. It concerns whole branches; it is not a bound on the number of
edges in a cyclic branch.

I also checked the loaded all-bridge consequence and its scope. The radial
bridge law makes every such loaded body an outer endpoint with the same
nearest-point application. The local argument in
`TRIANGLE_THREE_BRIDGES_LONG_CHAIN_EXCLUSION.md`, Section 1, gives radial D
of degree one or radial S of degree at most two without requiring the whole
component to be a tree. In the degree-two S case the two actual equal circle
weights split in the positive ratios of the incoming magnitudes. Both new
stresses satisfy the original force and moment equations. Their component
sizes sum to m+1<=10, so one has at most five bodies.

The small-core join is inherited at exactly the common canonical pose. I
checked the complete assemblies `FOUR_BODY_BLOCK_ONE_LEAF_CELL_CLOSED.md`
and `FIVE_BODY_BICONNECTED_CELL_CLOSED.md`, the named tree/two-load and
triangle/bowtie exits, and the complete five-body catalog and exit in
`DEEP_GATED_ROADMAP.md`, G3.M5. The four-body-block/leaf assembly explicitly
makes the Phi choice before the common normals and multiplier extraction;
the split changes neither the pose nor those normals. The finite generic
conditions are imposed on physical candidates before extraction and survive
thinning. The retained small component is an entire normalized stress, with
the omitted bodies still among the same nine physical squares. Thus this
join does not export a canonical motion to an arbitrary equality packing.

It follows that every outside nonleaf in the theorem is truly unloaded.
Every outside branching vertex has degree at most three. At A, the intact
triangle is one branch, so there are at most two additional tree branches.
These are valid statements in the newly selected single certificate used
throughout the rest of the proof.

## 2. Exact triangle and all-bridge geometry

Both triangle tips retain genuine positive degree two. If either were
unloaded, its opposite pair forces would put its two neighbors beyond
separated supports, contradicting their physical contact. Thus both tips
are loaded. The physical boundary-triangle exclusion makes A circle-clear.

The full end-triangle pressure theorem in `BOWTIE_CELL_CLOSED.md`, Section 2,
allows arbitrary other positive neighbors at A and supplies c_A dot M>0.
The full theorem `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md` gives M nonzero,
the strict support inequality h_A(M/|M|)<d, and, when needed, proper root
concurrence on the opposite M ray. These are conclusions for the intact
two-tip block. The proof never assigns A a degree-two equation or replaces
the two tips by a radial leaf.

The all-bridge localization in Section 2.1 uses only U's actual zero circle
load and its incident bridges. If U missed D_delta, it would be outer at
every bridge, with one unique nearest point and all forces in one direction.
That contradicts its genuine unloaded equation. The bound

    |c_U| <= delta + sqrt(2)/2 < 19/24

is therefore valid inside the cyclic component. No complete-tree premise
has been imported from `TREE_BODY_LOCALIZATION.md`.

The outward-support statement was checked in own square coordinates. If a
closed square avoids zero, some center coordinate has absolute value
strictly above 1/2. At a positive radial support p=t e that coordinate uses
the far face and has absolute value greater than one; hence t>1. Its outer
neighbor cannot be an unloaded all-bridge body, since that neighbor's
nearest radius would exceed one while it must meet D_delta.

Along an original terminal arm all internal vertices have exact degree two
and have already been proved unloaded. Their radial transmitter equations
retain every actual mean and give widths 1 or sqrt(2). For an arm of at least
three edges from an outside fork, W>=2 and the root support is
(r_L-W)e. Since r_L<=d, its center projection is below -89/60, contradicting
the preceding center bound. This excludes long terminal arms before any
two-arm geometry is applied.

## 3. Complete two-terminal-arm disk lemma

I checked all four cases against their actual geometric sections, including
their independence from root force equations:

| Terminal lengths | Direct source and verified conclusion |
| --- | --- |
| 1,1 | `TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md`, Section 1: complete S/S, S/D, D/D radial-support cover; strict origin containment for d<1, strict D_(d-1) containment for d>1, and the full origin-vertex exception at d=1. |
| 1,2 with direct D | `TRIANGLE_THREE_BRIDGES_MIXED_ARMS_D_EXCLUSION.md`, Section 1: the original arm is S of width one with d>1, and H=[d-2,d-1] times [r-1,r]. The other three side distances exceed epsilon. |
| 1,2 with direct S | `TRIANGLE_THREE_BRIDGES_MIXED_ARMS_S_EXCLUSION.md`, Section 1: d<1 is impossible, the original arm is S of width one, and for d>1 the entire root is [epsilon-1,epsilon] times [2sqrt(epsilon)-1,2sqrt(epsilon)]. All other side distances exceed epsilon. At d=1 the actual root application is zero. |
| 2,2 | `GLOBAL_CLOSURE_TWO_LEAF_ARMS_END_TRIANGLE_EXCLUSION.md`, Section 1: d>=1, both arms S of width one, and the full root is [epsilon-1,epsilon]^2 in their actual orthogonal directions, including epsilon=0. |

The last source received my separate full audit in
`REVIEW_TWO_LEAF_ARMS_END_TRIANGLE_ROOTED_BLOCKS_2026_10_26.md`. That audit
includes its distinct-direction argument, all negative applications, side
means and endpoint tangent cones. Its force-free classification allows
arbitrary other forces and loads at H, so it is valid at a degree-three
outside fork. No exact triangle equation from the mixed-arm sources is
being transferred to H.

These cases exhaust both S/D leaves and both transmitter widths. They imply
D_epsilon subset H, and strict origin-interior containment whenever d!=1.

## 4. Every outside fork when d differs from one

The graph choice is exhaustive. Root the bridge forest at A and choose an
outside branching vertex farthest from A. The degree bound makes it have
exactly two children; neither child branch can contain another branching
vertex. Both are therefore the terminal arms treated above.

Strict origin-interior containment in H makes the distinct square A avoid
zero. For d>1, the open disk D_epsilon is in H's interior, even when H has a
side tangent to the closed disk. Thus A is disjoint from that open disk.

For each actual A bridge, write its application as t n with n outward from
A. Zero is impossible. A negative t uses A's unique nearest point and all
such forces agree. A positive t exceeds one. Its neighbor cannot be an
outside unloaded body and hence is a genuine direct S leaf, with t=d>1;
the D radius is less than one.

For a direct S leaf, the whole unit inward segment from d e belongs to A,
so epsilon e belongs to A. Since A avoids the open D_epsilon, this is its
unique nearest point. A second outward S leaf would yield the same point
and repeat the same physical radial leaf. The branch containing H must be
incoming. There are at most two tree branches, and their resultants and M
are collinear by the genuine full A equation. The proved minimum-support
refinement excludes this case.

If there is no outward bridge, all tree forces have the same direction.
Two tree branches are excluded by the same refinement. With one bridge A
has exact positive degree three, and its nearest radius satisfies
rho>=epsilon for d>1 or rho>0 for d<1. I read
`OUTER_BRIDGED_TRIANGLE_EXCLUSION.md` in full: its theorem imposes no degree,
load or tree hypothesis on the far side of the bridge and explicitly allows
rho=max(d-1,0). Thus the original whole branch is retained and this join is
valid, including equality at the threshold.

## 5. Entire critical-radius interface

At d=1 an outside unloaded body avoiding zero would require a positive
outward radial bridge, because all incoming forces agree. Its support
radius exceeds one. The source's neighbor classification then forces that
neighbor to be A, which in turn has only incoming bridges. Two are excluded
by minimum support and one by the outer-triangle theorem at threshold zero.
The same argument shows A contains zero whenever an outside nonleaf exists.
This longer argument is valid. A possible optional simplification is that
the sharp contained-neighbor support bound already gives t<=d=1 directly
for every positive outward bridge; no such simplification is required for
acceptance.

For two squares both containing zero, their actual separating line passes
through zero. The radial application is parallel to its normal, so the
actual bridge application is exactly zero. Thus every A bridge to an
outside nonleaf is a genuine origin force. Because A has at most two tree
branches, at most one other branch can be a direct leaf. A D leaf would put
zero in A's open interior and is impossible; only S remains.

If all tree forces are origin forces, M belongs to A's inward normal cone
at zero. A side-interior zero gives unit support exactly one. At an origin
vertex, the unit resultant has two nonnegative own coordinates, whose sum
is at least one. Both contradict the strict bound h_A(M/|M|)<1.

I separately checked the direct-S plus arbitrary-origin-force case, rather
than applying an exact two-edge-arm equation to that branch. At a
side-interior zero, the sole norm-one outward radial support is the opposite
side foot. The direct leaf and origin force are opposite; pressure gives M
the positive leaf direction, so its support equals one, impossible.

At an origin vertex put A=[0,1]u+[0,1]v and let the genuine direct leaf be
S(u). The original equation is

    M=-alpha u-beta n, alpha,beta>0, n dot u<=0, n dot v<=0.

If n dot v=0, pressure again forces unit support one. Otherwise M dot v>0.
In the nonparallel triangle case the proper root concurrence has negative
v-coordinate. This excludes both u-axis normals. A -v normal has negative
dot product with M, whereas the physical nonobtuse-normal theorem makes
that dot product strictly positive for an A-owned root normal. I checked
`UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` in full for this use.

The origin cannot belong to a boundary tip; u is the actual S(u)
inner-face midpoint and cannot belong to another boundary square; a strict
normal at u+v has support greater than one. These exclusions retain axis
endpoints in their owned-side cases. The only remaining features are the
vertex v and an A-owned +v side. Sharp support equality makes a +v tip the
unique physical S(v), after which a second tip at its inner-face midpoint
v is impossible. Two nonparallel vertex-v ports would have concurrence v,
contrary to its negative v-coordinate.

In the parallel case the two root normals agree, since opposite ones
separate the touching tips. A strict vertex direction gives the same root
port to both. The two actual proper tip concurrences then lie on its normal
line. They cannot coincide because their positive radial directions are
distinct. Their connecting BC line would make the two forces at each tip
parallel, contradicting the genuine two-tip lemma. The remaining axis with
positive v-component is +v; equality makes both tips the same S(v).

This is a complete critical interface proof with the original arbitrary
branch force at zero. It needs neither a false degree-two equation at A nor
a replacement of the branch by a transmitter.

## 6. No-fork graph cover and inherited whole-family exits

Without outside branching there are at most two simple arms from A, each
ending at its genuine leaf, with all intermediate bodies unloaded. A path
of at least four edges gives root application at most d-3 and center
projection below -149/60, contrary to the universal 91/60 center bound.

For two arms, a length-three arm gives a negative signed support and a
unique nearest-point radius greater than 59/60. A direct leaf on the other
arm makes A meet D_epsilon and is impossible. A second arm of length at
least two has a negative signed application or the sole nonnegative
S/width-one application epsilon. The latter is too central. In the former
case uniqueness of the nearest point forces equal leaf directions. Equal
S or equal D leaves coincide, and an S/D pair on the same ray overlaps in
an open set. Thus both arm lengths are one or two.

The remaining families are exact whole components, not motifs with deleted
forces. With one arm, the length-one, length-two and length-three sources
have precisely the required genuine degrees and retained completion
squares. With two arms, the (1,1) common-articulation theorem, the complete
(1,2) mixed-arm assembly, and the newly accepted (2,2) theorem retain the
actual degree four at A. The no-arm case is the complete triangle-component
exclusion. These alternatives exhaust every finite bridge forest attached
only at A.

## 7. Final scope and review boundary

No mathematical correction is required for the reviewed source. The only
stale statement is its note that the (2,2) source still awaits independent
review; that prerequisite has now passed its full independent audit and
the root audit.

The complete same-root theorem is accepted with its minimum-support and
canonical-pose hypotheses attached. It does not cover forests attached at
two or three different triangle vertices, another cyclic block, or larger
blocks. In particular it does not by itself tick C1.3.b4, C1.3.b5 or
C1.3.b6, prove the unrestricted nine-square lower bound, or classify
original equality configurations.

This review used complete source arguments and exact inequalities. No Lean
compilation, CI, numerical pose search, or remote action was performed.
