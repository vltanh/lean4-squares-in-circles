# Two intact end triangles cannot be connected through an all-bridge forest

Date: October 26, 2026.
**Status: accepted complete theorem after full-source root review in REVIEW_BRIDGE_MATCHING_TRIANGLE_FORESTS_ROOT_2026_10_26.md and separate review in REVIEW_TWO_END_TRIANGLES_FOREST_ROOTED_BLOCKS_2026_10_26.md.**
No original gate or shared ledger has been changed by this source.

Use the unchanged common nine-square radius/Phi-minimizer pose in
79/40<=R<=sqrt(1105)/16, with the compatible physical normal system
and minimal positive scalar support of
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md. All original physical
squares, zero-stress contacts, masks and actual surviving means remain.

## 1. The existing strict inward-interface theorem is the full input

An intact bridged end triangle A--B--C--A has B,C of true positive
degree two and A of true positive degree three, whose remaining edge
is a bridge. Direct that bridge from its neighbor toward A, with unit
normal e and actual application p=rho e. Thus A lies in e.x>=rho.

OUTER_BRIDGED_TRIANGLE_CAP_EXCLUSION.md proves the full strict sign

    rho<0.                                                (1)

Its hypotheses allow arbitrary loads, cycles and degrees on the
other side of the bridge. It retains every physical tip mask,
actual support owner, endpoint mean and the common strict-normal
selection. The complete source, including its threshold-free
inheritance from the earlier outer-triangle theorem, has accepted
root and independent full-source reviews.

In particular (1) is stronger than the earlier necessary threshold
rho<max(d-1,0). No argument below replaces (1) by that weaker bound.

Writing r=-rho>0 and f=-e, (1) says exactly that A is the inner
body of its bridge and its neighbor is the outer body:

    p=r f,
    A subset {f.x<=r},      neighbor subset {f.x>=r}.       (2)

The neighbor has p as its unique nearest point to zero and therefore
avoids zero. These are statements about the unchanged radial bridge.

## 2. A bridge neighbor outside every cycle is a single actual transmitter

Suppose the neighbor U in (2) is all-bridge and is not a genuine
leaf. At the common canonical pose it cannot have positive circle
load: the exact loaded-articulation split in
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md excludes every
loaded all-bridge nonleaf by the accepted complete small-core
assembly. Its stated pose and finite-normal inheritance are retained.

Thus U is truly unloaded, all-bridge and avoids zero. The accepted
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md applies, with the
same minimal-support choice. It proves that U has exact positive
degree two and the full original side-transmitter geometry

    p_A=r f,
    p_V=(r+1)f,
    0<r<=d-1<1/60,      d=sqrt(R^2-1/4)-1.                (3)

Here A is its unique incoming neighbor, and V its unique outgoing
neighbor. In particular A contains zero. Every original transverse
slider and both support-mean endpoints remain in this conclusion.
No leaf formula is assigned to V.

V cannot be another truly unloaded all-bridge body. It lies wholly
in f.x>=r+1>1, whereas every unloaded all-bridge body meets the
central disk D_delta, delta=max(R-2,0)<1/12. Nor can V be a
loaded all-bridge nonleaf by the already established exact split.
Consequently V is either a genuine leaf, or a body belonging to
some positive cyclic block.

If V is itself the root of an intact bridged end triangle, that
triangle's actual interface from U has positive signed radius
r+1. This contradicts (1) directly, with every force at V retained.

This proves a useful full-interface implication: an intact bridged
end triangle followed by an all-bridge nonleaf can pass through
exactly one side transmitter, and its next cyclic block cannot
be another intact bridged end triangle.

## 3. No all-bridge path between two intact end-triangle roots

**Path theorem.** Let two disjoint positive triangles have roots
A_1,A_2 of exact degree three, each with exactly one exterior bridge,
and their other four vertices of exact degree two. There is no
positive path from A_1 to A_2 whose internal bodies are all-bridge.
Arbitrary further positive branches at those internal bodies are
allowed in the initial hypothesis and are dealt with by the proof.

If the path has one edge, it is the actual bridge A_1A_2. Applying
(1) at both ends would require both rho<0 and -rho<0. This is
impossible, including the zero-application case. This is also the
complete joined-triangles corollary in Section 5 of the strict
inward-interface source.

Otherwise let U be the first internal body from A_1. It is not a
leaf because the path continues toward A_2. Section 2 therefore
forces its actual degree to be two and identifies its other neighbor
V as its outgoing neighbor. The path must continue through that
actual edge; no off-path positive force has been discarded.

If V is still internal to the path, it is an all-bridge nonleaf,
contradicting Section 2. If V=A_2, its positive-radius interface
contradicts (1). Both alternatives are impossible, proving the
path theorem on the full original graph domain.

The proof requires neither a bound on the path length nor a list
of branches attached to it. Its change-of-support steps were
established before any path was selected, on the one common pose.

## 4. Entire two-triangle bridge-forest consequence

**Whole-family theorem.** The selected component cannot have exactly
two disjoint cyclic blocks, both triangles, where each triangle has
exactly one incident bridge and every other edge of the component
is a bridge. The intervening bridge forest may have arbitrary
genuine leaves, subdivisions and branching, within the nine actual
bodies.

Indeed the block tree provides a unique path between the two cyclic
blocks. Its endpoints are the two actual degree-three roots; every
internal body lies outside all cyclic blocks and hence is all-bridge.
The four other triangle vertices retain their genuine degree two.
All path-theorem hypotheses hold, yielding a contradiction.

Contracting the two triangle blocks here is solely a graph-theoretic
way of locating their unique connecting path. No physical body or
force resultant is replaced in an equilibrium equation. The proof
keeps every branch in the full graph until the minimal-support
theorem itself proves that a particular body has degree two.

This whole family includes the direct six-body bridge, arbitrarily
subdivided connecting paths, and every seven-, eight- or nine-body
bridge-tree attachment with those two exact end blocks. In the
coarse C2.33.b1 through C2.33.b4 range, it supplies a common exclusion
for all such disjoint end-triangle interfaces at the newly proved
minimal-support scope.

## 5. Precise limitations and inheritance

The theorem does not assign an exact degree-three equation to a
triangle root carrying two exterior bridges. It also does not treat
two triangles sharing a body as disjoint blocks, or allow an
unmentioned cyclic block on the connecting path. Those are different
whole-component families and remain outside this source.

The loaded-internal-body exclusion retains the accepted canonical
pose and small-core prerequisites from the articulation theorem.
The minimal-support choice preserves that pose, its radius, all
physical contacts, all surviving original normals and aggregate
means, and all nine physical squares. Any body not in the retained
stress remains a real packing obstacle and completion square.

No larger coarse cell, sharp lower bound or equality classification
is claimed by this assembly alone. No Lean compilation, CI,
numerical pose search or coefficient certificate is used.
