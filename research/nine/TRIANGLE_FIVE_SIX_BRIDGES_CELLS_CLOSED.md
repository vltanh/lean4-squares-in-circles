# Complete sole-triangle cells with five or six bridges

Date: October 26, 2026.
**Status: accepted complete theorem after full-source independent review in REVIEW_TRIANGLE_FIVE_SIX_BRIDGES_ROOTED_BLOCKS_2026_10_26.md.** The two original coarse rows close in this checkpoint. No new deep checklist ID is introduced.

## 1. Entire original domain and common selection

Keep all nine actual unit squares and their common radius/Phi-minimizer
pose in 79/40<=R<=sqrt(1105)/16. Use the compatible preselected physical
normal system and choose a normalized stress with minimum positive
original scalar support as proved in
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md. This is one common
certificate throughout the assembly. Its force, origin moment,
normalization and small-core inheritance have already been proved.

All physical bodies, every physical circle corner including individual
zero weights, actual contact means, surviving positive forces and
zero-stress contacts remain present. A square omitted from the positive
component still occupies its original position among the nine.

**Theorem.** The selected positive component cannot have exactly one
cyclic block of size three and exactly five or six bridges. These are
the entire original cells C1.3.b5 and C1.3.b6: respectively eight
positive-component bodies with one arbitrary completion square, and
nine positive-component bodies with no completion square.

A simple biconnected three-body block is the full triangle. There is
no separate positive-chord case on three vertices. Every remaining
edge in these two cells is an actual graph bridge; every component
obtained by deleting the triangle edges is a rooted tree attached
to just one triangle vertex. Attachment to two different triangle
vertices would make an additional cycle and contradict bridgehood.

## 2. Complete forest and root-degree reductions

The exact articulation split and accepted complete at-most-five-body
assemblies show that every loaded body incident only to bridges is
a genuine leaf. Every outside nonleaf is therefore truly unloaded.
The source preserves the unchanged canonical pose and preselected
normal system in this use of the smaller complete stresses.

ROOTED_TRIANGLE_FOREST_OUTSIDE_FORK_EXCLUSION.md excludes every
outside branching vertex, with its entire d=1 physical completion
cover. Consequently every bridge branch is a simple pendant path.

ROOTED_TRIANGLE_TWO_PATH_ROOT_EXCLUSION.md excludes two paths at
one triangle vertex. Its graph cover uses the minimum-support
articulation bound, so no root can have three unexamined paths.
Hence there is at most one path at each of the three triangle
vertices.

If all paths attach at one vertex, the complete theorem
GLOBAL_CLOSURE_ONE_ROOT_TRIANGLE_FORESTS_EXCLUDED.md excludes the
component, retaining every original path load and completion body.
Thus at least two distinct triangle roots are attached.

No remaining path has four or more edges. Its at least three
genuinely unloaded intermediate widths put the actual root support
at coordinate at most d-3 in its leaf direction. Its center
projection is therefore at most d-7/2<-149/60, contradicting the
universal center norm bound91/60. This argument is independent of
the root's possible circle load.

All path lengths are therefore in {1,2,3}. The complete long-arm
theorem ROOTED_TRIANGLE_LENGTH_THREE_ARM_GEOMETRY.md proves that
at most one triangle root can have length three, without declaring
such a root circle-clear. Its discarded width, leaf and critical
radius cases have full original-domain exclusions.

## 3. Exhaustive whole-cell path cover

The number of bridges is exactly the sum of these pendant-path
lengths. Up to a permutation of the three actual triangle vertices,
the remaining whole possibilities are:

| Original cell | All short paths | One length-three path | Two length-three paths |
| --- | --- | --- | --- |
| C1.3.b5 | (2,2,1) | (3,2) or (3,1,1) | Impossible: sum would be at least6 |
| C1.3.b6 | (2,2,2) | (3,2,1) | (3,3), already excluded by the full long-arm theorem |

This is a finite graph-theoretic cover, not a cover by poses or angle
intervals. A path permutation only relabels its actual bodies; no
symmetry of its physical squares or forces is assumed.

Every listed full original domain has an accepted complete exit:

1. TRIANGLE_DISTINCT_SHORT_PATHS_EXCLUSION.md excludes (2,2,1) and
   (2,2,2), with every S/D leaf, actual transmitter width, circle
   mask and shared mean. Its separate zero- and nonzero-cycle-moment
   proofs keep the true root equations throughout.
2. GLOBAL_CLOSURE_LONG_ARM_EXCLUDES_TWO_EDGE_NEIGHBOR.md excludes
   the full (3,2) and (3,2,1) layouts. The proof is geometric at
   the two actual touching roots and expressly retains a possible
   circle load at the long root.
3. TRIANGLE_LONG_ARM_TWO_DIRECT_ROOTS_EXCLUSION.md excludes the
   full (3,1,1) layout. The long arm's actual first transmitter
   and the two genuine direct-leaf roots would have three centers
   in a cap whose same-sign half has squared diameter below one.
4. ROOTED_TRIANGLE_LENGTH_THREE_ARM_GEOMETRY.md excludes (3,3)
   using the original two origin-containing internal squares,
   repeated radial terminals or separated actual triangle roots.

Thus both original cells are excluded with every initial attachment
layout, load, physical mask and arbitrary completion retained.

## 4. Exact count and remaining scope

This is a closure of two complete original coarse rows, C1.3.b5 and
C1.3.b6, at the explicitly inherited common canonical/minimum-support
scope. It does not by itself close G3.M8.ALL or G3.M9.ALL: all their
other cyclic block inventories remain separate obligations.

The sole-triangle cell C1.3.b4 has the additional length distribution
(3,1). It supplies only two of the three centers used in the (3,1,1)
cap theorem and remains outside this assembly. No conclusion for
that row is inferred by deleting a positive leaf from a larger graph.

The unrestricted sharp lower bound R^2>=1105/256, its equality
classification and the full old prerequisite-chain audit remain open.
This assembly adds no new original checklist ID, computational
certificate, Lean compilation or CI claim.
