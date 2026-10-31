# Complete sole-triangle cell with four bridges

Date: October 26, 2026.

**Status: accepted complete original-cell assembly after full root review in REVIEW_TRIANGLE_FOUR_BRIDGES_CELL_ROOT_2026_10_26.md and separate review in REVIEW_TRIANGLE_FOUR_BRIDGES_CELL_ROOTED_BLOCKS_2026_10_26.md.** Every substantive attachment
exit below has already received full source review. No shared ledger or
fine checklist ID is changed here.

## 1. The entire original cell and one common stress selection

Keep all nine actual unit squares in the common radius/Phi-minimizer
pose, in

    79/40<=R<=sqrt(1105)/16.

Fix the compatible preselected physical normal system and choose a
normalized stress with minimum positive original scalar support, exactly
as proved in `GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md`. Its full
force, origin-moment, normalization, planarity and small-core inheritance
are part of that accepted theorem. The physical pose does not change.
All nine squares, all physical circle corners including zero-weight
corners, every actual shared-side mean, all surviving positive forces
and every zero-stress physical contact remain in place.

**Theorem.** This selected positive component cannot have exactly one
cyclic block of size three and exactly four graph bridges. This is the
entire original coarse cell C1.3.b4: seven positive-component bodies and
two arbitrary physical completion squares.

The theorem is at the explicitly inherited common canonical-pose and
minimum-support scope. It does not assert that every original stress
representation already has minimum support. It excludes this graph
profile from the one legitimate common stress selection used by the
whole proof.

A simple biconnected block on three vertices is the full triangle A,B,C.
All other positive edges in the stated cell are bridges. Deleting the
three triangle edges therefore leaves trees, each attached to one
triangle vertex. A tree joining two triangle vertices would put its
connecting path on another cycle, contrary to bridgehood. Connectedness
rules out any detached positive tree. Each bridge adds one outside
vertex, so the body count is exactly 3+4=7.

## 2. Complete reduction of every rooted forest

The exact articulation split, together with the accepted common-pose
exclusions of all positive components on at most five bodies, proves
that a loaded body incident only to bridges is a genuine leaf. The
concrete small-core assemblies and their unchanged-pose inheritance are
listed in `GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md`, Section 4.
Consequently every outside nonleaf in the present graph is genuinely
unloaded, not merely treated as unloaded after a force is removed.

The complete theorem
`ROOTED_TRIANGLE_FOREST_OUTSIDE_FORK_EXCLUSION.md` excludes every
branching vertex outside the sole triangle, with the full critical
radius completion cases included. Thus every remaining bridge branch
is an actual simple pendant path. Its internal bodies have their true
positive degree two and zero total circle load, and its terminal is a
genuine radial S/D leaf.

At a triangle vertex, the intact remaining triangle is one component
after that vertex is deleted, and each of its pendant paths is another.
The minimum-support articulation bound k+ell<=3 therefore permits at
most two such paths at one triangle vertex, including when that vertex
has a circle load. The complete theorem
`ROOTED_TRIANGLE_TWO_PATH_ROOT_EXCLUSION.md` excludes two at one root,
while retaining every possible attachment at the other triangle roots.
It also covers the all-at-one-root case through the accepted full
one-root forest theorem. Hence there is at most one path at each of the
three triangle vertices.

These are whole-forest exclusions in the same selected stress. No
subgraph is assigned an isolated-component equation, and no positive
branch is discarded to obtain a smaller graph.

## 3. The four and only four remaining path distributions

The positive path lengths sum to the original bridge count four. There
are at most three paths, at distinct triangle roots. Up to a permutation
of those actual roots, the exhaustive positive-integer partitions are

    (4),       (3,1),       (2,2),       (2,1,1).           (1)

The apparent partition (1,1,1,1) would require four distinct triangle
roots and is impossible. All original alternatives with two or more
branches at one root, or an outside fork, were already exhausted in
Section 2. Thus (1) is a complete original graph cover, not a cover by
sampled poses or selected contact owners.

### 3.1. The single path (4) is impossible independently of its root load

Let e be its actual leaf direction and r_L its genuine radial support,
equal to d=sqrt(R^2-1/4)-1 for S or r=R-sqrt(2) for D. Each of its three
genuinely unloaded internal units has original transmitter width in
{1,sqrt(2)}. If W is their sum, then W>=3. The unchanged radial channel
equations give the actual root support and supporting half-plane

    p_A=(r_L-W)e,
    A subset {e dot x<=r_L-W}.

Throughout the radius window, r<7/10<9/10<d<61/60. Since every square's
supporting half-width is at least 1/2, the actual root center obeys

    c_A dot e<=r_L-W-1/2
                <=d-7/2<-149/60.

But every contained unit has |c_A|<91/60. This contradiction excludes the
entire four-edge path, regardless of any original circle load or other
force at A. No leaf-only equation has been applied there.

### 3.2. Complete exits for the three multi-root distributions

| Entire remaining attachment | Accepted complete source | Full original scope used |
| --- | --- | --- |
| (3,1) | `GLOBAL_CLOSURE_LONG_ARM_AND_DIRECT_LEAF_TRIANGLE_EXCLUSION.md` | A potentially loaded long root, both genuine direct-leaf types, every original width, slider, mean and triangle moment; both arbitrary extras retained |
| (2,2) | `TRIANGLE_DISTINCT_SHORT_PATHS_EXCLUSION.md` | Two genuinely clear length-two roots at distinct triangle vertices, all S/D terminals and true transmitter widths, the third root's full circle mask |
| (2,1,1) | `TRIANGLE_DISTINCT_SHORT_PATHS_EXCLUSION.md` | One true two-edge arm and two genuine direct leaves at three distinct roots, with all three full root equations and zero/nonzero moment alternatives |

The short-path source was independently reviewed in
`REVIEW_TRIANGLE_DISTINCT_SHORT_PATHS_GLOBAL_2026_10_26.md`, with the
accepted common prerequisites for actual radial concurrences and all
original parallel-root alternatives.

The new long/direct source has full root review in
`REVIEW_LONG_ARM_DIRECT_LEAF_ROOT_2026_10_26.md` and separate full review
in `REVIEW_LONG_ARM_DIRECT_LEAF_TRIANGLE_ROOTED_BLOCKS_2026_10_26.md`.
Its possible long-root circle load is retained in the actual aggregate
throughout. The source forces both triangle ports onto the long root's
inner side; their unchanged origin moments either give an impossible
common-point angular cover or put the actual first internal body inside
a contact triangle of area less than one. All collinear/coincident
contact cases and endpoint sliders are proved separately. Its sole
nonzero-moment concurrence use has the full aggregate noncollinearity
input, and both possible parallel neighboring roots are handled.

At the critical d=1 radius, the long-arm source invokes the complete
physical P theorem on actual squares. The short-path source likewise
keeps its entire physical critical-domain cover. Neither invokes a
completion result with either of the two original extra squares
removed, nor substitutes a physical S shape for an unstated leaf force.

Every row of (1) now has a whole-domain exclusion.

## 4. Whole C1.3.b4 conclusion

Sections 1--3 start from every original selected graph in C1.3.b4,
preserve the original nine-square packing and common stress choice,
exhaust every rooted forest and all four surviving path distributions,
and apply only the complete accepted exits at their genuine degrees.
Thus the entire original C1.3.b4 cell is excluded.

This closes one complete seven-body coarse profile. It does not by
itself close G3.M7.ALL, whose other cyclic block inventories remain
separate obligations. No new fine checklist label is introduced, and
no old fine label is changed by this assembly.

## 5. Corollary: the full sole-triangle inventory through nine bodies

For clarity, at the same common selected scope this completes every
possible bridge count for a component whose only cyclic block is one
triangle. Such a connected component has 3+b bodies, so b ranges from
zero to six in a nine-square packing. The exact complete joins are:

| Bridge count | Complete accepted exit |
| --- | --- |
| 0 | The three-body cyclic case of `CYCLIC_BLOCK_INVENTORY.md`, Section 6, included in the common at-most-five-body assembly |
| 1 | `TRIANGLE_LEAF_CELL_CLOSED.md` |
| 2 | `TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md` |
| 3 | `TRIANGLE_THREE_BRIDGES_CELL_CLOSED.md` |
| 4 | The complete assembly above |
| 5 or 6 | `TRIANGLE_FIVE_SIX_BRIDGES_CELLS_CLOSED.md` |

The earlier exits remain valid under the same minimum-support selection
because all their physical generic conditions were preselected and all
pose-based canonical hypotheses persist; the articulation source states
this inheritance explicitly. No additional re-selection is performed
between rows. Thus no surviving selected positive component has a sole
triangle cyclic block with any bridge forest among the original nine
physical squares.

Other cyclic block sizes and multi-block components remain separate.
The unrestricted sharp lower bound, equality classification and complete
old prerequisite-chain audit are not inferred from this one inventory
family. No numerical pose sample, Lean compilation, CI or remote action
is used.
