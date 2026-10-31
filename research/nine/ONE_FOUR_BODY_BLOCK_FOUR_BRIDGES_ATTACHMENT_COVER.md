# A complete 66-orbit attachment cover for C1.4.b4

Date: October 27, 2026.

**Status: complete finite hand cover and exact partial join, submitted
for full root and separate independent review.** The new whole-forest
dependencies have full independent reviews named below; their root
acceptance remains a separate requirement. This cover excludes 62 of
its 66 original rooted-forest orbits and leaves four explicitly stated
whole attachments open. These are attachment counts introduced here,
not additions to the original fine ledger. No coarse-cell closure or
shared metadata change is claimed.

Keep all nine original interior-disjoint physical unit squares and
the same compatible selected radius/Phi-minimizer pose and minimum-
positive-original-scalar-atom certificate, with

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60,
    epsilon=max(d-1,0)<1/60.

The original selected positive component has exactly one four-body
cyclic block and four bridges. Every positive edge, actual normal,
shared-side application mean, physical circle mask, individual zero
weight and original force/moment equation is retained. It has eight
positive bodies; the ninth physical unit is still present and arbitrary.

## 1. The original graph and its complete forest partition

A four-vertex biconnected simple block is C4, the diamond, or K4.
NO_POSITIVE_K4_SUBGRAPH.md excludes the last profile inside the actual
larger graph, without deleting its bridges. Thus consider C4 and the
diamond. Write the diamond hubs as H,K and its tips as B,D, so its
five block edges are HK,HB,KB,HD,KD.

Remove only the block edges for the purpose of describing the original
graph. The outside edges form rooted trees, each attached at one actual
block vertex. Distinct such trees have distinct outside bodies. A tree
cannot attach at two block vertices, since the joining path would be
part of the original cyclic block. Four bridges consequently supply
exactly four outside vertices.

GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md gives the actual
branch bound k+ell<=3 in this minimum-atom certificate. Each outside
nonleaf is all-bridge, has genuine zero circle load and has degree
at most three. At a block vertex the block remainder is one of its
articulation branches, so at most two outside tree branches attach
there. These are original degree statements, not equations obtained
by removing a branch force.

Partition the four original bridge edges by their outside rooted
trees. The partitions of four give exactly the following classes:

| Forest class | Complete original shape |
| --- | --- |
| 1+1+1+1 | Four direct genuine leaves |
| 2+1+1 | One two-edge arm and two direct genuine leaves |
| 2+2 | Two two-edge arms |
| 4 | One connected four-edge tree |
| 3+1, fork | A three-edge double-leaf fork and one direct leaf |
| 3+1, path | A three-edge path and one direct leaf |

The two-edge tree is necessarily a path. A three-edge tree is either
H--U--V--L or H--U with U--L,U--M. A connected four-edge tree has
exactly the three shapes proved in
FOUR_BODY_BLOCK_SINGLE_FOUR_EDGE_TREE_CLOSED.md, Section 1:

    H--U--V--W--L;
    H--U--V, V--L, V--M;
    H--U, U--L, U--V, V--M.

A four-child or three-child outside fork would violate the actual
branch bound. The displayed list therefore includes every original
outside tree, including all allowed repetitions of its block roots.

## 2. Hand counts of the root orbits

Quotient only by automorphisms of the actual block and interchange
of genuinely identical outside trees. The two different trees in a
3+1 forest remain distinguished.

| Original forest class | C4 | Diamond | Total |
| --- | ---: | ---: | ---: |
| Four direct leaves | 5 | 8 | 13 |
| One two-edge arm and two direct leaves | 6 | 12 | 18 |
| Two two-edge arms | 3 | 5 | 8 |
| One connected four-edge tree | 3 | 6 | 9 |
| Three-edge double-leaf fork and direct leaf | 3 | 6 | 9 |
| Three-edge path and direct leaf | 3 | 6 | 9 |
| **Total** | **23** | **43** | **66** |

Here is a direct verification of every row. No numerical or machine
enumeration is a premise of the cover.

For four direct leaves the allowed multiplicity patterns are
(2,2,0,0), (2,1,1,0), and (1,1,1,1). On C4 the two double roots
are adjacent or opposite; in (2,1,1,0) the zero root is adjacent or
opposite to the double root; the last pattern has one orbit. This
gives 2+2+1=5. On the diamond the two double roots are both hubs,
both tips, or a hub and a tip. In (2,1,1,0), the double root is a
hub or a tip and the zero root has the same or the other type.
Thus the diamond has 3+4+1=8.

For one two-edge arm and two direct leaves, first fix the arm root.
Its stabilizer fixes one further block root and exchanges the other
two, both on C4 and on the diamond. The unordered pair of direct-leaf
roots, with repetition allowed, consequently has six orbits after
excluding the pair that puts both leaves at the arm root: that pair
would give three outside branches at one block vertex. Explicitly,
write a for the arm root, b for the other fixed root, and c,d for
the exchanged roots. The six allowed pairs are

    {a,b}, {a,c}, {b,b}, {b,c}, {c,c}, {c,d}.

C4 has one arm-root orbit and the diamond has two, giving 6 and 12.

For two two-edge arms the unordered root pair allows repetition.
C4 gives same, adjacent, opposite. The diamond gives same hub,
same tip, two different hubs, two different tips, and hub/tip.
Thus this row has 3 and 5.

For one connected four-edge tree there are three actual tree shapes
and one C4 root orbit or two diamond root orbits, giving 3 and 6.

For each of the two 3+1 rows the ordered pair of block roots gives
same, adjacent, opposite on C4. On the diamond choose the root type
of the three-edge tree, then put the direct leaf at that same root,
the other root of its type, or a root of the other type. This gives
2 times 3=6. The fork and path are distinct original rooted trees,
so each has its own complete row.

## 3. Five entire forest classes are excluded

### 3.1. Four direct genuine leaves: all 13 orbits

At most two of the four actual leaves have any one root, by the
branch bound in Section 1. The whole physical theorem
FOUR_GENUINE_LEAVES_WITH_TWO_PER_ROOT_EXCLUSION.md applies at
their genuine degrees, for every D/S type and radius. It keeps all
nine actual units and imposes no extra block-root equation.

Its full independent review is
REVIEW_FOUR_GENUINE_LEAVES_TWO_PER_ROOT_ROOTED_BLOCKS_2026_10_27.md.

### 3.2. One short arm and two direct leaves: all 18 orbits

The actual terminal body of the two-edge arm is a genuine leaf
whose true root has positive degree two. Together with the two
direct genuine leaves, these are exactly the entire domain of
THREE_GENUINE_LEAVES_WITH_A_TRANSMITTER_ROOT_EXCLUSION.md.
The other two roots can coincide with each other or with the arm's
block root; all those cases are included there. No force at a
repeated block root is removed.

Its full independent review is
REVIEW_THREE_LEAVES_WITH_TRANSMITTER_ROOT_ROOTED_BLOCKS_2026_10_27.md.

### 3.3. Two short arms: all eight orbits

If the two arms have the same C4 root, apply
FOUR_CYCLE_TWO_SHORT_ARMS_SAME_ROOT_CLOSED.md at true degrees
H4,B2,C2,D2 and both original degree-two arm roots. If they have
the same diamond hub, apply
DIAMOND_TWO_SHORT_ARMS_SAME_HUB_CLOSED.md at the true H5,K3
and original private tip degrees. If they have the same diamond
tip, both actual hubs retain degree three, so Corollary 4.2 of
BOUNDARY_EDGE_OUTER_FACE_AND_DIAMOND_EXCLUSION.md excludes their
actual positive hub edge. Its arbitrary-tip scope includes the
tip with both genuine arms.

For distinct roots, apply
TWO_SHORT_ARMS_AT_NEARBY_DISTINCT_ROOTS_EXCLUSION.md. Adjacent
block roots physically touch. Opposite C4 roots have an actual
common block neighbor; the two diamond tips likewise have an
actual common hub. That common neighbor is distinct from both
roots and both outside arm bodies, as required. Thus every
distinct-root orbit satisfies the exact physical contact/bypass
premise, with all original arm types and actual means retained.

The three new complete arm sources have their full independent
reviews respectively in
REVIEW_C4_TWO_SHORT_ARMS_SAME_ROOT_ROOTED_BLOCKS_2026_10_27.md,
REVIEW_DIAMOND_TWO_SHORT_ARMS_SAME_HUB_ROOTED_BLOCKS_2026_10_27.md,
and REVIEW_TWO_SHORT_ARMS_NEARBY_DISTINCT_ROOTS_ROOTED_BLOCKS_2026_10_27.md.

### 3.4. One connected four-edge tree: all nine orbits

This is precisely the complete original scope of
FOUR_BODY_BLOCK_SINGLE_FOUR_EDGE_TREE_CLOSED.md. Its path proof
uses actual transmitter widths; the double-leaf stem has the
independent TWO_LEAF_ROOT_NO_UNLOADED_TRANSMITTER.md exit; and
its early fork is the complete original graph of
FOUR_BODY_BLOCK_DIRECT_LEAF_AND_SHORT_ARM_FORK_CLOSED.md.

The corrected negative-bridge dependency retains the full root
circle force and uses the actual equation

    M+beta*n+G_H=0.

It is
FOUR_BODY_BLOCK_NEGATIVE_BRIDGE_WITH_FULL_ROOT_LOAD_EXCLUSION.md.
The old erroneous sign/convex-combination argument is not used.
The corrected theorem and both full tree callers have a fresh
joint independent acceptance in
REVIEW_FOUR_BODY_NEGATIVE_BRIDGE_AND_FOUR_EDGE_TREE_ROOTED_BLOCKS_2026_10_27.md.

### 3.5. A three-edge double-leaf fork and a direct leaf: all nine orbits

Write the exact fork as H--U,U--L,U--M. The true U3 has its two
actual genuine leaves, and the other direct genuine leaf has a
block root C different from U. Its root may equal H. This is
exactly the full domain of
DOUBLE_LEAF_BRIDGE_FORK_WITH_ANOTHER_GENUINE_LEAF_EXCLUSION.md.
That theorem preserves every original force at H and C, including
the repeated-root case, and supplies all noncritical and critical
physical completion exits.

Its full independent review is
REVIEW_DOUBLE_LEAF_BRIDGE_FORK_OTHER_LEAF_ROOTED_BLOCKS_2026_10_27.md.

The five classes of this section therefore account for
13+18+8+9+9=57 complete attachment closures.

## 4. The three-edge path and one direct leaf: five closures and four residues

Write the original path as H--U--V--L and the genuine direct
leaf as C--M. Section 1 of
FOUR_CYCLE_LONG_ARM_OPPOSITE_LEAF_CLOSED.md uses only the actual
path, the full bridge equations and physical containment at H.
It does not use any cyclic force equation or an opposite-root
premise. It therefore exports the following exact reduction to
every original block profile and placement in this row.

Every D terminal, S/diagonal transmitter, and strict-low radius
is impossible. At d=1 the sharp support equality gives the real
physical H=S(-e); together with U,V,L this is the full closed-slider
P_ALL cage. In the only remaining strict-high case,

    d=1+epsilon,      0<epsilon<1/60,
    L is S,          U and V are actual side transmitters,
    p_HU=(epsilon-1)e,
    H subset {e.z<=epsilon-1},
    O belongs to closed U.

If C=H, the genuine root H meets D_epsilon and so h_H(e)>=-epsilon,
contrary to h_H(e)=epsilon-1<-epsilon. This excludes every same-root
placement at all radii. It uses no modified H equation.

The exact remaining placement cover is:

| Block | Path root H | Direct-leaf root C | Whole original status |
| --- | --- | --- | --- |
| C4 | Any root | Same root | Closed by the preceding near-root support contradiction |
| C4 | Any root | Adjacent root | **Open R1** |
| C4 | Any root | Opposite root | Closed by FOUR_CYCLE_LONG_ARM_OPPOSITE_LEAF_CLOSED.md |
| Diamond | Hub | Same hub | Closed by the preceding near-root support contradiction |
| Diamond | Hub | Other hub | **Open R2** |
| Diamond | Hub | Tip | **Open R3** |
| Diamond | Tip | Same tip | Closed by the preceding near-root support contradiction |
| Diamond | Tip | Other tip | Closed by the unchanged actual degree-three hub pair |
| Diamond | Tip | Hub | **Open R4** |

For the other-tip diamond row, both actual hubs retain exactly
their three original block neighbors. Corollary 4.2 of
BOUNDARY_EDGE_OUTER_FACE_AND_DIAMOND_EXCLUSION.md allows arbitrary
extra forces at the two tips, and directly excludes that true
hub pair. In particular the long arm and the other leaf are
retained at their actual tips.

The opposite-C4 source has full independent acceptance in
REVIEW_C4_LONG_ARM_OPPOSITE_LEAF_ROOTED_BLOCKS_2026_10_27.md.

## 5. Exact remaining scope

All four residuals are original high-radius S/side long-path
attachments with C different from H and positively adjacent to H.
The genuine direct leaf is S: a D root C would contain O openly
and overlap the distinct actual U, which contains O closed.
The same physical argument gives O not in int C. C is physically
clear and meets D_epsilon. H may still carry its original circle
force; no zero-load assertion at H is part of this cover.

The actual degrees of the two decorated block roots are:

| Residue | Original decorated-root degrees | Other actual block degrees |
| --- | --- | --- |
| R1: adjacent C4 | H3,C3 | Two degree-two roots |
| R2: hub/hub diamond | H4,C4 | Both tips degree two |
| R3: hub/tip diamond | H4,C3 | Other hub degree three, other tip degree two |
| R4: tip/hub diamond | H3,C4 | Other hub degree three, other tip degree two |

Thus the 66 original attachment orbits are covered exhaustively,
and 57+5=62 are excluded by complete original-domain implications.
The four displayed residues are still open; no isolated force mask,
side-position estimate or partial tilt chart is counted as a closure.
The entire C1.4.b4 coarse cell remains open until all four are closed
and the dependency review requirements are satisfied. No Lean
compilation, CI, numerical search or new finite proof table is used.
