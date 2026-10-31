# Independent full review: the C2.34.b2 marked attachment cover

Date: October 27, 2026.

Reviewer: leaf_pair. This review changes no original ID, shared ledger
or coarse-cell status.

**Verdict: PASS for the exact 66-orbit graph cover, all stated original-
degree theorem joins, and the fourteen-domain remainder at the frozen
source checkpoint.** This is a finite cover and reduction, not a
whole-cell closure. Later independently accepted exits may reduce this
retained list without changing its validity as an exhaustive cover.

Reviewed source:

    TRIANGLE_FOUR_BLOCK_TWO_BRIDGES_COMPLETE_ATTACHMENT_REMAINDER.md
    SHA256 af742d54e1baf9249d5338c36e92415e492348ea41bb3993f1980d547efb85a4

## 1. Exact graph budget and orbit count

The original component has a triangle, one four-body biconnected
block and exactly two bridges on eight stressed units, with the ninth
original physical unit retained. The four-body simple biconnected
list is exactly C4, diamond and K4; the last has the uniform positive-
subgraph exit. Marking the attachment root leaves exactly the C4,
diamond-hub and diamond-page types.

For blocks sharing H, the cyclic union has six units. Two actual
bridges add two units, and their rooted forest is exactly two direct
leaves, with repetitions allowed at one root, or one two-edge arm.
A second connection between already connected cyclic vertices would
put that edge on a cycle and would not be a bridge. No extra rooted
forest is omitted.

The root-preserving automorphisms independently exchange A,B and
P,Q while fixing H,K. Unordered two-root multisets have the exact
fixed counts 21,11,11,5: ten multisets on the four fixed vertices
plus the exchanged pair for a single transposition, and three
multisets on H,K plus AB,PQ for the double transposition. Burnside
therefore gives twelve direct-leaf orbits. The four arm-root orbits
are H,A,K,P. Their explicit representative lists have seven intact
direct-leaf rows, five non-intact direct-leaf rows, three intact
arm roots and one non-intact arm root. Thus each marked four-block
type has sixteen shared attachments, ten intact and six non-intact.

For disjoint cyclic blocks there are seven cyclic units and one
new unit. A direct HK connector leaves exactly one genuine leaf
at one of H,A,K,U,V. A two-edge H-T-K connector uses both bridges
and the only new unit. An internal connector branch would require
a third bridge and is excluded by the actual budget. Each marked
type therefore has six disjoint attachments, five intact and one
non-intact. The resulting exact totals are

    3*16+3*6=66,
    3*10+3*5=45 intact,
    3*6+3*1=21 non-intact.

I checked these explicit combinatorial counts directly; no pose
enumeration or extra computational test is needed for this review.

## 2. Every intact shared direct-leaf join has its exact premises

For all these rows the genuine intact tips A,B keep true degree two,
so the accepted origin-interior theorem applies at full H degree.

For HH, deleting H has four actual positive branches: the triangle
private pair, the connected private four-block, and the two distinct
leaf bodies. The minimum-support bound k+ell<=3 is explicitly a
branch-count theorem, not an edge-count theorem. I reread the full
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md and checked that the
source invokes exactly its common fixed-pose, fixed-normal minimal-
support scope.

For HK/HP, the complete S and D intact-root central-disk theorems
put the closed disk strictly inside H. I reread both complete sources:
their geometric conclusions allow all other actual H forces and do
not use an isolated H equation. The other actual genuine root meets
that disk and forces physical overlap.

For KK/PP, the double-leaf central-disk lemma is geometric at arbitrary
other root degrees. Its complete D/S support cover gives closed-origin
containment at every radius, with the critical origin-vertex case
retained. This contradicts O in int H. For KP/PQ, the actual two
distinct external leaf roots meet the disk and satisfy the accepted
intact-petal/two-near-units theorem, whose near units require no
degree or load assumption. The epsilon=0 endpoint is already closed-
origin overlap. These seven representatives close all twenty-one
intact shared direct-leaf orbits.

## 3. Every shared arm and non-intact join keeps true degrees

For an intact shared arm, the original bridge-only internal T is
unloaded by the common minimal-support articulation theorem. T is
off O because the distinct intact H contains O openly. I reread the
full off-origin bridge-transmitter source: its actual incoming
neighbor contains O closed and its outward neighbor need not be
assumed loaded until identified. The genuine boundary leaf cannot
be the incoming neighbor. Thus the incoming neighbor is exactly
the real cyclic arm root R. If R is K or P, it conflicts with H;
if R is H, the original arm has the complete S/side form and all
closed transverse slider endpoints. No T midpoint is fixed.

The page-rooted diamond H-arm has unchanged true degree-three hubs
and a true degree-two other page, so its boundary-triangle exit
applies with the full H triangle and arm still present. The other
two H-arm graphs correctly remain. Their stated C4 mask restrictions
use the actual intact-petal/sole-opposite theorem, the complete
near-root boundary-detour theorem, and the genuine unloaded paths.
They reduce masks without counting either remaining graph as closed.

For the non-intact direct-leaf AA rows, A is the real degree-four
double-leaf root and B the real boundary degree-two tip. The terminal
four-block has unchanged private degrees and the actual external
near unit X=A. Its complete near-origin transfer gives an original
block unit Z, without declaring Z a leaf root or assigning it a
degree. The full near-unit double-leaf lemma permits precisely this
A4, boundary B and arbitrary H,Z, including its complete critical
endpoint. I read the full double-leaf/terminal-four source and the
transfer's complete statement and graph/load cover.

For AB, I read the complete accepted shared two-leaf-triangle/four-
block theorem. Its A3/B3 hypotheses, full external origin moments,
terminal private degrees and common-only-H nesting argument match
all three current rows. The actual leaf edge in the inner-triangle
case remains present. The result is explicitly about eight stressed
units plus the ninth physical unit, so no smaller-component theorem
is substituted here.

For an arm at A, the complete small-radial-external-support theorem
and its sole-arm consequence have exactly true A3 and arbitrary
other triangle degrees. The genuine whole arm supplies the original
external moment and support; its side/diagonal and S/D alternatives
are covered before the surviving small-support contradiction.

For the page-diamond AH row, the untouched hubs and other page
retain their exact boundary-triangle degrees. For page-diamond AK,
the other page's genuine leaf raises that page to degree three, and
the source correctly does not call it a boundary degree-two page.
The two hubs remain true degree three and are loaded by their
physical neighbor contacts. Their actual positive boundary hub edge
has the two original common neighbors H,K, so the arbitrary-degree
boundary-edge theorem applies. This leaves precisely C4 AH/AK/AP,
hub-diamond AH/AK/AP and page-diamond AP: seven shared non-intact
domains.

## 4. Complete disjoint-block joins and necessary restrictions

The direct-connector private-triangle leaf A is the only non-intact
disjoint attachment. It has the original A3/B2 triangle and a fully
terminal disjoint four-block. The complete already reviewed
leaf-decorated-triangle/disjoint-four theorem permits both real
root external systems and every block mask. The original bridge
moment is zero by the full unchanged branch sum, with H's own
circle system retained until its physical clearance is proved.
All three graph/root types therefore have this exit.

In the intact disjoint attachments, E=H contains O openly and is
distinct from every four-block unit. A leaf at H or K, and the
two-edge connector, leave all three private block degrees intact.
The complete occupied-origin terminal-four theorem allows arbitrary
other K forces, including its genuine leaf. Its full private graph/
load cover therefore excludes all those rows. No private leaf is
silently absorbed into that terminal premise.

The remaining private-leaf placements U,V are retained except for
the page-diamond other-page U. In that row both hubs still have
true degree three and the actual boundary hub edge has the original
two common neighbors, so the same full boundary-edge theorem applies
without treating the decorated U as degree two.

The five retained private-leaf domains necessarily have genuine S
and d>1 because their actual root J differs from the origin-interior
H. The actual bridge endpoint K is clear by
GLOBAL_CLOSURE_INTACT_ROOT_DIRECT_BRIDGE_REDUCTION.md, Corollary 2:
the complete H equation has its intact petal and sole direct bridge,
so the required negative center-pressure bridge sign is valid. The
common same-nine lower-radius theorem supplies that source's R>2
scope. I reread that complete direct-bridge source.

For opposite-U C4, the unchanged degree-three S root U and true
degree-two V,W meet the complete intact-petal/opposite-leaf load
reduction. Its outside intact unit is the real H and its arbitrary
cycle root is the real bridge endpoint K. I reread this complete
source, including the one-transmitter detour and two-transmitter
original-means winding argument. It forces both V,W loaded without
closing the retained graph. The other-hub diamond has its two true
degree-two pages loaded directly. These are the exact stated
necessary restrictions only.

## 5. Full arithmetic and degree inventory

The disjoint groups in the original 66-orbit cover have these exact
counts at the frozen checkpoint:

| Original group | Total | Whole exits supplied | Retained |
| --- | ---: | ---: | ---: |
| Shared intact direct leaves | 21 | 21 | 0 |
| Shared intact arms | 9 | 7 | 2 |
| Shared non-intact attachments | 18 | 11 | 7 |
| Disjoint cyclic blocks | 18 | 13 | 5 |
| Total | 66 | 52 | 14 |

I checked every affected cyclic degree in Section 6 against the
displayed actual edge lists. Shared H has its two triangle edges
plus its original C4/page degree two or hub degree three, and then
its real extra leaf or arm when present. Decorated private pages
rise from two to three; decorated hubs rise from three to four.
Disjoint K additionally retains its genuine connector edge. The
table's H5/H6, K3/K4, P3/P4, private true2/true3 and original chord
counts all agree. Direct leaves remain true degree one and arm T
remains its actual degree two.

Thus the fourteen listed domains are exhaustive, disjoint as marked
attachment orbits, and retain every still-allowed load, mask, mean,
leaf type and force ratio. The cover does not assert physical
realizability, create replacement fine IDs, or close the entire
C2.34.b2 cell. No Lean compilation, CI, physical motion, changed
normal or mean, remote mutation or shared-ledger edit was used.
