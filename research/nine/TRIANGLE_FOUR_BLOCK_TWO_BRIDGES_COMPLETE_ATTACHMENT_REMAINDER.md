# C2.34.b2: complete original two-bridge attachment cover and twelve-domain remainder

Date: October 27, 2026.

**Status: accepted complete finite cover and original-degree joins after
full root and separate independent reviews. This is not a whole-cell
closure.** The full root review is
REVIEW_TRIANGLE_FOUR_BLOCK_TWO_BRIDGES_COVER_ROOT_2026_10_27.md.
No original ID, checkbox, coarse count, or shared ledger is changed
by this source.

The preceding fourteen-domain cover passed the separate complete
graph/load/source-scope review in
REVIEW_TRIANGLE_FOUR_BLOCK_TWO_BRIDGES_COVER_LEAF_PAIR_2026_10_27.md.
The subsequently fully root- and independently reviewed central-gap
theorem removes the two original domains in Section 5.1 below. This
current twelve-domain join passed the complete changed-cover review
REVIEW_TRIANGLE_FOUR_BLOCK_TWO_BRIDGES_TWELVE_DOMAIN_LEAF_PAIR_2026_10_27.md.
Both final reviews pin the complete source before this acceptance-only
header change.

Keep the same selected canonical nine-square packing, its minimum
positive-support compatible physical certificate, and

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

The original C2.34.b2 component has one triangle block, one four-body
biconnected block, exactly two bridges, and eight actual stressed
bodies. The ninth physical unit remains arbitrary and present. Every
original force, true degree, selected normal, application mean, circle
mask, individual zero weight, and zero-stress physical contact stays.
No bridge is deleted to invoke a smaller or larger component theorem.

## 1. Complete graph cover: 66 marked orbits after the uniform K4 exit

The only four-body biconnected simple graphs are C4, the diamond, and
K4. NO_POSITIVE_K4_SUBGRAPH.md excludes the last at arbitrary outside
degrees. For the remaining two graphs there are exactly three marked
four-block root types: C4, diamond hub, and diamond page.

Two distinct biconnected blocks either share one articulation or are
vertex-disjoint and connected by a unique bridge route. Deleting all
cyclic edges leaves a forest. Every tree outside the connecting route
attaches at only one vertex of that route or a cyclic block: a second
attachment would make one of its claimed bridges lie on a cycle.
This observation includes possible branches at internal route vertices.

### 1.1. Shared cyclic articulation

Write the triangle H-A-B-H. Use the following fixed four-block labels:

| Root type | All actual four-block edges | Fixed roles |
| --- | --- | --- |
| C4 | HP,PK,KQ,QH | K opposite H; P,Q interchangeable |
| Hub diamond | HK,HP,HQ,KP,KQ | K the other hub; P,Q the pages |
| Page diamond | HP,HQ,KP,KQ,PQ | K the other page; P,Q the hubs |

The shared cyclic cluster has six units. The two bridges add exactly
two units. Its entire bridge forest is therefore either two genuine
direct leaves, allowing a repeated root, or a two-edge pendant arm
R-T-L with true internal bridge-only T and genuine leaf L. No other
two-edge rooted forest exists. In particular a two-edge fork is the
two-direct-leaves case at one root.

The symmetries independently exchange A,B and P,Q, fixing H,K. A
direct-leaf pair is an unordered multiset of size two in the six
cyclic vertices. Burnside's fixed counts are

    21, 11, 11, 5;    (21+11+11+5)/4=12.

For example, the A/B transposition fixes all ten multisets on the
other four vertices and the additional pair AB. The double
transposition fixes the three multisets on H,K and the pairs AB,PQ.
The arm root has four orbits H,A,K,P. Thus each root type has
12+4=16 marked shared attachments, and all three types have 48.

The exact shared forest representatives are:

| Forest | Intact triangle H-A-B | Triangle not intact |
| --- | --- | --- |
| Two direct leaves | HH,HK,HP,KK,KP,PP,PQ | AA,AB,AH,AK,AP |
| One two-edge arm | Root H,K,P | Root A |

Hence each root type has ten intact and six non-intact attachments.
A repeated symbol denotes two distinct actual leaves at that vertex,
not one repeated body. The arm T,L is different from every cyclic
body. A leaf at A and one at H is recorded as AH without choosing
a new contact or changing an original force magnitude.

### 1.2. Disjoint cyclic blocks

Write the triangle H-A-B-H, with H its unique connector endpoint.
Write the four-block root as K and its other vertices U,V,W, where
U is opposite K in C4, the other hub for a hub-rooted diamond, or
the other page for a page-rooted diamond; V,W are interchangeable.

The cyclic blocks now have seven distinct bodies, leaving one new
body. There are exactly two possible bridge routes:

- One direct bridge HK, and one genuine leaf at a cyclic vertex.
  Its five root orbits are H,A,K,U,V.
- The full two-edge connector H-T-K, with its one new internal body
  T and no remaining bridge.

An internal connector branch would require a third bridge and a
second new unit, so it is excluded by this exact original budget,
not omitted by convention. Each marked four-block root type has
six disjoint attachments. Exactly the direct-connector leaf at A
breaks the intact triangle; the other five keep it intact.

Thus the complete post-K4 count is

    3*16+3*6 = 66 = 45 intact +21 non-intact.

The graph count was additionally checked by a direct finite
enumeration of all two-edge additions to each six-body shared
cluster, keeping connectedness and testing that both added edges
really are bridges, followed by the displayed exact automorphisms.
The disjoint route/leaf enumeration gives the same six representatives
per type. These checks count graphs; no physical pose is sampled.

## 2. All twenty-one shared intact two-direct-leaf attachments are excluded

In this section H-A-B is genuinely intact. The original true A2/B2
equations give their positive loads, and
ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md gives O in int H. All actual
closed units different from H consequently avoid O.

The complete two-leaf location cover is the seven representatives
in Section 1.1. The following exits retain arbitrary additional
forces at H and all real four-block degrees.

| Original two-leaf multiset | Complete original exit |
| --- | --- |
| HH | Removing H gives the actual triangle branch, the connected private four-block branch, and the two distinct leaf branches. Thus H has at least four articulation branches, contrary to the common minimum-support bound k+ell<=3 in GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md. |
| HK or HP | The genuine leaf at the actual intact H puts all of D_epsilon strictly inside H, by the complete intact-root S/D central-disk theorems. The other genuine root K or P has an actual point in D_epsilon, forcing overlap. |
| KK or PP | The actual double-leaf root K or P contains O closed at every radius, including its possible critical origin vertex, by TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md, Section 1. It cannot coexist with O in int H. |
| KP or PQ | The two distinct outside genuine roots both meet D_epsilon. INTACT_PETAL_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md excludes them beside the intact H. At epsilon=0, closed-origin overlap already gives the same exit. |

For HK/HP the two complete strict disk inputs are
GLOBAL_CLOSURE_INTACT_ROOT_S_LEAF_CENTRAL_DISK_EXCLUSION.md and
GLOBAL_CLOSURE_INTACT_ROOT_D_LEAF_CENTRAL_DISK_EXCLUSION.md. Their
hypotheses are geometric at the unchanged true H degree, not an
equation with its four-block forces omitted.

The seven rows hold for each of the three actual four-block root
types, giving all 21 shared intact direct-leaf orbits.

## 3. The shared intact two-edge-arm cover leaves exactly two graph domains

Let the real pendant arm be R-T-L. The minimum-support articulation
theorem makes the bridge-only nonleaf T unloaded, at its true degree
two. As O is in int H, T avoids O closed. The complete off-origin
bridge-transmitter theorem then makes T a genuine side transmitter
with an incoming neighbor containing O closed. The boundary genuine
leaf L cannot be that incoming neighbor, so the incoming neighbor
is precisely its actual cyclic root R.

If R is K or P, it is different from H, and closed-origin containment
in R is impossible. This excludes both marked root locations for
all three four-block types, keeping the actual full transverse slider
and both original arm applications.

The only remaining arm root is H. For a page-rooted diamond its two
true degree-three hubs and true degree-two other page form the
unchanged boundary-triangle obstruction in
ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md. The extra triangle and arm
forces at H do not change any of those three private degrees.

There remain exactly the following two intact shared arm graphs:

    C4 at H + H-T-L;
    hub diamond at H + H-T-L.

The actual T is off-origin and unloaded, so
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md gives the complete
necessary arm form

    d>1, genuine S leaf L,
    T=[epsilon,epsilon+1]e+[b-1/2,b+1/2]Je,
    |b|<=1/2, actual incoming point epsilon e.

H has true degree five in the C4 and six in the hub diamond.
The true C4 private degrees remain two; the diamond has its other
hub degree three, pages degree two, and its genuine positive chord.

The C4 sole-opposite private-load mask is already excluded by
INTACT_PETAL_SOLE_OPPOSITE_C4_NO_GENUINE_LEAF.md: the actual intact
petal and actual genuine leaf L meet its arbitrary-root hypotheses.
An adjacent-two mask is excluded by the physical boundary-detour
theorem FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md, Theorem 4.1, at the
near-origin H and its true unloaded channel. Empty and sole-adjacent
private-load masks have their original unloaded-appendage and two-
consecutive-transmitter exits. Therefore the surviving C4 graph here
can only have opposite-two or full-three private loads. This mask
restriction does not remove either of the two graph domains.

## 4. Shared attachments with a non-intact triangle: seven graph domains remain

The actual non-intact list is AA,AB,AH,AK,AP, and the arm rooted at A,
for each of the three root types. All leaves and arm bodies retain
their original distinct physical identities.

### 4.1. All three double-leaf AA attachments are excluded

Here A has true degree four: two triangle edges and two genuine
leaves. B has true degree two and is physically boundary, because
its actual two neighbors H,A touch. The four-body block at H is
terminal at its three private vertices. The near-origin transfer
in TERMINAL_FOUR_BLOCK_NEAR_ORIGIN_TRANSFER_AND_BROKEN_TRIANGLE_CHAIN_EXCLUSION.md
applies with the actual near unit X=A and gives a distinct actual
block unit Z meeting D_epsilon.

Apply DOUBLE_LEAF_TRIANGLE_WITH_TERMINAL_FOUR_BLOCK_EXCLUSION.md,
Section 2, to precisely this A4, actual boundary B, arbitrary H, and
actual near Z. Its entire critical endpoint proof requires no leaf
or degree assumption on Z. It excludes the whole AA family for
every four-block type and mask. Both A leaves, all full H forces,
all eight component bodies, and the ninth square remain.

### 4.2. All three two-private-tip AB attachments are excluded

Now A and B have true degree three, each with its own genuine leaf.
Their third triangle vertex H is the actual root of the terminal
four-block. Every private block vertex retains its genuine block
degree. The whole
TWO_LEAF_TRIANGLE_SHARED_TERMINAL_FOUR_BLOCK_EXCLUSION.md applies.

Its zero-origin-moment hypotheses are obtained from these original
radial leaves and the full private block equations, with no H force
removed. Its complete shared-only-H nesting proof keeps both true
A3/B3 systems and the real A-to-leaf edge. Every graph/root/load mask
and all low/critical/high radius cases are included. This is its
stated exact C2.34.b2 consequence, with the ninth physical unit kept.

### 4.3. All three arms at A are excluded

In the sole arm A-T-L, A has exactly its two original triangle
forces and the one original arm force, so its true degree is three.
The whole two-edge-arm consequence in
TRIANGLE_SMALL_RADIAL_EXTERNAL_SUPPORT_EXCLUSION.md, Section 6,
applies at arbitrary actual H degree and every real private block
mask. It retains the full T mean and side/diagonal width, the
genuine leaf's S/D choice, and the whole original A external.
No positive force is deleted to turn A into a leaf root.

### 4.4. The page-diamond AH and AK graphs are excluded

For AH, the actual page-rooted diamond retains two true degree-three
hubs P,Q and the other true degree-two page K. Their boundary-
triangle obstruction applies at arbitrary other forces on H.

For AK, both hubs P,Q still have true degree three even though K
now has its genuine leaf and true degree three. The unchanged
unloaded-diamond-hub obstruction forces both hubs physically
boundary. Their actual positive edge PQ has both original positive
common neighbors H,K. BOUNDARY_EDGE_OUTER_FACE_AND_DIAMOND_EXCLUSION.md
forbids two such common neighbors of a boundary edge, with arbitrary
degrees at H,K. K is not treated as a degree-two boundary page.

The only shared non-intact graph domains remaining are therefore:

| Four-block root type | Direct-leaf multisets still open |
| --- | --- |
| C4 | AH,AK,AP |
| Hub diamond | AH,AK,AP |
| Page diamond | AP |

There are exactly seven. The common triangle root H keeps the full
degree in each row, and a decorated private four-block body is never
treated as a terminal private vertex.

## 5. Disjoint blocks: three intact private-leaf graph domains remain

The complete disjoint list in Section 1.2 has five direct-connector
leaf locations and the two-edge connector, for each root type.

The sole non-intact possibility has the direct bridge HK and the
genuine leaf at the private triangle vertex A. Here A3/B2 is the
actual leaf-decorated triangle and the entire four-block is terminal
at K. LEAF_DECORATED_TRIANGLE_DISJOINT_TERMINAL_FOUR_BLOCK_EXCLUSION.md
excludes all three graph/root types and all private load masks.
The full external moment at H is the genuine original bridge moment,
zero by summing the complete original four-block side. Its actual
root K and all eight stressed bodies remain; the source explicitly
includes this two-bridge application with the ninth square present.

For each remaining attachment the triangle at H is intact, hence
O is in int H. If the direct-connector leaf is at H or K, the
four-block's three private degrees are unchanged. The complete
ORIGIN_OCCUPIED_ANY_TERMINAL_FOUR_BLOCK_EXCLUSION.md excludes that
terminal block with the actual outside origin-interior unit E=H.
It permits every real extra root force at K, including the genuine
K leaf in the latter case. The same theorem excludes the entire
two-edge connector H-T-K, since it also leaves the block terminal.

This leaves only a direct connector HK and a genuine leaf at a
private four-block vertex U or V. For a page-rooted diamond, the
leaf at the other page U still leaves both hubs V,W at true degree
three. They are physically boundary and their positive hub edge
has the two original common neighbors K,U. The same arbitrary-
common-neighbor boundary-edge theorem excludes this domain; U's
genuine leaf force is retained.

Before the additional whole central-gap exits in Section 5.1, the
exact disjoint candidate list is:

| Four-block root type | Private genuine leaf location still open |
| --- | --- |
| C4 | U opposite K; or V adjacent K |
| Hub diamond | U the other hub; or V a page |
| Page diamond | V a hub |

All five domains have a distinct actual genuine leaf root J outside
the intact H. Its leaf must be S and d>1: a D leaf puts O openly
inside J, while an S leaf at d<=1 puts O closed in J, both impossible
beside the actual O-interior H. J has its actual epsilon point and
avoids O closed. The intact-root direct-bridge theorem also makes
the actual bridge endpoint K physically clear, without changing
its original degree or identifying J with K.

For the C4 opposite-U row, the accepted
INTACT_PETAL_OPPOSITE_LEAF_C4_PRIVATE_LOAD_REDUCTION.md supplies its
full necessary load conclusion: both other private vertices V,W
are positively loaded. Its outside intact unit is precisely H,
its actual genuine leaf root is U3, and its C4 root K has its real
degree three including HK. The hub-diamond other-hub-U row likewise
has both true degree-two pages loaded directly. These are complete
load restrictions on existing graph domains, not extra closures.

### 5.1. The full central-gap theorem removes both opposite-root domains

INTACT_MIDDLE_TRIANGLE_OPPOSITE_LEAF_FOUR_RING_EXCLUSION.md,
Sections 1, 2.1 and 3.3, now excludes the entire C4 leaf-at-U and
hub-diamond leaf-at-U domains. Its full root and separate independent
source/scope reviews include exactly these two original b2 applications;
the separate review is
REVIEW_INTACT_CENTRAL_GAP_OPPOSITE_LEAF_RING_TRIANGLE_BRIDGES_2026_10_27.md.

Here the actual intact root is H, the actual four-block root is K,
the actual opposite genuine S root is U, and the physical boundary
pages are V,W. Their original positive ring is

    K-V-U-W-K,

with the positive K-U chord additionally retained for the diamond.
The whole C4 private-load reduction just stated proves V,W loaded;
the two degree-two diamond pages are loaded by their actual touching
hub neighbors. No false three-force equation is imposed on the
genuine degree-four diamond hub U.

The actual intact H contains O openly, and U has its genuine point
epsilon*e in D_epsilon. The complete intact-petal/two-near-unit theorem
forces every other actual square, including the ninth arbitrary square,
to avoid that disk. The segment from O to epsilon*e therefore has
a gap between the closed H and U meeting no other body. A zero-length
physical H/U gap is included. The original graph has no positive
H-U edge, and its original H/U applications lie outside the disk.

The theorem inserts only an auxiliary H-U curve through this free
gap, keeping one compatible embedding of the complete original graph
and every physical boundary vertex's protected access to infinity.
The three K-to-U paths then run through H,V,W. An inner V or W
contradicts boundary access. An inner H lies inside the actual ring
and traps its original boundary intact tip A through the retained
positive H-A edge, giving the same contradiction. The real HK bridge,
all diamond forces and all side means stay unchanged.

The true cyclic degrees are H3,K3,U3 for C4 and H3,K4,U4 for the
hub diamond. These are their original eight-body components with the
ninth physical square retained. The new theorem therefore removes
exactly these two whole graph domains, not merely a selected mask.

The three disjoint domains still requiring work are the C4 leaf at
V, the hub-diamond leaf at V, and the page-diamond leaf at V, each
with its distinct actual graph role from Section 1.2.

## 6. Exact current twelve-domain inventory and true degrees

The 66 graph orbits reduce to the following 12. Shared notation is
the one in Section 1.1; disjoint notation is Section 1.2.

| Domain | Four-block type | Bridges | Original affected cyclic degrees |
| --- | --- | --- | --- |
| Shared non-intact | C4 | Leaves at A,H | A3,H5; B,K,P,Q true2 |
| Shared non-intact | C4 | Leaves at A,K | A3,K3,H4; B,P,Q true2 |
| Shared non-intact | C4 | Leaves at A,P | A3,P3,H4; B,K,Q true2 |
| Shared non-intact | Hub diamond | Leaves at A,H | A3,H6; B,P,Q true2; K3 |
| Shared non-intact | Hub diamond | Leaves at A,K | A3,K4,H5; B,P,Q true2 |
| Shared non-intact | Hub diamond | Leaves at A,P | A3,P3,H5; B,Q true2; K3 |
| Shared non-intact | Page diamond | Leaves at A,P | A3,P4,H4; B,K true2; Q3 |
| Shared intact | C4 | H-T-L | H5; A,B,K,P,Q true2; T2,L1 |
| Shared intact | Hub diamond | H-T-L | H6; A,B,P,Q true2; K3; T2,L1 |
| Disjoint intact | C4 | HK and leaf at V | H3,K3,V3; A,B,U,W true2 |
| Disjoint intact | Hub diamond | HK and leaf at V | H3,K4,V3; A,B,W true2; U3 |
| Disjoint intact | Page diamond | HK and leaf at V | H3,K3,V4; A,B,U true2; W3 |

Every direct genuine leaf has degree one. In every row the affected
degree list is the actual list, including the original diamond chord.
No page carrying an extra leaf receives a false degree-two equation,
and no decorated hub receives a false degree-three equation.

Equivalently the retained graph count is

    7 shared non-intact +2 shared intact arms
      +3 disjoint intact private-leaf graphs =12.

The other 54 post-K4 graph orbits have the whole original exits
above. This is a finite graph/attachment remainder, not a claim that
the 12 retained domains are physically realizable. Every residual
mask, mean endpoint, allowed S/D choice and ninth physical square
remains except where a complete necessity was explicitly proved
above. No new parameter-cell subdivision or per-subcase gate ID is
introduced. The entire original C2.34.b2 cell remains open until
all remaining original domains are excluded.
