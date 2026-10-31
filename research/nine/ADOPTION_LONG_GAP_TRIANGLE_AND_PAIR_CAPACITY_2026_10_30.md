# Adoption: long-gap domination, the complete three-load cycle bound and pair capacity

Date: October 30, 2026 UTC (October 29, America/Chicago).

Input branch head: `168aadd76f975804b9c698b155554907026a55d6`.

**The entire seven-body simple positive cycle with exactly three loaded
bodies is now excluded.** More generally every entire simple positive
translational-stress cycle with exactly three loaded bodies has at most
six bodies. This is a complete physical family conclusion, for arbitrary
orientations, all physical circle masks and all individual zero circle
coefficients. It does not require torque balance or a common angular and
planar stress selection.

No original coarse parent is closed by this checkpoint. The original fine
and coarse identifier sequences and flags are unchanged: **2373/2513 fine
checked, 140 open; 36/58 coarse closed, 22 open**. The existing checked fine
entry for the three-load seven-cycle previously recorded its reduction to
one open run pattern; its explanation now records the complete exclusion.
No new checklist item is added to increase those counts.

## 1. The geometric theorem that closes the family

Write Q=1105/256. For any actual unit squares A,B in the disk D_sqrt(Q),
an actual support gap at least two implies that the open radius-3/2
neighborhoods of A and B cover the complete possible-center disk
|z|<=91/60. Therefore, for every other actual unit square C,

    dist(A,B)>=2  implies  dist(A,C)<1 or dist(B,C)<1.

This is a theorem about the actual occupied squares, without equilibrium
assumptions. The complete covering proof retains the endpoint tilts and
couples their transverse heights through their actual outer corners.
It includes the closed radius Q and weak gap two; the conclusion is strict.

On a genuine path of unloaded true-positive-degree-two bodies,
translational force balance alone gives a common signed normal and the
exact identity

    n.(c_V-c_U)=h_U(n)+h_V(n)+2*sum_internal h_i(n).

Thus three genuine paths between distinct retained A,B,C, with respective
internal counts at least 2,1,1, contradict the geometric theorem. All other
endpoint forces are retained; endpoint degrees and loads are unrestricted.
No suppression changes the physical packing or replaces a full star by a
two-force equation.

For an entire simple cycle with three loaded bodies, each unloaded run has
at most two bodies. The existing long-endpoint matching theorem permits
at most one run of size two. Seven bodies would therefore require exactly
(2,1,1), now excluded. Eight and nine were already excluded by matching;
the new argument supplies one uniform bound of six and closes the former
seven-body remainder.

Complete sources:

- TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md
- TRANSLATIONAL_LONG_CHANNEL_DOMINATING_PAIR_AND_THREE_LOAD_CYCLE_BOUND_2026_10_30.md

The first has complete root and separate block_ears reviews. The second
has a complete independent block_ears review; root also reconstructed its
force-only identity, geometric domination and exhaustive cycle join.

## 2. Pair-dependent completion capacity, with stagger retained

A near-central actual horizontal pair, with center abscissas s+/-1/2 and
both center heights and |s| at most 1/12, allows at most four extras whose
two absolute own-center coordinates are at most 1-d, where d is the larger
absolute pair height. The pair heights need not coincide.

The proof uses the rectangle genuinely covered by the two actual squares,
an exact separating-axis routing, and a continuous angular-capacity bound
on the radius-5/4 test circle. It does not replace a staggered union by its
convex hull. Hence any nine-square packing with the stated pair must have
at least three extras outside that own-coordinate class. Extracting such
a pair and controlling those remaining extras are still caller obligations.

The all-radii diagnostic shows why that pair information matters. At the
strictly smaller squared radius 17/4, an integral list of nine individual
profiles, 2A+2S+5B, passes every concentric-circle occupation inequality at
once and has exactly two near profiles. This is not a disjoint packing.
If its two A profiles were actually realized disjointly, they would form
the central pair and the five B profiles would violate the new capacity.

Complete sources:

- NEAR_CENTRAL_DOMINO_FOUR_NONPOLAR_COMPLETION_CAPACITY_2026_10_30.md
- STAGGERED_CENTRAL_PAIR_FOUR_NONPOLAR_COMPLETION_CAPACITY_2026_10_30.md
- ALL_RADII_NINE_PROFILE_OBSTRUCTION_AND_PAIR_DEPENDENCE_2026_10_30.md

Their complete root reviews include the direct old additive-measure input,
the entire continuous delta interval, every separator equality and the
literal staggered-pair join.

## 3. Two force-free inputs for a later two-channel theorem

Four actual unit squares meeting at p form one aligned two-by-two block.
If both coordinates of p in that frame have absolute value at most 1/60,
the total packing has at most eight squares. The incircle clearance from
the actual block places every other center in one of four narrow caps,
each of diameter less than one. The result allows arbitrary orientations
of every completing square.

Independently, any actual square with c.n>=89/60 has its entire outward
center ray free of every other closed square. The proof uses only actual
square circumradii, the center bound and the incircle separation. Both
ends of a gap-two pair satisfy this condition in their outward directions,
whether or not they carry a circle load. Each spoke deviates from its
center direction by less than fifteen degrees.

Complete sources:

- NEAR_CENTRAL_FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_2026_10_30.md
- NEAR_ANTIPODAL_ENDPOINTS_HAVE_PROTECTED_OUTWARD_RAYS_2026_10_30.md

Both have complete root and separate axial_chain reviews. This checkpoint
does not yet adopt a theorem that two long paths must meet at a near-central
junction. Crossing, the four-square contact and its exact location require
a separate complete assembly. The eight-square example at squared radius
17/4 is retained as a sharpness check.

## 4. General long-ear obstruction and a necessary large-block distinction

A genuine path with k unloaded true-degree-two internal bodies and any
physical return walk of l edges obey k+1<=l*sqrt(2). In particular a long
path with two internal bodies has no return of at most two physical edges.
The inequality is radius-free and uses no endpoint truncation.

An explicit seven-body biconnected core at squared radius 13/4 has full
positive force and torque balance but no two consecutive unloaded degree-two
bodies. Its exact original contacts and weights are supplied. It cannot
accept even an eighth arbitrary unit in the target disk, by a separate
center-capacity argument. This demonstrates why a bare large-block theorem
must retain the actual completion units or a stronger radius hypothesis.
The example lies below the research lower window; no contrary assertion
is made about a theorem using that additional window.

The complete source is
LARGE_BLOCK_LONG_EAR_OBSTRUCTION_AND_SUBCRITICAL_SEVEN_CORE_2026_10_30.md,
with a complete root review of every actual contact, force, torque and
completion inequality.

The prior head's exact four-square axial-chain estimate is also now fully
independently reviewed and adopted at its stated scope. It controls center
abscissas, endpoint heights and angular width excess; it does not assert a
solid row or equal center heights.

## 5. Exact frozen mathematical sources

| Source | SHA256 |
| --- | --- |
| TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` |
| TRANSLATIONAL_LONG_CHANNEL_DOMINATING_PAIR_AND_THREE_LOAD_CYCLE_BOUND_2026_10_30.md | `5b3c31c3aae5afc91cb2bbba0cabfdd9fcb6ff9f7893b5bd8673f43852a471b0` |
| NEAR_CENTRAL_DOMINO_FOUR_NONPOLAR_COMPLETION_CAPACITY_2026_10_30.md | `33168fb5ab4605739746348d1425b47da33c6f2a64803357f1f0608515a160b8` |
| STAGGERED_CENTRAL_PAIR_FOUR_NONPOLAR_COMPLETION_CAPACITY_2026_10_30.md | `8cce720d62d361f02912c49962d0da51aac4de382ac2294defc2f67e313ed98f` |
| ALL_RADII_NINE_PROFILE_OBSTRUCTION_AND_PAIR_DEPENDENCE_2026_10_30.md | `001070964ef60f1ff93852fbee25ea45439f48757ed7a8d390a2968c5d557a3c` |
| LARGE_BLOCK_LONG_EAR_OBSTRUCTION_AND_SUBCRITICAL_SEVEN_CORE_2026_10_30.md | `c2206265e00022a2b3fab3523ea5dd9ed5e258d80c49baece4e6f10d4e352b16` |
| NEAR_CENTRAL_FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_2026_10_30.md | `f9f2e43ce31d3275d0f111b1ef8b48592607cc03920c3610ef8fefcff9b7bda0` |
| NEAR_ANTIPODAL_ENDPOINTS_HAVE_PROTECTED_OUTWARD_RAYS_2026_10_30.md | `82ff38f0d73045652c517a10f70f86d93bc0d55d540f3b67c99b04896cc049de` |
| UNIFORM_FOUR_SQUARE_AXIAL_CHAIN_NEAR_DIAMETER_2026_10_30.md (unchanged input) | `a37aa0c0fa430c48754cbae49e2c945556cc0635d971e085426a40a261ad0013` |

## 6. Complete review records

- REVIEW_EXPANDED_ENDPOINT_COVER_AND_COMPLETE_THREE_LOAD_SEVEN_CYCLE_BLOCK_EARS_2026_10_30.md
- REVIEW_EXPANDED_ENDPOINT_COVER_AND_CHANNEL_TRIANGLE_ROOT_2026_10_30.md
- REVIEW_TRANSLATIONAL_LONG_GAP_DOMINATION_AND_THREE_LOAD_BOUND_BLOCK_EARS_2026_10_30.md
- REVIEW_PAIR_CAPACITY_AND_LARGE_BLOCK_DIAGNOSTICS_ROOT_2026_10_30.md
- REVIEW_STAGGERED_PAIR_NEAR_JUNCTION_AND_PROTECTED_RAYS_ROOT_2026_10_30.md
- REVIEW_PROTECTED_OUTWARD_RAYS_AND_NEAR_CENTRAL_JUNCTION_CAPACITY_AXIAL_INDEPENDENT_2026_10_30.md
- REVIEW_UNIFORM_FOUR_SQUARE_AXIAL_CHAIN_NEAR_DIAMETER_AXIAL_INDEPENDENT_2026_10_30.md

The exact checkpoint is
LONG_GAP_TRIANGLE_AND_PAIR_CAPACITY_CHECKPOINT_2026_10_30.json. It records
the file identities, rational comparisons and original-inventory checks.
The counts are bookkeeping for original entries, not a percentage proof
of the unrestricted theorem.

## 7. Remaining obligations

All 22 original coarse cells, the full unrestricted lower bound, equality
classification and G4.2.c remain open. The seven-body four-load cycle
includes the sharp record's opposite long/short orbit and cannot be
excluded indiscriminately. Other load counts, chorded blocks, articulation
attachments and the actual remaining completion units retain their full
obligations. No common angular/planar selection claim is used to strengthen
the new force-only theorem.

No Lean/Lake compilation, CI/workflow dispatch, numerical pose search,
mesh, new packing certificate or merge accompanies this hand-proof
checkpoint. The branch remains a draft.
