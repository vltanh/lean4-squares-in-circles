# Eleven-square current finite case ledger

**Target:** prove every unrestricted packing has q>=q_c, with q_c defined
in [the exact contact system](CANDIDATE_CONTACT_SYSTEM.md), then classify
all equality packings. All geometric cases allow independent square orientations
and weak contacts. No unresolved case is silently discarded.

The [universal lower bound](arc_budget/UNIVERSAL_LOWER_BOUND.md) gives
q>9/2 for every packing. Together with the construction, every minimizer
lies in 9/2<q<=q_c<U.

**Current closure:** the entire C branch is impossible at q<=U, by
[coordinate shrinking](COORDINATE_SHRINKING_REDUCTION.md) and the
[six-case axis exclusion](AXIS_ALIGNED_EXCLUSION.md). All 1105 historical
rank masks below are closed; the global oblique branch O remains open.

## The universal split

For a physical packing at q<=U=49013/10000, either there exists a common
orthonormal frame in which every pair separates on a coordinate projection,
or there is no such frame. Call these branches C and O. The split is
exhaustive by definition; it is not an extraction of useful oblique terminals.

For C, choose such a frame and compute the two full projection-order ranks
as in [the rank proof](COORDINATE_RANK_CASES.md). Its labeled rank mask is
one of the 1105 entries of `RANK_MASKS.json`. For an entry M, the exact
geometric domain is: physical Packing at q<=U, a chosen common separating
frame, and the image of the actual two longest-chain rank maps exactly M.
This retains the centers, orientations and all pairwise constraints. A mask
alone does not define a feasible packing.

For O, retain the 55 signed pair-owned separators of
[the raw cover](FINITE_SEPARATOR_COVER.md). The orientation-sorted 8^55
quadratic cells cover this branch too, but they have not been reduced to a
useful sharp terminal list. Coordinate-profile statements may not be used
inside O without proving a common-frame hypothesis for the relevant subset.

## Closed exclusion families

| ID | Hypotheses in branch C | Closed result |
| --- | --- | --- |
| C-L5 | A five-square common-direction projection chain | Cannot fit in q<=U |
| C-E44 | Some square has rank pair (4,4) | Contradicts the unconditional center bound already at q<=5 |
| C-D44 | Two vertex-disjoint four-chains in the same projection direction | q>=5; hence excluded at q<=U |
| C-S44 | Both first rank row and first rank column are full | Shared chain-start square violates the center bound |

C-D44 excludes all (3,4) and (4,3) rank grids, and every square-grid mask
with two full rows or columns. These are proved families, not sampled cases.

## Nine historical coordinate profile families now excluded

Let A=(3,3,3,2), B=(4,3,2,2), and C=(4,3,3,1) be unordered rank occupancy
profiles. The names below group masks for review only. Sorting a profile
does not authorize permuting geometric rank rows or columns. Each family
retains every directed mask listed in the machine-readable inventory.

| ID | Row profile | Column profile | Masks | Status at q<=U | Equality at q_c |
| --- | --- | --- | ---: | --- | --- |
| C-AA | A | A | 135 | EXCLUDED | NONE |
| C-AB | A | B | 180 | EXCLUDED | NONE |
| C-AC | A | C | 105 | EXCLUDED | NONE |
| C-BA | B | A | 180 | EXCLUDED | NONE |
| C-BB | B | B | 200 | EXCLUDED | NONE |
| C-BC | B | C | 80 | EXCLUDED | NONE |
| C-CA | C | A | 105 | EXCLUDED | NONE |
| C-CB | C | B | 80 | EXCLUDED | NONE |
| C-CC | C | C | 40 | EXCLUDED | NONE |
| Total | | | 1105 | EXCLUDED | NONE |

The counts are independently reproduced and emitted by
`classify_rank_masks.py`. These are numbers of necessary masks after the
listed exclusions, not numbers of realizable geometric or symmetry classes.

## Exhaustive oblique radial classes

[The refined radial extraction](CORE_RING_TWO_CASES.md) proves the following cover.
Core means center norm below 41/40; ring is its complement.
This threshold supersedes the earlier five-row bookkeeping partition.
For compactness use the overlapping closed threshold cover in that note.
Every core square has no circle contact. Ring arcs give a cyclic order.
Every row retains all eleven centers and frames and all 55 pair constraints.

| ID | Core | Ring | Sharp terminal status | Equality status |
| --- | ---: | ---: | --- | --- |
| O-3 | 3 | 8 | OPEN | Known candidate occurs here; global exhaustion open |
| O-4 | 4 | 7 | OPEN; all seven outer centers >11/10 | OPEN |
| O-5 | 5 | 6 | EXCLUDED by weighted occupied-circle measure | NONE |
| O-6 | 6 | 5 | EXCLUDED by the five-center theorem | NONE |

An actual packing determines one row, a ring cyclic order, and physical
separator data. This is an exhaustive coarse classification. Each row still
contains continuous geometric domains requiring sharp certificates.

## Minimizer contact supports

At an unrestricted minimizer, [sparse stress extraction](SPARSE_MINIMIZER_STRESS.md)
gives a connected positive contact component on k=4 through 11 bodies.
This component can contain both radial core and ring squares. Its circle
weights lie only on ring squares. All other bodies remain a physical
completion. Fixed-frame stresses use at most 2k+1 positive terms; a separate
full-angle stress uses at most 3k support-vertex atoms. The multipliers are
bounded and closed chart domains are specified.

All one-, two-, and three-body positive components are excluded. The
[small-graph exclusion](CLOSED_STRESS_GRAPH_FAMILIES.md) additionally rules
out every four-body full-angle component: stars and four-cycles have smaller
enclosing disks, and every four-path has unloaded internal bodies by the
[leaf-neighbor theorem](LEAF_NEIGHBOR_UNLOADED.md). Therefore full-angle
components have k=5 through 11; fixed-frame-only extraction retains k=4
through 11. Spanning physical contact stars are excluded for every k. The
remaining support counts are necessary restrictions, not solved sharp
terminals. Every omitted square remains a physical completion.

## Closed candidate terminals

- **F:** Fix the exact candidate frames and the fourteen selected separators.
  Arbitrary centers in this class satisfy q>=q_c by
  [positive stress](FIXED_ORIENTATION_STRESS.md); physical equality is exactly
  the known sliding family.
- **A:** Keep the three orientation groups and fourteen signed separators;
  both group angles vary throughout the full closed square `[0,pi/2]^2`.
  The [full angle-class theorem](FULL_GROUP_ANGLE_CLASS.md) gives q>=q_c
  for arbitrary centers and exactly the known slider equality family.
  Its 507 closed rectangles cover both angle orders and all endpoint ties.
- **L:** In some neighborhood of the whole candidate family, with arbitrary
  independent orientations and physical owner switches,
  [local sharpness and equality](LOCAL_OPTIMALITY.md) hold.

These are proved terminal theorems. Their hypotheses are not derived for every
packing in branch O; the complement of L still requires classification.

## Next proof obligations in order

1. **O geometric extraction.** Derive a finite realizable owner/contact
   structure or a universal sharp invariant from arbitrary Packing in the
   window. All such packings are now known to lack a common separating frame.
   Every minimizer-core reduction must retain all unstressed completions.
2. **O whole-domain sharp certificates.** For every extracted class, prove
   q>=q_c uniformly in its independent orientations and continuous center
   domain. A local or fixed-orientation theorem is only a conditional terminal.
3. **G5–G6 assembly.** Combine exhaustive coverage with exact attainment,
   then recover all equality cases on original centers. The known slider
   family is not yet globally exhaustive.

The generic stress identity is available. G2.4.a radial extraction is closed; the sharp reduced terminal
inventory G2.4.b–c remains open. Completing C does not provide the missing O
classification; the old 1105 masks are no longer an outstanding obligation.
