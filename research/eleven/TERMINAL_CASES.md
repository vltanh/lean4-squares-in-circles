# Eleven-square current finite case ledger

**Target:** prove every unrestricted packing has q>=q_c, with q_c defined
in [the exact contact system](CANDIDATE_CONTACT_SYSTEM.md), then classify
all equality packings. All geometric cases allow independent square orientations
and weak contacts. No unresolved case is silently discarded.

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

The generic stress identity is available. G2.4, the global reduced terminal
inventory, remains open. Completing C does not provide the missing O
classification; the old 1105 masks are no longer an outstanding obligation.
