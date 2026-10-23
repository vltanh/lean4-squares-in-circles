# Eleven-square current finite case ledger

**Target:** prove every unrestricted packing has q>=q_c, with q_c defined
in [the exact contact system](CANDIDATE_CONTACT_SYSTEM.md), then classify
all equality packings. All cases below allow independent square orientations
and weak contacts. No unresolved case is silently discarded.

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

## Nine open coordinate profile families

Let A=(3,3,3,2), B=(4,3,2,2), and C=(4,3,3,1) be unordered rank occupancy
profiles. The names below group masks for review only. Sorting a profile
does not authorize permuting geometric rank rows or columns. Each family
retains every directed mask listed in the machine-readable inventory.

| ID | Row profile | Column profile | Masks | Sharp bound | Equality |
| --- | --- | --- | ---: | --- | --- |
| C-AA | A | A | 135 | OPEN | OPEN |
| C-AB | A | B | 180 | OPEN | OPEN |
| C-AC | A | C | 105 | OPEN | OPEN |
| C-BA | B | A | 180 | OPEN | OPEN |
| C-BB | B | B | 200 | OPEN | OPEN |
| C-BC | B | C | 80 | OPEN | OPEN |
| C-CA | C | A | 105 | OPEN | OPEN |
| C-CB | C | B | 80 | OPEN | OPEN |
| C-CC | C | C | 40 | OPEN | OPEN |
| Total | | | 1105 | OPEN | OPEN |

The counts are independently reproduced and emitted by
`classify_rank_masks.py`. These are numbers of necessary masks after the
listed exclusions, not numbers of realizable geometric or symmetry classes.

## Next proof obligations in order

1. **C-CC extraction and sharp inequality.** Start with the smallest listed
   family, retaining all 40 masks. Use its two three-chains and four-chain
   structure to derive an actual endpoint or support terminal. Prove the
   extraction on the complete domain before treating one contact sketch as
   representative. If the proposed terminal fails, keep its exact witness.
2. **C remaining eight families.** Reuse a theorem only with proved
   hypotheses. Record a complete mask-to-terminal cover and all equality
   residues; each unresolved mask blocks the common-coordinate theorem.
3. **O geometric extraction.** Derive a finite realizable owner/contact
   structure or a universal sharp invariant from arbitrary Packing. Any
   minimizer-core reduction must retain all unstressed completions. The
   known construction already requires an oblique branch; this is essential
   for the global problem even if every C case is solved.
4. **G4–G6 assembly.** Prove all-angle certificates at q_c, then combine
   complete coverage with exact attainment and recover equality on original
   centers. Local isolation of the constructed contact root is not a
   substitute for any of these steps.

The generic stress identity is available for discovery and proof, but no
choice of weights uniformly certifying q>=q_c for these residual domains
is currently provided. G2.4, the global reduced terminal inventory, remains
open even though the raw finite cover and the conditional C inventory are
complete as stated.
