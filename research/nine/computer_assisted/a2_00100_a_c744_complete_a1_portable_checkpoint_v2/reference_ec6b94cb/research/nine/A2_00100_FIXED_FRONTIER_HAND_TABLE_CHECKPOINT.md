# Original-nine `001/00`: certified cover, 53 whole cells closed, 178 open

November 3, 2026, UTC. Computer-assisted discovery, exact rational replay,
and a geometric finite-table argument. No Lean, Lake, or CI.

**The entire `001/00` mask and its reversal `100/00` remain OPEN.** This
checkpoint establishes the previously missing finite full-domain cover
and excludes 53 of its 231 fixed remaining cells. It changes no whole-mask,
original positional-root, or roadmap-gate status. The global ledger is
still **8 of 32 masks closed; 24 OPEN**.

## 1. Accepted result and fixed accounting

The starting predicate is exactly `D_001/00^lt` in Sections 2–3 of
[the coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md): nine physical
unit squares with independent frames, all 36 corners strictly inside the
disk of squared radius `Q=1105/256`, all 36 physical pair constraints,
five marked center-cone comparisons, actual AB, BC, EF, FG links, and the
original strict weak CD comparison. No placement or orientation condition
is silently added to that predicate.

The accepted [low-gap assembly](WEAK_OUTER_LOW_GAP_HAND_TABLE_ASSEMBLY.md)
excludes `|y_D-y_C|<=2/3`. On its complement a common vertical reflection
gives `y_D-y_C>2/3`. Interchange the two unselected labels to arrange
`x_H<=x_I`. These operations preserve every original square and constraint.

The two complete version-13 forests now adopted cover this entire
normalized complement. They contain 11,278 proved terminal leaves and
231 unresolved cells. The independent path/trie audit and fresh exact
replay establish this coverage; it is not inferred from a producer's
reported counts. The retained common faces make this a finite cover,
not a claim of disjoint sets of physical packings.

| Normalized root | Baseline proved leaves | Fixed unresolved cells at adoption | Whole cells closed here | Cells still OPEN |
|---|---:|---:|---:|---:|
| `tan(theta_D) in [0,1]` | 6,318 | 130 | 24 | 106 |
| `tan(theta_D) in [-1,0]` | 4,960 | 101 | 29 | 72 |
| Total | **11,278** | **231** | **53** | **178** |

The [fixed register](gates/A2_00100_FIXED_FRONTIER.json) preserves all 231
original paths and stable IDs. An ID consists of the sign-root name and
the first 16 hexadecimal characters of SHA-256 of the compact JSON path.
The full path is retained, so identity does not depend on an unchecked
short-hash assumption. Each predicate means the full original physical
caller, its normalization and sign root, and every decoded path condition.
The frozen version-specific decoders and the physical review specify
those conditions exactly.

| Discovery pass | Entire original cells excluded | New proof leaves |
|---|---:|---:|
| Direct exact contradiction, no further split | 40 | 40 |
| Bounded search on all other 191 original cells | 10 | 76 |
| One larger trial on six named remaining cells | 3 | 94 |
| Accepted union | **53** | **210** |

The three accepted lists have no duplicate original-cell IDs. A timed-out
or unfinished internal search leaves its original parent OPEN. Its children
do not replace that parent in the 231-cell register. The final merged
forests have 11,488 proved leaves and exactly 178 unresolved original cells.
This is finite case accounting, with no claim about the fraction of
mathematical effort still required.

## 2. Why the cover is exhaustive

Represent the unchanged side frame of each square by

    u_i=(alpha_i,beta_i), v_i=(-beta_i,alpha_i),
    alpha_i>0, |beta_i|<=alpha_i,
    alpha_i^2+beta_i^2=1, t_i=beta_i/alpha_i in [-1,1].

A quarter-turn-equivalent side frame always has this form. Both D-sign
roots retain `t_D=0`; every other tangent has its full interval `[-1,1]`.
Every center coordinate lies in `[-91/60,91/60]`. Indeed the largest corner
norm squared is at least `|c_i|^2+|c_i|+1/2`, and substituting `91/60`
exceeds Q by `31/57600`.

Every internal node has one of the reviewed exhaustive child unions:
closed angle or center cuts; four signed original-inset separations;
eight owner/axis/sign choices for a physical separating axis; or the
complete escape union of an already proved analytic terminal. Equality
faces are included. For a first-satisfied escape, all predecessor
complements are retained with their closed boundaries.

The independent checker reconstructs a trie from the paths, checks both
root prefixes, and rejects a missing child, duplicate terminal, or
terminal which is an ancestor of another terminal. It independently
decodes the splits and compares each old leaf with its own historical
verifier. Thus a finite induction from the roots covers every normalized
physical caller by either a proved leaf or one of the fixed 231 paths.

The subsequent cell substitutions are checked separately. For each of the
53 original paths, all its new descendants have that prefix and form a
complete subtree. Every new terminal closes. Replacing those 53 paths
therefore preserves the two root covers and leaves precisely the other
178 original paths. The independent merged-root check gives:

| Final forest | Nodes | Proved terminal leaves | OPEN original cells |
|---|---:|---:|---:|
| Positive D root | 9,293 | 6,401 | 106 |
| Negative D root | 6,996 | 5,087 | 72 |

See the [independent baseline coverage review](A2_00100_V13_COVERAGE_INDEPENDENT_REVIEW.md)
and [independent whole-cell substitution review](A2_00100_V14_CELL_SUBSTITUTION_INDEPENDENT_REVIEW.md).
Their scope includes every retained split face; they do not establish
impossibility of an OPEN cell.

## 3. The exact hand/table implication at a proved leaf

The [physical source review](A2_00100_FIXED_FRONTIER_PHYSICAL_REVIEW.md)
connects each numerical row and analytic escape to the same original
squares. Original cosine, sine, corner and separating-axis variables are
shared across the constraints. Auxiliary product variables can be assigned
their actual physical values and satisfy their enclosing inequalities.
No independent pairwise choice of an original square's orientation is made.

For a weighted leaf, the finite table supplies valid rational rows

    a_j dot z <= b_j,

nonnegative rational weights `lambda_j=w_j/2^40`, and valid bounds
`|z_k|<=M_k`. Compute

    r_k = sum_j lambda_j a_jk,
    B = sum_j lambda_j b_j,
    reserve = -B - sum_k M_k |r_k|.

Every such leaf has `reserve>0`. Summing the rows gives `r dot z<=B`,
while the coordinate bounds give

    r dot z >= -sum_k M_k |r_k| > B,

the required contradiction. This argument allows a nonzero residual
coefficient vector; no approximate cancellation or optimizer tolerance
is accepted as a proof.

The printed new tables contain **116 weighted leaves and 2,163 explicit
rational rows**. All nonzero weighted rows, variable bounds, sums and
reserves are supplied in `whole_cell_rational_tables.json` inside the
archive. The remaining 94 new leaves use reviewed exact sign exclusions
or empty propagated intervals. They are identified explicitly rather
than assigned artificial weighted reserves.

The least new weighted reserve is

    8971750589962478164078650762531352890811
    / 39527199741536211915905594399274195442728960 > 0.

`check_cell_tables.py` checks the printed sums with standard-library
rational arithmetic and does not call an optimizer. A separate replay
regenerates every leaf's rows from its physical path and frozen source.
Historical leaves keep their original v9–v13 interpretation; their row
indices are never reinterpreted under the v14 row list.

The v14 mathematical additions are the already proved correlated-corner
row terminal and the original-center column union. Their guards are
checked at each use. The correlated row uses all seven relevant original
frames, without restricting B or C. The column inequality follows from
unit center distances: an ordered chain of m centers with transverse
total variation at most w<1 has longitudinal span at least
`m-2+sqrt(1-w^2)`. Convexity of `1-sqrt(1-u^2)` bounds the sum of its
adjacent losses. At `w=3/5`, all order, span and signed-variation children
are retained. Neither addition imposes an unproved placement restriction.

The strict CD bit remains part of every original caller. Analytic row
terminals may use it to exclude an equality configuration of a necessary
closed relaxation. The known aligned closed-Q boundary control is not
claimed to have a positive infeasibility margin.

## 4. Verification and preserved evidence

The [source-bound manifest](computer_assisted/a2_00100_fixed_frontier_manifest.json)
identifies the archive, exact forests, frozen verifier dependencies,
printed rational tables, fixed register, reports and reviews. The
[portable archive](computer_assisted/a2_00100_fixed_frontier_checkpoint.tar.gz)
contains the full baseline and final forests and complete new-cell proofs.

The accepted checks are:

1. Fresh root replay of every old positive-root leaf (6,318) and every old
   negative-root leaf (4,960), including complete root coverage.
2. An independently implemented path/trie and guard audit of both baseline
   covers and all 231 unresolved paths.
3. Independent whole-cell prefix and complete-child-union checks for all
   53 substitutions, followed by fresh exact replay of all 210 new leaves
   and both merged-root coverage checks.
4. Separate arithmetic replay of all printed new weighted rows and sums.
5. Six rejected damaged controls: missing root child, missing cell child,
   corrupt branch label, multiplier, reported reserve, and printed row.

The independent substitution reviewer uses the delivered exact verifier
for leaf arithmetic; it independently implements the coverage/substitution
logic. The printed-sum checker is a separate arithmetic implementation.
These are internal source and mathematical reviews, with no claim of
human or proof-kernel verification.

After extracting the archive, its README gives the portable commands:

```sh
python verify_payload.py --check-manifest
python check_cell_tables.py whole_cell_rational_tables.json
python check_payload_controls.py
```

The first command checks all new leaves and substitutions, hashes and
retention of the baseline leaves. Adding `--full` also repeats all old
leaf arithmetic. The delivered fresh baseline reports already cover that
arithmetic; an unchanged-byte report is never represented as a fresh replay.

## 5. A rigorous obstruction to a smaller proposed proof

The new [selected-seven obstruction theorem](SEVEN_ORIGINAL_ALL_OPEN_MASKS_OBSTRUCTION.md)
gives exact rational physical configurations for **all 24 currently OPEN
mask patterns** when only the seven selected originals A–G are required.
Fourteen representatives and exact whole-witness reversal cover the 24
patterns. Every original corner, all 21 selected physical pairs, all five
cone comparisons and the exact marked bits are checked at

    q=17/4 < Q, with Q-17/4=17/256.

The separate standard-library checker and root replay pass all 882
recorded checks. Thus no contradiction using only that seven-original
physical predicate can close any of those masks. Additional information
involving an omitted original, or an independently proved stronger
global selection hypothesis, is required. This does not assert that each
omitted original is individually indispensable, and supplies no
nine-square counterexample.

## 6. Exact remaining obligation

The 178 OPEN rows in the fixed register are the unresolved full-domain
cells. Their complete paths, sign roots and physical caller specify what
must still be excluded. The present exact inequalities fail to exclude
the entire domains of those rows. A feasible linear relaxation or a
numerical local search result is not a physical packing and does not
settle them.

A subsequent [full-matrix direct pass](A2_00100_FULL_MATRIX_CONTINUATION_OBSTRUCTION.md)
tested all 178 surviving original cells with every frozen v14 corner
support row, including the 128 rational directions omitted by the sparse
discovery accelerator. It imposed no new guard or split. It found zero
additional entire-cell exclusions; all 178 cells returned relaxed center
proposals. Thus adding those support directions alone did not close the
remaining domains. This negative discovery result changes no certificate
or cell status in the accepted package.

Further work must close a named original OPEN cell by a complete proof,
close another original full mask, or prove a global terminal-extraction
theorem. A new internal subdivision is allowed as a proof method; an
unfinished subtree keeps its original cell OPEN. No mandatory gate is
created by that subdivision.

Whole-witness reversal replaces `(e,f)` by `(-e,-f)`, reverses both chains,
and retains all nine original squares. It sends `abc/de` to `cba/ed` and
in particular `001/00` to `100/00`. A complete proof of either entire
predicate would therefore close both. The present nonempty frontier does
not provide that complete proof.

## Required handoff footer

| Field | Evidence and current status |
|---|---|
| Whole-mask target | Exact strict original-nine `001/00`; `100/00` by the proved whole-witness reversal |
| Full-mask cover | Certified: accepted low-gap theorem, common reflection, both closed D-sign roots, complete finite path covers |
| Uncovered fixed frontier | 231 original cells at adoption; 53 closed here; **178 OPEN** |
| Closed terminals | All stable IDs, full predicates, 210 exact leaves, complete subtree unions and independent replay in the manifest/register |
| Still open | Exactly the 178 OPEN original paths; entire-mask exclusion remains unproved |
| Whole-mask ledger | **8 CLOSED / 24 OPEN**, unchanged |
| Positional ledger | **5,838 historical closed-Q exclusions / 2,077 OPEN**, same 7,915 IDs; root 7820 preserved |
| Roadmap and equality | Same 15 IDs; A.2, unrestricted lower bound, global equality and manuscript OPEN |
| Restrictions | Computer-assisted discovery/replay; geometric hand/table argument; **no Lean, Lake, or CI** |
