# Independent review of version-14 whole-cell substitutions

November 2, 2026, America/Chicago. No Lean, Lake or CI.

The reviewer read `A2_00100_FIXED_FRONTIER_PHYSICAL_REVIEW.md`, compared
the complete v14 verifier against v13 after normalizing only the version
tags, and inspected the direct-cell and bounded-cell proof assemblers.
The inherited necessary row formulas are unchanged by this delta.
The new mathematical cases are the accepted correlated-corner row guards
and a unit-center column union. Both preserve the complete original-nine
caller. No critical mathematical or coverage defect was found.

This source review is independent of the producer. The separate portable
`review_v14_cells.py` checks whole-cell inclusion and complete descendant
coverage with the reviewer's own path decoder and trie implementation,
then freshly executes the delivered exact v14 arithmetic verifier on
every new proof leaf. It does not claim a second implementation of the
arithmetic formulas. Its final report determines the exact number of
whole original cells discharged; provisional search counts are not
acceptance evidence.

## 1. The physical-model review is correctly scoped

The caller keeps all nine originals, corners, physical pairs and strict
marked bits. A proof's necessary relaxation may retain only implications
of a particular physical pair until that pair is selected for an explicit
owned-axis branch. This is sound because an exclusion of the relaxation
excludes the complete original caller. It does not justify labeling an
unproved relaxed point as a physical packing.

The reviewed root normalization retains both closed D-sign intervals,
all independent folded original slopes, both extra labels and every
contact face. The two-root union plus the accepted low-gap proof is
the whole `001/00` domain after the stated common reflection. The
whole-witness reversal covers `100/00` as well.

The review's nonconsecutive-cone statement is valid: each successive
original cone pair has horizontal inset gap at least `1/sqrt(2)`, so
two such links give at least `sqrt(2)`, at least the sum of any two
original coordinate halfwidths. Its support formula retains the
nonnegative relative cosine on the whole canonical angle interval.
The original values of all auxiliary product variables satisfy the
McCormick and residual-variable bounds used in a Farkas certificate.

The circle-envelope negative-radicand handling is also valid. If the
lower absolute x bound plus the lower original coordinate halfwidth
already exceeds `sqrt(Q)`, the original's x projection contradicts
circle containment regardless of the y value. The second radicand is
weaker since the lower halfwidth is at least the lower corner offset.
The maximum of the two surviving y-envelope bounds retains the original
corner chirality; no independent sign is silently fixed.

The root review distinguishes a complete covering tree from a complete
exclusion tree, and an open cell from a proof leaf. It does not infer a
whole mask, positional root or roadmap closure from the finite cover.

## 2. Correlated-corner row guards

The new `correlated_row30_escape` and `correlated_row50_escape` nodes
are permitted only when every original in

\[
                    A,D,E,F,G,H,I
\]

has its entire tangent interval inside the specified bound. A tangent
bound `|t|<=eta` implies `|sin(theta)|<=eta`, so it is a conservative
guard for the accepted hand theorem. The precise choices are

| Tangent bound | Allowed total A,H,I,D height variation |
|---|---|
| `1/30` | `11/30` |
| `1/50` | `9/20` |

Original B and C receive no additional angle hypothesis. The existing
extra-strip theorem gives `x_A<x_H<=x_I<x_D`. If H/I have equal x,
unit center distance forces `|y_H-y_I|>=1`, which is incompatible with
either variation guard. Thus the hand theorem's strict horizontal
order follows. The already proved original E/A and G/D orders supply
the two shoulder premises.

The code retains all eight signed expressions whose maximum is

\[
         |y_H-y_A|+|y_I-y_H|+|y_D-y_I|.
\]

Since the whole closed region at or below the threshold is excluded,
at least one signed expression exceeds the threshold in any strict
original counterexample. The verifier uses the weaker closed escape
inequality and the usual closed predecessor complements. This retains
every threshold equality and orientation-zero face.

For a direct analytic row terminal, the code bounds each of the eight
expressions over the complete exact center intervals and takes their
maximum. It accepts only when that upper bound is at most the theorem's
variation threshold. This is a whole-cell implication, not a test of an
LP point. The fixed SHA-256 binds the exact 108-check arithmetic
companion of the accepted continuous hand proof.

## 3. Original-center column unions

Take any ordered list of m distinct original centers, with m equal
to three or four, and either coordinate as the longitudinal coordinate.
Suppose successive longitudinal gaps are positive and the sum of the
absolute transverse gaps is at most `w=3/5`. Write their transverse
absolute gaps as `u_j`, so `u_j>=0` and `sum u_j<=w`.

Each original contains an open disk of radius one half, giving unit
distance between distinct centers. Consequently each positive
longitudinal gap is at least `sqrt(1-u_j^2)`. Put
`f(u)=1-sqrt(1-u^2)`. On `[0,w]`, f is convex and f(0)=0, so

\[
 f(u_j)\le (u_j/w)f(w),\qquad
 \sum_j f(u_j)\le f(w).
\]

Adding the longitudinal lower bounds yields

\[
 \operatorname{span}\ge(m-1)-f(w)
                 =m-2+\sqrt{1-w^2}=m-2+4/5.       \tag{1}
\]

This is a direct pen-and-paper argument over the entire continuous
domain. It requires no common square orientation, selected chain,
pre-existing longitudinal order, or physical separator choice.

For an arbitrary ordered list, its necessary escape union therefore
contains: a failure of one of its `m-1` strict order comparisons; the
span bound (1); or one of the `2^(m-1)` signed transverse variations
at least `3/5`. The respective child counts are

\[
             2+1+4=7,\qquad 3+1+8=12.
\]

The verifier uses exactly these coefficients, retains both coordinate
directions, and retains every equality through closed halfspaces.
It enumerates all 504 ordered triples and 3,024 ordered quadruples of
the nine original labels, with no repeated original in a list.
The 3,528-entry list is a finite source for internal valid inequalities;
it does not add cases to the external 231-cell register.

## 4. Complete original-cell substitution

The direct pass copies a registered original frontier path unchanged,
attaches a proposed proof leaf, serializes the exact format, and accepts
it only after `replay_leaf` succeeds. A numerical contradiction that
fails replay does not change the cell's status.

The bounded pass begins with the same whole original path. Every
descendant extends that exact prefix. It maintains both pending paths
and explicitly unresolved paths; exhaustion of a node/depth/time budget
retains the original cell as OPEN. A cell is closed only when neither
set contains a path, every stored terminal has passed exact replay,
and the descendant trie contains the complete child union at every
internal node. Failed or unfinished trials are not inserted into the
accepted covering forest.

The independent checker binds every supplied cell ID to its original
path hash and exact baseline index, rejects duplicate substitutions,
checks that the prefix is one of the original 231 frontier paths, and
reconstructs every new path independently. It uses its own expected
7/12 child counts for column branches and its own whole-interval angle
guard checks for correlated-row branches. Each new leaf must explicitly
carry the v14 context tag.

After checking each closed cell, the reviewer substitutes its complete
proof into a copy of the original two forests, preserves every unchanged
historical leaf and every remaining original frontier cell, and verifies
the merged complete root unions. Historical proof indices are always
interpreted by their own immutable old verifier. New v14 row indices
are not substituted into an old certificate.

The checker hashes the supplied closure records and exact sources
before and after its run. Its report records the number of complete
original cells removed, the number left, the new exact leaf count,
positive minimum reserve, analytic terminals and full root coverage.
It makes no whole-mask claim while any original path remains OPEN.

## 5. Acceptance limit

This review accepts the new mathematical unions, their guards and
their complete-cell assembly discipline. Final closure counts require
the accompanying successful immutable replay report. Partial descendant
trees, trial-node counts and failed attempts have no effect on the
external register or the 32-mask ledger. The user-requested pen-and-paper
standard is supplied by the printed geometric reductions, complete
finite path cover and explicit rational contradiction tables; no Lean,
Lake or CI was used.

## 6. Final immutable acceptance addendum

The independent checker completed successfully on the final three immutable
closure files. It accepted **53 distinct complete original cells**: 40 by
a direct leaf, 10 by the bounded first pass, and 3 by the focused pass.
The fixed 231-cell register therefore has **178 open cells**. No original
parent is counted twice, and no unfinished internal tree is substituted.

All **210 new leaves** were freshly replayed: 116 positive rational
Farkas contradictions and 94 accepted analytic contradictions. The least
strict rational reserve is exactly

```text
8971750589962478164078650762531352890811/39527199741536211915905594399274195442728960
```

and is positive. The exact source hashes and every accepted original
cell ID are recorded in `v14_whole_cell_independent_replay.json`.

| Closure input | SHA-256 |
|---|---|
| `frontier_whole_cell_closed.json` | `4f3ab65434b3f2cd362c426c4d0c1a88d67d3475b90fb46c2c1ec8a890480d43` |
| `frontier_bounded_cell_closed.json` | `ca04ada8f0e91bf46c535a21d7203647fb5b28cd6252c040c37737a27db371b6` |
| `frontier_focused_cell_closed.json` | `7132a0ecc5e5d0ccab2771b945081312c4554e72e3e6e758905ae7ec90c3abd1` |

The current v14 verifier hash is
`ec1b7de7b15bcc9d89d12087bff974c68e6d056bdaae26b482d514027ec97993`.
All recorded input and verifier hashes were unchanged at the end of replay.

| Merged root | Nodes | Proved leaves | Original cells still open |
|---|---:|---:|---:|
| Negative D sign | 6,996 | 5,087 | 72 |
| Positive D sign | 9,293 | 6,401 | 106 |

The resulting two complete covering trees have 11,488 proved leaves and
178 original frontier paths. Their union still includes every normalized
original-nine caller. This is an accepted reduction of the unchanged
register from 231 open cells to 178; it is not a closure of `001/00`,
`100/00`, a positional root, or any additional entry of the 32-mask ledger.

The arithmetic run used the delivered exact verifier; the independent
parts are source and geometry review, original-cell identity, path
interpretation, ancestor inclusion, complete child unions and proof
assembly. This distinction is intentional. The report does not claim an
independent implementation of every linear row or a proof-assistant check.

The portable command is:

```sh
python review_v14_cells.py --base PACKAGE_DIRECTORY \
  --additional-bounded frontier_focused_cell_closed.json \
  --report v14_whole_cell_independent_replay.json
```

## 7. Independent review of the printed rational tables

The reviewer also wrote `review_v14_printed_tables.py`, which imports
neither the producer nor the bulk verifier nor the producer's table
checker. Its exact rational summation passed for all **116 weighted
leaves and 2,163 printed scalar rows**. The other 94 records retain
their analytic terminal identities and have no weighted rows.

Every record is bound to the same original cell ID, leaf index, full
path and certificate version as the accepted immutable closure inputs.
The checker verifies that every selected multiplier appears exactly
once, every multiplier is a positive integer, the full weighted
coefficient and right-hand-side sums agree, and the residual variable
bounds match the original 18 coordinates, 36 frame/inset variables and
six variables for every selected physical separator. It computes the
same positive minimum reserve independently. The printed dense and
exact-contact support rows additionally pass a direct check of their
original-corner coefficients and the rational Cauchy--Schwarz bound.

The table SHA-256 is
`9013a347271d7721f7cf120161f0a8609896178f5c9c4337653e7568961fdf31`.
The complete result is `v14_printed_tables_independent_review.json`.
Physical validity of the other generic row families and analytic
terminals remains supplied by the reviewed geometric derivations and
exact leaf replay; checking a printed sum is not substituted for that
obligation.

```sh
python review_v14_printed_tables.py --base PACKAGE_DIRECTORY \
  --report v14_printed_tables_independent_review.json
```
