# Exact transfers between the remaining fixed masks

This note records consequences of already accepted physical theorems. It
changes no fixed predicate, closure register, or numerical model. The masks
retain all nine original squares, every physical corner and pair constraint,
the five center-cone links, and their original strict/weak bit convention.

## 1. What a complete 001/00 proof would transfer immediately

The accepted simultaneous chain reversal sends

\[
abc/de\longleftrightarrow cba/ed.
\]

Reverse the original four-chain and three-chain labels and both vectors of
the orthonormal witness frame. Each directed horizontal gap, support
halfwidth, center-cone comparison, exact bit, physical pair, and corner norm
then has its corresponding original value. The squared radius and all strict
inequalities are preserved. Consequently a complete strict-radius proof of
`001/00` also proves `100/00` by this explicit transfer.

There is no analogous implication from `001/00` to `011/00`: actual BC and
strictly weak BC are different predicates. Nor does the `001/00` proof supply
an actual EF or FG link when a short-chain bit is one. Changing the witness
direction alone can change cones and bits. Changing the entire configuration
and its frame by an isometry preserves them and gives no new mask beyond
the explicit relabelings already justified.

The present 24 OPEN masks form 14 reversal classes. This is a way to share
proof work, not a new closure count.

| Class representative | Reversal partner |
|---|---|
| 001/00 | 100/00 |
| 001/01 | 100/10 |
| 001/10 | 100/01 |
| 001/11 | 100/11 |
| 011/00 | 110/00 |
| 011/01 | 110/10 |
| 011/10 | 110/01 |
| 011/11 | 110/11 |
| 101/00 | itself |
| 101/01 | 101/10 |
| 101/11 | itself |
| 111/00 | itself |
| 111/01 | 111/10 |
| 111/11 | itself |

Once both members of the first class are discharged, 22 masks in 13 reversal
classes remain unless an additional complete theorem has been established.
This note does not assert that the first class is already closed.

## 2. A direct original-row specialization for every short-00 mask

The accepted *Opposite endpoint tilts: a full-angle four-square row terminal*,
Sections 1–6, is a geometric theorem about seven distinct physical original
squares. Its four-row links need not be actual projections or selected
center-cone edges. Its assumptions are weak horizontal row order, opposite
canonical endpoint angle signs, total row height variation at most 23/100,
and an actual short three-chain. It proves squared containing radius at least
\(Q=1105/256\). At equality all seven frames align and each of the three
row horizontal gaps is one.

Apply that theorem with the literal original row

\[
(A,H,I,D)_{\mathrm{theorem}}=(A,B,C,D)_{\mathrm{caller}},
\]

and retain the same E,F,G. These seven labels are distinct. The original
main center-cone links imply

\[
x_A\le x_B\le x_C\le x_D.
\]

No actual main projection edge is needed for these inequalities. In fact the
physical incircles and each center cone make its horizontal gap positive,
but the theorem already includes the weak-order faces.

Write the actual canonical signed endpoint angles as \(\theta_A,\theta_D\)
and define

\[
V_{ABCD}=|y_B-y_A|+|y_C-y_B|+|y_D-y_C|.
\]

**Original-row consequence.** For any unchanged mask with short bits `00`,
the two additional guards

\[
\theta_A\theta_D\le0,
\qquad V_{ABCD}\le\frac{23}{100}
\tag{1}
\]

exclude its strict-radius domain \(q<Q\). If at least one main bit is one,
the same guarded domain is excluded even at closed \(q\le Q\).

For the closed-Q assertion, the geometric theorem forces equality, aligns
A,B,C,D,E,F,G, and makes all three original main horizontal gaps one.
Every original main support sum is then also one. This contradicts whichever
original main link has its retained strict weak bit. This argument does not
invoke the theorem's separate Section 7 attachment for original `001/00`;
in particular, it uses no actual-BC premise, large-CD-height normalization,
G-height order, or selected signed endpoint cap.

The two extras H,I remain the same physical originals and remain in the
caller. The argument does not replace them with virtual squares or erase
their constraints. They are simply unnecessary for this guarded theorem.

### 2.1. Complete closed escape family

For \(\varepsilon=(\varepsilon_1,\varepsilon_2,\varepsilon_3)
\in\{-1,1\}^3\), let

\[
L_\varepsilon=
-\varepsilon_1y_A+(\varepsilon_1-\varepsilon_2)y_B
+(\varepsilon_2-\varepsilon_3)y_C+\varepsilon_3y_D.
\]

The maximum of these eight literal expressions is \(V_{ABCD}\): choose
each sign to match its own height increment, independently, including a
zero increment. If (1) fails by height, its strict failure lies in at least
one closed halfspace

\[
L_\varepsilon\ge23/100.
\tag{2}
\]

If (1) fails by angle sign, both nonzero endpoint angles have the same sign.
That strict failure is contained in one of the two closed domains

\[
\{\theta_A\ge0,\ \theta_D\ge0\},\qquad
\{\theta_A\le0,\ \theta_D\le0\}.
\tag{3}
\]

Therefore (2) and (3) give a complete ten-domain necessary closed cover for
every surviving nonzero-main/00 caller at closed Q, or every surviving
main/00 caller at strict radius. The angle domains are two conjunctions,
each with both stated inequalities; they are not two single scalar rows.
Their overlap at zero and all threshold faces in (2) are retained. No
individual member is asserted impossible merely because it belongs to this
cover.

If a source-bound parent already proves opposite endpoint signs, (1)'s sign
guard is settled and the eight height members suffice. This does not mean
that either oversized closed same-sign domain in (3) was excluded: such a
domain may contain a zero-angle face satisfying the settled guard.

The eight rows, in lexicographic sign order, are recorded in the companion
JSON. There is no endpoint magnitude bound, selected physical separator,
shoulder order, or extra-square x-order in this original-row specialization.

## 3. The accepted full-caller replacement theorem supplies another cover

The already accepted *A near-horizontal replacement row excludes both
outer-weak callers* proves, for `001/00` and `011/00`, that neither original
extra X in {H,I} can satisfy

\[
x_B\le x_X\le x_D,\qquad
|y_X-y_B|\le1/8,\qquad |y_D-y_X|\le1/8.
\]

Its exact equality blocker retains the unchanged original C and the strict
weak CD comparison. Each extra therefore has six necessary closed order or
height escapes. In `011/00`, direct X=C also gives four main-height escapes,
so the full 4×6×6 product is a complete optional necessary cover. It contains
144 domains, not 144 exclusions. A common reflection reducing it to 3×6×6
requires an explicit normalization of the parent and every physical frame.

Reversal gives the corresponding `100/00` and `110/00` versions: the row
becomes A–X–C, and the strict weak comparison is AB. This is an application
to the reversed unchanged caller, not a claim that arbitrary row relabeling
preserves actual projection links.

The accepted unit-height blocker supplement widens the *aligned equality
blocker* to an offset in [0,1]. It does not widen the preceding row theorem's
1/8 guards. The signed-positive-D central-section cap likewise retains its
own original-001 premises and cannot be silently transplanted to `011/00`.

## 4. What remains missing

The ten-domain original-row cover can reduce `011/00`, `101/00`, and
`111/00` without a new geometric polynomial table, subject to independent
review of this relabeling and an exact caller attachment. It does not prove
that those masks imply opposite signs or small variation. All remaining
height and sign domains still require complete proofs.

For short bits other than `00`, the actual EFG chain needed by both endpoint
cap sums is missing. A replacement for the short chain, or a complete
physical relabeling/extraction theorem supplying an appropriate actual
three-chain, is required before either argument transfers.

The accepted selected-seven obstruction realizes every currently OPEN mask
below Q using A–G alone. It is not a nine-square counterexample, but it shows
that the full remaining predicates cannot all be excluded by ignoring H,I.
A global all-nine frame/chain extraction theorem might still be possible;
no such complete routing theorem is established by this note or by existing
finite unsuccessful screens.

All dependencies and the exact current mask snapshot are hash-bound in
`FULL_MASK_TRANSFER_AND_ORIGINAL_ROW_REDUCTION.json`. This note provides
zero original, mask, and roadmap closure credit.

## Appendix A. Literal premise and dependency mapping for Section 2

The source for this appendix is the unchanged accepted
`opposite_tilt_theorem/HAND_PROOF.md`, SHA-256
`db830ffbebdc807b0e05f78766e0a0509d11418be31b9a7ef0623b212328831a`.
Its Section 1 states a seven-square geometric theorem; its final paragraph
announces a separate original-001 consequence proved only in Section 7.
The present specialization uses the geometric theorem through Section 6.

### A.1. Original-label map

| Source theorem label | Unchanged caller label | Premise retained |
|---|---|---|
| A | A | Original physical unit square; canonical signed angle is the left endpoint angle |
| H, row index 1 | B | Original physical unit square; angle independent of the other row frames |
| I, row index 2 | C | Original physical unit square; angle independent of the other row frames |
| D | D | Original physical unit square; canonical signed angle is the right endpoint angle |
| E | E | Original left short-chain square |
| F | F | Original middle short-chain square |
| G | G | Original right short-chain square |

This is substitution into a seven-square theorem, not a permutation of the
existing nine-square certificate or its bit fields. The caller's original
H,I are still present and constrained. None of its labels, angles, selected
bits, or pair facts is rewritten.

### A.2. Every required pair premise

Here `actual` means horizontal gap at least the sum of the two physical
horizontal halfwidths; a main bit of one means the original strict reverse
inequality. Physical disjointness is a separate premise and includes contact.

| Exact caller pair | Original center cone retained? | Actual projection required by this specialization? | Role |
|---|---|---|---|
| AB | Yes | No; either original bit value is permitted | Proves weak row order; physical separation supplies one actual owned separator in source equation (6) |
| BC | Yes | No; either original bit value is permitted | Same row-order and physical-separator role |
| CD | Yes | No; either original bit value is permitted | Same row-order and physical-separator role |
| EF | Yes | **Yes**, the short-chain bit must be zero | Gives \(x_F-x_E\ge h_E+h_F\) in source equation (15) |
| FG | Yes | **Yes**, the short-chain bit must be zero | Gives \(x_G-x_F\ge h_F+h_G\) in source equation (15) |
| AE | Not a selected cone pair | No | Physical left-endpoint weighted cap, source equation (4) with direction −x |
| DG | Not a selected cone pair | No | Physical right-endpoint weighted cap, source equation (4) with direction +x |
| Every other original pair | All original facts retained | No new projection premise | All 36 physical pair constraints remain in the caller |

For the closed-Q contradiction, **at least one** of the three exact original
pairs AB, BC, CD must have its strict weak bit. Its identity comes from the
unchanged main mask and is not chosen by physical-separator ownership. No
particular one of these three bits is needed. For strict radius alone no
main bit assumption is used.

The endpoint-angle premise is the physical canonical sign condition
\(\theta_A\theta_D\le0\). The proof first treats \(\theta_A\ge0\),
\(\theta_D\le0\); common vertical reflection of all centers and frames
treats the other orientation. That reflection preserves the five cone
comparisons, horizontal supports, actual/strict weak bits, corner norms, and
all pair separations. Zero endpoint angles and the canonical endpoint
angles are retained. No same-sign case is inferred from this reflection.

### A.3. Literal source-to-lemma dependency check

| Source location | Mathematical input actually used | Why it remains valid after the substitution |
|---|---|---|
| Section 1, geometric statement (1)–(2) | Seven distinct physical squares; weak four-row order; opposite endpoint signs; variation bound; actual EFG | The table in A.1 preserves distinctness and the two endpoint labels; A.2 supplies the only two required actual projection links |
| Section 2, physical cap (4) | Universal endpoint toll, sharp small-angle toll, and unrestricted physical pair-cap equality classification | These are physical two-square inequalities for AE and DG; neither has an AB or BC actual-link premise |
| Section 2, pair support (5) and owner inequality (6) | Physical separation of each adjacent row pair, positive row gap, and height gap at most 23/100 | The pairs are now exactly AB, BC, CD. Each has both possible original owners and both axes retained; actual horizontal projection is not assumed |
| Sections 3–4, scalar inequality (7) | Four independent canonical angles with opposite endpoint signs, all eight owner patterns, all three choices of maximal owner slope | The scalar table is indexed by row indices 0,1,2,3 and owner indices, with no original bit or center-cone input. Relabeling its two internal indices changes no polynomial or certified box |
| Section 5, row inequality (14) | Sum the three physical owner inequalities and use total variation | The same sum is along the unchanged main row AB, BC, CD |
| Section 5, cap sum (15) | Pair caps on AE/DG and actual EF/FG | Precisely the explicit two actual short links in A.2; strict radius makes the cap sum strict |
| Section 6, equality | Zero maximal owner slope; actual row separation then follows from aligned physical owners; endpoint tolls vanish | This is a conclusion, not an added actual-main premise. It aligns the original A,B,C,D and forces their three original horizontal gaps to equal one |
| Section 7, equation (16) | Actual AB and BC plus the CD cone-inset inequality in a different AHID-row attachment | **Not used.** Its separate argument for recovering the two omitted B,C frames is unnecessary: those frames are already the internal row frames here |

The inherited physical texts are exactly
`UNIVERSAL_MAIN_ENDPOINT_TILT_TOLL.md`,
`SHARP_SMALL_MAIN_ENDPOINT_TILT_TOLL.md`, and
`PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`
inside the unchanged theorem packet. Its original manifest, all 101 immutable
inputs, scalar replay, and root review are retained by hash in the companion
dependency audit. This audit checks bytes and the literal dependency map;
it does not claim a second polynomial replay.

### A.4. Strict and equality faces

At \(q<Q\), source equation (15) is strict and contradicts the lower bound
\(2a+b\), with \(a=46\), \(b=27/2\). At \(q=Q\), the nonnegative
surplus forces maximal owned slope zero. Physical row projection then gives
each gap at least the adjacent support sum. The cap equality forces all
row halfwidths to 1/2 and the sum of its gaps to three. Thus each gap is
exactly one. A retained strict weak main bit demands that same gap be
strictly less than one, which is impossible.

No height ordering is assumed. Absolute increments and all eight signed
height sums include zero increments and equality at 23/100. If adjacent
main x coordinates coincide, their center cone also gives equal y
coordinates, contradicting the unit center-distance bound; the theorem's
weaker order formulation already safely includes this face. Same-sign
escape domains keep their zero-angle overlap. No closed overlap is discarded
as an independent exclusion merely because another theorem applies there.


## Committed source attachment and review

The normative v2 note and specification are preserved byte for byte in
[`computer_assisted/original_row_mask_transfer`](computer_assisted/original_row_mask_transfer).
Its [source map](computer_assisted/original_row_mask_transfer/SOURCE_BINDINGS.json)
locates every immutable input and both independent/root reviews in this
repository. The map explicitly selects the v2 specification; the earlier
JSON name in the historical prose above does not supersede that selection.
The previously accepted opposite-tilt polynomial table is reused unchanged.
Run `python -B -S computer_assisted/original_row_mask_transfer/verify_source_bindings.py`
from this directory to recheck every attachment.

The root read the full normative note and the geometric proof through its
separate original-001 section. The specialization uses Sections 1–6 only.
Only EF and FG require actual projection; each original main link supplies
row order and physical separation. At closed Q, all three main gaps become
one, contradicting any retained strictly weak main bit. Two closed same-sign
conjunctions and all eight signed-height escapes preserve every overlap.

This is a conditional theorem and a complete necessary cover. No escape
member is closed by the cover itself. The fixed ledger remains 218 CLOSED /
13 OPEN original cells, 8 CLOSED / 24 OPEN masks and 5,838 CLOSED / 2,077 OPEN
positional roots. No roadmap gate is added. No Lean, Lake or CI was run.
