# Two further complete originals from fixed center covers

This separately frozen addendum advances the certified `001/00` register
from **183 CLOSED / 48 OPEN** to **185 CLOSED / 46 OPEN**. The whole-mask
ledger remains **8 CLOSED / 24 OPEN**. Its preceding nine-proof checkpoint
is unchanged.

## Scope

This addendum proves the entire original cells
`positive-2c719a20ef7510de` (family D) and
`negative-e0dbb1642ee58e72` (family B) empty. All nine original unit squares,
their physical frames, all original corners and pair constraints, and
every inherited routing predicate remain in the premises.

The construction uses the same exact closed 8 by 8 center-cover formula
and physical hand/table rules as
[the three-B fixed-center assembly](A2_00100_THREE_B_FIXED_CENTER_COVER_CLOSURE.md).
Each original has one fixed covering rectangle for its pending tiles;
there is no additional subdivision. The rectangle proof and the static
proofs outside it cover the whole original, including every equality
face. These are two original-cell closures, with no whole-mask or
all-mask closure asserted here.

## 1. Proved parent states and the fixed covers

The exact original paths are part of the certificates and are checked
against their original identifiers. The D path is

```text
angle(3,1)
angle_cut(0,0,1)
alternate_four_escape(1,7,[7])
alternate_four_escape(1,8,[2])
```

The B path is the full original 15-step path recorded for
`negative-e0dbb1642ee58e72`; no suffix of that path is dropped. Both
whole-parent states are obtained by independent exact replay before the
center cover is considered.

| Original suffix | Earlier coordinate deductions | New whole-parent deductions | Whole-parent printed rows |
| --- | ---: | ---: | ---: |
| `2c719a20ef7510de` | 0 | 619 | 1,272 |
| `e0dbb1642ee58e72` | 69 | 916 | 1,232 |

Their complete proved I-center rectangles are:

| Original suffix | I horizontal interval | I vertical interval |
| --- | --- | --- |
| `2c719a20ef7510de` | `[44173/131072, 554585/524288]` | `[511719/1048576, 416230958895369/281474976710656]` |
| `e0dbb1642ee58e72` | `[-1/1048576, 5/4]` | `[-6257/131072, 91/60]` |

For a parent rectangle `[a,b] x [c,d]`, tile `8p+q` is the product of
the p-th closed horizontal eighth and the q-th closed vertical eighth,
where `0 <= p,q < 8`. Consecutive endpoints use the same exact rational
formula, so they coincide on shared faces.

| Original suffix | Initially pending tiles | Full covering tile set | Static tiles used outside it |
| --- | --- | --- | ---: |
| `2c719a20ef7510de` | `22,23,30,31,32,40,48,56` | all tiles `16` through `63` | 16 |
| `e0dbb1642ee58e72` | `40` | `40` | 63 |

The D covering rectangle is the entire rightmost six horizontal eighths
and all eight vertical eighths:

\[
I_x\in\left[\frac{1084661}{2097152},\frac{554585}{524288}\right],
\quad
I_y\in\left[\frac{511719}{1048576},
\frac{416230958895369}{281474976710656}\right].
\]

Its 16 outside tiles have ten exact weighted contradictions and six
original inset-pair contradictions. Although additional static
exclusions exist inside this rectangle, they are unnecessary to the
assembly. One full-rectangle induction covers all 48 enclosed tiles.

The B covering rectangle is the singleton grid tile 40:

\[
I_x\in\left[\frac{6553597}{8388608},\frac{3932159}{4194304}\right],
\quad
I_y\in\left[-\frac{6257}{131072},\frac{2324903}{15728640}\right].
\]

Its 63 outside tiles have 24 exact weighted contradictions and 39
original geometric contradictions. Tile 40 has the direct physical
interval contradiction in Section 3.

## 2. The full D rectangle

Starting from the checked whole-parent state, intersect only the two
I-center intervals with the displayed rectangle. Retain every parent
scalar and pair-difference bound. Three exact implication rounds prove
71, 137, and 206 new bounds respectively, for 414 in all. The rounds use
193, 199, and 208 printed physical rows. Each row and its guard is
reconstructed independently; every weighted bound and physical frame
refinement is checked with exact rational arithmetic.

The final contradiction needs only three physical rows on originals F
and H. Put

\[
X=x_H-x_F,\qquad Y=y_H-y_F,
\quad a=\frac{55735}{65536},
\quad b=\frac{461397670522011}{281474976710656}.
\]

The independently rebuilt rows are

\[
\begin{aligned}
-aX+bY&\le-c,\\
\frac5{13}X-\frac{12}{13}Y&\le-d,\\
\frac8{17}X-\frac{15}{17}Y&\le-e,
\end{aligned}
\]

where

\[
c=\frac{9138863583299675685284276449}{4951760157141521099596496896},
\quad d=\frac{1059983901}{1073741824},
\quad e=\frac{1069286725}{1073741824}.
\]

All three constants are positive. The first inequality is the
`owner_free_interval_radius_5_7` physical row. The other two are the
`ordered_euclidean_gap_5_7` rows with rational directions `(12/13,5/13)`
and `(15/17,8/17)`. Their applicability follows from the complete proved
rectangle state, not from a sampled placement of F or H.

For a short exact cancellation, multiply the three inequalities by

\[
1,\qquad
p=\frac{13(8b-15a)}{21}
 =\frac{54427387374581}{246290604621824},\qquad
q=\frac{17(12a-5b)}{21}
 =\frac{3204906154370435}{1970324836974592}.
\]

The weights are strictly positive, as witnessed by

\[
8b-15a=\frac{12560166317211}{35184372088832}>0,
\qquad
12a-5b=\frac{565571674300665}{281474976710656}>0.
\]

Their X and Y coefficients cancel exactly:

\[
-a+\frac5{13}p+\frac8{17}q=0,
\qquad
b-\frac{12}{13}p-\frac{15}{17}q=0.
\]

Adding gives `0 <= -c-pd-qe < 0`, a contradiction on the whole
rectangle. This exact hand cancellation uses the same three rows as
the stored rational dual. The independently replayed stored dual also
has positive reserve

\[
\frac{149662318780080754538091105427964023074697}
{115696004753119077577547366526801191895040}>1.
\]

The rectangle and its 16 outside static exclusions prove the entire D
original empty. Counting those static tables, the rectangle induction,
and its terminal, the center-cover portion uses 724 printed rows.

## 3. The B singleton rectangle

No new weighted deduction is needed on tile 40. Reconstruct the
effective original angle bounds, propagate the original physical
center inequalities on the entire restricted rectangle, and compute
the physical pair-difference bounds. Intersect those necessary bounds
with the independently proved whole-parent difference bounds.

For the original pair D,F, the parent gives

\[
y_F-y_D\in
\left[\frac{20491}{524288},\frac{314573}{524288}\right].
\]

The full tile's physical propagation gives

\[
y_F-y_D\in
\left[-\frac{122279}{1048576},
\frac{61148432866931}{2111062325329920}\right].
\]

These intervals are disjoint because

\[
\frac{20491}{524288}
-\frac{61148432866931}{2111062325329920}
=\frac{21359231066509}{2111062325329920}>0.
\]

There is also an independent pair contradiction on D,I. Its parent
lower endpoint is `41883/131072`, whereas the tile's physical upper
endpoint is `1327785828064883/4222124650659840`, with positive gap

\[
\frac{41883}{131072}
-\frac{1327785828064883}{4222124650659840}
=\frac{21360036372877}{4222124650659840}>0.
\]

Either pair excludes the entire tile, including its boundary. The
independent checker recomputes both witnesses from the physical
propagation and verified parent state. The original diagnostic marked
this tile open because its generic row constructor encountered the
empty relational intersection before producing a dual. That diagnostic
exception supplies no proof; the explicit rational inequalities above
provide the proof.

Together with the 63 outside static exclusions, tile 40 completes the
B original. Its center-cover portion has zero new bound rounds and
108 printed static rows.

## 4. Independent replay and accounting

The separate immutable checker `verify_fixed_i_parent_v3.py` handles
the D assembly. It accepts the explicit general-parent prior kind,
then obtains every parent premise from the same independently checked
whole-parent callback used for the earlier proofs. The separate
`verify_fixed_i_parent_v4.py` adds only the direct empty parent/physical
difference-intersection terminal for the B assembly. It recomputes the
restricted rectangle's effective angles and propagated positions,
checks every original pair difference against the parent, and compares
the exact empty-intersection witnesses with the recorded table.

The parent, fixed grid, rectangle, source bindings, and prior-path
hashes are checked. Every static tile outside the rectangle is
independently proved. Every closed grid face is accounted for. Neither
checker imports a discovery producer or optimizer.

Together these two original proofs use 69 earlier coordinate
deductions, 1,949 new exact deductions, and 3,336 printed rows. Their
complete cover consists of 79 outside static domains and two full
rectangles. Every one of their 128 original grid tiles is covered.

The checker output has scope `PASS_COMPLETE_ORIGINAL_PARENT`; it does
not promote these cells to a whole-mask conclusion. No Lean, Lake, or
CI execution is used or claimed.

## 5. Portable evidence

The [addendum manifest](computer_assisted/a2_00100_fixed_center_addendum_manifest.json)
binds the complete source snapshots, canonical parent inductions, both
fixed grids, explicit rectangle proofs and independent reports. Extract
the associated archive into a fresh directory and run:

```sh
python fixed_center_addendum_checkpoint/verify_all.py
```

The archive SHA-256 is
`85d0488876bf2364c971702874d2df5945251aafadcd85d37346746c655ce987`.
The [root integration review](computer_assisted/a2_00100_fixed_center_addendum_root_review.json)
records a fresh extracted replay of both whole-original proofs, all 215
immutable payload checks, the exact three-row hand cancellation, the
unchanged 231 original paths and precisely these two status changes.
