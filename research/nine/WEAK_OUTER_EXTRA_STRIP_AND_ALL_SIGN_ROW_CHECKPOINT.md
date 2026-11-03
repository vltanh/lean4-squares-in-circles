# Weak-outer continuation: fixed extra strip and all-sign row terminal

This checkpoint continues PR #11 from
`831ac93a883d01a08eaf0ea6e386b2edc4bec050`. It contains complete internal
hand arguments and finite rational tables for the original `001/00`
caller and its exact reversal `100/00`. It does **not** contain a complete
cover of their remaining original-nine placement domain. The fixed
accounting remains **8 complete masks and 24 open masks**. A.2, the global
lower bound, equality classification, and final manuscript remain open.
No Lean, Lake, or CI was run.

## 1. Unchanged original domain

Retain all nine original frames, all 36 original corners, all 36 physical
pairs, both extras, the five original center-cone links, and the exact
actual/strict-weak bits. Use `Q=1105/256`. The accepted low-gap proof
already excludes `|y_D-y_C|<=2/3`. In the complementary domain a common
vertical reflection gives

\[
 x_D-x_C\ge y_D-y_C>2/3,\qquad x_D-x_C<h_C+h_D.
\]

As before, `h_i` is the coordinate halfwidth of the unchanged original
square and `g_i=1/(4h_i)` is its contained aligned-inset halfwidth. A
closed necessary relaxation is used only to obtain valid implications
for this strict original caller. Its feasible aligned boundary controls
are never mislabeled counterexamples to the strict mask.

## 2. Complete finite inputs, including fresh source-bound replays

The following recovered or newly discovered finite tables have complete
independent exact replays in this continuation. No table has an open
frontier. The exact sources, packed certificates, damaged-certificate
controls, and reports are included in the checkpoint inventory.

| Original implication | Roots | Exact terminal leaves | Nodes |
|---|---:|---:|---:|
| `y_F>y_C` | 8 | 6,197 | 10,397 |
| `x_G-h_G<49/64` | 8 | 7,634 | 14,382 |
| `y_E>y_A` | 32 | 48,376 | 96,219 |
| `y_G-g_G>3/40` | 8 | 11,821 | 21,606 |
| `y_G-y_D<79/50` | 8 | 16,505 | 31,100 |

There are **90,533 exact terminal leaves** in these five complete component
tables. These are component leaves, not mask closures. Exact replay
checks every signed root, every closed angle child, every non-omitted
physical separator owner, and the rational terminal reserve. The
replayers do not call the numerical discovery solver.

The first four packages were recovered by exact byte identity from
previous work. Their immutable certificates and verifier dependencies
were matched before fresh complete root replays. The fifth table was
discovered during this continuation; its exact source delta from the
accepted original C,D,G kernel was independently inspected, then all
16,505 leaves were replayed again by the root integrator. The three-frame
table uses no claim about an extra square and no G upper-inset conclusion;
its use below is therefore acyclic.

## 3. The two extras have a fixed horizontal strip

The [unique-leftmost proof](WEAK_OUTER_UNIQUE_LEFTMOST_ORIGINAL_HAND_PROOF.md)
shows that every original other than A has `x>x_A`. The proof uses
`-x_A>91/64`, the A inset barrier, the universal center bound
`|c|<91/60`, and genuine unit center separation.

The new [D/G table and routing proof](WEAK_OUTER_NO_EXTRA_RIGHT_OF_D_HAND_TABLE.md)
shows, for each unchanged extra X,

\[
                         x_A<x_X<5/4<x_D.
\]

The hand argument assumes `x_X>=5/4`. Unit center separation forces X
more than `24/25` vertically from D. The C lower-region theorem and the
center-radius bound exclude the lower sign. The G horizontal bound then
forces G more than `31/50` above X; the opposite sign would put X outside
its center disk. Hence `y_G-y_D>79/50`, contradicting the complete table.
This retains every original extra orientation and the horizontal tie
faces. It makes no assertion that D is to the right of G.

The same document proves the all-angle F-side routing inequalities

\[
\begin{array}{ll}
x_X\le x_F:&|y_X-y_A|+|y_F-y_X|>3/5,\\
x_X\ge x_F:&|y_X-y_F|+|y_D-y_X|>3/5.
\end{array}
\]

They follow from the exact lower span `9/5` for two consecutive genuine
unit-center links of total vertical variation at most `3/5`, while both
available A/F and F/D spans are strictly shorter. Equality in the
horizontal comparison retains both implications.

## 4. Complete row terminals with either endpoint-tilt sign

The strongest accepted all-sign result is the
[correlated-corner row theorem](ALL_SIGN_CORRELATED_CORNER_ROW_HAND_STRENGTHENING.md).
It applies to the original row A,H,I,D and actual short chain E,F,G,
with the proved upward shoulder orders, under either set of guards:

| Total row height variation | Largest absolute sine of the seven original angles |
|---|---|
| `11/30` | `1/30` |
| `9/20` | `1/50` |

It proves `R^2>=Q`; at equality all seven originals are aligned and
`x_D-x_A=3`. The original AB,BC actual and CD inset comparisons then
contradict the original strict CD weak bit. Thus both regions are
excluded even at closed Q inside `001/00`, with no B/C angle assumption.
Both endpoint signs are retained.

The proof preserves the signed common slope of the four-row chain. An
exact circle-support deficit controls the difference of the two actual
endpoint corner heights. Completing the square pays the common slope
contribution, while signed angular variation pays the remaining changes
along the row. The resulting rational criterion has final positive
reserves

\[
 \frac{305395948055079229}{564669051336432000},\qquad
 \frac{13240758374442033713}{52010454158334000000}
\]

for the two displayed regions. Root independently checked the continuous
argument, both path-extremum cases, and equality; all **108 exact
arithmetic checks** passed. The criterion can also be evaluated for
other rational guards, provided every printed geometric and scalar
condition is verified.

The [all-sign seven-original theorem](ALL_SIGN_SMALL_ANGLE_THREE_LINK_ROW_HAND_TERMINAL.md)
is the simpler precursor retained in full. Suppose the sorted extras
give A,H,I,D in horizontal order and

\[
 |y_H-y_A|+|y_I-y_H|+|y_D-y_I|\le1/12.
\]

If the seven original squares A,H,I,D,E,F,G satisfy
`|sin(theta)|<=1/50`, then their physical nonoverlap, actual E/F/G chain,
and the proved shoulder orders imply `R^2>=Q`. At equality all seven
frames are aligned and `x_D-x_A=3`. There is no B/C angle assumption.
The original AB,BC actual links and CD inset comparison then force B,C
aligned as well, contradicting the retained strict CD weak bit. Thus
this entire row region is excluded even at closed Q, for every pair of
endpoint tilt signs.

The proof keeps signed frame differences in the physical support sum,
combines four fixed circle-support inequalities, and proves a complete
piecewise affine angular-variation bound. Its final exact positive
coefficient is

\[
             \frac{6513193240933}{74955006000000}>0.
\]

The independent root review checked the physical separator union,
all scalar sectors, and the equality argument. The arithmetic companion
passed all 70 exact rational checks. If `x_H=x_I`, the displayed variation
bound contradicts unit center separation immediately, so the terminal
also handles the closed sorted ordering used in a finite search.

The broader [inward-endpoint row argument](WEAK_OUTER_INWARD_ENDPOINT_THREE_LINK_ROW_HAND_TERMINAL.md)
has no angle-size guard but requires the stated opposite endpoint signs.
Its [continuous strengthening](WEAK_OUTER_THREE_LINK_ELEVEN_THIRTIETHS_HAND_STRENGTHENING.md)
allows total vertical variation up to `11/30`. These are separate valid
terminals; different toll estimates for one pair are never added together.

## 5. Other complete reusable inputs

The recovered F-order, G-edge, and E-order inputs yield the continuous
C/F and B/F vertical-inset separations, strict A/E overlap, and
`y_E-g_E>3/40`. The recovered deep-B nonlinear cylinder proof retains all
nine angles and eight center neighborhoods, leaving F's center free;
its complete exact certificate consists of 144 rational identities in
eight cases. The asymmetric B,X,D row proof and its positive-D variant
are also preserved with their independent reviews and exact companions.

The [alternate-chain reduction](ALTERNATE_FOUR_CHAIN_SATURATION_HAND_REDUCTION.md)
enumerates all 105 eligible four-tuples among A,B,C,D,H,I. Any tuple
having all three center-cone links and both actual outer links invokes
an already closed mask with unchanged E,F,G. The eight closed
inequalities in each complement retain all tie faces. This is a valid
conditional reduction; existence of a successful tuple is still to be
proved where it is needed.

The [small-tilt grid argument](SMALL_TILT_THREE_BY_THREE_GRID_HAND_EXCLUSION.md)
excludes a full 3 by 3 cone grid when all nine original folded slopes
are at most `1/43`. It supplies a four-chain in that frame, without
asserting actual outer links. The adaptive folded-angle chord is a
necessary relaxation only. An exact rotated-extra boundary control is
included to prevent an invalid global assumption that every extra tilt
must be below `1/8`.

## 6. What remains to be proved

The unrestricted remaining height placements of H and I have not been
covered. Complete component tables and the new boundary terminals do not
establish that every original-nine configuration enters one of those
terminals. Numerical low-F and upper-cap searches are discovery evidence,
and unfinished full-nine forests retain their open cells.

The new [disk/inset and diamond inequalities](DISK_INSET_AND_DIAMOND_SEPARATION_HAND_PROOF.md)
are valid for any two physical originals and give necessary rational
secant rows on a closed search cell. The geometry reviewer independently
checked both containment arguments and the diagonal distance scaling.
Several existing two-original cap theorems also transfer under their
explicit height/strip hypotheses; the independent review lists exactly
which ones. None of these cuts replaces the missing cover.

The next mathematical target remains the **whole** original `001/00`
domain and reversal `100/00`, or a proved universal terminal-extraction
theorem. No additional mandatory gate is introduced. The same 32 mask
predicates, 15 roadmap IDs, and positional ledger (5,838 historical
closed-Q exclusions and 2,077 open roots, with equality root 7820 retained)
remain unchanged.

The exact inventory is
`computer_assisted/weak_outer_extra_strip_row_checkpoint_manifest.json`.
The independent integration review is
[WEAK_OUTER_EXTRA_STRIP_ROW_INDEPENDENT_REVIEW.md](WEAK_OUTER_EXTRA_STRIP_ROW_INDEPENDENT_REVIEW.md).
