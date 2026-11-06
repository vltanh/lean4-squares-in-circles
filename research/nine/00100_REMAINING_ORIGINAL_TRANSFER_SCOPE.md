# Which current lemmas transfer to the other original cells

This is a scope audit and a choice of the next proof target. It does
not exclude an additional original or import archived closure totals.
All statements retain the nine original physical squares, all corners
and pair conditions, actual AB/BC/EF/FG, strictly weak CD, the five
selected center cones, y_D-y_C>2/3, and x_H<=x_I.

The original paths below were read from the
[fixed register at archive commit 6a9a45e](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/gates/A2_00100_FIXED_FRONTIER.json).
The archive is used here to identify the unchanged callers. Its
previously excluded siblings are not independently reproved by this
note.

## 1. The precise distinctions between the original callers

Canonical tilt signs, rather than any selected physical pair axis,
define the A and D sign columns.

| Original | A sign | D sign | Distinguishing original path |
|---|---|---|---|
| A-c744: positive-c744bc031d40ee64 | Nonpositive | Nonnegative | Inward A,H,I,D escape, entry 4 |
| C887: negative-887236b78100baf3 | Nonnegative | Nonpositive | Alternate A,B,H,D escape, entry 1 |
| Cd402: negative-d4021ade840b985c | Nonnegative | Nonpositive | Alternate A,B,H,D escape, entry 2 |
| Cb882: negative-b882d8ade0cf9ea0 | Nonnegative | Nonpositive | Alternate A,B,H,D escape, entry 3 |
| B7: negative-7c60be8b07a358e9 | Nonpositive | Nonpositive | y_F<=1/2; F/H side escape, entry 2 |
| B462: negative-462e78d2e2d8be05 | Nonpositive | Nonpositive | y_F>=1/2; F/H side escape, entry 1 |
| B16a: negative-16a2fc93c8d133f0 | Nonpositive | Nonpositive | y_F>=1/2; F/H side escape, entry 3 |

All sign and height boundaries are included. The alternate-chain
entries have these literal meanings, including their predecessor
conditions:

* C887 is the AB cone face (x_B-x_A)+(y_B-y_A)=0.
* Cd402 has y_H-y_B>=x_H-x_B. Its two earlier-row complements
  are already the two selected AB cone inequalities.
* Cb882 has y_H-y_B<=-|x_H-x_B|, after combining its primary
  row with the preceding entry-2 complement.

In particular, **Cd402 does not initially require H above B**.
Its one diagonal halfplane is not the full upward B/H cone.
The exact Cd402 rows are printed in the
[archived original-model attachment](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted/a2_00100_cd402_fresh_original_checkpoint_v1/CD402_FRESH_ORIGINAL_MODEL_HAND_PROOF.md).

For the three B originals, decoding the F/H side rows gives x_H<=x_F
in every case. With t=3/5, the remaining rows are equivalently:

| Original | Height rows, after removing only implied repetitions |
|---|---|
| B7 | 2y_H-y_A-y_F>=t; y_A-y_F<=t |
| B462 | y_A+y_F-2y_H>=t; y_A-y_F<=t |
| B16a | y_F-y_A>=t; abs(y_A+y_F-2y_H)<=t |

These follow from the literal `f_side_escape_rows` definition in the
[archived path decoder](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted/all_masks_continuation_and_strict011_design_v1/source_snapshot/ac_work/c887/c887_whole_eight_checkpoint_package/ancestry/legacy/current_proof/shared_capacity_three_b_v4/geometry/weak_outer_numeric_strict_bulk_v14_verify.py).
They are additional rows of the original caller, not replacements
for its physical constraints.

## 2. Transfers that the present proofs justify

The filenames of several recent lemmas mention Cb882, but their
proofs use fewer assumptions. Inspection of each dependency gives
the following valid scopes.

| Current conclusion | Scope beyond Cb882 | Reason |
|---|---|---|
| h_B<259/480, abs(tan(theta_B))<1/12, abs(y_A)<1/3 | All seven originals | Uses the main actual links, CD insets, and disk containment |
| x_A<-23/16, x_B<-7/16, x_C<57/80 | All seven originals | Section 1 of the geometric reduction uses no tilt sign or extra-square row |
| Both A/E and D/G inset pairs separate vertically | All seven originals | The endpoint-inset proof uses actual links and physical pair caps |
| B/F insets separate vertically | All seven originals | The endpoint-span outsider argument uses only originals A through G |
| y_C+(7/8)x_C<-7/32 and the lower-right pocket exclusion | All six nonpositive-D originals | The complete C-slant assembly assumes D<=0 and the large CD height, but no A sign or H order |
| y_G-y_D>=g_D+g_G | All six nonpositive-D originals | Every input to the G-order proof has the preceding scope; the contradiction only uses C and G |
| y_B<743/1920 | All six nonpositive-D originals | Combine C-slant, the BC cone, x_C<57/80, and x_B>-31/60 |
| y_A-g_A<-1/4 | C887, Cd402, Cb882 | Requires A>=0; its proof precedes either E height order and uses no H row |
| On E-down: x_E+h_E>-11/16 and F above B by insets | C887, Cd402, Cb882 | The endpoint and C/F-distance arguments use the preceding bounds and G-up, not H-down |

Here “all six nonpositive-D originals” includes Cb882. The source
proofs are the [inner-frame theorem](00100_INNER_FRAME_AND_DOWNWARD_CONE.md),
[A-height theorem](00100_SHARP_A_HEIGHT_AND_CB882_DEEP_B.md),
[geometric reduction](CB882_GEOMETRIC_REDUCTION.md),
[endpoint insets](00100_ENDPOINT_INSETS_ARE_VERTICAL.md),
[B/F insets](CB882_BF_VERTICAL.md),
[complete C-slant](00100_C_SLANT_LOWER_COMPLEMENT.md),
[G-order theorem](CB882_G_ABOVE_D.md),
[E-down routing](CB882_E_DOWN_ROUTING.md),
[E-down endpoint](CB882_E_DOWN_ENDPOINT.md), and
[E-down middle-height theorem](CB882_E_DOWN_F_ABOVE_B.md).

There are two further immediate consequences.

First, in B462 and B16a, the original y_F>=1/2 and the preceding
y_B<743/1920<1/2 exclude the lower B/F order. Their B/F insets
therefore satisfy y_F-y_B>=g_B+g_F without any extra-square hypothesis.

Second, reflecting only the vertical coordinate in the elementary
A-height and E-down endpoint proofs gives, for nonpositive A,

\[
 y_A+g_A>1/4,\qquad
 y_E-y_A\ge g_A+g_E\ \Longrightarrow\ x_E+h_E>-11/16.
\]

This reflection is legitimate because those two proofs use neither
the sign of D nor the sign of the CD height. It transports those
lemmas only; it does not identify a different original cell with the
given caller or transport the nonpositive-D C-slant theorem.

## 3. Bounds and closures that do not transfer

The following are specific to the downward B/H cone:

* y_B>-67/120 and the stronger B/H vertical clearance;
* x_H<-1/40 and the resulting H height bounds;
* the literal E-down exclusion table;
* the literal E-up/F-down exclusion table.

The latter tables contain B/H downward-cone or downward-inset rows.
Deleting those rows while retaining their certified deductions is
invalid. Those Cb882 tables therefore do not prove E-up or F-up
for Cd402. The broader proofs in Section 5 establish both orders
with fresh tables that use only A through G; those are the valid
sources for the Cd402 conclusions.

For A-c744, D is nonnegative. The present nonpositive-D C-slant,
pocket exclusion, and G-up argument do not apply. The unconditional
inset and coordinate reductions remain valid. A common reflection
cannot silently repair the missing D sign while retaining the
normalized CD height and the same marked caller.

## 4. Cd402 is the closest direct successor

Cd402 retains the same A/D signs as Cb882 and shares the whole-main-chain
reductions and the E-up, F-up and G-up conclusions proved without H-down.
Its exact changed input is the single halfplane
y_H-y_B>=x_H-x_B. It is therefore the closest next original for a
fresh complete hand/table proof.

In particular, a Cd402 initial enclosure must remove both B/H
downward-cone rows, the downward B/H inset row, y_B>-67/120,
x_H<-1/40, and y_H<-881/1920. Removing only the explicit cone
while retaining those contracted bounds would still change the
caller. Start B's lower height and both H coordinates from their
universal center bounds; retain the new C-slant, G-up, endpoint
verticality, and B/F verticality as proved necessary inequalities.

The [thirteen-domain handoff](00100_CD402_THIRTEEN_FRONTIER_HANDOFF.md)
reports that every surviving path in one archived continuation has
y_H-y_B>=g_B+g_H. This is a property of those complete saved paths,
not an initial Cd402 hypothesis supplied by that archive. The new
left-cap proof in Section 5 establishes that upward inset order on
the whole original. The three archived H/I alternatives still retain
their full saved ancestry. The later four-original exclusion of
saved leaf 480 and variation reductions do not remove that obligation.

C887 is a boundary case of the same alternate-chain cover. The
[sharp A-height argument](00100_SHARP_A_HEIGHT_AND_CB882_DEEP_B.md)
gives y_B<-2/3 there. Strict-radius interiorization removes the AB
tie while retaining that strict bound; the low-B downward-cone
obstruction then prevents entry into Cb882. Consequently a complete
Cd402 exclusion also excludes C887 **provided the other cited
alternate-chain siblings and their complete cover are supplied**.
This memo checked the transfer's hypotheses, not those archived
sibling proofs. It does not claim that C887 itself satisfies the
Cd402 halfplane before perturbation.

B16a and B462 are sensible later targets because they now inherit
G-up and F-up without H-down. Their nonpositive A sign prevents
direct reuse of the C-family E-down table. The archived completion
of selected I rectangles in B16a is partial evidence whose full
ancestry and remaining complement must still be retained; its old
rectangle counts are not a whole-original proof.

## 5. Subsequent whole-parent improvements

The [left-cap proof](CD402_H_ABOVE_B.md) now gives
x_X+g_X>-15/16 for every original X distinct from A, together
with abs(y_A)<1/4, throughout all seven callers. It also rules out
the leftward B/X inset alternative for every X distinct from A,B.
Combined with Cd402's exact diagonal escape, this proves H above B
on that whole original without its archived continuation.

The new [middle-height theorem](00100_C_F_ABOVE_B.md) proves
F above B throughout C887, Cd402 and Cb882. Its fresh E-up/F-down
table uses only A through G; the E-down implication was already
transferred in Section 2. This removes the former H-dependence of
the F-up conclusion. The old Cb882 table itself remains limited to
its stated caller; the new theorem supplies the broader proof.

Neither improvement excludes an additional whole original.

The subsequent [E-order theorem](00100_C_E_ABOVE_A.md) also
proves E above A on C887, Cd402 and Cb882 without any H/I row.
Its complete 38-leaf table uses the conditional E-down F-up lemma,
so it does not assume its own endpoint-order conclusion. Together
with the shared F-up and G-up proofs, all three C originals now
retain E above A, F above B, and G above D before their extra-square
conditions are used. Their remaining original exclusions stay open.

Within Cb882, the [complete positive C-primary alternative](CB882_C_PRIMARY_COMPLETE.md)
is now excluded with its full literal table. This result retains the
downward B/H escape and the selected positive C-owned primary separator;
it does not transfer to the other originals. Cb882's C-secondary and
D-secondary alternatives remain open.
