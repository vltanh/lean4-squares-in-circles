# Complete A-family inward-row child 5 by whole-parent capacity

## Statement and scope

The entire fixed original cell `positive-b819223a03e89ec7` is empty.
Its full literal path is

```text
angle(3,1)
angle_cut(0,0,0)
inward_row_escape(7,8,[5])
```

Thus the result excludes the whole existing inward-row child 5 under
positive D and nonpositive A. The immutable original register contains
exactly this one original cell under that three-step prefix; no later
F-height cut or other descendant predicate is assumed. All equality
faces, original strict bits, and marked cone comparisons are retained.

The proof keeps nine independent physical unit squares, their original
frames, all 36 original corners, and all 36 original pairs. It uses one
terminal domain: the unchanged original predicate. There are no new
branch nodes, fixed-grid tiles, or conditional subregions.

## 1. Acyclic whole-parent bounds

Replay the 47 earlier coordinate deductions for this original. Three
further rounds prove the following exact necessary bounds:

| Round | New deductions | Printed physical rows |
| --- | ---: | ---: |
| 1 | 171 | 269 |
| 2 | 121 | 229 |
| 3 | 214 | 243 |
| **Total before terminal** | **506** | **741** |

Each proposal is a nonnegative rational combination of physical rows
and previously proved interval bounds. Every residual coefficient is
charged against an explicit absolute variable bound. All proposals in
a round use only that round's old state, and their rounded-outward
conclusions are installed together. The physical frame identities are
then reapplied to the narrower scalar intervals.

The additional physical rules are the shared
[point/incircle coupling](ORIGINAL_POINT_INCIRCLE_FRAME_COUPLING_HAND_PROOF.md),
[perspective and directional support](ORIGINAL_FRAME_PERSPECTIVE_AND_DIRECTIONAL_SUPPORT_HAND_PROOF.md),
[support-height](ORIGINAL_SUPPORT_HEIGHT_PAIR_HAND_PROOF.md),
[three-original altitude](THREE_ORIGINAL_ALTITUDE_CAPACITY_HAND_PROOF.md),
and [sharp strip](THREE_ORIGINAL_SHARP_STRIP_CAPACITY_HAND_PROOF.md)
lemmas. The terminal uses these proved bounds with original rows; it
does not assume a physical realization of the linear relaxation.

## 2. Physical capacities joining the terminal

Two three-original constraints are useful in the final combination.
For endpoints A and I with middle original H, both projection
quantities have the proved lower bound

\[
\frac{2050313956857}{1099511627776}>0.
\]

The endpoint distance is at least
`270511058423281/140737488355328`, and the determinant numerator is at
most `33849878331/68719476736`. Thus H projects onto the A-I segment and
has perpendicular altitude at most

\[
\delta\le\frac{69324550821888}{270511058423281}<\frac{7}{10}.
\]

The altitude theorem gives
`|c_I-c_A| >= min(2,280/99-2 delta) = 2`. Its exact secant consequence is

\[
\frac{1022915}{262144}(x_A-x_I)
+\frac{720793}{1048576}(y_A-y_I)
\le -\frac{4350378525463}{549755813888}.
\]

For the second constraint, use transverse unit direction
`(24/25,-7/25)` and longitudinal unit direction `(7/25,24/25)`.
Original I lies between C and G in the longitudinal projection, because
the two consecutive projected differences have positive lower bounds
`22979769/26214400` and `23600167/26214400`. Their transverse width is at
most `5334001/13107200 < 7/10`. The sharp three-original strip theorem,
with its exact endpoint secant, therefore gives

\[
\frac{87496147}{409600000}(x_C-x_G)
+\frac{3209175657}{3276800000}(y_C-y_G)
\le -\frac{68634932017871337}{34359738368000000}.
\]

The physical folded-arc chord of G supplies the further necessary row

\[
-\alpha_G-\frac{27480703981409}{66344288255477}|\beta_G|\le-1.
\]

All three rows use original frames and original centers. Their guards
and exact coefficients are rebuilt from the old-state intervals by the
independent checker, along with the other terminal rows below.

## 3. Exact twenty-six-row terminal

For every selected physical row `a_j . z <= b_j`, multiply by the
positive weight `w_j / 2^40` in this table. The complete coefficient and
right-hand-side tables are printed in the immutable certificate.

| Row index | Physical row rule | Weight numerator `w_j` |
| --- | --- | ---: |
| `53` | `abs_equal_neg` | `38289590539` |
| `86` | `arc_chord` | `14724570611` |
| `96` | `corner_support` | `27194755446` |
| `454` | `arc_chord` | `7767286121` |
| `638` | `arc_chord` | `59104161919` |
| `767` | `corner_support` | `23184260576` |
| `964` | `width_lower` | `27205761699` |
| `1698` | `cone` | `194683829473` |
| `1703` | `chain` | `27205761699` |
| `1706` | `chain` | `27205761699` |
| `1729` | `all_pair_cap` | `2015241607` |
| `2006` | `signed_right_cap` | `1066440377` |
| `4536` | `dense_original_corner_support` | `77994124522` |
| `7110` | `contact_original_corner_support` | `1043055509` |
| `7541` | `contact_original_corner_support` | `591595014` |
| `7549` | `contact_original_corner_support` | `462760054` |
| `9692` | `certified_difference_upper` | `206408507694` |
| `12964` | `owner_free_interval_radius_2_8` | `86317223694` |
| `13236` | `ordered_euclidean_gap_2_8_0_1_1` | `181214678438` |
| `13423` | `original_stronger_altitude_capacity_0_7_8` | `53218156461` |
| `18083` | `sharp_rotated_three_square_strip_2_8_6_24/25_-7/25` | `3415273167` |
| `18191` | `physical_folded_arc_chord_6_0_199032864766431/281474976710656` | `15461609382` |
| `19542` | `directional_support_gap_2_8_2_5_1_1_0` | `7691973722` |
| `20324` | `directional_support_gap_6_8_8_9_1_1_0` | `11339125988` |
| `20614` | `directional_support_gap_3_8_3_11_1_1_0` | `517134778` |
| `20786` | `directional_support_gap_2_8_2_12_1_1_0` | `4188987587` |

Let `L = sum_j (w_j/2^40) a_j` and
`B = sum_j (w_j/2^40) b_j`. The printed absolute variable bounds `M_k`
give `L . z >= -C`, where `C = sum_k M_k |L_k|`. Exact addition yields

\[
B=-\frac{4806564628377369442042680543550398867160582486118489661}
{376751053509254010230294041844260073113079263526912000000},
\]

\[
C=\frac{558730955755797285113311806430452941627877042634835021289969}
{4861621072956894576513272798678836186868630339863522282777138010521600}.
\]

But `L . z <= B` by the weighted physical rows, whereas

\[
-B-C=
\frac{20811879574899124505286098598197503157525954258395064183852425929415562177040861}
{1631289337022991579987834092207186986714227496720874477179302485286623117312000000}
>\frac1{80}>0.
\]

The required inequalities `-C <= L . z <= B` are contradictory. The
reserve includes the full exact residual allowance; it is not a
numerical margin or a claim that approximate coefficients cancel.

The complete proof uses 47 earlier coordinate deductions and 506 new
deductions. Its three bound rounds and one terminal contain 767 printed
physical rows, including the 26 terminal rows above. Its scope is the
entire unchanged original cell and therefore the entire existing
inward-row child 5 described in the statement.

## 4. Immutable certificate and replay

The source-bound certificate `positive-b819223a03e89ec7.json` has SHA-256

```text
c14a54a4c5aafbe3d681af5c828bcd12d50e6e1152c45d243610a6bbef3d574a
```

The earlier coordinate prefix has SHA-256

```text
9b609b55a860734e20944fc19106710e50fbcc3920a72319bce611651e2d15f4
```

The canonical independent `verify_joint_original.py` replay, using
`independent_all_rules.py`, returned `PASS_COMPLETE_ORIGINAL_PARENT`.
It checks the immutable original identifier and path, replays the
coordinate prefix and all bounds, independently reconstructs every
physical row and old-state guard, and recomputes the terminal with
exact rational arithmetic. Discovery solver statuses have no role in
acceptance. The proof record and checker source bindings are frozen in
the bounded-final-pass addendum.

This closes one additional original and its existing inward-row child
5. Other original cells and masks remain separate obligations. No
whole-mask closure, Lean compilation, Lake invocation, or CI result is
claimed by this finite argument.
