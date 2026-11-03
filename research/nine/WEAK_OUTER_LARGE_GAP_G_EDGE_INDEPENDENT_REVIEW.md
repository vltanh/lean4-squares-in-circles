# Independent acceptance of the G-edge table and its original-pair consequences

November 3, 2026. Reviewed and replayed independently of the producer and
the table author. No Lean, Lake, or CI was run.

## Accepted scope

Retain the unchanged original-nine strict `001/00` caller, with AB and BC
actual, EF and FG actual, all five marked cones, and the common vertical
normalization

\[
 x_D-x_C\ge y_D-y_C\ge2/3,\qquad x_D-x_C<h_C+h_D,
 \qquad R^2\le1105/256.
\]

The complete table proves

\[
                         x_G-h_G<49/64.
\]

It does not by itself close a fixed mask or settle the placement of both
unselected originals.

## Independent source review

I compared the complete producer and exact verifier against the frozen,
independently accepted F-order kernel. The geometric changes are precisely
the following:

* The contrary closed half-space is `x_G-h_G>=49/64`. Its linear row is
  `-x_G<=-49/64-h_G^-`, a necessary weakening with the correct width endpoint.
* The G coordinate lower bound becomes `x_G>=49/64+h_G^-`. All subsequent
  corner, difference, and normal-error intervals use this necessary bound.
* The prior contrary F-order row is removed. The already accepted C-slant,
  C/G actual vertical comparison, D/G inset and affine clearances, and both
  endpoint-cap transfer forms remain valid independently of E/A order.
* The accepted all-tilts upward C/D normal theorem applies since the caller
  has `v>=2/3>=1/2`. The C/D and D/G omissions use exact component signs;
  the floating producer tests the equivalent signed angle endpoints and
  does not omit a possibly positive component by a tolerance.

The eight closed signed-angle roots cover all three original C,D,G frames.
The unchanged exact checker verifies both children of every angle split,
the full original owner/axis union at each separator split, and the paid
residual of each rational Farkas combination. The imported exact helper is
used for Fraction support and radical intervals, not as a claim from the
uncompleted four-original right-lower exploration.

## Fresh complete replay

The independent run used the packed certificate directly, without running
the producer or an optimizer. It returned:

| Quantity | Complete exact replay |
|---|---:|
| Orientation roots | 8 |
| Nodes | 14,382 |
| Terminal leaves | 7,634 |
| Maximum depth | 17 |
| Unresolved frontier | 0 |
| Positive reserve floor | `8767/15625000000` |

The report is
`computer_assisted/weak_outer_hand_G_edge_independent_replay.json`.
All three hashes matched before the replay and were unchanged afterward:

| Frozen artifact | SHA-256 |
|---|---|
| `extraction_search_G_edge_certificate.json.gz` | `2b175fba649fb55265302a9caeccde79f8add1b1a212cd034aea73a47fa3ad6d` |
| `extraction_search_G_edge_verify.py` | `f6be2c66e9132fa55940bad9bacdd4e5eb25d73ad5e6b203c8c7385c19020656` |
| `weak_outer_hand_right_lower_verify.py` | `c3c66a1fcfca7d2e0acd8d9b5a32340f8e8d2253e5e802ff1be34f5cbd0e109f` |

## B/F inset separation and order

The prior actual-link bounds give

\[
 x_F-x_B>\frac{27}{64}-\frac{115}{432}
          =\frac{269}{1728}>0.
\]

Actual FG, the new G-edge theorem, and `x_B>-31/60` give

\[
 x_F-x_B<\frac{49}{64}-\frac12+\frac{31}{60}
          =\frac{751}{960}.
\]

The actual-main width bound `h_A+h_B<69/64` implies
`g_B>16/37`, and `g_F>=1/sqrt(8)>7/20`. Therefore

\[
 g_B+g_F>\frac{579}{740}
          =\frac{751}{960}+\frac1{7104}.
\]

The unchanged contained aligned insets of B and F overlap horizontally,
so their disjoint interiors require vertical separation. The wrong order
`y_B>=y_F+g_B+g_F` contradicts the original BC cone: the already accepted
C/F inset result gives

\[
 y_F-y_C\ge g_C+g_F,
 \qquad x_C-x_F<g_C+g_F,
\]

and hence

\[
 y_B-y_C\ge g_B+g_C+2g_F
 > (x_F-x_B)+(x_C-x_F)=x_C-x_B.
\]

Consequently the necessary original comparisons are

\[
 y_F-y_B\ge g_B+g_F,
 \qquad y_F-y_B-(x_F-x_B)>1/7104.
\]

This argument has no E/A-order premise.

## Uniform A/E horizontal overlap

Actual EFG and `h_E+g_E>=1`, together with the same main width bound
`g_A>16/37`, imply

\[
 x_E-x_A-g_A-g_E
 <\rho+\frac{49}{64}-2-\frac{16}{37}
 =-\frac{5333}{35520}< -\frac3{20}.
\]

The reverse direction uses the prior A localization and the center bound:

\[
 x_A-x_E-g_A-g_E
 <\rho-\frac{59}{64}-1-\frac7{20}
 =-\frac{145}{192}< -\frac3{20}.
\]

Thus

\[
 |x_E-x_A|<g_A+g_E-3/20\le17/20<1.
\]

In the closed E-order contrary domain `y_E<=y_A`, the original insets
must therefore separate downward:

\[
 y_A-y_E\ge g_A+g_E,
 \qquad y_A-y_E-|x_E-x_A|>3/20.
\]

Every actual original A-to-E owned separating normal then has negative
vertical component. A nonnegative vertical component would give a
projection at most `|x_E-x_A|<1`, whereas the support requirement of two
original unit squares along an owned unit axis is at least one. This
supplies the signed left-cap premise throughout each nonnegative-A
orientation root, even before the E-order forest chooses an A/E owner.

All these hand consequences are accepted. Their use as append-only
necessary rows in the separate E-order table is acyclic.

## Fixed central strip in F

I also reviewed the complete author manuscript
`GLOBAL_OUTER_LINK_EXTRACTION_G_EDGE_AND_BF_VERTICAL_HAND_TABLE.md`.
The additional strip consequence follows from

\[
 -115/432<x_F<49/64-h_F\le17/64,\qquad g_F>7/20,
\]

and the exact reserves

\[
 7/20-115/432-1/12=1/2160>0,
 \qquad7/20-17/64-1/12=1/960>0.
\]

Thus `[-1/12,1/12]` lies strictly inside F's horizontal inset interval,
and

\[
 [-1/12,1/12]\times[y_F-g_F,y_F+g_F]\subseteq F.
\]

Its open rectangle lies in the interior of the same original F. The
contained B and C insets lie below the F inset by their established
vertical comparisons. This statement does not assert that the full
original B/F or C/F vertical projection intervals are disjoint.
