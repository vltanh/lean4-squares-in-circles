# Independent physical reduction and exact checker for original E-order

November 3, 2026. The five-frame numerical producer and the exact checker
have different owners. This document records the independent mathematical
reconstruction of the producer's necessary domain and its rational replay
contract. The exact checker is
`computer_assisted/extraction_search_E_order_verify.py`.

**Current status:** the original E-order theorem is complete. The physical
inequalities and branch rules below have been independently reviewed,
and a fresh direct-certificate replay passed every leaf of all thirty-two
roots. Section 9 records the exact complete result. Whole fixed-mask
coverage remains a separate obligation.

## 1. Unchanged physical caller and variables

Retain the original strict `001/00` predicate in the closed disk
`R^2<=Q=1105/256`, normalized by

\[
 d=x_D-x_C\ge v=y_D-y_C\ge2/3,
 \qquad d<h_C+h_D.
\]

The four original comparisons AB, BC, EF and FG are actual. The original
five marked center-cone comparisons AB, BC, CD, EF and FG are retained.
The contrary condition being excluded is `y_E<=y_A`.

All seven original centers remain variables. Five original physical
frames, A,C,D,E,G, are retained as signed slope intervals. The other two
originals remain represented by their actual halfwidths and contained
aligned-inset halfwidths,

\[
 h_i=(\alpha_i+|\beta_i|)/2,
 \qquad g_i=1/(4h_i),\qquad i=B,F.
\]

The eighteen variables, in order, are the fourteen center coordinates,
`h_B,h_F,g_B,g_F`. The physical nonoverlap disjunctions AE, CD and DG use
both original owners and all usable side axes. Five additional inset
disjunctions BF, BE, AE, CE and DF are available. Every original pair
also retains the necessary unit lower bound on center distance. Omitting
some other original physical inequalities enlarges the necessary domain;
it does not replace any selected physical square.

The accepted left-angle bound is `|tan(theta_A)|<7/40<1/5`. Thus the
thirty-two closed angle roots, A in `[-1/5,0]` or `[0,1/5]` and each of
C,D,E,G in `[-1,0]` or `[0,1]`, cover the caller. The initial pose box
uses fourteen copies of `[-rho,rho]`, two of `[1/2,5/7]`, and two of
`[7/20,1/2]`, where `rho=91/60`. These contain the exact original variables.

## 2. Dependency order

The necessary rows use already completed proofs of the following facts:

- G lies above D; the original D/G horizontal difference lies between
  `-1459/1728` and `11/60`.
- `y_C+(7/8)x_C<-7/32` from the completed three-frame slant forest.
- The original CG vertical projections separate with reserve `97/4480`.
- The original CF insets separate vertically, and
  `y_F-y_C-|x_F-x_C|>1/25`.
- The A inset crosses the horizontal axis with reserve `3/40`.
- `h_A+h_B<R-1<69/64`, so `h_A,h_B<37/64`.
- The ordinary, universal-toll and signed physical cap inequalities,
  including the linear left A-width toll `17(h_A-1/2)`.
- The independently completed G projection table
  `GLOBAL_OUTER_LINK_EXTRACTION_G_EDGE_AND_BF_VERTICAL_HAND_TABLE.md`,
  giving `x_G-h_G<49/64`, upward BF inset clearance, and horizontal
  AE inset overlap with reserve `3/20`.

The CF theorem depends on completed F-order, whose proof did not use
E-order or a CF inset row. The slant and CG proofs precede F-order. The
signed cap is a standalone original-pair theorem. Thus this E-order
model has no dependency on the conclusion it is trying to establish.

## 3. Containment, reciprocal and interval rows

For each physical frame, let its interval halfwidth bounds be
`h^-<=h<=h^+`, and put `g^-=1/(4h^+)`. The frame's support in each fixed
direction is bounded below by the exact endpoint/sign-event formula
from the reviewed rational helper. Its original circle support inequality
is

\[
 p x_i+q y_i\le\sqrt{Q(p^2+q^2)}-H_i(p,q).
\]

The direction list is independently reconstructed: ninety-six integer
directions, followed by 128 exact rational unit-circle directions. The
latter have coordinates

\[
 \left(\pm\frac{1024-k^2}{1024+k^2},
       \pm\frac{64k}{1024+k^2}\right),\qquad0\le k\le32,
\]

with duplicates removed and a fixed rational sort order.

For pose-free B and F, each direction instead retains both center-disk
containment `p x+q y<=rho sqrt(p^2+q^2)` and the contained-inset inequality
`p x+q y+g(|p|+|q|)<=sqrt(Q(p^2+q^2))`. Every original also retains
`±x+h<=sqrt(Q)` and `±y+h<=sqrt(Q)`.

The reciprocal lower tangents are exact:

\[
 g\ge\frac1{2q}-\frac{h}{4q^2},
 \qquad q\in\{16/32,17/32,\ldots,23/32\}.
\]

The upper secant is `g+(7/10)h<=17/20`. It is the chord of the convex
function `1/(4h)` on `[1/2,5/7]`; this interval contains every actual
square halfwidth. Context propagation also intersects the free g
interval with `[1/(4h^+),1/(4h^-)]`.

The physical height cap uses `j^-=sqrt(max(0,1/2-(h^+)^2))`. If `x_*`
is a valid lower bound for `|x|`, one of the two original far-corner
types supplies

\[
 |y|\le\max\left\{
 \sqrt{Q-(x_*+h^-)^2}-j^-,
 \sqrt{Q-(x_*+j^-)^2}-h^-
 \right\}.
\]

The radical bounds are outward. A negative radical argument makes
that corner type impossible; replacing its square root by zero is safe
for this necessary maximum, and a negative final height cap is an
explicit empty interval. For intervals that themselves are already
empty, the checker first records the corresponding exact contradiction
before using any interval product.

The interval context uses only the accepted horizontal localizations,
A barrier, contrary E-height order, slant, CF height and D/G clearance.
The latter is the maximum of the two independent necessary lower bounds

\[
 g_D^-+g_G^-,\qquad
 \frac78(h_D^-+h_G^-)-\frac{41}{120}.
\]

Physical width coefficients of either sign are eliminated in the safe
direction. Every physical-inset coefficient in this model is nonnegative,
so its lower interval endpoint is the correct elimination bound. The
checker explicitly rejects a negative physical-inset coefficient.

## 4. Complete fixed row list

The row count before selected disjunctions is 2,151. The fixed blocks are:

| Block | Count | Physical meaning |
|---|---:|---|
| Coordinate and free-width/inset bounds | 36 | Two sides of all eighteen intervals |
| Direction and axis containment | 2,044 | Five full frames and two center/inset models |
| B/F reciprocal envelopes | 18 | Eight lower tangents and one upper chord each |
| Actual AB,BC,EF,FG | 4 | Original full projection widths |
| Marked AB,BC,CD,EF,FG cones | 10 | Both signed vertical comparisons |
| Geometry and cap rows | 18 | Listed below |
| Unit-center square secants | 21 | Every pair of the seven originals |

The eighteen geometry/cap rows are, in their fixed order:

1. CD inset horizontal separation.
2. `v_CD>=2/3`.
3. The necessary closed inequality `d_CD<=h_C+h_D`.
4. Contrary `y_E<=y_A`.
5. The compressed left-cap inequality involving the same C and G.
6. Both original D/G horizontal bounds.
7. The maximum D/G vertical clearance above.
8. Accepted C-slant.
9. Actual vertical CG with reserve `97/4480`.
10. CF inset vertical separation.
11. Both signed strict CF cone comparisons, weakened to reserve `1/25`.
12. The direct A/E cap with linear A-width toll.
13. Two universal right-cap/width-canceled rows.
14. Two signed positive-D right-cap/width-canceled rows, or two zero rows
    when that entire D interval is not nonnegative.

For the unit-center row, if `l_x<=x_j-x_i<=u_x` and
`l_y<=y_j-y_i<=u_y`, the identity

\[
 z^2\le(l+u)z-lu\quad(l\le z\le u)
\]

and the actual center distance at least one imply

\[
 (l_x+u_x)(x_i-x_j)+(l_y+u_y)(y_i-y_j)
 \le-1-l_xu_x-l_yu_y.
\]

Every pair difference interval is checked for emptiness before this
product is evaluated. These secants are necessary linear relaxations
of the actual center-distance condition, including both coordinate
signs.

After the chosen disjunction rows there were initially two final rows. The first
is the inherited width bound `h_A+h_B<=69/64`. The second is the
conditional signed A/E row in the next section. Thus a leaf with m
chosen separating branches initially had `2153+m` possible row indices.
After the complete G projection theorem and its independent replay,
seven necessary rows were appended without changing any earlier row,
context interval or secant coefficient:

1. `x_G<=49/64+h_G^+`.
2. `y_E-y_A<=-g_A^--g_E^-` in this contrary E-order caller.
3. Both signed comparisons `y_E-y_A±(x_E-x_A)<=-3/20`.
4. `y_B-y_F+g_B+g_F<=0`, retaining the two free inset variables.
5. `y_B-y_F+x_F-x_B<=-1/7104`.
6. The signed A/E cap whenever A's whole slope interval is nonnegative.

There are now exactly `2160+m` possible row indices. Every earlier
valid multiplier list can be extended by zero on the seven new rows.

## 5. Conditional signed A/E strengthening

Suppose the entire A slope interval is nonnegative, and a chosen
**actual original A/E owned separator** has a certified strictly negative
vertical component. Reflect the entire physical pair in `y=0`.
A then has negative chirality, the same separator points upward, and
the left-cap load is unchanged. The accepted signed-main theorem gives

\[
 46(-x_A-h_A)+\frac{27}{2}(-x_E-h_E)
 +46(\alpha_A-1)+\frac{529}{16}\beta_A\le\frac{211}{4}.
\]

Writing

\[
 K_A=\min_{\theta_A\text{ in the interval}}
       \left(\frac{\alpha_A}{2}+\frac7{32}\beta_A\right)
\]

and collecting the same physical A width gives the necessary row

\[
 -46x_A-\frac{27}{2}x_E
 \le\frac{211}{4}+46-46K_A+\frac{27}{2}h_E^+.
\]

The activation test is exact and applies to a selected AE SAT owner.
An inset separator, a center-height order, or a numerical midpoint
normal alone never activates this row. It is replaced by `0<=0` when
its premise is not certified. The same signed cap may alternatively
be viewed after a half-turn as the accepted positive-main right cap.

For the later globally activated row, the completed G projection
theorem supplies `|x_E-x_A|<17/20`. Together with `y_E<y_A` in this
contrary branch, it proves that every actual owned separator points
downward. Existence of such a physical separator follows from original
nonoverlap. Thus the appended signed-cap row has its full physical
premise even before an AE SAT branch has been selected. The older
selection-dependent row and its indices are preserved unchanged.

## 6. Owned-axis and inset unions

An inset pair has all four horizontal/vertical signed separating
possibilities. Each uses the actual contained inset, with the same
free or interval physical halfwidth already used elsewhere.
The completed G projection theorem proves that AE's sole surviving
inset direction in this caller is E below A, and BF's is F above B.
Their other three inset alternatives are therefore individually
excluded before the remaining physical branch is visited.

For an original physical pair, the checker begins with both owners,
both side axes and both signs. It permits only the following proven
omissions:

- CD: negative axis signs, and the positive steep axis of an owner
  whose entire canonical slope interval is nonnegative, are excluded
  by the accepted strict-weak cone separator-sign theorem. In addition,
  the complete all-tilts upward-normal theorem excludes every option
  whose exact upper y component is nonpositive, since this caller has
  `v>=2/3>=1/2`. This excludes the positive shallow axis of a negative
  owner even when its interval includes the aligned endpoint.
- DG: a normal whose exact upper y component is nonpositive is
  unusable, because G lies above D, `|x_G-x_D|<1`, and the physical
  support sum is at least one.
- AE: the completed overlap theorem gives `|x_E-x_A|<17/20` and,
  in this contrary caller, E below A. Thus every actual owned separator
  points downward. An option with exact lower y component nonnegative
  is impossible. This also supplies the physical premise for the
  globally activated signed-A row among the seven appended rows.

Every missing branch must be justified individually by these exact
predicates, with both original owners considered. The floating
producer was corrected to use the zero threshold for the DG omission;
an epsilon around zero is not a proof of an impossible normal.

When packing an older discovery subtree, a child whose original owned
normal is now proved impossible may be removed at its parent interval
before its descendants are read. The parent omission is rechecked by
the exact full replay. This safely discards partial work below a proved
impossible physical option; no unresolved admissible branch is removed.

For a selected normal, the checker constructs a dyadic midpoint at
denominator `2^30`. The exact normal error is bounded against the
same physical pair's difference intervals. Its row is

\[
 \bar n\cdot(c_i-c_j)
 \le-\underline{H_i(n)+H_j(n)}
       +\sum_{k=x,y}\max\{e_kd_k\}.
\]

The support lower bound and the interval products are rational and
outward. Neither the producer's floating support nor its claimed
right-hand side is trusted.

## 7. Forest and arithmetic contract

Angle splits retain both closed midpoint children. Pose splits retain
both closed children at the recorded rational cut `integer/2^20`,
strictly inside the parent pose interval. Selected pairs may occur in
any adaptive order, but no pair/disjunction may be selected twice.
Every leaf's exact angle and pose intervals are reconstructed from
its root and path, not from serialized floating boxes.

A positive Farkas leaf supplies positive integer weights at a common
denominator `2^40`. The checker independently reconstructs every used
row, sums all eighteen residual coefficients, and accepts only when

\[
 -\sum_i\lambda_i b_i
 -\rho\left\|\sum_i\lambda_i a_i\right\|_1>0.
\]

All eighteen original variables have modulus less than rho, so this
strict rational reserve is a contradiction. No approximate dual
equality, optimizer lower bound, unverified variable box, or numerical
unsatisfiability status is used. Exact empty-width, empty-coordinate
and empty-difference leaves are separate explicit terminals.

The checker imports only the exact Fraction support/radical helpers
from `weak_outer_hand_right_lower_verify.py`; the final report binds
both exact source hashes and the certificate hash. Its optional
candidate-arithmetic mode is explicitly labeled
`PARTIAL_LEAF_ARITHMETIC_PASS` and never claims root coverage.

As an implementation consistency check, all reconstructed initial row indices
were compared with the numerical producer on five root/sign
controls, including the conditional AE cap and a selected inset branch.
All 2,157 initial rows in each control matched within the numerical discovery
precision. That comparison is not a mathematical proof premise.
After the seven appended G-projection consequences, three signed-root
controls compared all 2,164 rows (including four selected disjunctions)
and every exact physical/inset option union against the updated producer;
all agreed. The mathematical source review and complete exact forest
coverage remain the proof obligations.
Section 9 records the subsequent complete replay of all thirty-two
roots and every retained physical branch.

## 8. Partial candidate arithmetic checks

Both finalized-row pilot lists have now passed fresh exact arithmetic
checks, using the independent path and row reconstruction:

| Pilot | Candidate leaves | Exact empty-interval candidates | Remaining discovery frontier |
|---|---:|---:|---:|
| Nonnegative-A pilot | 5,194 | 0 | 14 |
| Nonpositive-A pilot | 4,996 | 3 | 26 |

Every other candidate had a strictly positive exact rational Farkas
reserve. The helper hash in both runs was
`c3c66a1fcfca7d2e0acd8d9b5a32340f8e8d2253e5e802ff1be34f5cbd0e109f`.
These are candidate checks only: neither run supplies a complete
root union, and both reports explicitly set `whole_domain_proved=false`.
At that checkpoint, discovery and full coverage were still outstanding.
They have since been completed as follows.

## 9. Complete independent forest replay

The author supplied the frozen packed certificate
`computer_assisted/weak_outer_hand_E_order_certificate.json.gz`.
I checked its announced hash and both exact-source hashes, then ran a
fresh direct-certificate replay with the independent checker. All hashes
were unchanged after completion. The separate report is
`computer_assisted/extraction_search_E_order_independent_exact_replay.json`.

The complete result is:

| Quantity | Exact replay result |
|---|---:|
| Closed orientation roots | 32 |
| Nodes | 96,219 |
| Terminal leaves | 48,376 |
| Positive rational Farkas leaves | 48,373 |
| Exact empty-interval leaves | 3 |
| Angle splits | 40,034 |
| Closed pose splits | 5,450 |
| Physical/inset separator splits | 2,359 |
| Maximum depth | 47 |
| Unresolved frontier | 0 |

The least exact reserve is strictly greater than
`453293/1000000000000`. The critical bindings are:

| Object | SHA-256 |
|---|---|
| Complete certificate | `40652b9d74badfe6af54c22c038f7995aeb32c165a042f2303cdf0f1b3c61d31` |
| Exact E-order verifier | `ada5283d34ddc7ea5f6084a626ffc3428a823d82c675cd95bd796f5ba8df8c3b` |
| Exact support helper | `c3c66a1fcfca7d2e0acd8d9b5a32340f8e8d2253e5e802ff1be34f5cbd0e109f` |

Every root, closed split, retained original owner and sign, exact
omission, interval terminal and Farkas reserve passed. In particular,
no raw discovery frontier, approximate LP optimum or favorable
midpoint configuration is used as evidence of coverage. The table
contradicts the original contrary condition `y_E<=y_A`. Therefore

\[
                              y_E>y_A
\]

holds throughout the unchanged original strict `001/00` caller with
`R^2<=Q` and `v_CD>=2/3`.

The new hand consequences are also independently accepted. The original
AE insets now separate upward, so the earlier A barrier gives
`y_E-g_E>3/40` and hence `y_E>17/40`. The unchanged BC cone and accepted
C-slant give

\[
 y_B\le y_C+x_C-x_B
 <-7/32+x_C/8+31/60<191/480,
\]

using `x_C<4/5`. Consequently `y_E-y_B>13/480`. These comparisons
retain the original E,B,A squares and complement the completed upward
BF and CF inset relations. They do not by themselves discharge the
remaining two-extra-square placement obligation or the whole mask.
