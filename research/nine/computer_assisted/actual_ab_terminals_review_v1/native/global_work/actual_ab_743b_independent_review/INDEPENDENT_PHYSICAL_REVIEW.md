# Independent review of the two new actual-AB terminals

Reviewed November 5, 2026 against the exact files restored from commit
`743b768c3de1853b8524be8bba4064c5735e9cbc`. This review checks physical
lifting, scalar-source attachment, equality, and application scope. It does
not rerun the complete scalar covers, install either terminal, or close a
registered original or mask. Root separately ran both complete exact covers.

## Result and exact hypotheses

Both physical derivations are sound at their stated conditional scope. In
each theorem the selected A,B,X,D,E,F,G are seven distinct original unit
squares; their original frames, corners, and physical pairs are retained.
The caller has actual horizontal AB, EF, and FG projection links and the
order `x_B <= x_X <= x_D`. All canonical angles lie in `[-pi/4,pi/4]`.

| Terminal | Vertical variation | Additional endpoint hypotheses |
|---|---:|---|
| `actual_AB_two_link_row_064_v1` | `|y_X-y_B|+|y_D-y_X| <= 16/25` | `theta_D >= 0`, `y_G >= y_D`, and the strict guard `|x_G-x_D| < 1` |
| `universal_actual_AB_two_link_v1` | `|y_X-y_B|+|y_D-y_X| <= 21/100` | None |

For either terminal all original corners in squared radius `q` imply
`q >= Q = 1105/256`. If `q=Q`, the theorem forces A,B,X,D aligned and
`x_D-x_A=3`. Original H or I can serve as X in the nine-square caller;
the two omitted originals remain physical. Distinctness is part of the
statement, so this review does not authorize identifying X with F or an
endpoint.

## Endpoint caps and their signs

The universal cap in `UNIVERSAL_MAIN_ENDPOINT_TILT_TOLL.md` is an original
physical pair theorem for arbitrary original frames and either genuine
separator owner. Its normalized main-endpoint toll is exactly

`T_u = max(2|beta|/23, 5|beta|/23 - (1-alpha))`.

Applying it to A,E and after a pi rotation to D,G gives the two printed
weighted caps for the universal terminal. The main and shoulder weights
are respectively 46 and 27/2. Their sum, using the actual EF/FG links and
`2h_F >= 1`, gives

`x_D-x_A-h_A-h_D + T_u(D)+T_u(A) <= 2`.

The arithmetic is `(2*(211/4) - 27/2)/46 = 2`. Each pair cap is strict
when `q<Q`, since replacing the actual circle radius by `sqrt(Q)` costs a
strictly positive sum of support-direction lengths. No orientation, side,
height, or D/G corridor assumption enters the universal cap.

For the 16/25 theorem, the D/G guards force every genuine separating normal
from D to G to have strictly positive vertical component. If `n_y <= 0`,
then `n dot (c_G-c_D) <= |x_G-x_D| < 1`, whereas an owned unit normal of
two physical unit squares needs support at least one. A pi rotation sends
this normal downward and keeps the canonical D angle unchanged, so the
accepted oriented cap applies with

`T_g(D) = 55|beta_D|/64 - 119(1-alpha_D)/92`.

The source's strict normal hypothesis is satisfied even though `y_G>=y_D`
is closed. In particular its horizontal-normal limiting faces do not
justify weakening the strict horizontal guard. The universal A/E cap
remains unchanged, and gives the same combined inequality with `T_g(D)`.

## Every physical row separator is retained

On either pair D/X or X/B, let `d>=0` be the horizontal separation in the
ordered row and `v` its vertical separation. The disjoint open half-unit
incircles imply `d^2+v^2 >= 1`. The relevant variation bound `w` satisfies
`|v| <= w` and `2w^2 < 1`: the two exact values are `512/625` and
`441/5000`. Thus `d>|v|` and `d>0`.

In a genuine owned separator the support sum is

`R_ij=(1+cos(theta_i-theta_j)+|sin(theta_i-theta_j)|)/2 >= 1`.

The cosine is nonnegative on the physical canonical-angle domain. A normal
whose horizontal component is nonpositive has projection at most `|v|<1`
and cannot separate. A shallow forward owned normal has projection at
most `alpha*d+|beta|*|v|`. For a steep forward normal the same upper bound
follows because `(alpha-|beta|)*(d-|v|)>=0`. This retains both axes,
signs, owners, and zero-angle faces and proves the printed bound

`d >= R_ij/alpha_owner - |tan(theta_owner)|*|v|`.

Actual AB supplies `h_A+h_B` without a vertical error term. No actual BC
edge is used in this seven-square inequality.

## Scalar attachment, complete domain, and strictness

The new checkers' dot-product and determinant polynomials reconstruct
exactly the displayed scalar C and the target slopes 641/1000 and 211/1000.
The common positive denominator is `product(1-x_i^4)`, with scale 736000.
For each owned pair the denominator cancellation leaves
`(1+x_owner^2)*(1-x_other^2)` times the unused factors, as in the checker.
The selected-slope numerator is respectively `-(641/500)*x_k` or
`-(211/500)*x_k` times those factors. These factors account for the two in
`|tan(theta_k)|=2x_k/(1-x_k^2)`.

For the good cap, `T_g-h_0` has scaled numerator
`-368000 + 529000*x_0 - 1536000*x_0^2`. For the universal cap the two
lower branches have scaled numerators
`-368000 - 416000*x_0 - 1104000*x_0^2` and
`-368000 - 608000*x_0 + 368000*x_0^2`. These match the reconstructed
formulas. Each universal branch is a lower bound on the max toll
everywhere; choosing one at a leaf adds no physical assumption.

The rational root intervals contain every canonical angle:
`sqrt(2)-1 < 29/70` follows from `99^2 > 2*70^2`, and
`sqrt(2)-1 < 5/12` follows from `17^2 > 2*12^2`. Both upper endpoints
are below one. The formal rational extension beyond the physical angle
range does not narrow the physical caller.

There are four sign patterns, four owner patterns, and all distinct
selected owners, giving 28 complete domains. The universal theorem may
take theta_D nonnegative in this scalar argument because simultaneous
angle reflection preserves C and every absolute tangent. This is a
scalar identity and imposes no orientation normalization on the caller.

The weighted signed polynomials are lower bounds on the absolute-value
polynomial. Strictly positive Bernstein coefficients prove strictness
on every non-origin leaf. On an origin leaf only the origin coefficient
may vanish; every nonzero point, including a closed face, has a positive
non-origin basis term. Consequently all three row angles must vanish at
equality, even if the selected owners alone happen to have zero angle.

The delivered report and per-domain hashes are checked in the accompanying
source audit. This review reads the complete checker logic but does not
claim to repeat its 121/351 leaf arithmetic. Root's fresh complete runs
and its separate damaged-input controls are additional evidence, not
silently included in this receipt.

## Equality and exact caller scope

Let M be the maximum selected absolute tangent. For either theorem,
subtracting the permitted variation from the scalar slope leaves exactly
`M/1000`. Summation gives the cap load at least `2+M/1000+T_u(A)`.
Below Q this contradicts the strict cap. At Q, the scalar strictness
forces D,X,B aligned, and `T_u(A)>=2|beta_A|/23` then forces A aligned.
Each remaining pair has vertical difference less than one, so aligned
square separation is horizontal. The cap and the three unit horizontal
gaps force `x_D-x_A=3`.

The unchanged nine-square `001/00` caller has actual AB and BC, the CD
center cone, and strictly weak CD. Its original inset separation yields

`3 >= h_A+2h_B+h_C+g_C+g_D = 1+2h_B+h_C+g_C >= 3`,

where `g_C=1/(4h_C)` and
`h_C+g_C-1=(2h_C-1)^2/(4h_C)>=0`.
Equality aligns C and gives `x_D-x_C=h_C+h_D=1`, contradicting the
strict weak bit. This is the required analytic equality-face blocker,
not an assumed numerical reserve.

For a fresh `011/00` caller, actual AB/EF/FG still meet the seven-square
theorem. Its strict-radius assumption contradicts `q>=Q` under the
quantitative guards. BC is weak in that mask, so this review expressly
does not attach the closed-Q `001/00` blocker to `011/00`.

Without a proved right order for X, a complete application retains six
closed complementary domains: `x_X<=x_B`, `x_X>=x_D`, and the four signed
forms of W at least the threshold. With a same-caller proof of `x_X<x_D`,
the right-order domain is unnecessary and five remain. Shared faces are
included. Using H or I is an alternative terminal for the same caller,
not permission to discard any complementary domain.

## Replay and installation limits

Both independent scalar checkers are standard-library exact arithmetic
and reject optimized Python. Their scalar reports deliberately require
separate physical lifting. The checkers do not themselves establish the
seven-square physical caller, the literal guards, unchanged nine-square
ancestry, or hashes of their external physical-cap dependencies. Actual
use must bind those inputs and a fresh accepted complete scalar replay.
The 16/25 monotonic restriction of A-c744's old components is valid only
with that exact same-original ancestry; it grants no transport between
registered originals. No runtime, fixed register, or proof ledger was
changed by this review.
