# Independent review: mixed-01 gap monotonicities

Date: October 26, 2026.

Reviewed source: `SIX_CYCLE_MIXED_01_GAP_MONOTONICITIES.md`.

**Verdict: accepted as three full-domain analytic monotonicity lemmas.**
The source accurately leaves directional monotonicity on
`c_0+c_1=1` and the final orbit exclusion unproved. This review does
not fill that separate gap or close any original gate.

## Physical scope and the Cauchy reduction

The numerator, all three force norms and the force normalization agree
with the original mixed `110` placement-01 model. The two-dimensional
triangle inequality and Cauchy lower bound eliminate the full positive
`q` interval pointwise; no optimizer or special value of that physical
force is assumed. Every shared mean, physical mask, transmitter and
extra square is retained through the cited exact closure source.

The consequence `c_0>3/10` follows correctly from the strict angular
inequality and the decreasing function `L`. The stated squared reserve
is positive. For `c_2>7/15`, concavity of sine minimizes the sum of
the first two sines at the endpoints for a fixed angle sum. The
resulting `s_2-c_2<=sqrt(2)-1` and the four fixed radical/rational
comparisons prove the strict third-angle bound. Neither consequence
drops a shared-mean endpoint by assumption.

## Derivatives and signs

Direct differentiation of `w`, `v`, `U_0`, `U_2`, and `D_1`
reproduces equations (8), (14), and (17) of the reviewed source.
In the first derivative, `w s_0-v c_0>0` and
`w s_2-v c_2>0` hold on the entire closed angle domain, since
`w>v>0` and each indicated sine is at least its cosine. Thus the
case distinction on `U` is exhaustive, and `U>0` indeed forces
`v>t_0`. Every division in the estimate of `U/V` is by a positive
quantity. The last quadratic has positive leading coefficient and
negative discriminant, giving strict negativity of the first angular
derivative even at `p=3/2`.

For the force derivative, the separately concave rectangle function
has its minimum at a corner after successively applying the two
one-dimensional chord inequalities. The four corner estimates cover
the full rectangle. The auxiliary ratio
`(p+c)/sqrt(p^2+2pc+1)` is increasing in `c>=0`, and
`p/sqrt(p^2+1)` is increasing in positive `p`; these observations
justify the uniform `17/10` lower bound used in Section 4. The
sum with the `13/10` support bound makes the derivative strictly
positive.

For the second angular derivative, the bound `c_0>3/10` gives
the claimed `w>11/3` and `v<3/2`, hence `J_2>3/2`.
The two displayed positive-force ranges cover every `p>=1+r`,
including their common endpoint `9/4`. The concave quadratic on
`[3/2,9/4]` has the stated two positive endpoint values. All
inequality directions in the estimate of the first two terms of the
derivative are correct. The strict bound on `J_2` then makes the
complete derivative negative in both ranges.

## Exact arithmetic and remaining logical boundary

All twelve displayed rational evaluations used for the derivative
bounds and rectangle-corner checks were independently recomputed with
exact rational arithmetic. They agree with the manuscript, including
the three support-corner values, the comparison for `K`, and the
`w` and `v` reserves. This is an audit of the finite arithmetic in
the analytic proof, not an extra computational proof dependency.

The final section correctly distinguishes coordinate monotonicity
from monotonicity along a constraint boundary. Increasing both angles
is not allowed past `c_0+c_1=1`, and no directional derivative sign
is inferred from the two separate negative partial derivatives.
The fixed endpoints in `SIX_CYCLE_MIXED_01_CAUCHY_AND_ENDPOINTS.md`
can be used only after a complete valid boundary argument is supplied.

No Lean compilation, CI, numerical optimization premise, interval
grid, coefficient packet, or physical-force reassignment was used in
this review.
