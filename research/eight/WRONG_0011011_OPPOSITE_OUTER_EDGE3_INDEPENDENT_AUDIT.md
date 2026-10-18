# Independent review: the whole opposite-sign outer edge 3

**PASS.** The two author components prove the entire outer/outer
edge-3 (negative source, positive target) row of word `0011011`:

\[
 \phi-T(b)-L(B)>.89777>.89765,
 \qquad 0\le b,B\le d,\quad |\phi-\pi/2|\le.7,
\]

whenever any of the four retained signed SAT inequalities holds.
The reflected edge-5 row follows from the already stated role symmetry.
This review asserts the pair theorem and its exact role binding; it does
not silently assert the subsequent whole-word cyclic assembly.

The reviewed manuscripts are
`WRONG_0011011_EDGE3_OPPOSITE_AXES12_HAND_PROOF.md` and
`WRONG_0011011_EDGE3_OPPOSITE_AXES34_HAND_PROOF.md`.
The companion `audit_wrong_0011011_opposite_outer_edge3.py` is portable
to the flattened `research/eight` layout. It records hashes of both
manuscripts, both author checkers and reports, and the shared label table.

## 1. Exact signed geometry and monotone contact reductions

I independently substituted the source sign \(-1\), target sign \(+1\)
into all four signed SAT expressions. The four formulas in the axes12
manuscript are correct, including their different signs in the upper
and lower quarter halves. The two labels match exactly the shared table's
role-3 `O-` and role-4 `O+` coefficients, with denominator \(100000\).

Both labels increase. Their derivative bounds follow from the displayed
circle derivative formulas, the positive increasing third derivatives,
endpoint convexity of the first derivatives, and the indicated square
completions. Consequently every reduction to a largest transverse
coordinate or smallest primary coordinate decreases the cost in the
claimed direction.

The lower secondary contacts have the compact domain
\((b+3/2)^2+(B+1/2)^2\le Q\), or its swapped version. Their angle
is below \(.571\), so the original \(.7\) angle cap creates no
unlisted boundary. The upper secondary contacts have transverse
coordinate below \(.543<d\), so they have no missing diagonal clamp.
For the derivative upper bound used there, if the transverse coordinate
is below \(.5\), the derivative is already negative; otherwise it is
at most that coordinate minus \(.5<.4\). Thus the uniform \(.4\)
bound used in the cost estimate is valid over the entire domain.

The common zero-exit proof is also valid. Separate concavity and its four
corner comparisons exclude all later roots in \([.31,.7]\). On the
early branch the denominator in its implicit derivative is positive,
the numerator exceeds \(.5\), and the denominator is below \(.4\).
Its slope therefore exceeds \(1.25\), which dominates either label
slope. Both zero exits reduce to their aligned endpoint.

## 2. Axes 1 and 2

The inverse-contact derivatives in axes12 equation (10) were rederived
directly from
\[
 z=(u-1)\cos x-y\sin x,
 \quad u^2+y^2=Q,
 \quad q=Q+1-2u,
 \quad v^2=q-z^2.
\]
In particular the negative mixed derivative is \(-r/v^3\), and the
large-coordinate second derivative has exactly the signs printed in
that manuscript.

For lower axis 1, the small rectangle lies strictly inside the contact
domain. The five Hessian bounds make the Hessian exceed \(.01I\).
The rational reference point and gradient bounds therefore give the
claimed strong-convexity lower bound over the entire rectangle.
Outside it, the source derivative excludes the stated stationary
points, the three middle target bounds exclude simultaneous stationarity,
and the negative target curvature excludes every remaining interior
minimum. All three boundary types of the quarter-disk are explicitly
covered. This is a complete compact-domain minimum argument.

The two aligned contact bounds have the correct derivative signs.
For the first, the third-derivative rows make the second derivative
decrease to its positive final value. For the second, all factors in its
stated endpoint lower estimate move in the required directions because
the target argument is at most \(a_0-1<.415\), where its second
derivative is negative.

Lower axis 2 has a positive primary-coordinate speed, and the squared
speed identity uses the source circle exactly. Its label slope lower
bound is sufficient to force cost increase away from alignment.
For upper axis 2, the inactive diagonal portion reaches the active
boundary before the source diagonal. The displayed inverse derivatives
have the correct plus sign. The source motion decreases both cost and
angle until alignment or the small-source strip. In that strip the
angle cap is inactive, and fixed-source concavity in the target
coordinate reduces the minimum to precisely alignment or the target
diagonal. The complete target-diagonal proof includes its small
strongly convex interval and both monotone continuations.

## 3. Axes 3 and 4

For lower axis 3, minimization in the target transverse coordinate is
strictly convex. The derivative at zero is negative, while the aligned
endpoint derivative decreases strictly and has its unique zero between
\(.5\) and \(.6\). Therefore the unique interior critical curve exits the
physical domain only at the stated aligned boundary.

I rederived its defining equation
\(S(B)=(B+.5)^2+L'(B)^{-2}=q(b)\), the slope
\(B'=r/(z-L''v^3)\), all four third partial derivatives, and the
reduced derivative identity
\[
 R'''=C_{bbb}+3C_{bbB}B'+3C_{bBB}(B')^2+C_{BBB}(B')^3.
\]
The terms involving \(B''\) cancel because \(C_B=0\) and
\(C_{bB}+C_{BB}B'=0\). No unproved stationary-point approximation
enters this identity.

The six fixed critical-curve brackets lie in the range where \(S'>0\).
They also define the same smooth continuation through \(b=.6\),
slightly beyond the physical exit. Their negative reduced third
derivatives imply that \(R''\) decreases. The positive bound for
\(R''(.5)\) gives strong convexity on \([0,.5]\). On the final
interval, \(R'\) is concave and starts positive; its nonnegative
superlevel set is an interval. Hence \(R\) has no interior minimum
there. Both resulting endpoints were already proved. This establishes
the entire lower axis-3 case, not only a neighborhood of its low point.

The primary-label bounds for axis 4 were independently rederived from
\(M'=T'/r\). The second derivative of \(T'-m r\) has the stated
linear numerator; its global sign justifies both the lower
square-completion bound and the endpoint-based upper bounds.
Lower axis 4 therefore increases away from alignment.

For upper axis 4, the derivative of the projection-speed quotient with
respect to the angle is exactly \(-r/v^2\). The three fixed
concavity rows and two positive endpoint values imply the whole
target-coordinate derivative is positive when \(B\ge.2\).
Decreasing that coordinate preserves the active contact and decreases
the angle until alignment or \(B=.2\). In the remaining strip, the
two squared product estimates force positive angular cost derivative.
The inactive source-diagonal part has derivative one. Thus its entire
minimum flows to the aligned contact already proved in axes12.

## 4. Independent arithmetic evidence

Both author checkers were copied to isolated temporary directories.
Their fresh outputs contain respectively **108** and **83** strict
comparisons and reproduce their frozen JSON reports byte for byte.

A separately written rational interval calculation additionally passed
**36** fixed comparisons. It uses binary square-root brackets of width
\(2^{-100}\), rather than either author's decimal-root implementation.
It independently reconstructs every one of the six critical-curve
brackets and negative third-derivative rows; checks the five shifted
Hessian determinants; evaluates the three low nonaligned geometric
reference poses with independent arctangent bounds; and verifies the
square completions and primary-speed products. Its displayed reserves
are rounded downward to a rational mesh only after their positivity
has been established exactly.

No correction was required for these two manuscripts. The earlier sign
repair in the different `(-- )` row is unrelated to this reviewed pair.
