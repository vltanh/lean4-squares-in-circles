# Independent geometric audit of the four-type dyadic pair verifier

Audited source: `verify_fourtype_pairs.cpp` as read on 2026-10-17. This note audits the formulas and interval logic. It does not substitute for successful completion of every required closed pair branch, nor does it independently prove the finite type-graph budget.

## 1. Exact boundary parametrization and monotonicity

Write \(t=|\tan\alpha|\in[0,1]\) and \(a=r\cos\alpha>0\). In a square's own frame its center has coordinate magnitudes \((a,ta)\). A unit square is contained in the disk with squared radius \(Q=9789/2500\) precisely when its farthest vertex satisfies

\[
(a+1/2)^2+(ta+1/2)^2\le Q.
\]

On the outer boundary equality holds. The positive root is

\[
a_+(t)=\frac{\sqrt{(1+t)^2+4(1+t^2)(Q-1/2)}-(1+t)}{2(1+t^2)}.
\]

Implicit differentiation gives

\[
a_+'(t)=-\frac{a(ta+1/2)}{(a+1/2)+t(ta+1/2)}<0.
\]

For the boundary of the radius-\(1/12\) forbidden core, the side branch is

\[
a_-(t)=7/12,\qquad 0\le t\le6/7.
\]

For \(6/7\le t\le1\), the corner branch is the larger root of

\[
(a-1/2)^2+(ta-1/2)^2=1/144,
\]

namely

\[
a_-(t)=\frac{(1+t)+\sqrt{(1+t)^2-4(1+t^2)(71/144)}}{2(1+t^2)}.
\]

On this branch \(a\ge ta\ge1/2\) and

\[
a_-'(t)=-\frac{a(ta-1/2)}{(a-1/2)+t(ta-1/2)}\le0.
\]

The denominator is positive because the core radius is positive. The companion derivative

\[
(ta)'=\frac{a(a-1/2)}{(a-1/2)+t(ta-1/2)}\ge0
\]

also confirms that the corner branch remains in \(ta\ge1/2\) after the transition.

At \(t=6/7\), the discriminant is exactly \(1/36\), and the larger-root formula gives \(a=7/12\), \(ta=1/2\). The two branches agree, and the corner derivative is zero at the transition. Therefore `local_a` may safely enclose a whole interval by taking the lower endpoint of the point enclosure at its largest \(t\) and the upper endpoint of the point enclosure at its smallest \(t\).

The code encloses \(6/7\) by outward dyadic endpoints. Its conditional branches therefore cover the exact transition. There is no omitted open endpoint.

## 2. Scaled actual SAT projections

Now allow signed \(t=\tan\alpha\) and \(u=\tan\beta\) in \([-1,1]\). Let \(a\) and \(b\) denote the local positive center coordinates of the source and target states. Put

\[
A=1+t^2,\quad B=1+u^2,\quad Z=\sqrt{AB},\quad K=1+tu,\quad L=u-t,
\]

and let \(\delta\in(3/5,\pi)\) be their positive center-angle gap. The source center is at \((r_a,0)\), its frame angle is \(\alpha\), the target center is \((r_b\cos\delta,r_b\sin\delta)\), and its frame angle is \(\delta+\beta\). The relative frame angle is

\[
\phi=\delta+\beta-\alpha.
\]

Writing \(C=\cos\delta\), \(S=\sin\delta\), the angle-addition identities give

\[
Z\cos\phi=KC-LS,\qquad Z\sin\phi=KS+LC.
\]

Thus the actual common pair-support width is

\[
w=\frac{Z+|KC-LS|+|KS+LC|}{2Z}.
\]

Let \(P_1,P_2,P_3,P_4\) be the center displacement projected on the source's first and second side normals and the target's first and second side normals. With \(V=bB\), \(W=aA\), their scaled values are exactly

| Axis | \(ZP_j=X_jC+Y_jS+C_j\) |
|---|---|
| source first | \(V C+Vt S-aZ\) |
| source second | \(-Vt C+V S+atZ\) |
| target first | \(-W C+Wu S+bZ\) |
| target second | \(Wu C+W S-buZ\) |

These agree with all entries of `g.X`, `g.Y`, and `g.C` in the source. No canonical-owner restriction is substituted for actual SAT: all four axes and both projection signs are retained.

For each signed projection \(\varepsilon P_j\), the scaled SAT margin is

\[
2Z(\varepsilon P_j-w)
=2\varepsilon(X_jC+Y_jS+C_j)-Z-|KC-LS|-|KS+LC|.
\]

Using \(-|x|-|y|=\min_{s_c,s_s\in\{-1,1\}}(-s_cx-s_sy)\), this equals the pointwise minimum of the four linear trigonometric expressions with coefficients

\[
\begin{aligned}
X'&=2\varepsilon X_j-s_cK-s_sL,\\
Y'&=2\varepsilon Y_j-s_sK+s_cL,\\
C'&=2\varepsilon C_j-Z.
\end{aligned}
\]

These exactly match `sat_upper`. For a whole parameter box, the minimum of four separately valid upper bounds remains an upper bound for this pointwise minimum. The later maximum over the eight signed projections is also safe. If `sat_upper<0`, every actual SAT alternative fails throughout that box and gap interval.

## 3. Monotone cost contraction

For fixed states define the width excess

\[
u(\delta)=\frac{|\cos\phi|+|\sin\phi|-1}{2}.
\]

It satisfies \(0\le u\le(\sqrt2-1)/2\). After reducing \(\phi\) modulo \(\pi/2\), its derivative away from the finitely many corners is \((\cos\phi-\sin\phi)/2\), so \(u\) is globally \(1/2\)-Lipschitz. Hence

\[
f(\delta)=\delta-\frac9{50}u(\delta)+\psi_b-\psi_a-\gamma
\]

is strictly increasing, with every secant slope at least \(91/100\).

The initial upper bound in `delta_upper` is an outward upper enclosure of

\[
\gamma-(\psi_b-\psi_a)+\frac9{50}\frac{\sqrt2-1}{2}.
\]

Every state in the parameter box has nonnegative cost at or above this bound. If the interval lower bound for `cost_at(mid)` is nonnegative, every state has nonnegative cost at \(\delta=\mathrm{mid}\), and monotonicity justifies lowering the upper bound to `mid`.

The lower bisection endpoint need not be a verified negative-cost point: it is only a search aid. The rejection step continues to cover the entire gap interval from the outward lower enclosure of \(3/5\) to the certified upper bound. Thus no possible negative-cost gap is removed by an inconclusive midpoint evaluation.

If the final upper bound lies below that lower endpoint, no actual gap \(\delta>3/5\) can violate the desired inequality. Otherwise all gaps that could have nonpositive cost are covered by `reject_all_gaps`. The latter accepts a box only when every closed gap subinterval has a strictly negative SAT upper bound.

## 4. Maximizing a linear trigonometric expression

All inspected gap intervals lie in \([3/5,5/2]\), which is inside \((0,\pi)\) and has length less than \(\pi\). Thus \(\sin\delta>0\). For interval coefficients, replacing the sine coefficient by its upper endpoint is safe. If the whole interval lies below \(157/100<\pi/2\), replacing the cosine coefficient by its upper endpoint is also safe. Otherwise maximizing the two scalar problems corresponding to its lower and upper endpoints covers both signs of \(\cos\delta\). Replacing the constant term by its upper endpoint is always safe.

For fixed real coefficients \(x,y\), set \(F(\delta)=x\cos\delta+y\sin\delta\). Its derivative zeros are separated by \(\pi\), so the interval contains at most one unless \(x=y=0\), which is harmless. If an interior maximum exists, its value is \(\sqrt{x^2+y^2}\), its left endpoint derivative is nonnegative, and its right endpoint derivative is nonpositive. Therefore the code may exclude that candidate maximum only when the exact interval derivative enclosures rule out one of those necessary signs. Otherwise adding an outward enclosure of \(\sqrt{x^2+y^2}\) safely bounds it. Endpoint values cover every remaining case, including a stationary endpoint.

This proves the maximum logic in `scalar_trig_max` and `trig_max`. It does not rely on sampled angles or approximate root selection.

## 5. Arithmetic scope checked

The included base uses \(2^{-48}\) dyadic outward rounding, signed 128-bit products, corrected integer square roots, and alternating Taylor enclosures for sine and cosine. At argument magnitude at most \(5/2\), the omitted Taylor tails after degrees 16 through 19 have decreasing magnitudes, so the chosen truncation signs give valid upper and lower bounds. The floating-point square-root seed is corrected by exact integer inequalities.

The new geometric formulas only use \(|t|,|u|\le1\), \(1\le A,B\le2\), \(1\le Z\le2\), and \(0<a,b<3/2\). Their coefficients and all intermediate quantities are far below the signed 64-bit scaled range of magnitude \(2^{15}\), and their products are within the signed 128-bit range. A production certificate should retain explicit parameter validation and ideally executable range checks; no numerical floating-point branch determines acceptance in these formulas.

## 6. Directed sign and type coverage

Reflection followed by source/target reversal sends a positive-gap state pair

\[
(\tau_a,\alpha;\tau_b,\beta;\delta)
\quad\longmapsto\quad
(\tau_b,-\beta;\tau_a,-\alpha;\delta).
\]

It preserves the geometric SAT problem and the width. Since the potential is odd, the potential difference also remains unchanged:

\[
\psi(-\alpha)-\psi(-\beta)=\psi(\beta)-\psi(\alpha).
\]

Together with a symmetric cost matrix, this permits restriction to unordered type pairs provided **all four sign combinations** are verified for each off-diagonal pair. In particular, checking the 10 type pairs with \(\tau_a\le\tau_b\), all four sign combinations, and all \(8\times8\) affine-piece pairs is a sufficient finite cover. The diagonal same-sign branches are duplicates under the displayed symmetry, but retaining them is harmless. Reflection alone does not justify identifying the two same-sign branches for a fixed off-diagonal ordered type pair.

The potential has intentionally different one-sided values at outer type cuts. This is sound when all closed branches are verified: assign each actual boundary state one type and its potential consistently for both incident edges. Telescoping then uses that same state value twice. No continuity of the potential at type cuts is required. The exact knots of types 0, 1, 2, 3 are respectively \(k/8\), \(k/32\), \((56+5k)/224\), and \((6+k)/14\), for \(k=0,\ldots,8\), as implemented by `actual_knot`.

## Audit conclusion

The boundary monotonicity, transition at \(6/7\), scaled SAT identities, cost contraction, and linear-trigonometric maximum logic are mathematically valid. Complete proof status still requires all prescribed closed pair branches to terminate successfully with the intended rational potential and cost matrix, followed by the separately audited seven-type-walk implication.
