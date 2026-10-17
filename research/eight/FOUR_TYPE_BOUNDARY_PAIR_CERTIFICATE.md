# Four-type boundary-pair certificate

This note records the continuous inequality needed by the seven-state odd-cycle route. The inequality is validated by exact dyadic interval arithmetic, not by the numerical state graph that suggested it. The completed run is recorded in `fourtype_pair_logs_checked/manifest.json`, with status `ALL BRANCHES PASSED`: all 40 closed sign/type branches, and all 64 affine-piece rectangles in each branch, completed successfully. The executable was built with undefined-behavior checks and no recovery; those checks remained clean.

The complete tangent cover used 3,746,056 nodes and 1,874,308 terminal rectangles, with maximum depth 24. Its accounting identity is
\(3,746,056=2(1,874,308)-2,560\). The least negative accepted SAT upper margin was \(-53,128/2^{48}<0\). The per-branch and aggregate records are retained alongside the manifest.

## Statement and exact data

Put

\[
Q=\frac{9789}{2500},\qquad \varepsilon=\frac1{12},\qquad
\beta=\frac9{50}.
\]

A unit square has center radius \(r\), and its first side axis has angle \(\alpha\in[-\pi/4,\pi/4]\) relative to the center ray. Write \(t=\tan\alpha\) and \(a=r\cos\alpha\). The two radial boundary curves are as follows.

* On the outer disk boundary, \(a\) is the positive root of
  \[
  (1+t^2)a^2+(1+|t|)a+\frac12-Q=0.
  \]
* On the inner core boundary, \(a=7/12\) for \(|t|\le6/7\). For \(|t|\ge6/7\), it is the larger root of
  \[
  (1+t^2)a^2-(1+|t|)a+\frac12-\frac1{144}=0.
  \]

The four types are core, outer \(|t|\in[0,1/4]\), outer \(|t|\in[1/4,3/7]\), and outer \(|t|\in[3/7,1]\), numbered \(0,1,2,3\). At a common type cut, choose either adjacent type and keep that choice consistently for both edges incident to the state. The verifier covers both closed choices.

The state potential \(\psi\) is odd in \(t\). On each positive type domain it is piecewise affine on eight equal subintervals. Its nine nodal values, multiplied by \(10^8\), are

| Type | Nodal numerators, in order |
|---|---|
| 0 | 0, 4963699, 8978948, 12327199, 14841828, 8212593, -5496777, -2591030, 0 |
| 1 | 0, -1166957, -2242117, -3190746, -3838175, -4292398, -4663542, -4951387, -5168609 |
| 2 | -5846760, -6217415, -5611024, -6755028, -6673340, -6247421, -5827636, -5445707, -5034897 |
| 3 | -6028360, -5413423, -4267209, -3424593, -2597544, -1806376, -1103832, -526867, 0 |

The symmetric cost matrix is

\[
\Gamma=\frac1{10^6}
\begin{pmatrix}
910793&910782&900470&883157\\
910782&910793&900481&883146\\
900470&900481&890169&893458\\
883157&883146&893458&910793
\end{pmatrix}.
\]

For any two boundary states with a directed center-angle gap \(\delta\in[3/5,\pi)\), let

\[
w=\frac{1+|\cos(\delta+\alpha_B-\alpha_A)|+
|\sin(\delta+\alpha_B-\alpha_A)|}{2}.
\]

The certified pair theorem is: **if the two actual unit squares have disjoint interiors, then**

\[
\delta-\beta(w-1)+\psi(B)-\psi(A)
\ge \Gamma_{\tau(A),\tau(B)}.
\tag{P}
\]

The fourfold SAT test uses the two actual side axes of each square. Neither center distance alone nor freely chosen separating axes are substituted for it.

## Algebraic SAT formula

Let \(t,u\) be the two signed tangents and \(a,b\) their positive local radial coordinates. Set

\[
A=1+t^2,\quad B=1+u^2,\quad Z=\sqrt{AB},
\quad K=1+tu,\quad L=u-t.
\]

Writing \(C=\cos\delta\), \(S=\sin\delta\), the relative-frame sine and cosine have numerators

\[
Z\cos(\delta+\alpha_B-\alpha_A)=KC-LS,
\qquad
Z\sin(\delta+\alpha_B-\alpha_A)=KS+LC.
\]

The four center-separation projections, multiplied by \(Z\), are

\[
\begin{aligned}
P_1&=bB(C+tS)-aZ,\\
P_2&=bB(S-tC)+atZ,\\
P_3&=bZ-aA(C-uS),\\
P_4&=-buZ+aA(S+uC).
\end{aligned}
\]

For each axis and each sign \(s\in\{-1,1\}\), the exact SAT margin multiplied by \(2Z\) is

\[
F=2sP_k-Z-|KC-LS|-|KS+LC|.
\]

Thus a pair can be disjoint only if at least one of these eight margins is nonnegative. For every \(\sigma,\tau\in\{-1,1\}\),

\[
F\le 2sP_k-Z-\sigma(KC-LS)-\tau(KS+LC).
\tag{S}
\]

The right side of (S) is affine in \(\cos\delta,\sin\delta\). The verifier encloses its maximum on a gap interval and takes the minimum of the four valid upper bounds. A strict negative bound for all eight signed axes excludes every true separating axis throughout the box.

## Eliminating the gap variable

The width excess \(w-1\) lies in \([0,(\sqrt2-1)/2]\), and is Lipschitz in \(\delta\) with constant \(1/2\). Consequently

\[
H(\delta)=\delta-\frac9{50}(w-1)+\psi(B)-\psi(A)-\Gamma_{ij}
\]

is strictly increasing, with every secant slope at least \(91/100\). If (P) fails, then

\[
\delta<\Gamma_{ij}-\psi(B)+\psi(A)
 +\frac9{50}\frac{\sqrt2-1}{2}.
\]

An exact upper enclosure gives the initial gap endpoint. Interval evaluation of \(H\) at a trial endpoint permits monotone bisection to reduce it. A trial endpoint replaces the current upper endpoint only when the interval lower bound for \(H\) is nonnegative. The lower endpoint used in the bisection is merely a search aid; it is never used to discard possible gaps.

The final rejection test covers the whole interval from \(3/5\) through the certified upper endpoint. That one-dimensional interval may itself be split to sharpen (S). The main branch-and-bound state contains only the two tangents. This is a complete continuous cover, rather than a first-contact sampling rule.

## Exact arithmetic and maximum calculation

All enclosing endpoints are integer multiples of \(2^{-48}\). Products use signed 128-bit intermediates and directed quotient rounding. Square roots start from a floating-point seed, then exact integer comparisons correct it to the integer floor; the seed cannot affect acceptance. Sine and cosine bounds are alternating Taylor polynomials with outward interval coefficients, inherited from the existing PR #9 dyadic certificate arithmetic.

The signed linear-trigonometric expression \(x\cos\delta+y\sin\delta+z\) is maximized using endpoints and the possible interior stationary maximum \(\sqrt{x^2+y^2}+z\). Endpoint derivative enclosures exclude an interior maximum whenever possible. Every gap interval lies in \([3/5,5/2]\), where sine is positive and interval length is less than \(\pi\). This justifies choosing the upper coefficient for the sine term and considering both cosine coefficient endpoints when its sign could change. The implemented rational potential and relaxed matrix in fact give a much smaller initial gap upper bound.

On either radial boundary, \(a\) is nonincreasing in \(|t|\), so point-root enclosures at the two tangent endpoints enclose the entire boundary arc. On the outer curve this follows from

\[
a'=-\frac{a(ta+1/2)}{(a+1/2)+t(ta+1/2)}<0.
\]

On the core corner curve it follows from

\[
a'=-\frac{a(ta-1/2)}{(a-1/2)+t(ta-1/2)}\le0.
\]

The core side is constant, and the corner root agrees exactly at \(t=6/7\). Both signs are recovered by odd reflection of the potential.

## Complete branch cover and reproducibility

There are ten unordered type pairs. For each, all four choices of the two tangent signs are checked, giving 40 full branches. Each branch starts from all 64 pairs of closed affine-piece intervals. Source/target reversal followed by reflection preserves the gap, true SAT condition, and cost, because \(\psi\) is odd and \(\Gamma\) is symmetric. It therefore covers the opposite ordering of distinct types without further branches.

Every tangent rectangle is bisected into two closed subrectangles until the signed SAT upper bound is strictly negative on its whole possible cost-failure domain. No numerical tolerance permits acceptance. A node or depth limit produces a failure, and each piece checks its binary-tree node/leaf identity.

The runner additionally requires exactly the 64 distinct affine-piece completions and the matching final branch completion line. It stores all branch logs and hashes of the executable, verifier source, arithmetic source, and each log. A successful manifest must say `ALL BRANCHES PASSED` and contain all 40 branches. A truncated log or an exit without a complete branch report is rejected.

Build and run from this directory:

```sh
g++ -O3 -std=c++17 -fsanitize=undefined -fno-sanitize-recover=all verify_fourtype_pairs.cpp -o /tmp/n8-fourtype
python run_fourtype_pairs.py /tmp/n8-fourtype 3 /tmp/n8-fourtype-logs
```

The geometric and arithmetic acceptance argument has been independently reviewed in `FOUR_TYPE_PAIR_VERIFIER_GEOMETRY_AUDIT.md` and `FOUR_TYPE_PAIR_VALIDATOR_AUDIT.md`. The separate note `FOUR_TYPE_ODD_CYCLE_LEMMA.md` proves the finite type budget by a short loop-and-triangle argument, including rational bounds for \(\pi\) and \(\sqrt2\).

## Consequence of the completed certificate

For every closed seven-state boundary cycle, the potentials telescope. The exact type lemma gives

\[
\sum_{i=0}^{6}\Gamma_{\tau_i,\tau_{i+1}}
\ge\frac{6209669}{10^6}.
\]

Consequently its adjusted total satisfies

\[
\sum_{i=0}^{6}\delta_i
-\frac9{50}\sum_{i=0}^{6}(w_i-1)
+\frac9{50}(\sqrt2-1)>2\pi,
\]

because the rational lower margin obtained from \(\sqrt2>239/169\) and \(\pi<355/113\) is

\[
\frac{6209669}{10^6}+\frac9{50}\frac{70}{169}-\frac{710}{113}
=\frac{19848893}{19097000000}>0.
\]

The separate radial-boundary reduction transfers any hypothetical low-cost seven-exterior cycle to these boundary states at the same cost. Therefore any packing branch whose exterior orientation width satisfies \(\sum(w_i-1)\ge\sqrt2-1\) is excluded at \(Q\), conditional only on the central-core input and that hand reduction. This includes the entire M5 branch; it does not rely on its former small-J/diffuse split.

This is a computer-assisted continuous certificate with hand reductions and a hand finite-type argument. It is not a pen-and-paper proof of the 40 pair inequalities, nor a Lean formalization. Those are separate proof standards and must not be reported as completed merely because this verifier passes.
