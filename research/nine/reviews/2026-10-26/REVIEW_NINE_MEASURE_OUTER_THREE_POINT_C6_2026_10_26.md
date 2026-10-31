# Independent review: the complete outer measure curve

Date: October 26, 2026.

Reviewer: C6 completion agent, independent of the reduction and checker
author.

**Verdict: PASS.** The complete source
`NINE_RADIUS_TWO_MEASURE_OUTER_CURVE_ANALYTIC_REDUCTION.md` and its
standalone checker
`NINE_RADIUS_TWO_MEASURE_OUTER_THREE_POINT_CHECK.py` prove the stated
whole-curve charge with all branch transitions and endpoints retained.
The exact reduction is 97 charged leaves to three fixed mass checks
and one fixed derivative enclosure. The three outer empty leaves are
also unnecessary because the new domain is exactly the closed curve.
This review does not change the accepted original 208-leaf source or
either of its checkers.

## 1. Physical and measure scope

I checked the join to the accepted outward-comparison theorem and the
normalization
\[
 a=\sqrt{4-b^2},\qquad 1/2\le b\le\sqrt2.
\]
This is a lower comparison for the measure of the original square,
not a motion of any packing square. Since
\(a-1\ge\sqrt2-1>1/10\), the atom and radius-1/10 circle have zero
mass throughout this curve. The three retained weights and the
normalization by \(2000\pi\) agree with the accepted measure. No
packing contact, force, mask or orientation assumption is added.

The actual circle intersections in (4) retain both clipping faces.
I independently derived all three transition values. The upper clip
equation is \(a=(5-r^2)/2\); the radius-1 lower clip is
\(a+b=5/2\). For the larger radii, the opposite-corner bound
\(5-\sqrt{15}<6/5<(11/10)^2\) removes lower clipping. These give
exactly (8), continuously at every transition. The positive-x branch
is the only branch because \(a-1>0\), and the upper x face is
inactive because \(a\ge\sqrt2>27/20\).

## 2. Whole-interval calculus

I rederived both derivatives in (10) and the polynomial identities
(11)--(12). All compared factors are positive, so the difference of
squares in (11) proves the claimed decreasing sign until the diagonal;
the zero diagonal derivative is retained. For convexity, the
\(b\le1\) sign is direct. On \(b\ge1\), replacing \(v\) by
\(t\le v\) in the subtracted term gives (13) in the correct direction.
The polynomial expansion about \(a=7/4\), its whole-domain coefficient
bound, and the quadratic reserve \(1799/1600\) prove strict positivity
without a subdivision. I also checked the monotonicity and strict
convexity of each strip function, including its zero first derivative
at \(b=1/2\).

For the initial range, the radius-1 term has just the stated increase
then decrease, and its value at \(b_1\) exceeds its left endpoint.
Both other terms increase there. I independently checked the cosine
comparisons, including reserves \(231/10000\) and \(3677/819200\).
For the final range, all three terms decrease to the diagonal. Thus
the two outer ranges really reduce to their respective endpoints.

On the intervening range, the exact branch formula is (20).
The lower bound for \(h_{27/20}''\) handles both signs of \(b-1\),
and the reserves \(585083/115316136\) and \(689/1056000\) independently
check. Hence \(M''>1/30\) on the entire intervening interval.
The fixed point \(13/12\) lies strictly inside it. Integrating this
uniform curvature and completing the square gives exactly
\[
 M(b)>3013/3000+(|b-13/12|-1/5)^2/60.
\]
This step uses no sampled minimum or unproved critical point.

## 3. Exact fixed derivative enclosure

I checked each radical interval in the seven-row table by positive
squaring. The dependent radicands for \(t_1,t_2\) use opposite
endpoints of the one common interval for \(a_*\), with the displayed
four reserves unchanged. I independently reconstructed the signed
substitutions in the derivative numerator. They give
\[
-\frac{1254291053647768750}{34246309814693847}<T
 <-\frac{798076820624315593050}{62929379411568326209},
\]
with the lower endpoint above \(-40\) and the upper endpoint below
zero. Therefore \(|M'(13/12)|<1/150\) using \(\pi>3\). No sign
of an unbounded radical expression is inferred from floating point.

## 4. Independent mass evaluation and checker execution

I read the standalone exact checker and executed it successfully. It
reproduced all three displayed integer margins and the full fixed
derivative bounds. The three boxes enclose the intended exact
parameters; their common open rectangles are contained in those
actual squares. Only the three large circles are counted and no atom
is accidentally charged.

For an independent numerical implementation, I evaluated the same
three common rectangles using the already independently reviewed
\(2^{80}\) inverse-trigonometric implementation from
`NINE_RADIUS_TWO_MEASURE_INDEPENDENT_CHECK.py`. These evaluations use
the higher target \(1005/1000=201/200\), not merely target one.
The resulting positive integer reserves were:

| Fixed square | Independent integer reserve |
| --- | ---: |
| \(b=1/2\) | 41710100045798634478003694 |
| \(b=13/12\) | 28806203097097727099813416 |
| \(a=b=\sqrt2\) | 5642871899810464564262128 |

Thus the fixed charge claims agree under a separate precision and
inverse-trigonometric implementation. The proof of the complete
continuous domain comes from Sections 1--4 of the manuscript, not
from these three isolated evaluations alone.

## 5. Accepted scope and remaining finite work

The whole outer curve has charge strictly greater than
\(3013/3000>1\). Combined with the separately reviewed line reduction,
the same global measure proof can use 21 charged checks: 14 corner,
2 middle, 2 fixed line and 3 fixed outer checks. It additionally
retains three corner empty tests and the one fixed outer derivative
enclosure. This is 187 fewer charged checks than the original 208.

This is an accepted analytic reduction of the finite certificate,
not a claim that the global measure theorem is table-free. No new
original graph gate is closed by this scalar reduction alone. No
Lean compilation or CI was run.
