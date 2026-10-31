# Independent full-source review of the quarter-turn cap-arc theorem at height one quarter

Date: October 26, 2026.

**Verdict: PASS for the strengthened threshold \(H>1/4\), every unit-square orientation, and the stated conditional capacity consequence.**

Reviewed in full: RADIUS_TWO_CAP_INNER_ARC_QUARTER_TURN.md.

This is a separate review by an agent who authored neither the earlier height-threshold proof nor the strengthened outer-face argument. The earlier review at threshold \(1/(2\sqrt2)\) is not used as certification of the new threshold.

## 1. Complete physical domain

The hypotheses are exactly one actual closed unit square \(S\subseteq D_R\), \(R\le2\), and its actual containment in a half-plane \(n\cdot p\ge H>1/4\). The proof makes no circle-touching, stress, frame or center-box assumption.

Changing signs and order of the actual own axes puts its center at \(x\ge y\ge0\), with
\[
 a=x+\tfrac12,\quad b=y+\tfrac12,\quad
 A=a-1,\quad B=b-1,\quad q=a^2+b^2\le4.
\]
The farthest-corner formula and the closest-point formula are correct for this own frame, including \(B\le0\). The alternatives \(a>5/4\) and \(a\le5/4\) exhaust the whole physical domain.

## 2. Entire inner-face case

For \(a>5/4\), the bounds \(A\in(1/4,1)\), \(B\in[-1/2,1/2)\) and \(A^2+B^2<5/4<(5/4)^2\) follow from actual containment.

I independently expanded
\[
 E=A^2+B^2+\sqrt2AB
 =(1-1/\sqrt2)q+\frac{(a+b)^2}{\sqrt2}
 -(2+\sqrt2)(a+b)+2+\sqrt2.
\]
Its convexity on the complete fixed-\(q\) interval justifies the two endpoint estimates. The enlargement to the whole interval does not assume that auxiliary endpoints satisfy the cap premise.

At \(b=1/2\), the correct lower and upper ranges are \(1/4<A<1\). The quadratic upper bound has endpoint values \(11/80\) and \(11/20\), both below \(3/5\). At the other endpoint \(a=b=v\), enlarging to \(v\in[3/4,\sqrt2]\) is valid; its two endpoint values are \((2+\sqrt2)/16\) and \(2-\sqrt2\), both strictly below \(3/5\). Thus the claimed bound \(E<3/5<25/32\) is uniform.

The exact closed inner-circle intersection is
\[
 [\beta,\min(\alpha,\gamma)]
\]
with the stated principal angles. The lower endpoint \(\beta>-\alpha\), the positive first coordinate, and the first outer face beyond the circle justify that full interval description.

The use of
\[
 (\sqrt2A+B)^2<r^2-B^2
\]
is safe even if \(\sqrt2A+B\) is negative: it always implies its strict upper bound by the positive square root. The conversion to \(A<r\cos(\beta+\pi/4)\) is exact, and both angles lie on the strictly decreasing cosine branch. This proves \(\alpha-\beta>\pi/4\).

The opposite-face strip estimate is monotone on the entire stated interval, and both alternatives \(b\le r\) and \(b>r\) are covered. At \(b=r\), the possible top point at angle \(\pi/2\) is outside the first-coordinate range since \(\alpha<\pi/2\). No exceptional open-interior point or second arc remains.

## 3. Strengthened outer-face argument

For \(a\le5/4\), the cap premise genuinely supplies the missing restriction. If \(B\le0\), the actual closest point would have norm at most \(1/4\), contradicting \(n\cdot p\ge H>1/4\). Hence
\[
 0<B\le A\le1/4,\qquad
 1/16<k^2=A^2+B^2\le1/8.
\]
The whole square lies in the open first quadrant, so the four-face angular interval is exact.

Three of the four possible upper-minus-lower differences are handled by valid full-strip or inner-inner estimates. For the fourth, I independently differentiated at fixed \(k^2\), with \(B=\sqrt{k^2-A^2}\). Its sign comparison is
\[
 B^2[r^2-(1+B)^2]-A^2[r^2-(1+A)^2].
\]
The positive factors needed before squaring hold throughout the open interval. Direct factorization gives
\[
 (A-B)\{(A+B)(k^2-9/16)+2(k^2+AB)\}.
\]
Writing \(w=A+B\), I independently expanded the bracket as
\[
 (w-1/4)^2+(k^2-1/16)(w+1),
\]
which is strictly positive because \(k^2>1/16\). Thus the outer-outer length is nondecreasing away from the diagonal on one entire connected interval. That interval remains in \(B>0\), \(A\le1/4\); endpoint continuity correctly handles \(a=r\) or \(b=r\).

The diagonal length increases with \(k\). At the strict lower threshold, the exact comparison is
\[
 \left(\frac{4+1/\sqrt2}{5}\right)^2
 -\sin^2(3\pi/8)=\frac{16-9\sqrt2}{100}>0.
\]
Both compared arguments belong to \((0,1)\), so the principal arcsine comparison is valid. The outer-outer difference, and hence all four possible differences, is strictly greater than \(\pi/4\). This proves existence, connectedness, and the strict length bound throughout the entire new outer-face domain.

## 4. Radial-center point, disjointness and exact scope

The actual support half-width gives
\[
 |c|\ge n\cdot c\ge H+\tfrac12>\tfrac34.
\]
Actual containment gives \(|c|\le(\sqrt{15}-1)/2<3/2\). Thus
\(\lvert5/4-|c|\rvert<1/2\), and the radial-center point lies in the open inscribed disk and consequently in the unique open square arc. The center is nonzero.

Two physically interior-disjoint units have disjoint open arcs on the same inner circle. Their two lengths, each strictly greater than \(\pi/4\), cannot fit inside one interval of length at most \(\pi/2\). This proves precisely the conditional consequence stated in the source.

The proof supplies no pocket routing theorem or C6 height bound by itself. It does not discard any square, replace any original mean, change any corner mask or assume positive circle weights on an extra. Its strict threshold, orientation endpoints, all angular branches and both face cases have been checked. No numerical sampling, coefficient packet, Lean compilation or CI is needed.

