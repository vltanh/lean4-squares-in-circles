# Independent full-source and equality review of the sharp radius-two cap-arc theorem

Date: October 26, 2026.

**Verdict: PASS for the sharp single-square arc bound, its complete equality classification, and the weak-interval pair-capacity consequence.**

Reviewed in full: RADIUS_TWO_CAP_INNER_ARC_SHARP_BOUND.md.

The complete underlying orientation and face-case domain was independently audited in REVIEW_RADIUS_TWO_CAP_ARC_QUARTER_TURN_C6_2026_10_26.md. That review establishes the exact connected open and closed intersections, including face endpoints, and the actual radial-center point. The present review checks the new sharper length and every equality step.

## 1. Whole inner-face case

The accepted convex estimate \(E<3/5\) applies on the entire inner-face domain \(a>r\), with \(1/4<A<1\) and \(-1/2\le B<1/2\). Put
\[
 \beta_0=\arcsin(2/5),\qquad\Lambda=2\beta_0.
\]
The displayed double-angle values are exact.

The difference between the two cross-term coefficients is positive and less than \(3/50\), with both radical substitutions in the correct directions. For negative \(AB\), the new term only lowers E; for positive \(AB\), its increase is less than \((3/50)(1/2)\). Thus
\[
 E_\Lambda<63/100<289/400=r^2\cos^2\Lambda
\]
holds throughout the whole domain. The last reserve is exactly \(37/400\).

I independently expanded the equivalent squared comparison. Since its right side is strictly positive, taking its positive square root gives the asserted upper bound even if \(A+B\sin\Lambda\) is negative. The trigonometric substitution is exact, and
\[
 0<\beta+\Lambda<3\beta_0<\pi/2
\]
places the comparison on the strictly decreasing principal cosine branch. Therefore the inner-face contribution \(\alpha-\beta\) is strictly greater than \(\Lambda\).

The other contribution is the complete opposite-face strip function D(b). Its derivative is strictly positive for \(b>1/2\), and continuity covers \(b=r\). For \(b>r\), the separate \(\gamma=\pi/2\) expression is strictly larger than \(\Lambda\). Thus the entire open arc has length at least \(\Lambda\), with equality exactly at \(b=1/2\).

At that endpoint, \(\beta=-\beta_0\), \(\gamma=\beta_0\), and the strict inner-face bound gives \(\alpha>\beta_0\). Hence the whole open arc is exactly \((-\beta_0,\beta_0)\), not merely an arc of that length selected from a larger intersection.

## 2. Whole outer-face case

The original height premise forces \(0<B\le A\le1/4\) and \(k>1/4\). The exact four-face interval therefore has four possible upper-minus-lower differences.

Both strip differences are strictly greater than \(\Lambda\), since their arguments a,b exceed 1. The inner-inner comparison is strict: \(\arcsin(1/5)<\pi/12\), and \(\Lambda<\pi/3\), with the displayed radical bounds proving the needed elementary sine inequalities.

For the outer-outer difference, the accepted fixed-k derivative covers one whole connected interval and minimizes its length on the diagonal. The strict \(k>1/4\) comparison is valid. Its remaining fixed-angle inequality reduces to
\[
 4\sqrt2-1>\sqrt{21}.
\]
Both sides are positive; its squared difference is \(12-8\sqrt2>0\). The comparison angle \(\pi/4+\beta_0\) is below \(\pi/2\), so the principal arcsine comparison has the claimed direction. This proves that all four differences, including their \(a=r\) boundary, are strictly greater than \(\Lambda\).

There is no outer-face equality case. Combining both complete face domains, equality occurs precisely at \(b=1/2\), or equivalently when one of the actual center own-coordinates is zero. The cap premise gives center norm \(>3/4\), so at equality the other coordinate is positive and \(a>5/4\). Thus this equality characterization has no missing zero-center or face-boundary case.

The displayed example is valid: its far corner has norm below 2, it lies above support height \(1/2\), and its whole inner-circle open arc is exactly \((-\beta_0,\beta_0)\). This confirms sharpness for one actual unit.

## 3. The weak common-interval endpoint

Assume two physically interior-disjoint squares have both full open arcs in one actual circle interval of length at most \(2\Lambda\). Since each is a connected open arc of length at least \(\Lambda\), disjointness forces equality in every length comparison. In an ordinary unwrapped interval of length \(2\Lambda<\pi\), the two open intervals of length \(\Lambda\) must be adjacent and have one common endpoint. There is no positive-length unused gap.

The proven equality classification makes each unit's arc symmetric about its own actual radial-center axis. Therefore the adjacent endpoint p has, in each unit's own origin-based axes, the exact coordinates
\[
                    (\sqrt{21}/4,\ \pm1/2).
\]
The radial coordinate is strictly between each unit's radial faces:
\[
                  A<1<\sqrt{21}/4<r<a.
\]
Thus the common endpoint is on a transverse side only, not at a radial-face intersection.

For a sufficiently small positive \(\epsilon\), the single point \((1-\epsilon)p\) remains strictly between both units' radial faces. Its two absolute transverse coordinates are each strictly below \(1/2\). It consequently lies in both open square interiors, contradicting physical nonoverlap. The same radial contraction works simultaneously because both positive radial-face margins are strict.

This proves the pair-capacity conclusion even at the weak available-length endpoint. It does not assume that either extra touches the containing circle, has positive circle weight, or initially has a prescribed radial orientation. The radial orientation is a consequence solely of the exhausted equality case.

I also checked the final exact double-angle data
\[
 \cos(2\Lambda)=-47/625,\qquad
 \sin(2\Lambda)=136\sqrt{21}/625.
\]

## 4. Exact scope

The theorem applies to every actual unit square contained in \(D_R\), \(R\le2\), and in an actual cap of height \(H>1/4\). It retains every orientation and all original geometric endpoint cases. The pair theorem still requires a separately proved common available interval and physical routing. It supplies neither an unproved pocket label nor a C6 endpoint-angle bound.

All length bounds and equality statements have been checked across both exhaustive face cases. No sampled orientation, coefficient packet, altered physical mean, force deletion, Lean compilation or CI enters the argument. No parent completion gate is asserted.

