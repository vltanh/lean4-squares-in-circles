# Independent review of the analytic 95-to-2 measure-line reduction

Date: October 26, 2026. Reviewer: C6 completion agent.

**Verdict: PASS for the full analytic reduction, open-interior boundary
scope, and standalone exact two-point checker:**

- NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md;
- NINE_RADIUS_TWO_MEASURE_LINE_TWO_POINT_CHECK.py.

I read both complete sources and the relevant normalization, vertical
translation, common-rectangle and exact-arithmetic sections of
NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md. I also read the original and
independent interval primitives to check that the new two fixed
rectangles use the same reviewed mathematical lower bounds.

## 1. Exact charges and the atom boundary

For \(a\in[9/10,11/10]\), the radius-\(1/10\) circle has only
the active lower x constraint, yielding exactly
\(\arccos(10(a-1))/\pi\), including both tangent endpoints
in the angular-measure sense.

For the larger circles, the negative x branch is excluded by the
actual strip, and the positive branch automatically satisfies the
lower x bound. The positive-part formula (4) consequently has the
correct factor of pi. The radius-\(27/20\) contribution is zero
on the entire line. The radius-one term is active at its left
endpoint and constant for \(a\ge1\); the radius-\(11/10\)
term is active throughout the closed right interval.

The origin atom is present exactly for \(a<1\). The continuous
extension of the scalar submeasure L to \(a=1\) is used only
to locate its scalar minimum; the actual square at \(a=1\)
is separately covered by the atom-free right formula. No
boundary square receives an unearned atom.

## 2. Complete left and right monotonicity arguments

I independently differentiated the two exact charge formulas.

For L, the sign of the derivative is precisely the sign of H,
because both terms being compared before squaring are positive.
The quadratic H has
\[
 H'(a)=2[3858^2-(3858^2-714^2)a]\ge2\,714^2>0
\]
on the entire closed left interval. Its endpoint signs give
one critical point and the correct decreasing-then-increasing
pattern. Fresh Fraction arithmetic reproduces
\[
 H(927/1000)=-68424471/31250,\qquad
 H(928/1000)=14285817/15625.
\]
Thus the one fixed common rectangle truly encloses the unique
global minimum of the left submeasure.

For U, the positive factor in (12) is correctly separated.
Its derivative sign is that of the increasing affine J.
Independent exact arithmetic gives
\(J(1)=-482994\) and \(J(11/10)=53604\), and its unique zero is
exactly
\[
                         a_*=\frac{324943}{298110}.
\]
The derivative signs prove the entire right interval is minimized
there, including the atom-free endpoint \(a=1\) by continuity.
No sampled minimizer, local numerical claim or unproved critical
point uniqueness is used.

## 3. Two exact full-rectangle charges

The four quadrant angular formulas lower-bound the mass of the
complete common open rectangle
\((a_h/B-1,a_l/B)\times(-1/2,1/2)\).
The first rectangle is contained in every square in the entire
critical enclosure \((927/1000,928/1000)\), and its origin is
strictly inside. It is charged only by the atom and the two
circles actually used to define L. The second is an outward
floor/ceiling enclosure of the exact rational \(a_*\), and
correctly receives no atom.

I inspected the standalone verifier in full. Its integer
floor/ceiling arithmetic keeps all powers, alternating terms,
square roots, half-angle ratios, minimum/maximum endpoints and
positive parts in the required outward directions. The
16-term arctangent remainder and Machin identity provide the
stated pi enclosure independently of any floating-point value.
The mass normalization uses the upper pi numerator and is
therefore conservative.

Running the standalone saved checker reproduced exactly:
\[
 \begin{array}{c|r}
 \text{left}&1153182092959159440\\
 \text{right}&2475502032000671400
 \end{array}
\]
at scale \(2^{56}\), with the stated two boxes and their exact
origin-atom flags.

I separately evaluated these same two new rectangles using the
accepted independently implemented \(2^{80}\) inverse-trigonometric
primitives in NINE_RADIUS_TWO_MEASURE_INDEPENDENT_CHECK.py,
with the left check again restricted to its two permitted circles.
The resulting strict integer margins were
\[
 \begin{array}{c|r}
 \text{left}&19347185060999821130904660\\
 \text{right}&41532032299372156640399944.
 \end{array}
\]
This second evaluation uses the independent half-angle and
32-term arctangent implementation, not the new checker's
16-term implementation. Both signs are strictly positive.

## 4. Exact replacement scope

The analytic minima and the two full-rectangle checks prove the
entire original line charge, with all endpoints retained.
The accepted vertical-translation theorem supplies exactly the
same two-dimensional region as the former 95 line leaves.

I accept replacement of those 95 charged line leaves by these
two fixed charges: 93 charge obligations are removed. The
unchanged 14 corner, 2 middle and 97 outer charges then total
115 charges, with the original six empty-domain checks unchanged.
This review does not itself replace the outer-curve witness or
modify either accepted full checker.

The theorem continues to concern every actual contained unit,
with arbitrary orientation, and retains all nine original squares
in the global measure argument. It is a finite-certificate
reduction with an analytic whole-line proof; it does not claim
that the global measure theorem has become certificate-free.
No Lean compilation or CI was used.

