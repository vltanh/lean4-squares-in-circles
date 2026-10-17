# Exact pair-validator arithmetic: proved narrowing and overflow bounds

## Scope and conclusion

This note covers the executed arithmetic in `verify_fourtype_pairs.cpp` and
`verify_boundary_pair_costs.cpp`, including their shared
`exact_dyadic_base.cpp`, for the following checked rational datasets:

- the completed four-type certificate;
- `three_core_pair_data_v2.json` / `.hpp`;
- `two_core_short_pair_data.json` / `.hpp` (the data and engine, independently
  of whether its geometric cover has completed).

No validated source is modified by this audit. In particular the unchecked
`Integer(q)` narrowing in `floor_div` is justified for these inputs by the
bounds below. This is a mathematical range argument, in addition to the
sanitizer runs. It is not a claim that an arbitrary future data header is safe.
Future headers must satisfy the same data bounds or receive a new range audit.

Put

\[
S=2^{48},\qquad \varepsilon=S^{-1}.
\]

Every executed dyadic interval endpoint has absolute value below

\[
4096S=2^{60}<2^{63}-1.
\tag{A}
\]

Every signed 128-bit product or numerator has absolute value below
\(2^{120}<2^{127}-1\). Every result narrowed by `floor_div` or `ceil_div`
is bounded by (A). Thus the narrowing conversions, endpoint additions and
negations, and wide products stay in their declared integer ranges.

The bound concerns the executed pair-checking path. The included arithmetic
file also contains an older, renamed marker-verifier `main`; it is not called
by either pair verifier.

## 1. Data bounds actually used

All three datasets satisfy the following conservative conditions:

1. Absolute positive and, when present, negative potential node values are at
   most 1 after division by the potential denominator.
2. Every exact tangent interval lies in \([0,1]\); there are at most 256
   pieces, and every reciprocal positive knot step is at most 256.
3. Every pair cost has absolute value at most 2, and \(0\le\beta<2\).
4. All integer data numerators and denominators are smaller than \(2^{31}\)
   in absolute value, with positive denominators. The limited differences
   of potential numerators are therefore smaller than \(2^{32}\).
5. The executed command-line type/piece indices are valid, and signs are
   exactly \(-1\) or \(+1\).

The actual bounds are substantially smaller:

| Dataset | Maximum absolute node value | Maximum pair cost | Largest reciprocal step |
|---|---:|---:|---:|
| four type | 0.14841828 | 0.910793 | 224/5 |
| three core v2 | 0.07593139 | 0.9396 | 8 |
| short two core, signed roles | 0.22940620 | 0.98722 | 8 |

The signed-role row includes both potential tables. All have eight pieces
per positive tangent domain. The generic main also checks the exact tangent
domain endpoint inequality by integer cross multiplication.

Outward rounding a rational number changes an endpoint by less than
\(\varepsilon\). In the generic knot expression
\(l+k\Delta\), the upper endpoint overshoots its exact value by less than
\((k+2)\varepsilon\). Thus even using the conservative 256-piece allowance,
all tangent boxes satisfy

\[
0\le x,y<1.01.
\tag{B}
\]

Bisecting a dyadic interval cannot increase this enclosing range. The
original four-type knot formulas satisfy the same bound directly.

## 2. Potential arithmetic, including independent signed tables

Let \(v_0,v_1\) be consecutive exact node values, each of absolute value at
most 1, and let \(D=1/\Delta\le256\). The stored rational intervals for
\(v_1-v_0\) and \(D\) stay inside \([-2,2]\) and \([0,256]\), since
these enclosing endpoints are themselves dyadic. Consequently the computed
slope has absolute value below 513, including multiplication rounding.

The intercept is computed as \(v_0-ml\). By (B), its absolute value is below

\[
1+513(1.01)+\varepsilon<520.
\]

Evaluating the affine expression at a tangent box therefore gives the
conservative absolute bound

\[
513(1.01)+520+\varepsilon<1040.
\]

The optional final multiplication by the sign has no larger magnitude.
Selecting a separately supplied negative-sign table has exactly the same
bound. Hence the potential difference `dpsi` has absolute value below 2080.
These deliberately loose bounds do not assume dependency cancellation
between the slope and intercept intervals.

No operation in either verifier squares a potential or multiplies two
potential values. The largest raw product in this part is a slope times a
tangent, bounded by 519 in unscaled units.

## 3. Boundary coordinates and all interval divisors

Write \(t=\pm x\), \(u=\pm y\). The auxiliary geometry uses

\[
A=1+t^2,\quad B=1+u^2,\quad Z=\sqrt{AB},
\quad K=1+tu,\quad L=u-t.
\]

Using (B) and allowing all dyadic rounding errors gives

\[
1\le A,B<2.1,\quad 1\le Z<2.2,
\qquad |K|,|L|<2.1.
\tag{C}
\]

The lower bounds 1 are exact in the interval engine: `square` returns a
nonnegative lower endpoint, products of endpoints at least \(S\) round
no lower than \(S\), and the integer square root of an input at least
\(S^2\) is at least \(S\).

The disk boundary formula has radicand

\[
(1+x)^2+4(1+x^2)(Q-1/2)<33,
\]

so its square-root upper endpoint is below 6. Its numerator has absolute
value below 6, and its denominator is \(2(1+x^2)\ge2\). The computed
outer coordinate consequently has absolute value below 3.

For the core corner, the radicand is at most \((1+x)^2<4.1\). Its numerator
is below 4.2, and its denominator is again at least 2. The core side value
\(7/12\) is smaller still. Thus both stored local coordinates satisfy
\(|a|,|b|<3\), including their endpoint enclosures.

These are the only interval division sites:

- outer and core coordinate formulas: divisor \(2(1+x^2)\ge2\);
- width evaluation: divisor \(2Z\ge2\).

In particular **no reciprocal of a nearly zero interval occurs**. The
explicit reciprocal knot step is a rational constant bounded in section 1.

The four scaled projection coefficients satisfy

\[
|X_j|,|Y_j|<6.5,\qquad |C_j|<6.7.
\]

Therefore every signed linear-trigonometric SAT upper expression has
cosine and sine coefficients below 18 in absolute value and constant term
below 16. Its stationary square-root radicand is below
\(2(18)^2+2\varepsilon<649\).

## 4. Taylor-Horner operations cannot produce large hidden intermediates

Every call to `point_trig` has a dyadic argument between the lower gap bound
and \(5/2\). `delta_upper` refuses a larger upper gap before trigonometric
calls, and a gap bound below the lower endpoint is discarded without such
calls. Thus \(x^2\le25/4<7\) inside every polynomial evaluation.

For the ten cosine coefficients and ten sine coefficients, define the
positive rational majorants

\[
P_c=\sum_{j=0}^{9}\frac{7^j}{(2j)!}<8,
\qquad
P_s=\sum_{j=0}^{9}\frac{7^j}{(2j+1)!}<3.
\]

These two finite rational inequalities can be checked without numerical
transcendentals; their positive gaps are respectively

\[
8-P_c=\frac{10898395304293}{11878244352000},\qquad
3-P_s=\frac{868613894121971}{2482553069568000}.
\]

Every partial Horner suffix has a smaller absolute majorant than the
corresponding full positive sum: dropping low-index terms and dividing
powers of 7 cannot increase it. Rounding contributes at most

\[
E\le\frac{4\cdot7^9-1}{3}\varepsilon
=53804809\varepsilon<2^{-20}
\]

to any completed suffix. This follows from the recurrence
\(E_k\le7E_{k+1}+2\varepsilon\), accounting for a coefficient enclosure
and the multiplication rounding at each stage.

Thus all cosine-Horner values have absolute value below 9, all sine-Horner
values below 4, and the final sine multiplication by \(x\le5/2\) gives
absolute value below 11. These bounds also cover the shorter degree-16 and
degree-17 polynomials. Their raw Horner multiplication intermediates are
below 63, before adding a coefficient of magnitude at most 1.

Endpoint values and derivatives in `scalar_trig_max` therefore have absolute
value below \(2(18)(11)+2\varepsilon<400\). Adding the SAT constant keeps
every upper bound below 416 in absolute value. The stationary root is
smaller than 26. The maxima/minima selectors do not increase these bounds.

## 5. Cost contraction and the overall bound

The width expression before division has absolute value below 94, since
\(|K|,|L|<2.1\) and both trigonometric enclosures have magnitude below 11.
Its divisor is at least 2. After subtracting \(1/2\), the width enclosure
has absolute value below 48. Hence \(|\beta\,\text{width}|<96\).

The cost expression has absolute value below

\[
5/2+96+2080+2<2200.
\]

The initial cost-derived upper gap bound has magnitude below 2083.
If it is larger than \(5/2\), the program throws before trigonometric
processing. If it is below the lower gap bound, the violating-cost domain
is empty. Otherwise every gap subdivision stays inside the established
trigonometric domain. When \(\beta=0\), returning this initial bound
immediately only omits an unnecessary refinement loop.

Combining the explicit operation bounds gives this conservative inventory:

| Executed quantity | Absolute unscaled bound |
|---|---:|
| Reciprocal knot step | 256 |
| Affine slope | 513 |
| Affine intercept | 520 |
| Evaluated potential interval | 1040 |
| Potential difference | 2080 |
| Initial cost-derived gap | 2083 |
| Cost expression | 2200 |
| Other geometric, root-radicand, and trig intermediates | 650 |

Every endpoint addition, subtraction, multiplication result, quotient
result, and rational conversion stays below 4096 in unscaled absolute value.
This proves (A), rather than inferring it from the small final accepted
margins.

## 6. Raw integers, wide numerators, and narrowing conversions

An interval endpoint below \(2^{60}\) multiplied by another such endpoint
has absolute value below \(2^{120}\), within signed 128-bit range. Products
with the scale \(S\) are smaller. Rational conversions have data numerators
below \(2^{32}\), so their wide numerators are below \(2^{80}\). The exact
endpoint-validation cross-products are also safely within 128-bit range
under the data limits of section 1.

For every call to `floor_div` and `ceil_div`, the **result** is the endpoint
of one of the rational/operation enclosures already bounded above, with at
most the one-unit rounding included in those bounds. Therefore its
`Integer(q)` narrowing lies strictly between \(-2^{60}\) and \(2^{60}\).
Negating the dividend in `ceil_div` stays within signed 128-bit range;
negating a quotient or endpoint stays within signed 64-bit range.

Every square-root radicand in interval units is below 649, so the exact
integer input to `integer_sqrt` is below \(649S^2\), and its root is below
\(26S\). The floating seed and the corrected integer root therefore lie
far inside signed 64-bit range. The exact correction products are below
\((26S+1)^2<2^{107}\). Acceptance uses the corrected integer inequalities,
not the approximate seed.

The factorial construction stops at
\(19!=121645100408832000<2^{57}\), so its ordinary signed 64-bit
multiplications do not overflow. The loop counters, piece indices, gap
midpoints, depth values, and node accounting also remain in range for the
manifested inputs and enforced budgets. The `INT64_MIN` and `INT64_MAX`
initializers are comparison sentinels; the code never negates, multiplies,
or narrows them.

## Result

The unchecked narrowing is safe for the stated data and executed branches.
No change to their validated source or hashes is required to establish that
fact. For future general-purpose use, checked narrowing and checked endpoint
addition would still be sensible defensive programming, but they are not an
unproved premise of these certificates once this bounded-input argument is
attached.
