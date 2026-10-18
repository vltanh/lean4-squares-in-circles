# Independent audit of the complete C/M hand estimate

**PASS.** The restored manuscript proves the full C/M table entry
\(\mathcal C>.9005\), for both orders, all four sign pairs, both retained
source axes, and every admissible frame angle. Reflected reversal supplies
the target axes. There is no frame-concentration premise in this proof.

The author's standalone replay passes **213 strict rational comparisons**.
An independent Python `Fraction` reconstruction, transcribed directly from
the two scalar formulas in the manuscript, passes **66 further comparisons**:
all 17 degree-16 Bernstein lower bounds, all nine positive degree-eight
coefficients, 36 curvature bounds and sign checks, and four stationary-test
comparisons. These checks replay fixed displayed arithmetic; they do not
replace the continuous arguments audited below.

## 1. Geometry and complete case cover

The center convention is \((a,-\sigma b)\), and the actual frame difference
is \(\phi=\delta+\alpha_t-\alpha_s\). With the already proved
\(\delta>.76\), the C/M angle ranges give \(\phi>-.432\).
The universal label and width estimates close every \(\phi\ge2.18\).
Thus no unstated lift or modulo-quarter convention is used when the
intermediate interval is divided into quadrants.

The primary and transverse signed separator formulas agree with this
center convention. Their support multiplier has the correct direction:
if \(M\ge0\) and \(\lambda\ge0\), then
\(\mathcal C\ge\mathcal C-\lambda M\). All multipliers used in the
remaining cases are nonnegative. Reflected reversal changes the signs to
\((-\tau,-\sigma)\), preserves the cost and the frame difference, and
converts a retained target axis to the corresponding source axis.

| Order and source axis | Whole-domain argument independently checked |
|---|---|
| C to M, primary | Both source signs are bounded by the negative core label. Separation is impossible through 1.5. The negative target sign has a direct cost reserve; the positive target sign remains geometrically impossible through 2.18. |
| C to M, transverse | A negative core source must lie on its side, because the middle center norm is below 1.34. This makes the residual after the multiplier \(g\) nonnegative for either source sign. A negative target reduces to both arc endpoints in every quadrant. A positive target is impossible through .7, has the full-circle polynomial bound through 1.53, and then has the high-endpoint continuation. |
| M to C, transverse | A negative source cannot separate because the core center norm is below .8. For a positive source, each target sign has a complete endpoint reduction, including the negative-angle interval. |
| M to C, primary | Both source signs are bounded by the negative middle label. Separation is impossible through .6. A negative target on the whole core, and a positive target on the side, use the same cancellation through 1.94 and a direct tail thereafter. The positive core corner has its own geometric barrier and final label bound. |

The arc derivative \(a'=-(b+1/2)/(a+1/2)\), the core corner derivative,
and the label bounds have the required signs throughout their respective
closed arcs. Every side/corner junction and every angle endpoint is in at
least one proved case. The interval at zero and the quarter-turn endpoint
are covered with their actual width formulas.

## 2. The support and monotonicity arguments

For a negative middle target, the coefficient of the concave coordinate
\(A(B)\) is positive, so the target functional is concave and its minimum
is at an endpoint. The trigonometric derivative amplitudes are strictly
below one in the first quadrant; the second-quadrant and negative-angle
derivatives have the stated signs. For a positive target, complete-circle
support is a valid enlargement of the middle arc. From 1.53 onward the
functional decreases along the actual arc, because its derivative is
bounded above by a decreasing negative function. The endpoint cost
decreases up to the quarter turn and increases afterward. The shared
quarter-turn value exceeds .9006.

For M to C on the transverse axis, the source functions \(M-\lambda b\)
decrease whenever the proof uses them. The positive-core functional is
strictly decreasing on the full side and corner, so the diagonal endpoint
is its actual minimum. In the negative-angle, negative-core case,
\(\lambda=g/\cos z\) cancels the core \(B\)-coefficient. Multiplication
of the scalar derivative by \(\cos^2z>0\) gives

\[
\frac{13g}{12}-1.09+1.09\sin^2z-.014g\sin z>0.
\]

Completing this quadratic has the direction claimed in the manuscript.

For the primary M to C case, \(\lambda=g/\sin\phi\) cancels the core
\(B\)-coefficient in both stated target cases. For a negative core target,
the remaining coefficient \(K-\lambda\cos\phi\) is positive, so replacing
its core coordinate by \(7/12\) is a lower bound. A positive target on the
side gives exactly the same expression. No such substitution is made for
the positive corner: that corner is separately impossible through 2.13,
and its remaining interval forces \(b<.381\), hence \(M(b)<.394\).

On the endpoint continuation \([1.2,\pi/2]\), direct differentiation
confirms the displayed third derivative. It is strictly negative.
Consequently \(G'\) is concave; since \(G'(1.2)>0\), its nonnegative set
is an interval containing the left endpoint. This permits no interior
minimum of \(G\). Both endpoint values exceed the target. After the quarter
turn the separate derivative lower bound is positive. Thus the argument
does not assume monotonicity across a width-formula change.

## 3. Independent reconstruction of the scalar bounds

For the C to M full-circle bound, collecting the support terms gives

\[
F=x+K_F+(g-.09)\sin x-.09\cos x
-\sqrt Q\sqrt{p^2+q^2+g^2+2g(p\sin x-q\cos x)}.
\]

The lower Taylor polynomial uses \(S_7\) in the positive sine term and
\(C_8\) in the negative cosine term. The squared norm upper polynomial
uses \(S_9\) and \(C_{10}\). The independently reconstructed
\(P=T^2-QV\) has degree 16 and all 17 displayed positive Bernstein bounds
on \([.7,1.53]\). Every Bernstein coefficient of \(T\) exceeds four.
The positivity of \(T\) makes squaring reversible in the needed direction.

For the M to C full-circle bound, put
\(X=p+g/\sin x\), \(N=\sqrt{X^2+q^2}\), and \(Z=\sqrt Q X/N\).
Differentiation independently gives

\[
F'=1+.09(s-c)+\frac g{s^2}\{c(Z-1)-13/12\},
\]
\[
F''=.09(s+c)+\frac g{s^3}
\{(1+c^2)(1-Z)+(13/6)c\}
-\frac{\sqrt Q q^2g^2c^2}{s^4N^3}.
\]

Both \(N\) and \(Z\) decrease on \([.6,1.2]\). The denominator choice
in the curvature table is correct: when its numerator lower bound is
negative, the lower sine endpoint is used. The independent reconstruction
confirms all eight positive numerator cases and the one negative case,
as well as \(F''>.03\) on all nine fixed intervals. The bound on \(s+c\)
uses concavity and the minimum of the two endpoints; it is valid also for
intervals below or across \(\pi/4\).

At the single test point 1.08, the norm and trigonometric bounds yield
\(F>.9006\) and \(|F'|<.0003\), with the correct negative-denominator
term directions in the derivative estimate. Integrating the curvature
bound and completing the square gives

\[
F>.9006-\frac{.0003^2}{.06}=.9005985>.9005.
\]

These are two complete scalar proofs on fixed stated intervals. No
sampled minimizer, adaptive state cover, or unknown endpoint value is used.

## 4. Reviewed files and gate consequence

The reviewed manuscript SHA-256 is
`736a208d70fc42ad4b089ff5b191101a73227df317ea58c880ade6463d3c124d`.
The reviewed author checker SHA-256 is
`44ec19058873a123896c1844835c97a9acb46c4fb113ba8ac143b5f8bed7c2f8`.
The independent reconstruction is
`audit_core_mid_polynomial_and_curvature.py`; its output is
`core_mid_independent_arithmetic.json`.

The **final 16 frame-table branches pass review**. Together with the
other nine independently reviewed entries, the full four-type table now
has a hand proof on all 128 ordered source-axis branches. Its finite
seven-walk budget proves the required \(D<.7\), so the common quarter table
and all four double-increment-word exclusions have their hand premise.
