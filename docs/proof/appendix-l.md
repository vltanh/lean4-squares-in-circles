# Appendix L. Eight squares: the exact polynomial checks

[Contents](README.md) · [← Appendix K](appendix-k.md) · [Appendix M →](appendix-m.md)

Many inequalities of the proof of eight squares come down to the positivity of
an explicit polynomial with rational coefficients: in one variable on an
interval, or in two variables on a triangle or a rectangle. Sines, cosines,
square roots and quotients enter these polynomials through Taylor polynomials
with signed remainders, through rational majorants and through cleared
denominators. Each such positivity is proved by a *check*: a Boolean value
computed from natural numbers and integers, which the Lean kernel evaluates,
together with a soundness theorem that turns the value `true` into the real
inequality at every point of the domain. This appendix describes the checks:
the bound by Chebyshev coefficients (§L.1), what the kernel computes (§L.2), two
variables (§L.3), trigonometric terms and radicals (§L.4), a worked example
(§L.5), the interval evaluations of Appendices J and M (§L.6), and the checks of
the whole proof (§L.7).

A proposition about natural numbers or integers built from decidable
comparisons has a decision procedure; `decide +kernel` proves it by asking the
kernel to reduce that procedure to `true` by definitional unfolding. The kernel
evaluates arithmetic on natural number literals with arbitrary-precision
integers (sums, products, quotients, remainders, comparisons and bit
operations), so these reductions are exact and fast. No compiled code and no
external program is trusted.

## L.1 A polynomial on an interval

Let $T_j$ be the Chebyshev polynomials, $T_j(\cos\theta) = \cos j\theta$, so
that $|T_j(u)| \le 1$ for $|u| \le 1$.

### Lemma L.1 (Chebyshev bound)

Let $p$ be a polynomial with rational coefficients, $a < b$ rationals and
$D \ge \deg p$. Write the *centred* polynomial as
$\tilde p(u) = p\left(\frac{a + b}2 + \frac{b - a}2u\right) = \sum_{i \le D} p_i u^i$,
and for $j \le D$ let

```math
c_j = \sum_{i \le D} p_i\,\gamma_{ij}, \qquad \gamma_{ij} = \begin{cases} \epsilon_j\,2^{-i}\binom i{(i - j)/2}, & j \le i \text{ and } i - j \text{ even}, \\ 0, & \text{otherwise}, \end{cases} \qquad \epsilon_0 = 1, \ \epsilon_j = 2 \ (j \ge 1) .
```

Then $\tilde p = \sum_{j \le D} c_j T_j$, and for every $x$ in $[a, b]$

```math
c_0 - \sum_{j = 1}^D |c_j| \;\le\; p(x) \;\le\; c_0 + \sum_{j = 1}^D |c_j| . \tag{L.1}
```

*Proof.* From $(2\cos\theta)^i = \sum_k \binom ik e^{\mathrm i(i - 2k)\theta}$,
$u^i = 2^{-i}\sum_{k = 0}^i \binom ik T_{|i - 2k|}(u)$, and grouping $k$ with
$i - k$ gives the coefficient $\gamma_{ij}$ of $T_j$. (The formal proof
derives the same identity by induction on $i$ from
$2u\,T_{n + 1} = T_{n + 2} + T_n$.) So $\tilde p = \sum_j c_jT_j$. For
$x \in [a, b]$, $u = \frac{2x - a - b}{b - a}$ lies in $[-1, 1]$, where every
$|T_j(u)| \le 1$. $\square$

*Lean:
[`Eight.WholeIntervalPolynomial.centered`](../../SquaresInCircles/Eight/Arithmetic/WholeIntervalPolynomial.lean#L26),
[`Eight.WholeIntervalPolynomial.monomialCoefficient`](../../SquaresInCircles/Eight/Arithmetic/WholeIntervalPolynomial.lean#L30),
[`Eight.WholeIntervalPolynomial.coefficient`](../../SquaresInCircles/Eight/Arithmetic/WholeIntervalPolynomial.lean#L35),
[`Eight.WholeIntervalPolynomial.expansion`](../../SquaresInCircles/Eight/Arithmetic/WholeIntervalPolynomial.lean#L44),
[`Eight.WholeIntervalPolynomial.sum_monomialCoefficient_mul_T`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L140),
[`Eight.WholeIntervalPolynomial.eq_expansion_of_natDegree_le`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L200),
[`Eight.WholeIntervalPolynomial.series_bounds`](../../SquaresInCircles/Eight/Arithmetic/WholeIntervalPolynomial.lean#L56),
[`Eight.WholeIntervalPolynomial.interval_bounds`](../../SquaresInCircles/Eight/Arithmetic/WholeIntervalPolynomial.lean#L75),
[`Eight.WholeIntervalPolynomial.positive_on_interval`](../../SquaresInCircles/Eight/Arithmetic/WholeIntervalPolynomial.lean#L101).*

The bound (L.1) is exact for $p$ constant and loses at most
$2\sum_{j \ge 1}|c_j|$; the Chebyshev coefficients of the polynomials of the
proof decrease quickly, so the loss comes mostly from the first few. Where the
linear or quadratic part dominates, three variants keep it exactly. In the
Chebyshev basis, $c_0 - c_2 + c_1u + 2c_2u^2$ is minimized exactly and only the
tail $j \ge 3$ is bounded by its coefficient sum. In the power basis
$p(x) = \sum_i a_i x^i$ on $|x| \le r$, the part $a_0 + a_1x + a_2x^2$ is kept
and $\sum_{i \ge 3}|a_i|\,r^{i - 2}x^2$ bounds the rest. And with the
Bernstein polynomials $\binom Di x^i(b - x)^{D - i}/b^D$ on $[0, b]$, which are
nonnegative and add up to 1, $p$ is at least the least of its Bernstein
coefficients.

*Lean:
[`Eight.ChebyshevLeadingBounds.quadratic_lower`](../../SquaresInCircles/Eight/Owners/ChebyshevLeadingBounds.lean#L52),
[`Eight.ChebyshevLeadingBounds.cubic_lower`](../../SquaresInCircles/Eight/Owners/ChebyshevLeadingBounds.lean#L67),
[`Eight.PowerTailBounds.quadratic_lower`](../../SquaresInCircles/Eight/Owners/PowerTailBounds.lean#L86),
[`Eight.WholeIntervalBernstein.lower_on_interval`](../../SquaresInCircles/Eight/Owners/WholeIntervalBernstein.lean#L524).*

## L.2 What the kernel computes

The polynomial ring over $\mathbb Q$ is not computable in Lean, so a check
never manipulates $p$ itself. It manipulates integer lists.

### Lemma L.2 (integer representations)

A *scaled list* $(l, s)$, with integers $l_0, \dots, l_n$ and a natural number
$s$, *represents* $p$ if $\sum_k l_kX^k = s\,p$.

1. Lists that represent $p + q$, $p - q$, $pq$, $p^m$, a rational constant and
   $X$ are computed from lists that represent $p$ and $q$ by integer operations.
2. If $(l, s)$ represents $p$ and $\frac{a + b}2 = \frac{\nu\sigma}\delta$,
   $\frac{b - a}2 = \frac{\nu\tau}\delta$ with natural numbers $\nu$,
   $\delta \ne 0$ and integers $\sigma$, $\tau$, then a list computed from $l$
   by integer operations represents the centred polynomial $\tilde p$, with the
   scale $s\,\delta^n$: it multiplies $l_k$ by $\nu^k\delta^{n - k}$ and
   composes with $\sigma + \tau X$ by Horner's rule.
3. If $(l, s)$ represents $\tilde p$, $s \ne 0$ and $n \le D$, then integers
   $C_0, \dots, C_D$ computed from $l$ satisfy $c_j = C_j/(s\,2^{n + 1}/2)$,
   where $c_j$ are the coefficients of Lemma L.1.

*Proof.* (1) The operations of polynomials act on coefficient lists by sums,
convolutions and repeated products. (2)
$\delta^n\,p(\nu(\sigma + \tau u)/\delta)$ has the coefficients of (2) composed
with $\sigma + \tau u$. (3) Horner's rule
$\tilde p = l_0 + u(l_1 + u(l_2 + \cdots))/s$ in the Chebyshev basis: since
$2u\,T_0 = 2T_1$ and $2u\,T_j = T_{j + 1} + T_{j - 1}$ for $j \ge 1$,
multiplication by $2u$ maps the Chebyshev coefficients $(v_0, v_1, v_2, \dots)$
of a polynomial to $(v_1, 2v_0 + v_2, v_1 + v_3, v_2 + v_4, \dots)$, an integer
operation, and each Horner step doubles the scale. $\square$

*Lean:
[`Eight.WholeIntervalPolynomial.Certificate.Scaled`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L308),
[`Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L313),
[`Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.mul`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L348),
[`Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.centered`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L515),
[`Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.eq_expansion`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L404),
[`Eight.WholeIntervalPolynomial.Certificate.twoX`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L536),
[`Eight.WholeIntervalPolynomial.Certificate.chebList`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L541),
[`Eight.WholeIntervalPolynomial.Certificate.chebList_spec`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L604),
[`Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.coefficient_eq`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L630).*

### Theorem L.3 (a univariate check)

Let $(l, s)$ represent the centred polynomial of $p$ on $[a, b]$, with
$s \ne 0$ and $l$ of length $n + 1 \le D + 1$, let $C_j$ be the integers of
Lemma L.2 (3), and let $\rho = m/d$ with $d > 0$. If

```math
m\,s\,2^{n + 1} < 2d\left(C_0 - \sum_{j = 1}^D |C_j|\right),
```

then $\rho < p(x)$ for every real $x$ in $[a, b]$.

*Proof.* By Lemma L.2 (3),
$C_0 - \sum_{j \ge 1}|C_j| = \frac{s\,2^{n + 1}}2\left(c_0 - \sum_{j \ge 1}|c_j|\right)$,
so the hypothesis says $\frac md < c_0 - \sum_{j \ge 1}|c_j|$. The expansion of
Lemma L.1 holds as $\deg\tilde p \le n \le D$, and (L.1) concludes. $\square$

*Lean:
[`Eight.WholeIntervalPolynomial.Certificate.lowerZ`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L655),
[`Eight.WholeIntervalPolynomial.Certificate.lowerOn_eq_of_rep`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L686),
[`Eight.WholeIntervalPolynomial.Certificate.upperOn_eq_of_rep`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L694),
[`Eight.WholeIntervalPolynomial.positive_on_interval`](../../SquaresInCircles/Eight/Arithmetic/WholeIntervalPolynomial.lean#L101).*

The hypotheses $s \ne 0$, $n \le D$ and the inequality of Theorem L.3 are
closed statements about integers computed from the formula of $p$; each is
proved by `decide +kernel`. The lists themselves are built along the syntax of
$p$ by a tactic that applies the rules of Lemma L.2 (1), so $p$ is never
expanded by hand and no coefficient is copied from elsewhere. The upper bound
of (L.1) is checked in the same way.

## L.3 Two variables

### Lemma L.4 (Chebyshev bound on a square)

Let $q(x, y) = \sum_{a, b \le D} q_{ab}\,x^ay^b$ have rational coefficients
and put $c_{ij} = \sum_{a, b} q_{ab}\,\gamma_{ai}\gamma_{bj}$. Then
$q = \sum_{i, j} c_{ij}\,T_i(x)T_j(y)$, and on $[-1, 1]^2$

```math
c_{00} - \sum_{(i, j) \ne (0, 0)} |c_{ij}| \;\le\; q \;\le\; c_{00} + \sum_{(i, j) \ne (0, 0)} |c_{ij}| .
```

*Proof.* Lemma L.1 in each variable, and $|T_i(x)T_j(y)| \le 1$. $\square$

*Lean:
[`Eight.TensorWholeIntervalPolynomial.coefficient`](../../SquaresInCircles/Eight/Arithmetic/TensorWholeIntervalPolynomial.lean#L64),
[`Eight.TensorWholeIntervalPolynomial.expansion`](../../SquaresInCircles/Eight/Arithmetic/TensorWholeIntervalPolynomial.lean#L82),
[`Eight.TensorWholeIntervalPolynomial.lower_bound`](../../SquaresInCircles/Eight/Arithmetic/TensorWholeIntervalPolynomial.lean#L111),
[`Eight.TwoVariablePolynomial.square_bounds`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L166).*

### Lemma L.5 (rectangles, triangles and trapezoids)

Let $U = \frac{X + 1}2$ and $V = \frac{Y + 1}2$, which run over $[0, 1]$ when
$X, Y$ run over $[-1, 1]$. The substitutions

```math
(x, y) = (aU,\ bV), \qquad (x, y) = (dU(1 - V),\ dUV), \qquad (x, y) = (dU,\ (l + dU)V)
```

map the square $[-1, 1]^2$ onto the rectangle $[0, a] \times [0, b]$, the
triangle $x, y \ge 0$, $x + y \le d$, and the trapezoid $0 \le x \le d$,
$0 \le y \le l + x$ ($a, b, d, l > 0$). So a bound of the substituted
polynomial on the square (Lemma L.4) is a bound of $q$ on the region.

*Proof.* Each map is onto: for the triangle, a point $(x, y) \ne o$ comes from
$U = (x + y)/d$, $V = y/(x + y)$, and $o$ from $U = 0$; the trapezoid is
similar. $\square$

*Lean:
[`Eight.TwoVariablePolynomial.rectangle`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L137),
[`Eight.TwoVariablePolynomial.triangle`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L140),
[`Eight.TwoVariablePolynomial.trapezoid`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L143),
[`Eight.TwoVariablePolynomial.rectangle_bounds`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L186),
[`Eight.TwoVariablePolynomial.triangle_bounds`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L201),
[`Eight.TwoVariablePolynomial.trapezoid_bounds`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L230).*

![Three panels, each the image of a 10 by 10 grid of the square [-1, 1]^2 under one substitution of Lemma L.5, with the lines of constant U in blue and those of constant V in orange: the rectangle (aU, bV) with a straight grid; the triangle (dU(1 - V), dUV) with vertices o, (d, 0) and (0, d), whose lines of constant U are segments parallel to its long side and whose lines of constant V are rays from o, the whole side U = 0 collapsed to o; and the trapezoid (dU, (l + dU)V) over [0, d], whose lines of constant U are vertical segments and whose lines of constant V are segments that, extended, meet at the point (-l, 0)](figures/appendix-l/regions.svg)

*Figure L.1.* Lemma L.5: the images of a grid of the square $[-1, 1]^2$ under
the three substitutions (lines of constant $U$ blue, of constant $V$ orange).
The rectangle is a product; the triangle is covered by segments parallel to
its long side and by rays from $o$, the side $U = 0$ of the square collapsing to
the vertex $o$; the trapezoid by vertical segments and by segments through
$(-l, 0)$. One square, and so one check, covers the whole region.

The kernel computes bivariate coefficients on *packed* natural numbers. A
polynomial $\sum n_{ij}X^iY^j$ of total degree at most $B$ with coefficients
$0 \le n_{ij} < 2^w$ is stored as the single number
$\sum n_{ij}\,2^{w(Si + j)}$, with $S = 2B + 1$, and a polynomial with
coefficients of both signs as the difference of two such numbers. As the
digits of a product of two such polynomials do not overlap, one product of
natural numbers in the kernel computes the product of polynomials, provided no
digit overflows; this is guaranteed by bounds on the sums of the digits, which
are checked along the computation and recorded in a flag that every
representation lemma assumes. The digit sum of a packed number, kept below
$2^w - 1$, is its remainder modulo $2^w - 1$, since $2^w \equiv 1$; so the sum
of the absolute values of the
Chebyshev coefficients of Lemma L.4, computed in one variable and then in the
other by the recurrence of Lemma L.2 (3) with shifts and masks, takes two
remainders.
The substitutions of Lemma L.5 are computed on packed numbers too.

*Lean:
[`Eight.PackedModels.pack`](../../SquaresInCircles/Eight/Arithmetic/PackedModels.lean#L182),
[`Eight.BivariateCertificate.XM`](../../SquaresInCircles/Eight/Arithmetic/BivariateCertificates.lean#L1407),
[`Eight.BivariateCertificate.XM.Rep`](../../SquaresInCircles/Eight/Arithmetic/BivariateCertificates.lean#L1434),
[`Eight.BivariateCertificate.XM.rep_mul`](../../SquaresInCircles/Eight/Arithmetic/BivariateCertificates.lean#L1604),
[`Eight.BivariateCertificate.XM.rep_triangleM`](../../SquaresInCircles/Eight/Arithmetic/BivariateCertificates.lean#L2350),
[`Eight.BivariateCertificate.XM.rep_rectangleM`](../../SquaresInCircles/Eight/Arithmetic/BivariateCertificates.lean#L2360),
[`Eight.BivariateCertificate.XM.final_spec`](../../SquaresInCircles/Eight/Arithmetic/BivariateCertificates.lean#L2514),
[`Eight.BivariateCertificate.XM.lowerCheck`](../../SquaresInCircles/Eight/Arithmetic/BivariateCertificates.lean#L2613),
[`Eight.BivariateCertificate.XM.lower_certificate`](../../SquaresInCircles/Eight/Arithmetic/BivariateCertificates.lean#L2624).*

Often a bivariate numerator vanishes on one side of its region, or its bound is
needed along a side. The restriction of a numerator to the line $y = 0$, the
line $x = 0$, a line $y = tx$ or a polynomial curve is a ring homomorphism to
univariate polynomials, computed on scaled lists, so the univariate checks of
§L.2 apply along the side; an exact quotient by $X$ or by $X(\ell - X)$, which
removes a vanishing side or the two ends of a chord, is verified by multiplying
back.

*Lean:
[`Eight.CertificateRestrictions.yZero`](../../SquaresInCircles/Eight/Arithmetic/CertificateRestrictions.lean#L67),
[`Eight.CertificateRestrictions.onLine`](../../SquaresInCircles/Eight/Arithmetic/CertificateRestrictions.lean#L707),
[`Eight.CertificateRestrictions.RepOn`](../../SquaresInCircles/Eight/Arithmetic/CertificateRestrictions.lean#L329),
[`Eight.CertificateRestrictions.lower_cert`](../../SquaresInCircles/Eight/Arithmetic/CertificateRestrictions.lean#L477),
[`Eight.CertificateRestrictions.edge_div`](../../SquaresInCircles/Eight/Arithmetic/CertificateRestrictions.lean#L628),
[`Eight.CertificateRestrictions.chord_cert`](../../SquaresInCircles/Eight/Arithmetic/CertificateRestrictions.lean#L663).*

## L.4 Trigonometric terms and radicals

### Lemma L.6 (Taylor polynomials)

For $x \ge 0$, with $S_k$ and $C_k$ the Taylor polynomials of degree $k$ of
the sine and the cosine,

```math
S_7 \le \sin x \le S_9, \qquad C_{10} \le \cos x \le C_8, \qquad S_{11} \le \sin x \le S_{13}, \qquad C_{14} \le \cos x \le C_{12}, \qquad S_{15} \le \sin x \le S_{17}, \qquad C_{18} \le \cos x \le C_{16} .
```

For $0 \le x \le \frac7{10}$, $0 \le \sin x - S_{15}(x) < 10^{-15}$ and
$0 \le C_{16}(x) - \cos x < 10^{-15}$.

*Proof.* Each difference vanishes at 0 and its derivative is the difference
before it, so the inequalities follow one from another, starting from
$\sin x \ge S_7(x)$. The remainders are at most
$(\frac7{10})^{17}/17!$ and $(\frac7{10})^{18}/18!$. $\square$

*Lean:
[`Eight.Arithmetic.trig_taylor_bounds`](../../SquaresInCircles/Eight/Arithmetic/Taylor.lean#L75),
[`Eight.HighOrderTaylor.S11_le_sin`](../../SquaresInCircles/Eight/Arithmetic/HighOrderTaylor.lean#L30),
[`Eight.HighOrderTaylor.sin_le_S13`](../../SquaresInCircles/Eight/Arithmetic/HighOrderTaylor.lean#L50),
[`Eight.HighOrderTaylor.C14_le_cos`](../../SquaresInCircles/Eight/Arithmetic/HighOrderTaylor.lean#L60),
[`Eight.HighOrderTaylor.frame_remainders`](../../SquaresInCircles/Eight/Arithmetic/HighOrderTaylor.lean#L116).*

So a sine or a cosine of a frame angle in $[0, \frac7{10}]$ is replaced by a
polynomial on the side that the inequality needs. A frame angle that ranges
over an interval becomes the variable of a check, and a fixed rational value of
$\pi$ or of an angle enters through rational bounds.

### Lemma L.7 (rational majorants of roots)

For $P \ge 0$ and $w > 0$, $\sqrt P \le \frac{P + w^2}{2w}$, with equality
exactly at $w = \sqrt P$. Hence, for polynomials $A$, $P_j \ge 0$ and $w_j > 0$
($j = 1, \dots, k$) and $\bar R \ge 0$, if

```math
2A\prod_j w_j - \bar R\sum_j\left(P_j + w_j^2\right)\prod_{i \ne j} w_i > 0 ,
```

then $A > \bar R\sum_j\sqrt{P_j}$.

*Proof.* $(\sqrt P - w)^2 \ge 0$; divide the hypothesis by $\prod_j w_j$.
$\square$

The bivariate checks of the owner analysis use this with *cubic masses*: $w_j$
is a rational constant $\rho_j$ times the Taylor polynomial
$1 + \frac\delta2 - \frac{\delta^2}8 + \frac{\delta^3}{16}$ of
$\sqrt{1 + \delta}$, with $\delta = (P_j - P_j(0))/P_j(0)$, all truncated to
total degree 3; for $\rho_j$ near $\sqrt{P_j(0)}$ this is a polynomial
approximation of $\sqrt{P_j}$. The positivity of each mass is a check of its
own.

*Lean:
[`Eight.TwoVariablePolynomial.cubicMass`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L129),
[`Eight.GlobalGA.PositiveBT3.LargeCertificate.numerator`](../../SquaresInCircles/Eight/Owners/GA/Positive/BT3LargeData.lean#L67),
[`Eight.GlobalGA.PositiveBT3.LargeCertificate.mass`](../../SquaresInCircles/Eight/Owners/GA/Positive/BT3LargeData.lean#L60).*

### Lemma L.8 (Taylor models)

An expression in two variables $x, y \in [-1, 1]$ built from rational
constants, sums, products, powers, sines and cosines of arguments in
$[0, \frac7{10}]$, square roots and reciprocals has a *model*, computed by
integer operations when the checks below pass: a polynomial $m(x, y)$ and a
number $e \ge 0$ with $|v(x, y) - m(x, y)| \le e$ on the whole square, where
$v$ is the value of the expression. In particular:

1. a product of models is truncated to total degree $B$ and rounded to
   multiples of $2^{-K}$, and the discarded and rounded parts are added to the
   error, bounded by the sums of their absolute coefficients;
2. $\sin$ and $\cos$ use $S_{13}$ and $C_{14}$, with the errors
   $(\frac7{10})^{15}/15!$ and $(\frac7{10})^{16}/16!$, after a check that the
   model of the argument lies in $[0, \frac7{10}]$;
3. $\sqrt v$ and $1/v$ are expanded about a rational $v_0 > 0$ at the constant
   term of the model of $v$: $v = v_0(1 + h)$ with
   $|h| \le \sigma < \frac{19}{200}$, and
   $(1 + h)^{1/2}$ or $(1 + h)^{-1}$ is replaced by its binomial series up to
   degree 12, with the error $|\kappa_{13}|\,\sigma^{13}/(1 - \sigma)$, since
   the absolute binomial coefficients $|\kappa_n|$ decrease from $n = 13$ on.

If all the Bernstein coefficients of degree $n$ in each variable of $m$ are
at least $\rho + e$, then $v \ge \rho$ on the square.

*Proof.* (1) and (2) by the triangle inequality and Lemma L.6. (3) The
binomial series of $(1 + h)^\alpha$ converges for $|h| < 1$, and its tail from
degree 13 is at most $|\kappa_{13}|\sum_{k \ge 0}\sigma^{13 + k}$. The Bernstein
polynomials of degree $n$ in each variable are nonnegative on the square and
add up to 1. $\square$

*Lean:
[`Eight.PackedModels.Model`](../../SquaresInCircles/Eight/Arithmetic/PackedModels.lean#L840),
[`Eight.PackedModels.Model.Contains`](../../SquaresInCircles/Eight/Arithmetic/PackedModels.lean#L858),
[`Eight.PackedModels.Model.contains_mul`](../../SquaresInCircles/Eight/Arithmetic/PackedModels.lean#L1373),
[`Eight.PackedModels.Model.contains_sin`](../../SquaresInCircles/Eight/Arithmetic/PackedModels.lean#L1587),
[`Eight.PackedModels.Model.contains_sqrt`](../../SquaresInCircles/Eight/Arithmetic/PackedModels.lean#L2836),
[`Eight.RoundedBinomialEnclosure.binomial_remainder`](../../SquaresInCircles/Eight/Arithmetic/RoundedBinomialEnclosure.lean#L116),
[`Eight.PackedModels.IE.eval_sound`](../../SquaresInCircles/Eight/Arithmetic/PackedModels.lean#L3092),
[`Eight.PackedModels.bernCheck_sound`](../../SquaresInCircles/Eight/Arithmetic/PackedModels.lean#L2519),
[`Eight.PackedModels.check_lt`](../../SquaresInCircles/Eight/Arithmetic/PackedModels.lean#L3317).*

A second family of models, with exact rational coefficients, certifies a root
or a reciprocal by its residual: if $r$ is any polynomial and $P$ the model of
$v$, then $|\sqrt v - r| \le |v - r^2|/(\sqrt v + r)$ and
$|1/v - r| = |1 - vr|/v$, and the norms of $r^2 - P$ and $Pr - 1$ bound the
numerators. The square-root domains, the denominators and the trigonometric
arguments are checked on the rationals.

*Lean:
[`Eight.TensorResidualEnclosure.Contains.root`](../../SquaresInCircles/Eight/Owners/Tensor/ResidualEnclosure.lean#L51),
[`Eight.TensorResidualEnclosure.Contains.reciprocal`](../../SquaresInCircles/Eight/Owners/Tensor/ResidualEnclosure.lean#L103),
[`Eight.TensorRadicalExpression.Expr.Valid`](../../SquaresInCircles/Eight/Arithmetic/TensorRadicalExpression.lean#L65),
[`Eight.TensorRadicalExpression.Expr.contains`](../../SquaresInCircles/Eight/Arithmetic/TensorRadicalExpression.lean#L108).*

## L.5 A worked example

In the word analysis of [Chapter 11](11-eight.md), a reference contact at the
frame angle $p \in [\frac{11}{50}, \frac7{10}]$ and the squared radius
$q \in [\frac{19577}{5000}, \frac{9789}{2500}]$ defines a gap $g(p)$, and the
proof needs $g' > 0$. With $R = \sqrt q$, $u = \sqrt{q/2} - 1 - \sin p$,
$z = \sqrt{q - u^2}$, the point
$(x, y) = (z\cos p - u\sin p,\ z\sin p + u\cos p)$ of the circle of radius $R$,
$\beta = x(1 - \cos p/z)$ and $\ell = 1 + \cos\frac7{10} - y$,

```math
g' = \beta\left(\frac\ell{\sqrt{q - \ell^2}} + \frac yx\left(1 - \frac{\cos p}R\right)\right) - \frac{x\sin p}R ,
```

a function of $p$ and $q$ with four radicals and several quotients.

*The polynomial.* Let $S_3$, $S_5$, $C_2$, $C_4$ be Taylor polynomials of the
sine and the cosine in $p$, $R_\ell = \frac{19787}{10000}$ and
$R_h = \frac{4947}{2500}$ (bounds of $R$), $Z_\ell = \frac{981}{500}$ (a lower
bound of $z$), $P_\ell = \frac{3991}{10000}$ and $P_h = \frac{3993}{10000}$
(bounds of $\sqrt{q/2} - 1$), and

```math
\begin{gathered}
Y_\ell = (Z_\ell - C_4)S_3 + P_\ell C_2, \qquad Y_h = (R_h - C_2)S_5 + P_h C_4, \qquad X_\ell = Z_\ell C_2 - P_h S_5 + S_3^2, \qquad X_h = R_h C_4 - P_\ell S_3 + S_5^2, \\
A_\ell = 1 - C_4/Z_\ell, \qquad L_\ell = \tfrac{1103}{625} - Y_h, \qquad N = R_\ell\,X_\ell A_\ell\left(L_\ell X_h + R_h\,Y_\ell A_\ell\right) - R_h\,X_h^2\,S_5 ,
\end{gathered}
```

a polynomial in $p$ of degree 27 with rational coefficients.

*The check.* A scaled list representing $N$ is built along this formula. It is
centred on $[\frac{11}{50}, \frac7{10}]$ with $\nu = 1$, $\delta = 50$,
$\sigma = 23$, $\tau = 12$, since $\frac{a + b}2 = \frac{23}{50}$ and
$\frac{b - a}2 = \frac{12}{50}$; its 28 Chebyshev coefficients are computed; and
the inequality of Theorem L.3 for $\rho = \frac{8179}{10000}$ is decided. In
exact arithmetic $c_0 \approx 2.23622$ and
$\sum_{j \ge 1}|c_j| \approx 1.41830$, almost all of it from
$|c_1| \approx 1.22176$ and $|c_2| \approx 0.19456$; the coefficients from $c_3$
on are below $0.0016$ and fall to $10^{-34}$. So
$N > c_0 - \sum|c_j| \approx 0.817922 > 0.8179$ on the interval (Figure L.2).
The same check proves $Y_\ell$, $Y_h$, $X_\ell$, $X_h$, $A_\ell$ and $L_\ell$
positive there, at degree 10.

*The transfer.* From the circle and contact formulas, on the same interval and
for the same $q$: $R_\ell \le R \le R_h$, $Z_\ell < z \le R$,
$X_\ell \le x \le X_h$, $Y_\ell \le y$, $L_\ell \le \ell$,
$X_\ell A_\ell \le \beta$, $A_\ell \le 1 - \cos p/R$ and $0 \le \sin p \le S_5$,
with the polynomials evaluated at $p$. Replacing each factor of $g'$ by its
bound in the unfavourable direction, and the radical $\sqrt{q - \ell^2} \le R$
by $R_h$,

```math
g' \ge X_\ell A_\ell\left(\frac{L_\ell}{R_h} + \frac{Y_\ell A_\ell}{X_h}\right) - \frac{X_h S_5}{R_\ell} = \frac N{R_\ell R_h X_h} > 0 .
```

So the reference gap increases on $[\frac{11}{50}, \frac7{10}]$.

*Lean:
[`Eight.OutsideDE2Polynomial.certificate`](../../SquaresInCircles/Eight/Words/Outside/EEndpoint.lean#L50),
[`Eight.OutsideDE2Polynomial.expansion_identity`](../../SquaresInCircles/Eight/Words/Outside/EEndpoint.lean#L80),
[`Eight.OutsideDE2Polynomial.coefficient_reserve`](../../SquaresInCircles/Eight/Words/Outside/EEndpoint.lean#L87),
[`Eight.OutsideDE2Polynomial.certificate_positive`](../../SquaresInCircles/Eight/Words/Outside/EEndpoint.lean#L104),
[`Eight.OutsideDE2Polynomial.factor_positive`](../../SquaresInCircles/Eight/Words/Outside/EEndpoint.lean#L171),
[`Eight.OutsideDE2Polynomial.derivative_lower_positive`](../../SquaresInCircles/Eight/Words/Outside/EEndpoint.lean#L197),
[`Eight.OutsideDE2Polynomial.derivative_positive`](../../SquaresInCircles/Eight/Words/Outside/EEndpoint.lean#L220),
[`Eight.OutsideDE2Reference.Bounds`](../../SquaresInCircles/Eight/Words/Outside/EEndpoint.lean#L349),
[`Eight.OutsideDE2Reference.derivative_pos`](../../SquaresInCircles/Eight/Words/Outside/EEndpoint.lean#L453),
[`Eight.OutsideDE2Reference.gap_deriv`](../../SquaresInCircles/Eight/Words/Outside/ECycle.lean#L235),
[`Eight.OutsideDE2Reference.gap_strictMono`](../../SquaresInCircles/Eight/Words/Outside/ECycle.lean#L335).*

![Two panels. Left: the polynomial N of degree 27 against p from 11/50 to 7/10, decreasing from about 3.65 to its least value, about 1.21, at 7/10, and the dashed horizontal line of the Chebyshev bound c0 - sum |cj|, about 0.818, below the whole curve. Right: the absolute values of the 28 Chebyshev coefficients c0 to c27 on a logarithmic scale, from about 2.2 and 1.2 down to about 10^-34, falling roughly geometrically](figures/appendix-l/example.svg)

*Figure L.2.* The check of §L.5. Left: the polynomial $N$ on
$[\frac{11}{50}, \frac7{10}]$ (solid) and the bound
$c_0 - \sum_{j \ge 1}|c_j| \approx 0.8179$ of Lemma L.1 (dashed), which lies
below $N$ everywhere. Right: the Chebyshev coefficients $|c_j|$ on a
logarithmic scale; past $j = 2$ they are too small to matter.

## L.6 Interval evaluation

Appendix J and §M.6 bound expressions with square roots and reciprocals on
boxes by interval arithmetic instead.

### Lemma L.9 (interval evaluation)

Let an expression in $n$ variables be built from rational constants, sums,
negatives, products, powers, reciprocals and square roots, and let a box of
rational intervals be given.

1. *(Fixed point.)* Enclose every input by integers $l, h$ with
   $l\,2^{-p} \le x \le h\,2^{-p}$, and every operation by rounding its
   integer result outwards at the scale $2^{-p}$; a reciprocal or a square root
   is admitted only if the enclosure of its argument has a positive lower end.
   If one pass succeeds, the value of the expression at every point of the box
   lies in the final enclosure, and every radicand and every inverted value is
   positive on the box.
2. *(Rational.)* Give each square root, and any subexpression, a rational
   bracket, and check on the rationals that every reciprocal has an argument of
   positive interval value, that every square-root bracket is nonnegative and
   its ends square to bounds of the interval value of its argument, and that
   every other bracket contains the interval value of its subexpression. Then
   the value at every point of the box lies in the interval value.

*Proof.* Each operation of interval arithmetic contains the results of the
operation on members of its operands; a product lies between the four products
of the endpoints; outward rounding only enlarges an interval. Induction on the
expression. $\square$

*Lean:
[`Eight.Stationary.FixedEval.DI`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L1199),
[`Eight.Stationary.FixedEval.eval_sound`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L1422),
[`Eight.Stationary.FixedEval.bounded_sound`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L1512),
[`Eight.Stationary.FixedEval.regular_sound`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L1531),
[`Eight.Arithmetic.QInterval`](../../SquaresInCircles/Eight/Arithmetic/Interval.lean#L27),
[`Eight.Arithmetic.QInterval.product_between_corners`](../../SquaresInCircles/Eight/Arithmetic/Interval.lean#L69),
[`Eight.Arithmetic.QInterval.mem_sqrt`](../../SquaresInCircles/Eight/Arithmetic/Interval.lean#L144),
[`Eight.Arithmetic.ScalarExpr.Valid`](../../SquaresInCircles/Eight/Arithmetic/ScalarExpr.lean#L73),
[`Eight.Arithmetic.ScalarExpr.sound`](../../SquaresInCircles/Eight/Arithmetic/ScalarExpr.lean#L90).*

The fixed-point evaluation, at 80 to 200 bits, gives the bounds of
Lemma J.2 and Proposition J.5 (46 checks); the rational one gives the eighteen
bounds on the box of parameters of the family in §M.6 (54 checks).

## L.7 The checks of the proof

| kind of check | method | modules | `decide +kernel` |
| --- | --- | --: | --: |
| one variable on an interval | §L.1, §L.2 | 40 | 526 |
| two variables on a triangle, rectangle or trapezoid, and along its sides | §L.3, Lemma L.7 | 15 | 137 |
| Taylor models with sines, cosines, roots and reciprocals | Lemma L.8 | 7 | 7 |
| interval evaluation | §L.6 | 2 | 100 |
| identities of formulas, finite enumerations | | 3 | 9 |
| total | | 67 | 779 |

*Table L.1.* The kernel checks of the proof of eight squares, by kind, counted
as occurrences of `decide +kernel` in the Lean files. One occurrence may decide
a conjunction: an inequality with its side conditions ($s \ne 0$, the length of
a list, the flag of a packed model), or the same check for several cases.

All of the checks of the first three kinds belong to the owner and word analysis
of Chapter 11. A typical one-variable check proves, on an interval of a frame
angle, that a margin, a gap, a derivative or a weighted sum of constraints is
positive, after Taylor polynomials have replaced the sines and cosines and
rational bounds the constants; the Chebyshev expansions have degrees from a few
units up to 84. The two-variable checks bound, over triangles, rectangles and
trapezoids of two angles, numerators of weighted sums with cubic masses (Lemma
L.7) and their restrictions to the sides, with degrees up to 39 in each
variable, and a tangent cap on the square $[0, 0.09]^2$ by one tensor expansion
of degree 14. The seven Taylor-model checks each decide a whole list of
inequalities at once, on the gains and derivatives of the sign cases of the
sliding square $T$, whose formulas mix roots, reciprocals, sines and cosines.
The interval evaluations are those of Appendix J and §M.6. The last line of
Table L.1 counts the six identities between the symbolic derivatives of the
stationary formulas (§J.1) and the finite enumerations of the quarter words and
of the four-type walks of Chapter 11.
