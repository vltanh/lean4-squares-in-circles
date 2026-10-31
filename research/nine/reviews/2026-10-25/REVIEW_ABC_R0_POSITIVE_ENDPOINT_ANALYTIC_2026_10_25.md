# Independent review: the table-free positive R0 endpoint

Date: October 25, 2026. Reviewer: `certificate_reduction`, independent
of the positive-endpoint author `root`.

**Verdict: PASS.** `ABC_R0_POSITIVE_ENDPOINT_ANALYTIC.md` proves
\(M_+(x)>0\) on the entire half-line \(x\ge1\). Its proof uses
global Taylor remainder signs, direct rational comparisons and a short
completed-square identity. No Bernstein coefficients, finite sign table,
numerical sample or unproved tail truncation is required.

This review covers the positive-endpoint source and its use in the
original pressure theorem. The separate angular reduction and negative
endpoint were authored by this reviewer; their independent acceptance
must come from a different reviewer.

## 1. Exact endpoint and signs of the comparisons

I compared the endpoint in Section 1 directly with equation (15) of
`ABC_R0_ANGULAR_ENDPOINT_REDUCTION.md`. They agree term by term:

\[
 K\left(\sqrt{x^2+1}-\frac{rx}{2\sqrt{x^2+1}}
 +\frac{rx^3}{16(x^2+1)^{5/2}}\right)
 -\sqrt{2x^2+1}-\frac{rx}{\sqrt{2x^2+1}}
 -\frac x2+\frac{8+16r}{25}.
\]

Every denominator is positive for \(x\ge1\), and \(K,r\) are
positive. With \(t=1/x^2\ge0\), the five Taylor or tangent bounds
are used in the correct directions. A lower bound is used for each
positively multiplied term, and an upper bound for each subtracted
term. In particular the possibly negative tangent lower bound for
\((1+t)^{-5/2}\) is valid even at \(x=1\); its positivity is neither
assumed nor needed.

The third derivative of \(\sqrt{1+t}\) is positive on \([0,\infty)\),
so its quadratic Taylor polynomial is a lower bound. The third
derivative of \((1+t)^{-1/2}\) is negative there, so its quadratic
Taylor polynomial is an upper bound. The other two bounds follow from
global concavity or convexity. Consequently the proof uses rigorous
whole-domain inequalities, rather than asymptotic expansions.

## 2. Independent reconstruction of the six coefficients

I expanded the five comparison terms separately. Their contributions
to the powers of \(x\) are

\[
 K\sqrt{x^2+1}\ge Kx+\frac K{2x}-\frac K{8x^3},
\]

\[
 -\frac{Krx}{2\sqrt{x^2+1}}
 \ge-\frac{Kr}{2}+\frac{Kr}{4x^2}-\frac{3Kr}{16x^4},
\]

\[
 \frac{Krx^3}{16(x^2+1)^{5/2}}
 \ge\frac{Kr}{16x^2}-\frac{5Kr}{32x^4},
\]

\[
 -\sqrt{2x^2+1}\ge-\sqrt2x-\frac{\sqrt2}{4x},
\]

\[
 -\frac{rx}{\sqrt{2x^2+1}}
 \ge-\frac12+\frac1{8x^2}-\frac3{64x^4}.
\]

Adding the remaining \(-x/2+(8+16r)/25\) gives exactly all six
displayed coefficients A--F of the source, including
\(D=79r/128+1/8\) and \(F=869r/1280+3/64\).

The bounds \(140/99<\sqrt2<99/70\) have the stated squared integer
reserves. Taking reciprocals gives \(70/99<r<99/140\), with the
correct reversal of the inequalities. Substituting these bounds proves
each of the six rational relaxations. I independently checked the exact
positive rational comparisons; no decimal value was used to establish
a sign.

Multiplication of the relaxed expression by \(1500x^4>0\) gives
precisely

\[
 P(x)=90x^5-639x^4+950x^3+840x^2-375x-795.
\]

At least one coefficient relaxation is strict, and all its multipliers
are positive. The resulting lower inequality for \(M_+\) is therefore
strict over the whole original domain.

## 3. The quintic proof covers every x >= 1

I differentiated P and independently expanded \(P'(1+z)\) using exact
rational arithmetic. The result is

\[
 2049+1512z-2118z^2-756z^3+450z^4.
\]

For \(0\le z\le1/2\), the displayed lower bound is exactly 1425.
Together with \(P(1)=71\), this proves positivity on the first closed
interval, including its upper endpoint.

I independently multiplied out the entire completed-square identity
in Section 3.2. The cubic multiplier

\[
 Q(x)=90x^3+36x^2-365x/8-135/16
\]

reproduces every coefficient of P after adding the stated linear and
constant remainder. Its derivative is positive for every \(x\ge3/2\),
and direct substitution gives \(Q(3/2)=2463/8>300\). The constant
remainder \(44085/512\) is greater than 80. Therefore P is strictly
greater than the stated quadratic in \(y=x-15/4\).

This comparison is valid even at \(y=0\), because the constant
comparison remains strict. Its quadratic has positive leading
coefficient and negative discriminant:
\((26025/128)^2<204^2<4\cdot300\cdot80\). It is positive for
every real y, hence for the complete unbounded tail. No large-x cutoff
or additional interval is implicit in the argument.

## 4. Original scalar and pressure reserve are preserved

I read Section 4 of `ABC_R0_FULL_ANGLE_BLOCK_PRESSURE.md` directly.
It requires precisely the original strict scalar positivity at the two
genuine ratios \((\mu/\gamma,D)\) and \((\eta/\nu,-D)\).
It does not require the new lower bound \(M_+\) to have a particular
uniform numerical reserve.

The pressure reserve comes afterward from the unchanged Cauchy bound

\[
 [1+h(D)]^2+[1+h(-D)]^2\le2434/625
\]

and the unchanged strict comparison
\(79/40-\sqrt{2434}/25>1/640\). Thus the new endpoint proof
preserves the original block-pressure lower bound

\[
 c_H\mathbin{\cdot}F_{\rm block}
    >\sqrt{\gamma^2+\nu^2}/640>0.
\]

Once the independently reviewed angular reduction and negative endpoint
are joined, all \(x\ge1\) and both closed angular endpoints are
included. The already accepted elementary small-ratio proof covers
\(0\le x\le1\), including the common interface. No force ratio is
fixed or bounded above; no physical square, force, true degree, contact
normal, application mean, circle mask or completion square is changed.

This positive-endpoint result creates no new geometric gate by itself.
It is suitable for replacing the remaining large-ratio scalar
certificate after the separate angular/negative-endpoint review passes.
No Lean compilation, CI or workflow dispatch was run.
