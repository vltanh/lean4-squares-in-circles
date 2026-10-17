# A hand bound for the nonaligned mid/core contact regime

This proves one continuous regime of the four-type pair theorem. The proof
uses four fixed curvature intervals and one rational test point. It does
not use a subdivision tree or a numerical minimization result.

## Labels and the separating-axis reduction

Let

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad \beta=\frac9{50},
 \quad g=\frac{269343}{250000}=1.077372,
\]

\[
 c_M=-\frac{2143075}{10^6},\quad
 p=\frac{1489593}{10^6},\quad q=\frac{1580219}{10^6}.
\tag{1}
\]

Use the mid label \(\ell_M(a,b)=c_M+pa+qb\). For the core label
take

\[
 \ell_C(A,B)=p_C(A-7/12)+gB,\qquad p_C\le-2.
\tag{2}
\]

Every core-boundary state has \(A\le7/12\). No endpoint-identification
condition on the lifted potential is needed; see
`LIFTED_STATE_POTENTIAL_TELESCOPING.md`.

Consider negative signed tangents on both the outer source and the core
target. Separation on the source \(-e\) axis means

\[
 M=a-A\cos\phi+B\sin\phi-1-h(\phi)\ge0,
\]

and the corrected cost is

\[
 C=\phi-\beta h(\phi)-\ell_M(a,b)+\ell_C(A,B).
\]

We prove

\[
 \boxed{C>\frac{1801}{2000}=0.9005}
 \qquad\text{for }1\le\phi\le\frac{29}{25}.
\tag{3}
\]

Put \(s=\sin\phi\), \(c=\cos\phi\), and choose
\(\lambda=g/s>0\). Subtracting \(\lambda M\) cancels the core's
\(B\)-coefficient. Its remaining coefficient is
\(p_C+g\cot\phi<0\): throughout this interval
\(g\cot\phi<1\), whereas \(p_C\le-2\).
Thus the core contribution is minimized at its largest primary
coordinate \(A=7/12\), giving exactly \((7\lambda/12)c\).

The source coefficient pair is \((-p-\lambda,-q)\). Enlarge its
outer arc to the full circle of centre \((-1/2,-1/2)\) and radius
\(R\). Its support minimum is

\[
 \frac{p+q+\lambda}{2}
 -R\sqrt{(p+\lambda)^2+q^2}.
\]

Using \(h=(s+c-1)/2\) and collecting terms proves \(C\ge F(\phi)\),
where

\[
 F(\phi)=\phi-\frac\beta2(s+c-1)-c_M
 +\frac{p+q+g}{2}
 +\frac g{s}+\frac{13g}{12}\frac c{s}
 -R\sqrt{(p+g/s)^2+q^2}.
\tag{4}
\]

The remainder of the proof is a scalar inequality for this explicitly
specified function.

## Derivatives with the cancellations retained

Write

\[
 X=p+g/s,\qquad N=\sqrt{X^2+q^2},\qquad Z=RX/N.
\]

Direct differentiation gives

\[
 F'=1+\frac\beta2(s-c)
 +\frac g{s^2}\left[c(Z-1)-\frac{13}{12}\right],
\tag{5}
\]

\[
 F''=\frac\beta2(s+c)
 +\frac g{s^3}\left[(1+c^2)(1-Z)+\frac{13}{6}c\right]
 -\frac{Rq^2g^2c^2}{s^4N^3}.
\tag{6}
\]

The identity (6) can also be checked from
\(\lambda'=-gc/s^2\), \(\lambda''=g(1+c^2)/s^3\), and
\((X/N)'=q^2\lambda'/N^3\).

## Four fixed intervals prove positive curvature

In the following table all numbers after the first column are integer
numerators with common denominator \(1000\). They assert

\[
 s_j^-<\sin x_j<s_j^+,\quad
 c_j^-<\cos x_j<c_j^+,\quad
 Z(x_j)<z_j^+,\quad N(x_j)>n_j^-.
\]

For the last two columns use the conservative bound
\(R<1979/1000\).

| \(x_j\) | \(1000s_j^-\) | \(1000s_j^+\) | \(1000c_j^-\) | \(1000c_j^+\) | \(1000z_j^+\) | \(1000n_j^-\) |
|---|---:|---:|---:|---:|---:|---:|
| \(1\) | 841 | 842 | 540 | 541 | 1720 | 3188 |
| \(26/25\) | 862 | 863 | 506 | 507 | 1715 | 3161 |
| \(27/25\) | 881 | 882 | 471 | 472 | 1710 | 3138 |
| \(28/25\) | 900 | 901 | 435 | 436 | 1706 | 3115 |
| \(29/25\) | 916 | 917 | 399 | 400 | 1703 | 3097 |

Here is a direct rational procedure to check every entry. For sine use
the lower Taylor polynomial through degree 11 and upper polynomial
through degree 13; for cosine use the lower polynomial through degree
10 and upper polynomial through degree 12. The alternating remainder
has the stated sign on \([0,6/5]\). For a row set

\[
 X^+=p+g/s_j^-,\qquad X^-=p+g/s_j^+.
\]

The last columns follow from the rational comparisons

\[
 (z_j^+)^2\bigl[(X^+)^2+q^2\bigr]
  >(1979/1000)^2(X^+)^2,
\qquad (X^-)^2+q^2>(n_j^-)^2.
\tag{7}
\]

The monotonicity of \(X/\sqrt{X^2+q^2}\) for \(X>0\) justifies
the first comparison. These tests involve rational arithmetic only.

Both \(N\) and \(Z\) decrease with \(\phi\) on the interval,
because \(s\) increases and \(X\) decreases. Also \(s+c\)
decreases there. On the interval \([x_j,x_{j+1}]\), define the rational
numbers

\[
 B_j=(1+(c_j^+)^2)(1-z_j^+)+\frac{13}{6}c_{j+1}^-,
\]

\[
 D_j=\frac\beta2(s_{j+1}^-+c_{j+1}^-)
 +\frac g{(s_{j+1}^+)^3}B_j
 -\frac{(1979/1000)q^2g^2(c_j^+)^2}
 {(s_j^-)^4(n_{j+1}^-)^3}.
\tag{8}
\]

Substitution of the displayed three-digit table gives the following
strict rational lower bounds:

| Interval | \(B_j\) is greater than | \(D_j\) is greater than |
|---|---:|---:|
| \([1,26/25]\) | \(165/1000\) | \(294/1000\) |
| \([26/25,27/25]\) | \(121/1000\) | \(226/1000\) |
| \([27/25,28/25]\) | \(74/1000\) | \(159/1000\) |
| \([28/25,29/25]\) | \(24/1000\) | \(96/1000\) |

In particular each \(B_j\) is positive. Formula (6), with the indicated
monotonic endpoint bounds, gives \(F''\ge D_j\). The negative
coefficient \(1-z_j^+\) is multiplied by the upper bound
\(1+(c_j^+)^2\), so that direction of the comparison is preserved.
We have proved on the entire interval

\[
 F''>\frac1{20}.
\tag{9}
\]

## One rational test point

At \(x_0=27/25\), use these four closed rational brackets, with common
denominator \(10^9\):

| Quantity | Lower numerator | Upper numerator |
|---|---:|---:|
| \(\sin x_0\) | 881957806 | 881957807 |
| \(\cos x_0\) | 471328364 | 471328365 |
| \(R\) | 1978787507 | 1978787508 |
| \(N(x_0)\) | 3138070988 | 3138070991 |

For the trigonometric entries, the same alternating Taylor bounds
through degrees 19/21 for sine and 18/20 for cosine suffice. The two
root entries follow by squaring; for \(N\), use
\(p+g/s^+\le X\le p+g/s^-\).

Substitution in (4), taking the sign of each term into account, gives

\[
 F(x_0)>\frac{4503}{5000}=0.9006.
\tag{10}
\]

For completeness, (10) follows by the single rational comparison

\[
 x_0-\frac\beta2(s^++c^+-1)-c_M
 +\frac{p+q+g}{2}+\frac g{s^+}
 +\frac{13g}{12}\frac{c^-}{s^+}-R^+N^+
 >\frac{4503}{5000}.
\]

Formula (5), with the same brackets, gives

\[
 |F'(x_0)|<\frac1{2500}.
\tag{11}
\]

One explicit way to check the sign-sensitive last substitution is to
bound \(Z\) between
\(R^-(p+g/s^+)/N^+\) and \(R^+(p+g/s^-)/N^-\).
Then \(Z-1>0\) but \(c(Z-1)-13/12<0\); use those signs in (5).
The resulting derivative interval lies inside
\((-296/10^6,-295/10^6)\), which is already stronger than (11).

Integrating (9) and completing the square proves for every \(\phi\)
in the stated interval

\[
 F(\phi)\ge F(x_0)-\frac{F'(x_0)^2}{2(1/20)}
 >\frac{4503}{5000}-\frac1{625000}
 =\frac{1801}{2000}+\frac{123}{1250000}.
\]

This establishes (3) with a strict rational reserve. Reversal followed
by reflection proves the corresponding positive core/mid target-axis
regime as well.
