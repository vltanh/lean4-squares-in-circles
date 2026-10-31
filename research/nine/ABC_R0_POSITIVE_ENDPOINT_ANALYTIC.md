# ABC R0: the positive angular endpoint has an elementary proof

Date: October 25, 2026. Author: root.

**Status: accepted complete hand proof after two independent reviews.**
See `REVIEW_ABC_R0_POSITIVE_ENDPOINT_ANALYTIC_2026_10_25.md` and
`REVIEW_ABC_R0_TABLE_FREE_2026_10_25.md`.
This supplies the entire positive-endpoint inequality in
`ABC_R0_ANGULAR_ENDPOINT_REDUCTION.md`, with no coefficient certificate,
angle subdivision or bounded force-ratio assumption.

## 1. Exact endpoint and claim

Put K=79/40, r=1/sqrt(2), L=x^2+1, and let x>=1. The exact endpoint is

\[
\begin{aligned}
 M_+(x)={}&K\left(\sqrt L-\frac{rx}{2\sqrt L}
                         +\frac{rx^3}{16L^{5/2}}\right)\\
 &-\frac{2x^2+1+rx}{\sqrt{2x^2+1}}-\frac x2
       +\frac{8+16r}{25}.
\end{aligned}
\tag{1}
\]

**Theorem.** M_+(x)>0 for every real x>=1.

All denominators in (1) are positive. This is the endpoint of a lower
comparison for the original scalar, not an additional physical
restriction or a replacement of the actual force ratio by a special
value.

## 2. Five global Taylor and tangent inequalities

For every t>=0, elementary Taylor remainder signs and convexity give

\[
\begin{aligned}
 \sqrt{1+t}&\ge1+\frac t2-\frac{t^2}{8},\\
 \sqrt{1+t/2}&\le1+\frac t4,\\
 (1+t)^{-1/2}&\le1-\frac t2+\frac{3t^2}{8},\\
 (1+t)^{-5/2}&\ge1-\frac{5t}{2},\\
 (1+t/2)^{-1/2}&\le1-\frac t4+\frac{3t^2}{32}.
\end{aligned}
\tag{2}
\]

For precision, the third derivative of sqrt(1+t) is positive, so its
quadratic Taylor polynomial is a lower bound on the entire nonnegative
axis. The third derivative of (1+t)^(-1/2) is negative, so its quadratic
Taylor polynomial is an upper bound there; replacing t by t/2 gives
the last line. The other two lines are respectively the tangent upper
bound for a concave function and the tangent lower bound for a convex
function. A possibly negative tangent lower bound remains valid. These
are global inequalities with controlled remainders, not truncated
asymptotic series.

Apply (2) with t=1/x^2. In particular

\[
 \frac{rx}{\sqrt{2x^2+1}}
       =\frac12(1+t/2)^{-1/2},\qquad
 \frac{rx^3}{L^{5/2}}=\frac r{x^2}(1+t)^{-5/2}.
\]

Keeping the signs of every multiplier in (1) gives

\[
 M_+(x)\ge A x+B+\frac Cx+\frac D{x^2}
                         -\frac E{x^3}-\frac F{x^4},
\tag{3}
\]

where

\[
\begin{aligned}
 A&=\frac{59}{40}-\sqrt2,&
 B&=-\frac9{50}-\frac{139r}{400},\\
 C&=\frac{79}{80}-\frac{\sqrt2}{4},&
 D&=\frac{79r}{128}+\frac18,\\
 E&=\frac{79}{320},&
 F&=\frac{869r}{1280}+\frac3{64}.
\end{aligned}
\tag{4}
\]

The elementary enclosure

\[
 \frac{140}{99}<\sqrt2<\frac{99}{70},
 \qquad \frac{70}{99}<r<\frac{99}{140}
\tag{5}
\]

has squared integer reserves two and one. Substitution in (4) proves

\[
 A>\frac3{50},\quad B>-\frac{213}{500},\quad
 C>\frac{19}{30},\quad D>\frac{14}{25},\quad
 E<\frac14,\quad F<\frac{53}{100}.
\tag{6}
\]

For example the respective useful comparisons are
A>17/280>3/50, C>71/112>19/30, and
D>3557/6336>14/25. For B and F, inserting r<99/140 gives
B>-9/50-13761/56000>-213/500 and
F<94431/179200<53/100. Every inequality is a direct positive rational
comparison.

Since x>0, (3)--(6) yield the single strict lower bound

\[
 M_+(x)>
 \frac{3x}{50}-\frac{213}{500}+\frac{19}{30x}
       +\frac{14}{25x^2}-\frac1{4x^3}-\frac{53}{100x^4}
       =\frac{P(x)}{1500x^4},
\tag{7}
\]

with the short quintic

\[
 P(x)=90x^5-639x^4+950x^3+840x^2-375x-795.
\tag{8}
\]

## 3. Positivity of the quintic on the entire half-line

### 3.1. The interval 1<=x<=3/2

Write z=x-1, so 0<=z<=1/2. Direct differentiation and expansion give

\[
 P'(1+z)=2049+1512z-2118z^2-756z^3+450z^4.
\]

Drop its nonnegative variable terms and use z^2<=1/4 and z^3<=1/8:

\[
 P'(1+z)\ge2049-\frac{2118}{4}-\frac{756}{8}=1425>0.
\]

Hence P(x)>=P(1)=71>0 throughout this interval.

### 3.2. The entire tail x>=3/2

The following is an exact polynomial identity:

\[
\begin{aligned}
 P(x)={}&\left(x-\frac{15}{4}\right)^2 Q(x)
       +\frac{26025}{128}\left(x-\frac{15}{4}\right)
       +\frac{44085}{512},\\
 Q(x)={}&90x^3+36x^2-\frac{365}{8}x-\frac{135}{16}.
\end{aligned}
\tag{9}
\]

Here Q'(x)=270x^2+72x-365/8>0 for x>=3/2, and
Q(3/2)=2463/8>300. Also 44085/512>80. With y=x-15/4,
(9) therefore implies

\[
 P(x)>300y^2+\frac{26025}{128}y+80.
\tag{10}
\]

The quadratic on the right is positive for every real y. Its leading
coefficient is positive and its discriminant is negative, because

\[
 0<\frac{26025}{128}<204,
 \qquad 204^2=41616<96000=4\cdot300\cdot80.
\]

This proves P(x)>0 for all x>=3/2 without solving a critical point,
subdividing the unbounded tail, or invoking a finite sign table.
Together with Section 3.1 and (7), it proves the theorem.

## 4. Join to the full-angle pressure argument

`ABC_R0_ANGULAR_ENDPOINT_REDUCTION.md` proves that for every original
x>=1 and -1/sqrt(2)<=d<=1/sqrt(2), the original scalar is at least
min(M_-(x),M_+(x)). Its complete negative-endpoint proof and the present
positive-endpoint theorem therefore prove strict positivity throughout
that entire domain. Section 2 of `ABC_R0_WEIGHTED_CAUCHY_REDUCTION.md`
already gives a table-free proof for 0<=x<=1, including x=0.

Only strict positivity of that scalar is required in Section 4 of
`ABC_R0_FULL_ANGLE_BLOCK_PRESSURE.md`. Applying it at the unchanged
ratios (mu/gamma,D) and (eta/nu,-D), followed by the same Cauchy bound,
retains the original strict block-pressure reserve

    c_H dot F_block > sqrt(gamma^2+nu^2)/640 > 0.

Thus no claimed pressure constant is weakened by the endpoint lower
bound in (7). Both actual positive force ratios remain arbitrary and
unbounded; every original angle, circle mask, contact owner, application
mean and completion square remains in the physical assembly.

Independent review of the full angular reduction and both endpoints has
passed. The current270-sign packet is fully superseded. This replacement
does not itself close a new geometric case or the unrestricted theorem.
No Lean compilation, CI or workflow dispatch is used.
