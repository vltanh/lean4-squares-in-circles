# Wrong word 0010111: every core/core entry

## Statement

For the exact rational role labels of the word 0010111, every allowed
core/core pair has corrected cost

\[
 C>.898>\frac{17953}{20000}.
 \tag{1}
\]

This is a hand proof covering all nineteen allowed edge/sign rows.
It uses one elementary core-angle lemma, one center-distance bound,
and two immediate exceptional cases. The companion
verify_short_all_core_core_hand.js checks 54 fixed exact comparisons
and regenerates the entire table from the original integer labels.
Its output is short_all_core_core_hand_arithmetic.json.

The angle lemma below is the same statewise lemma independently
rederived in WRONG_0011011_ALL_CORE_CORE_HAND_PROOF.md. It does not
depend on that note's different role coefficients.

## 1. Core geometry and original role labels

Put

\[
 a_c=\frac7{12},\qquad d_c=\frac12+\frac{\sqrt2}{24},\qquad \rho=\frac1{12}.
\]

The positive core curve consists of \(a=a_c,\ 0\le b\le1/2\), followed
by

\[
 (a-\tfrac12)^2+(b-\tfrac12)^2=\rho^2,\qquad
 \frac12\le b\le a.
 \tag{2}
\]

Its local angle is \(\alpha=\arctan(b/a)\). A signed role label is
\(\ell_i=c_i^\sigma+\sigma g_i^\sigma b\). The following numbers are
integer numerators with common denominator 100000.

| Role | Sign | c | g |
|---:|:---:|---:|---:|
| 0 | + | 3177 | 108816 |
| 1 | + | 25648 | 62095 |
| 1 | − | −14041 | 62095 |
| 2 | − | 11680 | 113855 |
| 3 | + | 4149 | 104729 |
| 3 | − | −15540 | 62750 |
| 4 | + | 25812 | 58829 |
| 4 | − | 3897 | 104073 |
| 5 | + | 2448 | 99195 |
| 5 | − | 1027 | 95269 |
| 6 | + | 9072 | 95324 |
| 6 | − | 7651 | 99173 |

All \(g\)'s lie strictly between zero and \(8/7\). Define

\[
 \psi_i^\sigma=\sigma(\alpha-g_i^\sigma b)-c_i^\sigma.
\]

For a pair with positive center-ray gap \(\delta\) and lifted
frame difference \(\phi\),

\[
 \delta=\phi+\sigma\alpha-\tau\alpha',\qquad
 C=\phi+\ell_i-\ell_{i+1}
   =\delta-\psi_i^\sigma+\psi_{i+1}^\tau.
 \tag{3}
\]

The word supplies \(|\phi-k_i\pi/2|<.7\), with
\((k_0,\ldots,k_6)=(0,0,1,0,1,1,1)\). The consecutive-zero argument
supplies role 0 positive and role 2 negative. A zero-quarter edge
cannot have signs \((-,+)\), since its center gap would be at most .7,
contrary to the exterior common-point bound \(\delta>.76\).
These are exactly the sign restrictions used in the nineteen rows.

## 2. A statewise core endpoint lemma

For every core state and every \(0\le g\le8/7\),

\[
 0\le\alpha-gb\le\frac\pi4-gd_c.
 \tag{4}
\]

For the lower bound, concavity of atan on \([0,1]\) gives
\(\alpha\ge\pi b/(4a)\ge9b/7\), since \(a\le7/12\) and \(\pi>3\).

For the upper bound, \(d_c-b\ge0\), so the hardest case is \(g=8/7\).
On the side set \(x=b/a_c\). The desired nonnegative difference is

\[
 J(x)=\frac\pi4-\arctan x-\frac87d_c+\frac23x.
\]

Its derivative is \(2/3-1/(1+x^2)\), so its minimum on
\([0,6/7]\) occurs at \(x=1/\sqrt2\). With \(v=3-2\sqrt2\), tangent
subtraction gives

\[
 J(1/\sqrt2)=\arctan v-\frac{1+v}{7}
 \ge v-\frac{v^3}{3}-\frac{1+v}{7}>\frac1{400}.
 \tag{5}
\]

The last inequality is a single rational comparison after squaring
bounds for \(\sqrt2\).

On the corner put \(a=1/2+e,\ b=1/2+d\), with
\(e^2+d^2=\rho^2,\ 0\le d\le e\).
Then \(a'=-d/e,\ a''=-\rho^2/e^3\le-12\), and

\[
 \alpha''=
 \frac{-ba''(a^2+b^2)-2(a-ba')(aa'+b)}{(a^2+b^2)^2}>0.
\]

Indeed the first numerator term is at least \(3\).
Also \(0\le2(aa'+b)=1-d/e\le1\), and
\(a-ba'\le a+b\le7/6\), so the second term is at most \(7/6\).
Consequently \(\alpha-gb\) is convex on the corner. Its maximum is
at the join or diagonal endpoint. The join was handled on the side,
and the diagonal gives equality in the upper bound of (4).
This proves (4) on the entire curve.

It follows that the exact marker ranges used below are

\[
\begin{array}{c|cc}
 \sigma&\text{lower}(\psi)&\text{upper}(\psi)\\\hline
 +&-c&\pi/4-gd_c-c\\
 -&-\pi/4+gd_c-c&-c.
\end{array}
\tag{6}
\]

## 3. Every core/core center gap exceeds \(27/20\)

Every core center has norm less than \(4/5\). On the side this follows
from \((7/12)^2+1/4<16/25\). On the corner,

\[
 a^2+b^2\le\frac12+\frac{\sqrt2}{12}+\frac1{144}<\frac{16}{25}.
\]

Disjoint unit squares have center distance at least one because their
open incircles of radius \(1/2\) are disjoint. If
\(0\le\delta\le27/20\), separate convexity in the two radii would give

\[
 |P-P'|^2\le
 \max\left\{\frac{16}{25},
 \frac{32}{25}(1-\cos(27/20))\right\}<1.
 \tag{7}
\]

The second strict inequality is checked by the alternating cosine
series, or by the fixed rational bracket in the companion checker.
Thus

\[
 \delta>\frac{27}{20}=1.35.
 \tag{8}
\]

## 4. Two exceptional rows

All rows except the following two use (6) and (8) directly.

On edge 4 with signs \((+,-)\), the cost is

\[
 C=\phi+.24785+.58829b+.95269B
 \ge\frac\pi2-.7+.24785>1.1186.
 \tag{9}
\]

On edge 5 with signs \((+,-)\),

\[
 C=\phi-.05203+.99195b+.99173B.
 \tag{10}
\]

If \(\phi\ge.951\), this is at least .89897.
If \(\phi<.951\), then \(0<\phi<\pi/2\).
Feasibility forces \(b+B>.1\): otherwise every separating-axis
projection has absolute value at most \(a_c+.1<1\), while
\(W=(1+\sin\phi+\cos\phi)/2\ge1\).

For example the source secondary projection is
\(b+A\sin\phi+B\cos\phi\le a_c+.1\). The absolute primary projection
\(|a-A\cos\phi+B\sin\phi|\) is bounded by the same number: its positive
part is at most \(a_c+.1\) and its negative part at most \(a_c\).
The target axes obey the identical bounds after reversal.
Hence none of the eight signed SAT axes can separate if \(b+B\le.1\).

Therefore in this lower branch,

\[
 C>\frac\pi2-.7-.05203+\frac{.99173}{10}>.9179.
 \tag{11}
\]

Both branches of (10) exceed .898.

## 5. Complete core/core table

For every unexceptional row the lower bound is
\(1.35-\operatorname{upper}(\psi_i^\sigma)
+\operatorname{lower}(\psi_{i+1}^\tau)\).
The next values are rational lower bounds obtained by substituting
(6). The two exceptional rows use (9)--(11).

| Edge | Signs | Strict lower bound |
|---:|:---:|---:|
| 0 | ++ | 0.948092279520 |
| 0 | +- | 0.906648945771 |
| 1 | +- | 0.902313204996 |
| 1 | -- | 0.943756538745 |
| 2 | -+ | 1.425310000000 |
| 2 | -- | 1.187527628702 |
| 3 | ++ | 0.933328991674 |
| 3 | +- | 0.948771431642 |
| 3 | -- | 0.951922439967 |
| 4 | ++ | 1.127052157294 |
| 4 | +- | 1.118646326794 |
| 4 | -+ | 1.364490000000 |
| 4 | -- | 1.125784633216 |
| 5 | ++ | 1.052788050902 |
| 5 | +- | 0.898970000000 |
| 5 | -+ | 1.269550000000 |
| 5 | -- | 1.052665087278 |
| 6 | ++ | 1.156342042277 |
| 6 | -+ | 1.394740000000 |

Every row exceeds .898, so there is strict reserve over
\(17953/20000\). There is no equality case at that threshold.
The checker generates these nineteen rows from the original table,
so no unlisted sign or radial assumption enters their enumeration.

The inequality \(7(17953/20000)>710/113>2\pi\) explains the global
role-table target, but this note only proves the core/core component;
the outer and mixed components remain separate stated premises of
the eventual wrong-word exclusion.

