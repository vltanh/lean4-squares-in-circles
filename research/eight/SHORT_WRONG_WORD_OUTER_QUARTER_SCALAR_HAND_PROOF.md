# Wrong word 0010111: all outer quarter-one scalar envelopes

## Statement and the role of the table

Together with the six contact neighborhoods in
`SHORT_WRONG_WORD_OUTER_QUARTER_ALIGNED_HAND_PROOF.md`, this note covers
**all 48 allowed outer/outer quarter-one branches** of `0010111`, on their
whole continuous state domains. Its conclusion on edge2 is `C>.8975`;
on edges4,5,6 it is `C>.89765`.

The finite table below consists of 140 scalar inequalities in one angle.
Every state coordinate is eliminated analytically by a positive separating
axis multiplier and a circular support formula. An elementary cubic
majorant eliminates the one remaining radical. Each resulting inequality
is one polynomial identity on its entire displayed interval; all its
Bernstein coefficients are nonnegative. No state box cover, optimizer
completeness assumption, adaptive subdivision, or hidden continuous
minimum is a premise of this proof.

`short_quarter_scalar_hand_table.json` is the fixed rational table.
`verify_short_quarter_scalar_hand.js` expands exactly the formulas in this
note using rational arithmetic and verifies the displayed coefficient
signs. `short_quarter_scalar_hand_arithmetic.json` prints every coefficient
lower bound, together with every table row. The checker only expands
fixed polynomials and compares fixed rational numbers; it performs no
search, minimization, or selection of angle intervals.

All terminating decimals here and in the table denote exact rationals.

**Complete table-free component.**
[`formalization/HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md`](formalization/HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md)
now proves the entire outer/outer role-5 opposite-sign family, all four
original axes and both angle halves, with strict cost greater than
42643/47500. None of that component's scalar angle rows is needed.
The remaining role/sign families are separate obligations.

## 1. State coordinates and normalization

Use

\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 d=\sqrt{Q/2}-.5,\quad a_0=\sqrt{Q-.25}-.5,
 \quad r_0=\frac{.5}{a_0+.5}.
\tag{1}
\]

An outer state is `(a,-sigma b)` in its own frame, where

\[
 a=\sqrt{Q-(b+.5)^2}-.5,\qquad 0\le b\le d,
 \qquad a'=-\frac{b+.5}{a+.5},\quad r_0\le-a'\le1.
\tag{2}
\]

For an original branch `(i,sigma,tau,j)`, with axis number `j`, take its
two exact role labels from `short_hand_labels.json`:

\[
 \ell_s=c_s+p_sa+\sigma q_sb,
 \qquad \ell_t=c_t+p_tA+\tau q_tB.
\]

If `j` is1 or4, put

\[
 c=c_s-c_t,\quad(p,q,P,t)=(p_s,q_s,p_t,q_t).
\tag{3}
\]

If `j` is3 or2, reflect and reverse. The new source and target signs are
`(-tau,-sigma)`, their coefficients are

\[
 (p,q,P,t)=(-p_t,q_t,-p_s,q_s),\quad c=c_s-c_t,
\tag{4}
\]

and the axis is respectively1 or4. Both transformations preserve the
corrected cost and the angle `phi`. This is merely a relabeling of the
same signed separator; it assumes no additional symmetry of the role
potentials.

Every row therefore has the normalized cost

\[
 C=\phi+c+pa+\sigma qb-PA-\tau tB.
\tag{5}
\]

Write `phi=pi/2+r u`, with `r=+1` or `-1`, `0<=u<=.7`, and abbreviate
`s=sin u`, `k=cos u`. The two normalized separators are

\[
 \begin{array}{ll}
 j=1:& \sigma b+A k+\tau rBs\ge W,\\
 j=4:& a+rAs-\tau Bk\ge W,
 \end{array}
 \qquad W=(1+k+s)/2.
\tag{6}
\]

The whole proof supplies the common frame range `|phi-pi/2|<=.7` and the
four-axis reduction. This note addresses every one of the retained axes,
including cases where more than one axis separates.

## 2. A support lemma that removes both states

For real constants `X,Y`, let `m(X,Y)` be the minimum of `Xa(b)+Yb` on
the arc (2). The following lower bounds are immediate:

\[
 \begin{array}{c|c|l}
 \text{rule}&\text{lower bound}&\text{sufficient premise}\\\hline
 E&\min(Xa_0,(X+Y)d)&X\ge0,\\
 A&Xa_0&Y-Xr_0\ge0,\quad Y-X\ge0,\\
 D&(X+Y)d&Xr_0-Y\ge0,\quad X-Y\ge0,\\
 N&-(X+Y)/2-R\sqrt{X^2+Y^2}&\text{none}.
 \end{array}
\tag{7}
\]

For `E`, the function is concave, so a minimum is at an endpoint.
For `A` or `D`, its derivative `Y-X(-a')` has the indicated sign throughout
`r0<=-a'<=1`. Rule `N` is the minimum over the entire circle centered at
`(-.5,-.5)` of radius `R`; enlarging the arc to that circle is legitimate.

Choose the positive rational multiplier `lambda` displayed in a row
(zero is allowed). Subtract `lambda` times its separator minus `W` from
(5). The corrected cost is at least

\[
 \frac\pi2+ru+c+\lambda W+
 m(X_s,Y_s)+m(X,Y),
\tag{8}
\]

where

\[
 \begin{array}{c|cc|cc}
 j&X_s&Y_s&X&Y\\\hline
 1&p&\sigma(q-\lambda)&-P-\lambda k&\tau(-r\lambda s-t)\\
 4&p-\lambda&\sigma q&-P-r\lambda s&\tau(\lambda k-t).
 \end{array}
\tag{9}
\]

The source coefficients are constant. The column `S` of the table is a
rational lower bound for `m(Xs,Ys)`, verified by one of the rules (7).
For this constant choice the checker uses `E` when `Xs>=0`; otherwise it
uses a monotonicity rule if its two displayed inequalities hold, and rule
`N` in the remaining case. Each asserted `S` is rounded down to six
decimal places; its comparison with (7) is exact.

The target rule, in the table's `T` column, is one of `A,D,E,N`.
For `A` and `D` the two premises in (7), and for `E` its one premise,
are themselves included among the fixed nonnegative polynomials below.
Rule `E` contributes both endpoint lower bounds to the table: both
are proved sufficient, which proves their minimum sufficient.

## 3. An algebraic radical majorant

For any `v>=0` and `h>0`, set

\[
 T_h(v)=\frac{5h+15v/h-5v^2/h^3+v^3/h^5}{16}.
\tag{10}
\]

The elementary identity

\[
 T_h(v)-\sqrt v=
 \frac{(\sqrt v-h)^4(v+4h\sqrt v+5h^2)}{16h^5}\ge0
\tag{11}
\]

proves a global upper bound, with no restriction on `v/h^2`. For a target
rule `N`, take the positive rational `h` in the table and substitute
`T_h(v)` for its radical. From (9) and `s²+k²=1`, the exact squared norm is

\[
 \begin{array}{ll}
 j=1:&v=P^2+t^2+\lambda^2+2\lambda(Pk+rt s),\\
 j=4:&v=P^2+t^2+\lambda^2+2\lambda(rP s-tk).
 \end{array}
\tag{12}
\]

This form is useful: it uses only a constant and first harmonics. Thus
the scalar lower bound is at most cubic in `sin u,cos u`. In particular,
there is no radical in a variable state coordinate left to analyze.

## 4. The explicit lower polynomials

Here are full instructions for constructing each polynomial; they are
also a compact specification of every table coefficient.

First use these three fixed enclosures, which follow by squaring their
positive rational endpoints:

\[
 \begin{aligned}
 R&\in[1.97878750754091,1.97878750754092],\\
 d&\in[.89921406510940,.89921406510941],\\
 a_0&\in[1.41457567100389,1.41457567100390].
 \end{aligned}
\tag{13}
\]

The checker obtains the same bounds, or tighter ones, by integer square
root at denominator `10^14`. Operations on interval coefficients use
ordinary rational endpoint addition and the four endpoint products for
multiplication. For division by a positive constant interval, use its
reciprocal interval. These are only enclosures of fixed coefficients,
never subdivisions of a variable domain.

For `0<=u<=.7`, the alternating series gives

\[
 \begin{aligned}
 \sin u&=u-u^3/3!+u^5/5!-u^7/7!+\eta u^9/9!,
                   &&0\le\eta\le1,\\
 \cos u&=1-u^2/2!+u^4/4!-u^6/6!+u^8/8!
                   -\zeta u^{10}/10!,&&0\le\zeta\le1.
 \end{aligned}
\tag{14}
\]

The parameters in (14) may depend on `u`; the stated bounds hold pointwise.
Substitute the corresponding interval coefficients into (9), (12), (10),
and the lower bound (8), replacing the source bound by its rational `S`.
For rule `N`, the target bound is

\[
 -(X+Y)/2-R T_h(v).
\tag{15}
\]

For rules `A,D,E` it is the specified endpoint expression(s). Finally
subtract the required edge bound `g=.8975` on edge2 or `.89765` otherwise.

Expanding with rational interval coefficient arithmetic produces
`sum [L_j,U_j]u^j`. Its lower polynomial is

\[
 P(u)=\sum_j L_j u^j.
\tag{16}
\]

Because `u>=0`, (16) is a lower bound at every point of the interval,
including for the pointwise remainder parameters in (14). No derivative
of a Taylor remainder is taken. The same construction gives lower
polynomials for the target-rule premises from (7).

The cost polynomials have degree at most30. For a displayed interval
`[l,h]`, expand `P(l+(h-l)z)=sum A_j z^j`. Its Bernstein coefficients of
degree `n=deg P` are the explicit rationals

\[
 B_k=\sum_{j=0}^k A_j\frac{\binom kj}{\binom nj},
 \quad0\le k\le n,
\tag{17}
\]

where

\[
 A_j=(h-l)^j\sum_{m=j}^nL_m\binom mj l^{m-j}.
\tag{18}
\]

Every premise polynomial has `Bk>=0`. Every cost polynomial has `Bk>0`.
The table gives the smallest cost coefficient for each row, rounded down;
its positivity can also be checked directly by (10),(12)--(18).
Since the Bernstein basis polynomials are nonnegative and sum to1,
these signs prove all the continuous scalar inequalities.

The common constant `pi/2` is enclosed by
`[3.141592653589793238,3.141592653589793239]/2`. For completeness, the
Machin identity and alternating series prove this rational bracket:
use `16 atan(1/5)-4 atan(1/239)`, with last indices25 and6 for the lower
bound and24 and7 for the upper bound. No numerical value of pi is assumed.

## 5. Completeness of the cover

There are8 raw quarter-one cases on edge2,16 each on edges4 and5, and8 on
edge6. These are exactly the allowed source/target signs and four axes;
role2 is negative and role0 positive. The table covers both signs of `x`
for each raw case.

For the six cases covered near alignment by the companion contact note,
the scalar intervals start at `u=.3` on the negative `+f` side, `.1` on
the positive `+f` side, `.03` on the negative `-e` side, and `.06` on the
positive `-e` side. Every other scalar interval chain starts at0. Every
chain ends at `.7`, with exact rational endpoint equality between
successive intervals. All intervals are closed, so boundaries and contact
ties are included. `audit_short_whole_word_hand.py` explicitly enumerates
this48-case cover and checks these rational endpoint equalities.

The following complete rational table uses `r` for the sign in
`phi=pi/2+r u`. The case column records original `edge,source sign,target
sign,axis`, before normalization. The `h` column matters only for `T=N`.
The final column is a lower bound for every Bernstein coefficient of the
cost polynomial(s); target premises have separate nonnegative coefficient
lists in the arithmetic record. Thus every row can be independently
expanded from its displayed constants and the preceding formulas.

<!-- BEGIN FIXED TABLE -->

| # | Original case | r | u interval | lambda | S | T | h | Cost coefficient >= |
|---:|---|---:|---|---:|---:|:---:|---:|---:|
| 1 | 2 -- 1 | -1 | [0,0.7] | 1.091655 | 0.129193 | A | — | 0.16407937 |
| 2 | 2 -- 1 | 1 | [0,0.7] | 0.933083 | 0.129192 | A | — | 0.34965421 |
| 3 | 2 -- 2 | -1 | [0,0.7] | 1.045846 | -1.010539 | E | — | 0.30290652 |
| 4 | 2 -- 2 | 1 | [0,0.7] | 1.0032 | -0.950213 | A | — | 0.31156008 |
| 5 | 2 -- 3 | -1 | [0.3,0.7] | 0.943626 | 0.468889 | N | 1.009289 | 0.07818581 |
| 6 | 2 -- 3 | 1 | [0.1,0.7] | 0.943626 | 0.468889 | D | — | 0.05682483 |
| 7 | 2 -- 4 | -1 | [0.03,0.7] | 0.928089 | -1.544400 | E | — | 0.01407482 |
| 8 | 2 -- 4 | 1 | [0.06,0.22] | 0.979034 | -1.590229 | E | — | 0.00152804 |
| 9 | 2 -- 4 | 1 | [0.22,0.38] | 0.0 | -0.709849 | E | — | 0.11744672 |
| 10 | 2 -- 4 | 1 | [0.38,0.7] | 0.0 | -0.709849 | E | — | 0.27744672 |
| 11 | 2 -+ 1 | -1 | [0,0.7] | 0.9331 | 0.129193 | N | 1.880539 | 0.00009473 |
| 12 | 2 -+ 1 | 1 | [0,0.7] | 0.9331 | 0.129193 | N | 1.880514 | 0.00009473 |
| 13 | 2 -+ 2 | -1 | [0,0.35] | 0.9331 | -2.397295 | E | — | 0.00009452 |
| 14 | 2 -+ 2 | -1 | [0.35,0.7] | 3.0 | -4.992713 | E | — | 1.00014699 |
| 15 | 2 -+ 2 | 1 | [0,0.0875] | 0.9331 | -2.397295 | E | — | 0.00009452 |
| 16 | 2 -+ 2 | 1 | [0.0875,0.175] | 0.898458 | -2.362070 | A | — | 0.01465119 |
| 17 | 2 -+ 2 | 1 | [0.175,0.35] | 0.872685 | -2.336210 | N | 0.135594 | 0.02055248 |
| 18 | 2 -+ 2 | 1 | [0.35,0.7] | 0.843239 | -2.307040 | N | 0.343487 | 0.04836768 |
| 19 | 2 -+ 3 | -1 | [0,0.7] | 1.114985 | -0.729271 | N | 1.350468 | 0.00085878 |
| 20 | 2 -+ 3 | 1 | [0,0.7] | 1.114985 | -0.729271 | N | 1.350483 | 0.00085878 |
| 21 | 2 -+ 4 | -1 | [0,0.35] | 1.072339 | -1.677887 | N | 0.530889 | 0.00016952 |
| 22 | 2 -+ 4 | -1 | [0.35,0.7] | 3.0 | -4.119008 | E | — | 1.01538845 |
| 23 | 2 -+ 4 | 1 | [0,0.0875] | 1.06921 | -1.674847 | A | — | 0.00018897 |
| 24 | 2 -+ 4 | 1 | [0.0875,0.175] | 1.031867 | -1.639092 | N | 0.674583 | 0.00139272 |
| 25 | 2 -+ 4 | 1 | [0.175,0.35] | 0.990488 | -1.600643 | N | 0.811298 | 0.00277005 |
| 26 | 2 -+ 4 | 1 | [0.35,0.7] | 0.913574 | -1.531348 | N | 1.057714 | 0.00712544 |
| 27 | 4 -- 1 | -1 | [0,0.7] | 1.091655 | 0.273508 | A | — | 0.14021905 |
| 28 | 4 -- 1 | 1 | [0,0.7] | 0.878254 | 0.273508 | A | — | 0.34852566 |
| 29 | 4 -- 2 | -1 | [0,0.7] | 1.012342 | -1.135441 | E | — | 0.29293553 |
| 30 | 4 -- 2 | 1 | [0,0.7] | 0.9909 | -1.105109 | A | — | 0.30149230 |
| 31 | 4 -- 3 | -1 | [0.3,0.4] | 0.710313 | 0.296594 | D | — | 0.00085678 |
| 32 | 4 -- 3 | -1 | [0.4,0.5] | 0.710313 | 0.296594 | N | 0.673329 | 0.00324089 |
| 33 | 4 -- 3 | -1 | [0.5,0.7] | 0.729219 | 0.279593 | N | 0.486434 | 0.00046158 |
| 34 | 4 -- 3 | 1 | [0.1,0.7] | 0.710313 | 0.296594 | D | — | 0.06758728 |
| 35 | 4 -- 4 | -1 | [0.03,0.365] | 0.698047 | -1.143924 | E | — | 0.00297711 |
| 36 | 4 -- 4 | -1 | [0.365,0.7] | 0.71348 | -1.157802 | E | — | 0.00206052 |
| 37 | 4 -- 4 | 1 | [0.06,0.7] | 0.660331 | -1.110009 | A | — | 0.01263466 |
| 38 | 4 -+ 1 | -1 | [0,0.7] | 1.009824 | 0.273508 | N | 1.332205 | 0.00045570 |
| 39 | 4 -+ 1 | 1 | [0,0.7] | 1.009824 | 0.273508 | N | 1.332096 | 0.00045570 |
| 40 | 4 -+ 2 | -1 | [0,0.7] | 1.012342 | -1.699233 | E | — | 0.00045353 |
| 41 | 4 -+ 2 | 1 | [0,0.7] | 0.990429 | -1.677438 | A | — | 0.00033519 |
| 42 | 4 -+ 3 | -1 | [0,0.7] | 1.08532 | 0.000000 | N | 1.17659 | 0.00046264 |
| 43 | 4 -+ 3 | 1 | [0,0.7] | 1.08532 | 0.000000 | N | 1.176602 | 0.00046264 |
| 44 | 4 -+ 4 | -1 | [0,0.7] | 1.060006 | -1.473613 | E | — | 0.00022932 |
| 45 | 4 -+ 4 | 1 | [0,0.0875] | 1.06921 | -1.482678 | A | — | 0.00036831 |
| 46 | 4 -+ 4 | 1 | [0.0875,0.175] | 0.982011 | -1.399471 | A | — | 0.00351234 |
| 47 | 4 -+ 4 | 1 | [0.175,0.35] | 0.838249 | -1.269996 | N | 0.194312 | 0.01657846 |
| 48 | 4 -+ 4 | 1 | [0.35,0.7] | 0.807682 | -1.242509 | N | 0.38394 | 0.04573901 |
| 49 | 4 +- 1 | -1 | [0,0.7] | 0.71553 | 0.000000 | A | — | 0.12461633 |
| 50 | 4 +- 1 | 1 | [0,0.7] | 0.0 | 0.000000 | E | — | 0.73689040 |
| 51 | 4 +- 2 | -1 | [0,0.7] | 0.7082 | -0.705209 | E | — | 0.44328732 |
| 52 | 4 +- 2 | 1 | [0,0.7] | 0.0 | 0.296594 | E | — | 0.73689032 |
| 53 | 4 +- 3 | -1 | [0,0.7] | 0.710313 | 0.296594 | A | — | 0.12397663 |
| 54 | 4 +- 3 | 1 | [0,0.7] | 0.0 | 0.296594 | E | — | 0.73689032 |
| 55 | 4 +- 4 | -1 | [0,0.7] | 0.626346 | -0.886014 | E | — | 0.47611421 |
| 56 | 4 +- 4 | 1 | [0,0.7] | 0.0 | 0.000000 | E | — | 0.73689040 |
| 57 | 4 ++ 1 | -1 | [0,0.175] | 0.71553 | 0.000000 | D | — | 0.00244853 |
| 58 | 4 ++ 1 | -1 | [0.175,0.35] | 0.71553 | 0.000000 | N | 1.024926 | 0.00536559 |
| 59 | 4 ++ 1 | -1 | [0.35,0.7] | 0.71553 | 0.000000 | N | 0.692537 | 0.00044192 |
| 60 | 4 ++ 1 | 1 | [0,0.7] | 0.71553 | 0.000000 | D | — | 0.00244853 |
| 61 | 4 ++ 2 | -1 | [0,0.7] | 0.7 | -1.410723 | E | — | 0.00088332 |
| 62 | 4 ++ 2 | 1 | [0,0.7] | 0.71553 | -1.424688 | A | — | 0.00244832 |
| 63 | 4 ++ 3 | -1 | [0,0.7] | 1.091655 | 0.000000 | A | — | 0.13919697 |
| 64 | 4 ++ 3 | 1 | [0,0.7] | 0.86884 | 0.000000 | A | — | 0.35140640 |
| 65 | 4 ++ 4 | -1 | [0,0.7] | 1.1415 | -1.614739 | E | — | 0.23836732 |
| 66 | 4 ++ 4 | 1 | [0,0.7] | 0.86884 | -1.229040 | N | 0.327673 | 0.14878281 |
| 67 | 5 -- 1 | -1 | [0,0.7] | 1.091655 | -0.296595 | A | — | 0.02339261 |
| 68 | 5 -- 1 | 1 | [0,0.7] | 0.7212 | -0.308389 | A | — | 0.28501598 |
| 69 | 5 -- 2 | -1 | [0,0.35] | 1.066555 | -1.771863 | A | — | 0.15363424 |
| 70 | 5 -- 2 | -1 | [0.35,0.7] | 3.0 | -4.506867 | E | — | 0.88064571 |
| 71 | 5 -- 2 | 1 | [0,0.7] | 0.7212 | -1.283332 | N | 0.425367 | 0.26959529 |
| 72 | 5 -- 3 | -1 | [0,0.7] | 0.878256 | -0.264961 | N | 1.025145 | 0.00032753 |
| 73 | 5 -- 3 | 1 | [0,0.7] | 0.755569 | -0.263140 | N | 1.273513 | 0.02616439 |
| 74 | 5 -- 4 | -1 | [0,0.7] | 0.705045 | -1.572147 | A | — | 0.02529496 |
| 75 | 5 -- 4 | 1 | [0,0.7] | 0.755569 | -1.621801 | A | — | 0.02616496 |
| 76 | 5 -+ 1 | -1 | [0,0.0875] | 0.805212 | -0.296595 | N | 1.298172 | 0.00030157 |
| 77 | 5 -+ 1 | -1 | [0.0875,0.175] | 0.838247 | -0.296595 | N | 1.29969 | 0.00066449 |
| 78 | 5 -+ 1 | -1 | [0.175,0.35] | 0.906477 | -0.296595 | N | 1.300836 | 0.00259267 |
| 79 | 5 -+ 1 | -1 | [0.35,0.525] | 1.022312 | -0.296595 | N | 1.149034 | 0.00297948 |
| 80 | 5 -+ 1 | -1 | [0.525,0.7] | 1.093606 | -0.296595 | A | — | 0.00027543 |
| 81 | 5 -+ 1 | 1 | [0,0.7] | 0.774048 | -0.296607 | N | 1.29681 | 0.00103622 |
| 82 | 5 -+ 2 | -1 | [0,0.175] | 0.774048 | -1.652382 | N | 0.217132 | 0.00103626 |
| 83 | 5 -+ 2 | -1 | [0.175,0.35] | 1.778669 | -2.866998 | E | — | 0.19537725 |
| 84 | 5 -+ 2 | -1 | [0.35,0.7] | 3.0 | -4.552473 | E | — | 0.85547971 |
| 85 | 5 -+ 2 | 1 | [0,0.1] | 0.774048 | -1.652382 | N | 0.21713 | 0.00103626 |
| 86 | 5 -+ 2 | 1 | [0.1,0.35] | 0.745829 | -1.624016 | N | 0.30358 | 0.03060825 |
| 87 | 5 -+ 2 | 1 | [0.35,0.7] | 0.68189 | -1.561746 | N | 0.482485 | 0.10440705 |
| 88 | 5 -+ 3 | -1 | [0,0.0875] | 0.802327 | -0.308746 | N | 1.286528 | 0.00029530 |
| 89 | 5 -+ 3 | -1 | [0.0875,0.175] | 0.840687 | -0.308746 | N | 1.292098 | 0.00078907 |
| 90 | 5 -+ 3 | -1 | [0.175,0.35] | 0.907761 | -0.308746 | N | 1.292209 | 0.00290777 |
| 91 | 5 -+ 3 | -1 | [0.35,0.525] | 1.020019 | -0.308746 | N | 1.138002 | 0.00308234 |
| 92 | 5 -+ 3 | -1 | [0.525,0.7] | 1.093606 | -0.308746 | A | — | 0.00027564 |
| 93 | 5 -+ 3 | 1 | [0,0.7] | 0.776094 | -0.308757 | N | 1.288845 | 0.00084984 |
| 94 | 5 -+ 4 | -1 | [0,0.175] | 0.776094 | -1.642464 | N | 0.225997 | 0.00085019 |
| 95 | 5 -+ 4 | -1 | [0.175,0.35] | 1.777116 | -2.852435 | E | — | 0.19573022 |
| 96 | 5 -+ 4 | -1 | [0.35,0.7] | 3.0 | -4.540322 | E | — | 0.85547950 |
| 97 | 5 -+ 4 | 1 | [0,0.1] | 0.776094 | -1.642464 | N | 0.22598 | 0.00085019 |
| 98 | 5 -+ 4 | 1 | [0.1,0.35] | 0.747569 | -1.613823 | N | 0.310357 | 0.03022649 |
| 99 | 5 -+ 4 | 1 | [0.35,0.7] | 0.682959 | -1.551012 | N | 0.491985 | 0.10364384 |
| 100 | 5 +- 1 | -1 | [0,0.7] | 0.86884 | 0.000000 | A | — | 0.02760910 |
| 101 | 5 +- 1 | 1 | [0,0.7] | 0.0 | 0.000000 | A | — | 0.62108696 |
| 102 | 5 +- 2 | -1 | [0,0.7] | 0.592712 | -1.101576 | A | — | 0.33672483 |
| 103 | 5 +- 2 | 1 | [0,0.7] | 0.0 | -0.263140 | E | — | 0.62108632 |
| 104 | 5 +- 3 | -1 | [0,0.7] | 0.871621 | -0.263949 | A | — | 0.02714043 |
| 105 | 5 +- 3 | 1 | [0,0.7] | 0.0 | -0.263140 | E | — | 0.62108632 |
| 106 | 5 +- 4 | -1 | [0,0.7] | 0.627339 | -0.887419 | A | — | 0.36100696 |
| 107 | 5 +- 4 | 1 | [0,0.7] | 0.0 | 0.000000 | A | — | 0.62108696 |
| 108 | 5 ++ 1 | -1 | [0,0.7] | 0.86884 | 0.000000 | N | 1.018574 | 0.00037551 |
| 109 | 5 ++ 1 | 1 | [0,0.7] | 0.751908 | 0.000000 | N | 1.279841 | 0.02649233 |
| 110 | 5 ++ 2 | -1 | [0,0.7] | 0.708204 | -1.587023 | E | — | 0.02584732 |
| 111 | 5 ++ 2 | 1 | [0,0.7] | 0.751908 | -1.630082 | A | — | 0.02649232 |
| 112 | 5 ++ 3 | -1 | [0,0.7] | 1.091655 | -0.308746 | A | — | 0.02351097 |
| 113 | 5 ++ 3 | 1 | [0,0.7] | 0.720963 | -0.321023 | A | — | 0.28474960 |
| 114 | 5 ++ 4 | -1 | [0,0.35] | 1.059755 | -1.499104 | A | — | 0.15657204 |
| 115 | 5 ++ 4 | -1 | [0.35,0.7] | 3.0 | -4.243728 | E | — | 0.88076350 |
| 116 | 5 ++ 4 | 1 | [0,0.7] | 0.720963 | -1.019857 | N | 0.431774 | 0.27086999 |
| 117 | 6 -+ 1 | -1 | [0,0.7] | 1.101434 | 0.263139 | N | 1.452886 | 0.00048308 |
| 118 | 6 -+ 1 | 1 | [0,0.7] | 1.101434 | 0.263139 | N | 1.452978 | 0.00048308 |
| 119 | 6 -+ 2 | -1 | [0,0.7] | 1.101434 | -1.850637 | E | — | 0.00048269 |
| 120 | 6 -+ 2 | 1 | [0,0.0875] | 1.06921 | -1.818719 | E | — | 0.00017667 |
| 121 | 6 -+ 2 | 1 | [0.0875,0.175] | 0.973865 | -1.728113 | E | — | 0.00324034 |
| 122 | 6 -+ 2 | 1 | [0.175,0.35] | 0.8608 | -1.626193 | A | — | 0.01564944 |
| 123 | 6 -+ 2 | 1 | [0.35,0.7] | 0.821708 | -1.591041 | N | 0.242224 | 0.02372966 |
| 124 | 6 -+ 3 | -1 | [0,0.7] | 1.12741 | 0.000000 | N | 1.241864 | 0.03222712 |
| 125 | 6 -+ 3 | 1 | [0,0.7] | 1.12741 | 0.000000 | N | 1.241942 | 0.03222712 |
| 126 | 6 -+ 4 | -1 | [0,0.7] | 1.145898 | -1.600332 | E | — | 0.03211232 |
| 127 | 6 -+ 4 | 1 | [0,0.1] | 1.066062 | -1.521706 | A | — | 0.03090232 |
| 128 | 6 -+ 4 | 1 | [0.1,0.35] | 0.999534 | -1.459857 | A | — | 0.03246390 |
| 129 | 6 -+ 4 | 1 | [0.35,0.7] | 0.880954 | -1.353222 | N | 0.455884 | 0.05324526 |
| 130 | 6 ++ 1 | -1 | [0.3,0.4] | 0.70963 | 0.308745 | D | — | 0.00030495 |
| 131 | 6 ++ 1 | -1 | [0.4,0.5] | 0.70963 | 0.308745 | N | 0.936958 | 0.00308323 |
| 132 | 6 ++ 1 | -1 | [0.5,0.7] | 0.741924 | 0.279705 | N | 0.809253 | 0.00036278 |
| 133 | 6 ++ 1 | 1 | [0.1,0.7] | 0.70963 | 0.308745 | D | — | 0.06735590 |
| 134 | 6 ++ 2 | -1 | [0.03,0.365] | 0.697286 | -1.479159 | E | — | 0.00267799 |
| 135 | 6 ++ 2 | -1 | [0.365,0.7] | 0.71348 | -1.493721 | E | — | 0.00125844 |
| 136 | 6 ++ 2 | 1 | [0.06,0.7] | 0.655737 | -1.441798 | A | — | 0.01223894 |
| 137 | 6 ++ 3 | -1 | [0,0.7] | 1.091655 | 0.000000 | A | — | 0.20244226 |
| 138 | 6 ++ 3 | 1 | [0,0.7] | 0.94766 | 0.000000 | A | — | 0.38197483 |
| 139 | 6 ++ 4 | -1 | [0,0.7] | 1.145898 | -1.312215 | E | — | 0.29978932 |
| 140 | 6 ++ 4 | 1 | [0,0.7] | 0.94766 | -1.031792 | N | 0.365882 | 0.15572347 |

The table has 310 premise/cost polynomials and 4,475 displayed coefficient comparisons. All are nonnegative; all cost coefficients are strictly positive. The weakest cost reserve exceeds .000094. Together with the contact-neighborhood proof, this completes all48 outer/outer quarter-one branches.
