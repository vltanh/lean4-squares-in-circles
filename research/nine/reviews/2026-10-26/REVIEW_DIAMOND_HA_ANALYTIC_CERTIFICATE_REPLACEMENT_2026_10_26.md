# Independent full audit of the analytic diamond HA replacement

Date: October 26, 2026.

**Verdict: PASS after the author corrected one harmless endpoint
comparison.** In the introductory lower bound for \(\chi\), the
comparison with \((5\rho-3)/\sqrt{1+\rho^2}-\rho\) is non-strict
when \(h=0,\rho=1\). The saved source now correctly reads \(\ge\),
followed by the strictly positive endpoint bound. No subsequent
estimate or conclusion depended on the intermediate strict sign.

Reviewed source:
NEGATIVE_H_OWNED_LEFT_DIAMOND_HA_ANALYTIC_REPLACEMENT.md.
The original physical derivation and join were checked against
NEGATIVE_H_OWNED_LEFT_DIAMOND_HA_PRESSURE.md, including its contrary
projection assumption, original A2 concurrence, genuine HK offset,
circle-corner comparison, and final radius contradiction.

This is an independent hand-source and exact-algebra review, not a
Lean build or CI result. It certifies replacement of the specified
288-sign packet on the full original physical domain. It does not
claim a new component exclusion or change any other proof obligation.

## 1. Original physical domain and endpoint preservation

The original inequalities \(a>b>0\), \(5/6<\rho=u/v\le1\), and
\(z_A=z(wn-Jn)\), with \(z>0\), imply \(w>\rho\) directly from
\(b=z(wv-u)>0\). Under the original contrary assumption
\(c_H\cdot n\le0\), the unchanged bound
\(Z=z_A\cdot n\le\sqrt2+1/2\) gives \(w<4\). I checked the exact
reserve \(16q_0-17(9/4+99/70)=41/350\), the positive square
comparison for \(\sqrt2<99/70\), and the conversion from
\(17Z^2<16q\) to \(w^2<16\).

The complete physical range satisfies
\(0\le h\le1/\sqrt{61}<13/100\).
The lower \(\chi\) comparison is nondecreasing in \(\rho\), with
strictly positive minimum \(7/\sqrt{61}-5/6\); its exact squared
reserve is \(239\). Its upper bound is below \(1/2\). The equality
case \(h=0\) is included throughout and no division by \(h\) occurs.

On the whole physical portion \(\rho<w\le1\), I checked
\(0<B_0\le h\), the strict lower bound \(A_0-g>2/5\), and all
factor signs in the unsquared expression. The lower reserve
\(27/50\) is valid without assuming any sign for \(C_1\).
Thus this portion of the physical domain is fully covered, despite
the later polynomial proof using only \(1\le w\le4\).

The new source does not claim the historical algebraic extension
\(w<\rho\), and none of the original physical cases lies there.

## 2. Unsquared lower polynomial

I independently derived
\[
 A_0=\frac{U(w+1)+h(1-w)}2,\qquad
 B_0=\frac{U(w-1)+h(w+1)}2,\qquad
 \chi=U-1+h(1/v-w).
\]
The bounds
\[
 \frac{140}{99}-\frac38h^2\le U<\frac{99}{70},
 \qquad \frac1v\ge\sqrt2-h
\]
hold on the entire enlarged rectangle \(0\le h\le13/100\),
\(1\le w\le4\). The first follows from the exact difference of
squares and \(U,\sqrt2>7/5\); the second follows by multiplying
by the positive \(U+h\).

The source's lower scalar \(c\) is strictly positive throughout
that rectangle. Its two-endpoint concavity argument and exact
minimum \(433559/7920000\) check. The additional reserve
\(U_L-7/5\ge61807/7920000>0\) gives \(A>1/2\).
The inequalities \(0\le B\le B_0\le\overline B\) have the stated
directions because \(w\ge1\).

I checked the square comparison
\(\sqrt{1+\chi^2}\ge1+(47/100)\chi^2\) for \(0\le\chi\le1/2\);
the remaining squared coefficient is at least
\(191\chi^2/40000\).
In every use of the physical unsquared expression,
\(A,c,B,h\) are nonnegative and \(1-gh,2-gh\) are positive.
The negative linear term therefore requires the upper bound
\(\overline B\), while the two positive terms permit the lower
bounds \(A,c,B\). This produces exactly
\[
 Q=2A(1+c+\kappa c^2)-2\overline B(1-gh)
             +hB^2(2-gh)(1+\kappa c^2),
 \qquad\kappa=47/100.
\]
No coefficient-sign assumption on the original radical is hidden
in this comparison.

## 3. Independent reconstruction of both polynomial identities

For verification I implemented a separate two-variable rational
polynomial dictionary using only Python's Fraction. The program
starts from the displayed factors defining \(Q\); it does not import
the author's polynomial class, expanded polynomial, coefficient
packet, or verification script. The local review program is
/tmp/review_ha_analytic_independent.py.

Fresh multiplication gives degrees at most \((10,5)\). I extracted
the coefficient of \(h^3\), shifted \(w=3+t\), and verified the
entire identity
\[
 P_3=A_3+B_3t+M_3t^2+(t+2)t^2\{D_3+E_3(t-2)\}.
\]
Every rational in the source agrees exactly. In particular,
\[
 D_3-4E_3=\frac{5943569249}{9605960100}>0,
\]
and the concave quadratic's two endpoint values are exactly
\[
 \frac{23116297}{19602000}>0,\qquad
 \frac{112199935709}{64039734000}>0.
\]
Thus \(P_3>0\) on the whole interval \(1\le w\le4\).

Separately, I kept only the coefficients of \(h^0,h^1,h^2\),
substituted \(h=(13/100)x\), \(w=4-3z\), and subtracted
\((7/50)x^2\). Fresh expansion agrees exactly with all four
displayed polynomials \(G_0+zG_1+z^2G_2+z^3G_3\).
All six rational rounding differences in the source match the
fresh subtraction and are positive. This checks the actual low
polynomial, including the signs of both negative terms in \(G_1\).

These are exact identity checks. There is no pose sample, angular
grid, radical endpoint packet, or Bernstein coefficient premise.

## 4. Structural bound for every higher-degree term

The factor estimates are valid uniformly in \(1\le w\le4\).
In particular the bounds for \(t_2=b_1^2+2b_0b_2\) and for
\(J_2=\kappa(\ell^2-2\gamma\zeta)\) correctly retain the opposite
signs of their two terms: their absolute value is bounded by the
larger positive summand, not by a false signed upper bound.

The asserted six bounds for \(r_i=2t_i-gt_{i-1}\) follow from
the displayed \(t_i\) bounds and \(g\le21/10\). Each is strictly
below its stated integer bound, and every \(|r_i|<38\).
I checked all five \(J_i\) product bounds and
\(\sum|J_i|<10\). The analogous difference estimate for \(F_2\)
also has the correct sign and is below \(16/5\).

The coefficient of \(h^4\) in \(2AF\) is bounded in absolute
value by \(193/10<20\); the degree-five and degree-six bounds
are smaller. For \(hB^2(2-gh)J\), convolution is bounded by
\(38\sum|J_i|<380\). The linear \(\overline B\) term has degree
at most two and contributes nothing to the tail. It follows
uniformly that every coefficient of \(h^i\), \(4\le i\le10\),
has absolute value below \(400\).

Dropping the nonnegative cubic contribution and summing the
absolute tail gives the stated geometric-series bound. With
\(h=Hx\), the use of \(x^4\le x^2\) is valid on \([0,1]\).
The exact tail budget and reserve are
\[
 \frac{400H^4}{1-H}=\frac{28561}{217500},\qquad
 \frac7{50}-\frac{400H^4}{1-H}=\frac{1889}{217500}>0.
\]
No individual sign of any tail coefficient is needed.

## 5. Whole-rectangle positivity and final physical contradiction

The source's two elementary scalar intervals cover \([0,1]\),
including the shared endpoint \(x=9/10\). On the first,
\(G_1>l(9/10)=4551/50000>0\), while the completed-square
minimum of \(f\) is \(509/18125>161/10000\).
On the second, \(zG_1>-13/100\) follows for every
\(0\le z\le1\), whether \(G_1\) is positive or negative.
The increasing \(f\) has
\(f(9/10)=1461/10000\). The terms \(z^2G_2,z^3G_3\)
are nonnegative. Hence the strict uniform bound
\[
                         Q>161/10000
\]
is valid throughout the full rectangle, including \(h=0\).

I rechecked the original norm comparison, keeping \(T\) fixed:
the true HK formula gives \(c_K/s_K>\chi\), hence
\(c_K>c_*\); the derivative of the candidate corner norm is
strictly negative because the original \(a>3/2\) and
\(\beta_T>0\). Thus the original physical proof gives
\(|T+e_*|^2-q>0\). The exact algebraic identity remains
\[
                  |T+e_*|^2-q=\mathcal D(1-zG).
\]
The unsquared proof yields \(G>g>0\). The derivative of
\((1+w^2)/g^2\) has the sign of \(w/2-2/5>0\) on the
whole actual \(w>5/6\) range, and the final exact reserve is
\[
             q_0-\frac{1700}{441}=\frac{32281}{705600}>0.
\]
It follows that \(zG>1\), contradicting the original physical
norm comparison and proving the same HA pressure sign.

## 6. Precisely accepted scope

The complete original low left-singleton diamond domain is
preserved: true H5/K3/A2/B2 degrees and forces, HA/AK ownership,
the real A2 concurrence, the forced HK offset, the intact HXY
petal, every physical mask and original mean, and all three
extra squares. In particular no fictitious K2 equation or
comparison packing is introduced.

The 288 historical scalar signs can therefore be removed from
this proof route. The accepted conclusion is the original strict
HA projection sign, not a stronger algebraic statement on the
unneeded region \(w<\rho\). Every separate component assembly
and later pressure generalization keeps its own physical proof
and review requirements. No other certificate or remaining
completion obligation is retired by this review.
