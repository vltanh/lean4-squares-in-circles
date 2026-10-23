# Global BT0 exclusion with a core E and negative DE3

## 1. Statement and relation to the other path theorem

Use the actual G0--G2 boundary cycle and the unchanged G1 marker F,
with

\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 \kappa=49/50,\quad m=1.077372,\quad A=13/12,
 \quad T_*=16761/4520.
\tag{1}
\]

All decimals below are exact rationals. Suppose the original BT
owner is 0, E is core, and the original DE owner is 3 with
`d_DE=-t<=0`. The global sign and owner results give
`y_A=b_A>0`, `y_T=b_T>0`, `y_D=-b_D<0`, `y_E=-b_E<=0`, and
original AB and TD owners 0 or 2. B has either sign.

**Theorem.** Every such candidate has

\[
 \boxed{\pi+d_{AB}+d_{BT}+d_{TD}+d_{DE}
                       +\kappa b_A+F_E>T_*.}
\tag{2}
\]

Together with `HAND_G3_GLOBAL_BT0_DE2_PATH_EXCLUSION.md`, this
covers every original DE owner, E kind, and sign of every actual
error under an original BT0 witness. The complementary charge in
`HAND_G3_GLOBAL_RETURN_WITH_LINEAR_A_CHARGE.md` is greater than
`103/40`; because `T_*+103/40=710/113>2 pi`, the complete cycle is
excluded.

The proof below also supplies an analytic tail inequality usable
after other valid prefix comparisons. No frame order, mismatch
bound, radial selection of A/B/T/D, or sampled-angle premise is
assumed.

## 2. Reduce to two retained-prefix scalars

The total-negative-error lemma in Section 2 of
`HAND_G3_GLOBAL_BT0_DE2_PATH_EXCLUSION.md` gives

\[
               \sum_i\max(0,-d_i)<7/10.
\tag{3}
\]

Put

\[
 r=\max(0,-d_{BT}),\qquad s=\max(0,-d_{TD}),\qquad
 p=r+s,
\]

so `p+t<7/10`. Choose the TD and DE multipliers

\[
 c=3/5+(2/5)p,
 \qquad
 e=
 \begin{cases}
 \kappa,&0\le t\le1/5,\\
 m\sec t,&1/5<t\le7/10.
 \end{cases}
\tag{4}
\]

These satisfy `3/5<=c<=.88<kappa<=e<1.41`.
For the last bound, the degree-6 lower cosine polynomial C at
`7/10` gives `1.41 C(7/10)-m=25283497/24000000000>0`.

Give BT multiplier kappa. Give AB multiplier kappa when its error
is nonnegative and `kappa sec(-d_AB)` when it is negative. The
exact comparisons in Section 3 of the DE2 path theorem remove the
AB error with nonnegative gain. They also remove positive BT0 and
TD errors with nonnegative gain; the TD comparison is valid because
`c<=kappa`. At aligned AB the positive-A and signed-B terms cancel
exactly against the BT0 multiplier kappa. These are comparisons of
dual lower bounds, not assertions that moving a frame preserves
the original configuration.

For the core E marker,

\[
 F_E=7.506931(7/12-a_E)+m b_E.
\]

The DE3 error is negative. Since `e cos t<=m` and
`e sin t<7.506931`,

\[
 F_E+e a_E\sin t-e b_E\cos t\ge e(7/12)\sin t.
\tag{5}
\]

This identity and its nonnegative remainders are written out in
Section 1 of `HAND_G3_CORE_E_DE3_BASE_SCALAR.md`.

For positive a,c define

\[
                 N_{a,c}(z)=\sqrt{a^2+c^2-2ac\sin z}.
\tag{6}
\]

Full shifted-circle support, retaining both T and D circles,
now gives the following lower bound for original TD0:

\[
\begin{split}
 \pi-p-t+\tfrac32\kappa+c+e
 +\kappa\cos r+c\cos s
 +\tfrac e2\cos t+eA\sin t\\
 -R\{N_{\kappa,c}(r)+N_{e,c}(s)\}.
\end{split}
\tag{7}
\]

For original TD2, the same expression has its two norm terms
replaced by `N_(kappa,c)(p)+N_(e,c)(0)`.
For completeness, in TD0 the forces on T and D are

\[
 (\kappa\cos r,c-\kappa\sin r),\qquad
 (e-c\sin s,c\cos s).
\tag{8}
\]

In TD2 they are

\[
 (\kappa\cos r-c\sin s,c\cos s-\kappa\sin r),
 \qquad(e,c).
\tag{9}
\]

For every force `(u,v)`, its support on an actual unsigned center
is at most `R sqrt(u^2+v^2)-(u+v)/2`. Substitution of (8)--(9),
the right-hand sides `W(-z)=(1+cos z+sin z)/2`, and (5) gives
(7) exactly. No sign restriction on a force component is needed.

Section 6 of the DE2 path theorem proves, for every positive a,c,
that `a cos z-R N_(a,c)(z)` is strictly concave on `[0,7/10]`.
Apply this with `(a,c)=(kappa,c)` and `(a,c)=(c,e)` to (7).
With p fixed, the minimum over `r+s=p` is at one of the endpoints.
For TD2, the cosine sum is concave in the same split and its smaller
endpoint is `kappa cos p+c`, since `c<=kappa`.

Thus every retained path is bounded below by the smaller of the
following two scalars:

\[
\begin{split}
 L_B(p,t)={}&\pi-p-t+\tfrac32\kappa+2c+e
 +\kappa\cos p+\tfrac e2\cos t+eA\sin t\\
 &-R\{N_{\kappa,c}(p)+N_{e,c}(0)\},\\[2mm]
 L_W(p,t)={}&\pi-p-t+\tfrac52\kappa+c+e
 +c\cos p+\tfrac e2\cos t+eA\sin t\\
 &-R\{N_{\kappa,c}(0)+N_{e,c}(p)\}.
\end{split}
\tag{10}
\]

It remains to prove `L_B,L_W>T_*` on the whole intrinsic triangle
`p,t>=0`, `p+t<=7/10` with the two-piece choice (4).

## 3. Small DE error: one prefix scalar

On `0<=t<=1/5` we have `e=kappa`. The norm sums in (10) are
identical, giving the exact comparison

\[
                L_W-L_B=(\kappa-c)(1-\cos p)\ge0.
\tag{11}
\]

The entire t dependence of `L_B` is

\[
             g(t)=-t+(\kappa/2)\cos t+\kappa A\sin t.
\]

It is concave on `[0,1/5]`, and the alternating lower sine and
cosine polynomials give

\[
 g(1/5)-g(0)\ge\frac{38921489}{33750000000}>0.
\tag{12}
\]

Therefore `g(t)>=g(0)` throughout this interval. Both scalars in
(10) are consequently at least

\[
 K(p)=\pi-p+3\kappa+2c+\kappa\cos p
       -R\{N_{\kappa,c}(p)+N_{\kappa,c}(0)\}.
\tag{13}
\]

We prove `K(p)>T_*` on the entire interval `[0,7/10]` with one
explicit polynomial bound. Put

\[
\begin{split}
 S(p)&=p-p^3/6+p^5/120-p^7/5040,\\
 C(p)&=1-p^2/2+p^4/24-p^6/720,\\
 P_1(p)&=1.149087-0.308159p-0.293179p^2,\\
 P_2(p)&=1.149087+0.210926p+0.041598p^2,\\
 X_1(p)&=\kappa^2+c^2-2\kappa cS(p),\\
 X_2(p)&=\kappa^2+c^2.
\end{split}
\tag{14}
\]

Both P polynomials are positive: P1 decreases to the positive
endpoint `78971799/100000000`, and every coefficient of P2 is
positive. The elementary inequality
`sqrt(X)<=(X+P^2)/(2P)` for positive P, together with
`pi>3.14159`, `R<1.979`, `S<=sin`, and `C<=cos`, gives

\[
 K(p)-T_*\ge \frac{H(p)}{2P_1(p)P_2(p)},
\tag{15}
\]

where the following is an explicit degree-10 polynomial:

\[
\begin{split}
 H(p)={}&2P_1P_2\{3.14159-p+3\kappa+2c
                              +\kappa C(p)-T_*\}\\
 &-1.979\{P_2(X_1+P_1^2)+P_1(X_2+P_2^2)\}.
\end{split}
\tag{16}
\]

Write `H(7/20+z)=sum_(j=0)^10 A_j z^j`. Direct rational
expansion of the displayed polynomials gives the three aggregate
bounds

\[
 A_0>0.01047,\qquad |A_1|<0.02111,\qquad
 A_2-\sum_{j=3}^{10}|A_j|(7/20)^{j-2}>0.0837.
\tag{17}
\]

These are whole-interval coefficient sums. Their exact positive
reserves, respectively, are

\[
\begin{gathered}
 \frac{631697687829474930933136903}
      {86784000000000000000000000000000},\\
 \frac{7476427893374208084518549}
      {6508800000000000000000000000000},\\
 \frac{4978588449906973234884153}
      {72320000000000000000000000000}.
\end{gathered}
\tag{18}
\]

For `|z|<=7/20`, (17) and completion of the square yield

\[
 H(p)>0.01047-0.02111|z|+0.0837z^2
 \ge\frac{30597239}{3348000000}>0.0091>0.
\tag{19}
\]

This proves both required scalar inequalities for `t<=1/5`.

## 4. Larger DE error: increase the prefix from zero

On `1/5<=t<=7/10`, the choice is `e=m sec t` and
`c=3/5+(2/5)p`. The whole-strip monotonicity theorem in
`HAND_G3_CORE_E_DE3_SATURATED_PREFIX_MONOTONICITY.md` proves

\[
           \partial_p L_B(p,t)>0,\qquad
           \partial_p L_W(p,t)>0
\tag{20}
\]

for the required range. In that theorem e is held fixed during
the p derivative; here e depends only on t, so this is exactly the
derivative needed. Therefore

\[
              L_B(p,t),L_W(p,t)\ge L_B(0,t)=L_W(0,t).
\tag{21}
\]

At `p=0` we have `c=3/5`, and the common value is the scalar
`L_0(t)` of `HAND_G3_CORE_E_DE3_BASE_SCALAR.md` with `e=m sec t`.
Its whole-interval proof on `[1/5,7/10]` gives `L_0(t)>T_*`.
This finishes (10), hence (2).

The only final scalar ingredients are one concavity comparison,
one degree-10 polynomial on a whole interval, the two whole-strip
derivative bounds, and the aligned-prefix base scalar. No
configuration mesh, generated row inventory, or numerical oracle
enters the proof.
