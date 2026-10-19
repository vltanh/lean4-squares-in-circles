# Exact square completion enlarges the hand terminal to S ≤ 1/500

This is a conditional geometric theorem. It assumes the seven named signed
separators, the frame lifts, and the two projected-slider bounds in
`HUMAN_BROAD_TERMINAL_ARITHMETIC.md`. It replaces that note's nonlinear
remainder estimate. It does not assume proximity of any actual center to a
comparison center. The remaining global capture hypotheses still have to be
proved separately.

The proof uses the same nine owner bounds and four fixed arithmetic rectangles
as that note. Its only additional numerical comparisons are the rational sums
in Section 6. In particular, it uses neither a new search nor an interval cover.

## 1. Statement and notation

Suppose seven actual unit squares lie in a centered disk of squared radius
\(r\le4\). Set the actual A frame to zero and the actual G frame to t, where
\(1/10\le t\le4/25\). Use the reference frames zero for B,T,D,E and t for H,
and write their errors as \(a_B,a_T,a_D,a_E,a_H\). Thus \(a_A=a_G=0\).
The five tree differences are

\[
\Delta_{AB}=-a_B,\quad \Delta_{TB}=a_T-a_B,\quad
\Delta_{DT}=a_D-a_T,\quad \Delta_{ED}=a_E-a_D,\quad
\Delta_{HG}=a_H.
\]

Put \(S=\sum_e|\Delta_e|\), and assume \(S\le1/500\).
The allowed signed witnesses are:

| Directed edge | Chosen owner normal |
|---|---|
| A→B | positive f-axis of A or B |
| T→B | positive e-axis of T or B |
| D→T | positive e-axis of D or T |
| E→D | positive f-axis of E or D |
| G→A | G's positive e-axis |
| H→G | positive e-axis of H or G |
| H→E | H's positive f-axis |

Take the stationary comparison at \(q=q_*\), this actual t, and
\(y=Y(q_*,t)\). Use the comparison coordinates, selected vertices, weights and
reference centers from the broad terminal note. Its edge weights are

\[
\lambda_{AB}=\alpha,\quad \lambda_{TB}=\lambda_{DT}=\beta,\quad
\lambda_{ED}=\delta,\quad \lambda_{HE}=\epsilon,\quad
\lambda_{GA}=\lambda_{HG}=\omega.
\]

Choose the two comparison sliders from the actual projections:

\[
 Z=(p_T)_y\in[29/50,7/5],\qquad
 \eta=(p_G-p_H^0-e_t)\cdot f_t\in[-1/2,37/100].                 \tag{1}
\]

Thus the actual T center and G center have the forms

\[
p_T=X_Te_0+Zf_0,\qquad
p_G=U_Ge_t+V_Gf_t,\qquad V_G=h_2+1/2+\eta.                  \tag{2}
\]

Their longitudinal coordinates \(X_T,U_G\) are unrestricted apart from
containment. In fact, every actual center p satisfies \(|p|\le3/2\): the
radius-1/2 disk centered at p lies in its square and hence in the radius-2
containing disk. Consequently

\[
 |X_T|,|U_G|,|V_G|\le3/2.                                  \tag{3}
\]

We prove

\[
\boxed{
r\ge q_*+\frac{3\mu_H}{8}(t-t_*)^2+
\sum_{i=A,B,D,E,H}\mu_i\left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +\frac9{100000}S\ \ge q_* .}                              \tag{4}
\]

Here \(o_i\) are the actual selected corner offsets, and the actual center
force coefficients \(F_i\) are given below. At zero frame error the square in
(4) is exactly \(|p_i-p_i^0|^2\). Thus equality requires \(t=t_*\), \(S=0\)
and equality of all five anchored centers. The two slider coordinates remain
subject to the actual packing constraints.

## 2. Complete the five center squares exactly

The reference selected corner offsets are

\[
o_A^0=(1/2,-1/2),\quad o_B^0=(1/2,1/2),\quad
o_D^0=(-1/2,1/2),\quad o_E^0=(-1/2,-1/2),\quad
o_H^0=-\tfrac12e_t-\tfrac12f_t,
\]

and \(o_i=R(a_i)o_i^0\). For each directed edge i→j with its chosen actual
normal \(n_e\), write the nonnegative signed gap as

\[
g_e=n_e\cdot(p_j-p_i)-w_e\ge0,
\]

where \(w_e\) is the sum of the two true square support radii. Positivity and
normalization of the disk weights give

\[
r\ge\mathcal D:=\sum_{i=A,B,D,E,H}\mu_i|p_i+o_i|^2-
\sum_e\lambda_e g_e .                                    \tag{5}
\]

For compactness put

\[
b=a_{\mathrm{owner}(AB)},\quad u=a_{\mathrm{owner}(TB)},\quad
v=a_{\mathrm{owner}(DT)},\quad d=a_{\mathrm{owner}(ED)},\quad h=a_H,
\]

and let \(n=R(h)e_t\) if H owns HG, and \(n=e_t\) if G owns HG.
The coefficients of the actual centers in \(-\sum\lambda_e g_e\) are exactly

\[
\begin{aligned}
F_A&=\alpha R(b)f_0-\omega e_t,&
F_B&=-\alpha R(b)f_0-\beta R(u)e_0,\\
F_D&=\beta R(v)e_0-\delta R(d)f_0,&
F_E&=\delta R(d)f_0-\epsilon R(h)f_t,\\
F_H&=\omega n+\epsilon R(h)f_t,&
F_T&=\beta(R(u)e_0-R(v)e_0),\\
F_G&=\omega(e_t-n).
\end{aligned}                                             \tag{6}
\]

For each anchored label i the identity

\[
\mu_i|p_i+o_i|^2+F_i\cdot p_i
=\mu_i\left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
-F_i\cdot o_i-\frac{|F_i|^2}{4\mu_i}                       \tag{7}
\]

is exact. Write \(\mathcal C\) for the sum of the five nonnegative squares
on its right. The entire remaining function is

\[
\mathcal L=-\sum_i\frac{|F_i|^2}{4\mu_i}
+\left(\sum_e\lambda_e w_e-\sum_iF_i\cdot o_i\right)
+F_T\cdot p_T+F_G\cdot p_G,
\qquad\mathcal D=\mathcal C+\mathcal L.                    \tag{8}
\]

At zero errors, the reference force identities give
\(F_i^0=-2\mu_iP_i^0\), and the two slider forces vanish. Thus
\(\mathcal L(0)=q_*+\mu_HF(q_*,Y(q_*,t),t)\).

The smooth first derivative of \(\mathcal L\) is exactly the angular linear
term in the broad note's owner table. Indeed, at the reference anchored
centers every completed square in (7) has both value and first derivative
zero. The first variations of \(F_T\) and \(F_G\) are parallel to \(f_0\)
and \(f_t\), respectively, so (1) makes their scalar products with actual
and reference slider centers identical at first order. No bound on a center
displacement enters this argument.

The smallest of that note's nine displayed owner bounds is exactly
\(1869/100000\). Including the five support cusps, its first-order term is
therefore at least

\[
\frac{1869}{100000}S.                                     \tag{9}
\]

## 3. The force norms leave just five trigonometric terms

Up to constants independent of the error angles, the first sum in (8) is

\[
K_A\sin(t-b)-K_B\sin(u-b)+K_D\sin(v-d)
+K_E\cos(t+h-d)+\begin{cases}0,&\text{H owns HG},\\
K_H\sin h,&\text{G owns HG},\end{cases}                    \tag{10}
\]

where all five coefficients are positive and the force identities simplify
them to

\[
\begin{aligned}
K_A&=\frac{\alpha\omega}{2\mu_A}=\frac{\alpha x_1}{\cos t},&
K_B&=\frac{\alpha\beta}{2\mu_B}=\beta(y+2),\\
K_D&=\frac{\beta\delta}{2\mu_D}=-\delta x_3,&
K_E&=\frac{\delta\epsilon}{2\mu_E}=-\frac{\delta x_4}{\sin t},&
K_H&=\frac{\omega\epsilon}{2\mu_H}=-\epsilon h_1.
\end{aligned}                                             \tag{11}
\]

To check signs in (10), use
\((R(b)f_0)\cdot e_t=\sin(t-b)\),
\((R(b)f_0)\cdot R(u)e_0=\sin(u-b)\), and
\(e_t\cdot R(h)f_t=-\sin h\).

Identify the two zero error roots A and G. The five error differences form
a tree, so the difference of any two errors has magnitude at most S.
Put \(S_C=|\Delta_{AB}|+|\Delta_{TB}|+|\Delta_{DT}|+|\Delta_{ED}|\)
and \(S_H=|h|\), so \(S_C+S_H=S\). All A–E errors have magnitude at most
\(S_C\).

Use the elementary estimates

\[
|\sin x-x|\le |x|^3/6,\qquad 0\le1-\cos x\le x^2/2.
\]

After subtracting the value and smooth linear term at zero, (10) is bounded
below by

\[
-\frac{K_A\sin t+K_E}{2}S^2
-\frac{K_A+K_B+K_D+K_H}{6}S^3.                            \tag{12}
\]

For the E term this uses the global bound \(|(\cos x)''|\le1\); no cubic
term is needed. For A, expand
\(\sin(t-b)=\sin t\cos b-\cos t\sin b\). The B,D,H sine terms have
zero second derivative at the reference angle and cost only cubically.

## 4. Exact support and selected-offset cancellation

For a small aligned difference \(\Delta\), put
\(c_\Delta=\cos\Delta\), \(s_\Delta=\sin\Delta\), and
\(a_\Delta=|\sin\Delta|\). The contribution of an edge to
\(\sum\lambda_e w_e-\sum_iF_i\cdot o_i\), divided by its edge weight,
is exactly as follows. A slider has no selected offset in this sum.

| Edge | Owner | Contribution divided by the edge weight |
|---|---|---|
| AB | A or B | \(1+c_\Delta-s_\Delta/2+a_\Delta/2\) |
| TB | B | \(1+c_\Delta/2+a_\Delta/2\) |
| TB | T | \(1/2+c_\Delta+s_\Delta/2+a_\Delta/2\) |
| DT | D | \(1+c_\Delta/2+a_\Delta/2\) |
| DT | T | \(1/2+c_\Delta+s_\Delta/2+a_\Delta/2\) |
| ED | E or D | \(1+c_\Delta+s_\Delta/2+a_\Delta/2\) |
| HG | H | \(1+c_\Delta/2+a_\Delta/2\) |
| HG | G | \(1/2+c_\Delta-s_\Delta/2+a_\Delta/2\) |

The \(\Delta\) in each row is that edge's tree difference from Section 1.
The cosine coefficient never exceeds 1, the smooth sine coefficient has
magnitude at most 1/2, and the cusp coefficient is exactly 1/2. If
\(w=4209/5000\), the printed maximum-edge-weight bound gives
\(\lambda_e<w\). Subtracting the constant, the smooth linear term and the
linear cusp, all five rows together therefore lose at most

\[
\frac w2\sum_e\Delta_e^2+\frac w6\sum_e|\Delta_e|^3
\le \frac w2S^2+\frac w6S^3.                              \tag{13}
\]

For the mixed edge HE let \(v_0=t+h-a_E\). Since \(|h-a_E|\le S\le.002\)
and \(.10\le t\le.16\), this angle lies strictly between zero and \(\pi/2\).
Its true support sum is \((1+\cos v_0+\sin v_0)/2\). The H selected-offset
contribution is 1/2; the E selected-offset contribution is
\((\sin v_0-\cos v_0)/2\). Their cosines cancel exactly, giving

\[
\epsilon(1+\sin v_0).                                    \tag{14}
\]

After its value and linear term, (14) loses at most
\(\epsilon(\sin t)S^2/2+\epsilon S^3/6\).
The GA contribution is \(\omega(1/2+\cos t)\), constant in every error.

## 5. The actual slider coordinates require only a small quadratic loss

Equations (2) and (6) give

\[
F_T\cdot p_T=\beta X_T(\cos u-\cos v)+\beta Z(\sin u-\sin v).
\]

Both \(|u|,|v|\le S_C\). Since the cosine values lie in
\([\cos S_C,1]\), their difference has magnitude at most \(S_C^2/2\),
rather than the sum of two separate quadratic estimates. Using (1) and (3),
the remainder after the linear term \(\beta Z(u-v)\) is bounded below by

\[
-\frac{3\beta}{4}S_C^2-\frac{7\beta}{15}S_C^3.             \tag{15}
\]

The G term is zero if G owns HG. If H owns it, then

\[
F_G\cdot p_G=\omega U_G(1-\cos h)-\omega V_G\sin h.
\]

After its linear term \(-\omega V_Gh\), (3) gives the lower bound
\(-3\omega S_H^2/4-\omega S_H^3/4\).
Because \(S_C^j+S_H^j\le S^j\) for j=2,3, the total slider remainder is
at least

\[
-\frac{3w}{4}S^2-\frac{7w}{15}S^3.                        \tag{16}
\]

## 6. Five quadratic constants and seven cubic constants

All quantities in this section are rational. The broad terminal note supplies

\[
w=\frac{4209}{5000},\quad X_1=\frac{17649}{10000},\quad
X_4=\frac{19049}{10000},\quad Y_2=\frac{221}{200},\quad
X_3=\frac{6793}{5000},\quad H_1=\frac{14263}{10000},
\]

as strict upper bounds for the corresponding weights and positive coordinate
magnitudes. With \(z_+=81/1000\), define

\[
s_-=\frac{40}{401},\quad s_+=\frac{2z_+}{1+z_+^2},\quad
c_-=\frac{1-z_+^2}{1+z_+^2},\quad
\tau_+=\frac{2z_+}{1-z_+^2}.
\]

These bound \(\sin t\) below and above, \(\cos t\) below, and \(\tan t\)
above throughout the rational comparison chart. Equations (12)--(16) give
the total quadratic coefficient

\[
\begin{aligned}
C_2&=\frac{wX_4}{2s_-}+\frac{wX_1\tau_+}{2}
 +\frac{ws_+}{2}+\frac w2+\frac{3w}{4}\\
&=\frac{26453303561590200213}{2850910772000000000}
 <\frac{232}{25}=9.28,                                    \tag{17}
\end{aligned}
\]

and the total cubic coefficient

\[
\begin{aligned}
C_3&=\frac w6\left(\frac{X_1}{c_-}+Y_2+X_3+H_1\right)
 +\frac w6+\frac w6+\frac{7w}{15}\\
&=\frac{25398850783}{17277200000}<\frac32.                  \tag{18}
\end{aligned}
\]

Thus, for \(S\le1/500\),

\[
C_2S^2+C_3S^3
<\left(\frac{232}{25}+\frac3{1000}\right)S^2
=\frac{9283}{1000}S^2<\frac{93}{10}S^2.                   \tag{19}
\]

No decimal approximation is needed to verify (17)--(19); cross-multiplication
of the displayed integers suffices. The companion
`verify_exact_center_square_constants.py` checks exactly these fixed sums and
the nine inherited reserve values, without importing any other proof code.

## 7. Conclusion

Combining (8), (9) and (19) gives

\[
r\ge q_*+\mu_HF(q_*,Y(q_*,t),t)+\mathcal C
+\left(\frac{1869}{100000}-\frac{93}{10}S\right)S.
\]

Since \(S\le1/500\), its last coefficient is at least

\[
\frac{1869}{100000}-\frac{93}{5000}=\frac9{100000}>0.
\]

The already proved stationary-family estimate
\(F(q_*,Y(q_*,t),t)\ge3(t-t_*)^2/8\) now gives (4).
The entire argument applies to all 32 allowed owner assignments because the
force and support identities cover each owner explicitly, and the one
first-order input is the uniform nine-scalar owner table.

