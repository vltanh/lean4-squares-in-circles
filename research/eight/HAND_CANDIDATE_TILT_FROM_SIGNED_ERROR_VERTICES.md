# The candidate tilt follows at total mismatch at most 1/1000

## 1. Statement and scope

Assume the candidate cyclic order, real frame lifts, exterior-square
conditions and signed-tangent bounds (1)–(3) of
HAND_CANDIDATE_MIXED_OWNERS_AND_TILT.md. Assume also

\[
q\le Q=\frac{1957767069}{500000000}=3.915534138,
\qquad S\le\varepsilon=\frac1{1000},
\tag{1}
\]

and the seven intended canonical owner sets

\[
\{1,3\},\quad\{1\},\quad\{1,3\},\quad\{3,4\},\quad
\{1,3\},\quad\{3,4\},\quad\{2\}.
\tag{2}
\]

The quarter theorem at \(S\le3/200\) and
HAND_CANDIDATE_MIXED_OWNERS_WITH_TOTAL_MISMATCH.md supply (2) at the
threshold (1). This note proves

\[
\boxed{\frac1{10}<t=\theta_G-\theta_A<\frac4{25}.}
\tag{3}
\]

Thus the remaining candidate capture target is precisely \(S\le1/1000\).
The already proved automatic-slider terminal then applies directly. No
separate capture of centers, radial types, slider values or smaller
mismatch is required.

The proof retains the signed differences in the five aligned edges.
It uses one common nonnegative edge-weight vector per half-angle
interval, then treats the finitely many possible worst error alternatives.
It does not choose a different edge-weight vector after selecting a worst
error. That distinction is necessary for the argument.

All centers satisfying the stated conditions are included. Neither the
two radial-boundary equalities nor a contact equality is assumed.
The strict inequalities in (3) include the two endpoint cases.

## 2. The actual separating functions and their derivatives

Use roles \(0,\ldots,6=(H,G,A,B,T,D,E)\), signs
\(\sigma=(+,-,+,-,+,-,-)\), and own-frame centers
\((a_i,-\sigma_i b_i)\). Write \(x=(a_0,\ldots,a_6,b_0,\ldots,b_6)\).
The four forward projections for a pair are

\[
\begin{aligned}
F_1&=\sigma b+A\sin\phi-\tau B\cos\phi,\\
F_2&=-a\cos\phi+\sigma b\sin\phi+A,\\
F_3&=a\sin\phi+\sigma b\cos\phi-\tau B,\\
F_4&=a-A\cos\phi-\tau B\sin\phi.
\end{aligned}
\tag{4}
\]

The actual selected projection is at least
\(W(\phi)=(1+|\sin\phi|+|\cos\phi|)/2\).
Every actual center has norm less than \(3/2\). Consequently, for fixed
own-frame coordinates, every projection in (4) has second derivative
with absolute value at most \(3/2\).

Normalize \(\theta_A=0\), put \(t=\theta_G\), and let

\[
I=\{0,2,3,4,5\},\qquad d_i=\theta_{i+1}-\theta_i,\qquad
\Delta=\sum_{i\in I}d_i.
\tag{5}
\]

Thus \(S=\sum_{i\in I}|d_i|\). The aligned nominal angles are
\(k_i\pi/2\), G→A has the exact angle \(\pi/2-t\), and E→H has
angle \(\pi/2+t-\Delta\).

Let \(f_i^0(t)\cdot x\) denote the nominal selected projection, and let
\(f_i'(t)\cdot x\) denote its derivative with respect to that pair's
relative canonical angle, at the nominal value. Differentiating (4)
gives the following complete table on the aligned edges:

| Edge \(i\) | Actual canonical owner | \(f_i'\cdot x\) |
|---|---:|---|
| H→G, \(i=0\) | 1 | \(a_G\) |
| H→G, \(i=0\) | 3 | \(a_H\) |
| A→B, \(i=2\) | 1 | \(a_B\) |
| A→B, \(i=2\) | 3 | \(a_A\) |
| B→T, \(i=3\) | 3 | \(b_B\) |
| B→T, \(i=3\) | 4 | \(a_T\) |
| T→D, \(i=4\) | 1 | \(a_D\) |
| T→D, \(i=4\) | 3 | \(a_T\) |
| D→E, \(i=5\) | 3 | \(b_D\) |
| D→E, \(i=5\) | 4 | \(a_E\) |

The two possible nominal projections agree on each aligned edge, as in
the earlier owner proof; only the displayed derivative depends on its
owner. The mixed owners are fixed by (2). In particular, writing
\(c=\cos t,s=\sin t\),

\[
f_6'\cdot x=a_Ec+b_Es.
\tag{6}
\]

Write \(w_i^0=1\) on \(I\), and
\(w_1^0=w_6^0=W_t=(1+c+|s|)/2\). The derivative of the last
nominal width is

\[
w_6'=
\begin{cases}
(c-s)/2,&t\ge0,\\
-(c+s)/2,&t\le0.
\end{cases}
\tag{7}
\]

At zero either one-sided value in (7) is allowed, in the corresponding
closed half-angle interval.

## 3. A uniform second-order necessary inequality

For an aligned edge, Taylor's theorem and
\(|F_j''|\le3/2\) give

\[
F_i^{\rm actual}
\le f_i^0\cdot x+(f_i'\cdot x)d_i+\frac34d_i^2.
\tag{8}
\]

Also, for \(|d_i|\le\varepsilon\),

\[
W(k_i\pi/2+d_i)
\ge1+\frac12|d_i|-\left(\frac14+\frac{\varepsilon}{12}\right)d_i^2.
\tag{9}
\]

Since the actual projection is at least the actual width, (8)–(9)
imply the necessary inequality

\[
f_i^0\cdot x-1
\ge\frac12|d_i|-(f_i'\cdot x)d_i-\frac{1001}{1000}d_i^2.
\tag{10}
\]

Here \(1+\varepsilon/12<1001/1000\); the same constant works for
every \(\varepsilon\le1/500\).

We also need a width estimate valid when an error crosses the cusp at
\(t=0\). Away from the quarter-angle cusps,

\[
W''(\phi)=-\frac{|\sin\phi|+|\cos\phi|}{2}
\ge-\frac{\sqrt2}{2}>-\frac34.
\tag{11}
\]

At every cusp the derivative jumps upward. Thus the function
\(W(\phi)+3\phi^2/8\) is convex: its derivative is increasing on every
smooth interval and has only upward jumps. Its supporting-line
inequality, valid also for either endpoint derivative at a cusp, is

\[
W(u+v)\ge W(u)+W'(u)v-\frac38v^2.
\tag{12}
\]

For the last edge take \(u=\pi/2+t\), \(v=-\Delta\). The projection
Taylor bound contributes \(3\Delta^2/4\), while (12) contributes
\(3\Delta^2/8\). Their combination is

\[
f_6^0\cdot x-w_6^0
\ge(f_6'\cdot x-w_6')\Delta-\frac98\Delta^2.
\tag{13}
\]

G→A has no angle error. Fix nonnegative weights
\(\lambda_0,\ldots,\lambda_6\), and set

\[
\begin{aligned}
B_0(x,t)&=\sum_i\lambda_i(f_i^0\cdot x-w_i^0),\\
c_j(x,t)&=\lambda_j f_j'\cdot x-\lambda_6 f_6'\cdot x
                         +\lambda_6w_6',\qquad j\in I,\\
R_\lambda&=\varepsilon^2\left(
\frac{1001}{1000}\max_{j\in I}\lambda_j+\frac98\lambda_6\right).
\end{aligned}
\tag{14}
\]

Multiply (10) and (13) by the corresponding weights, and add the
unchanged G→A inequality. Since
\(\sum d_i^2\le S^2\le\varepsilon^2\) and
\(\Delta^2\le\varepsilon^2\), every actual packing necessarily satisfies

\[
B_0(x,t)+
\sum_{j\in I}\left(c_j(x,t)d_j-\frac{\lambda_j}{2}|d_j|\right)
+R_\lambda\ge0.
\tag{15}
\]

The second-order loss \(R_\lambda\) is a fixed rational constant for
each weight vector. No center proximity enters this estimate.

## 4. Exactly 21 possible error alternatives suffice

For arbitrary real numbers \(c_j\), the maximum over the full closed
ball \(\sum|d_j|\le\varepsilon\) is

\[
\max_{\sum|d_j|\le\varepsilon}
\sum_j\left(c_jd_j-\frac{\lambda_j}{2}|d_j|\right)
=\varepsilon\max\left(0,\max_j(|c_j|-\lambda_j/2)\right).
\tag{16}
\]

To prove (16), each summand is at most
\((|c_j|-\lambda_j/2)|d_j|\). If every coefficient is nonpositive,
zero attains the maximum. Otherwise spend the whole allowed absolute
sum on one largest positive coefficient, with the sign of its \(c_j\).
Thus a maximizing alternative is either zero or exactly one signed
coordinate \(d_j=\pm\varepsilon\).

Apply (16) to the fixed weight vector in (14). For the actual center
coordinates, (15) implies that at least one of these alternatives
satisfies the corresponding inequality. On a nonzero alternative only
the owner of edge \(j\) affects \(c_j\), through the table in Section 2.
The other four aligned owners have identical nominal values and make
no derivative contribution. There are therefore

\[
1+5\cdot2\cdot2=21
\tag{17}
\]

alternatives covering all 32 aligned-owner assignments.

This is an exact maximum argument. The alternative need not equal the
actual error vector. It merely gives a necessary disjunction containing
every actual error vector.

For clarity, let
\[
C^0=\sum_i\lambda_i f_i^0,\qquad
w^0=\sum_i\lambda_i w_i^0.
\]
The zero alternative is the linear inequality
\[
C^0\cdot x\ge w^0-R_\lambda.
\tag{18}
\]
For edge \(j\), its stated owner, and sign \(\eta\in\{-1,+1\}\), the
alternative is exactly
\[
\begin{aligned}
C^v&=C^0+\eta\varepsilon(\lambda_j f_j'-\lambda_6f_6'),\\
b^v&=w^0-\eta\varepsilon\lambda_6w_6'
                 +\frac{\varepsilon\lambda_j}{2}-R_\lambda,\\
C^v\cdot x&\ge b^v.
\end{aligned}
\tag{19}
\]

All 21 alternatives in one angle interval use the same seven
\(\lambda_i\). One may use different additional valid cone inequalities
or different positive circle weights for different alternatives.
Those choices are made only after the common-weight disjunction
(18)–(19) has been derived.

## 5. Eliminate each alternative by a rational quartic

Use the 35 linear inequalities \(K_h\cdot x\ge v_h\) from the earlier
capture note. They include
\(7/12\le a_G,a_T\le349/250\), the primary bounds for the other roles,
the signed-tangent ratio bounds and \(b_i\le9/10\).
For one alternative choose nonnegative rational \(\kappa_h\) and
positive rational \(\mu_i\), and put

\[
\widetilde C=C^v+\sum_h\kappa_hK_h,\qquad
L=b^v+\sum_h\kappa_hv_h+\frac12\sum_{r=0}^{13}\widetilde C_r.
\tag{20}
\]

Adding the valid linear rows to (18) or (19), then completing the seven
circle squares, gives the necessary inequality

\[
L(t)\le Q\sum_i\mu_i+
\sum_i\frac{\widetilde C_{a_i}(t)^2+
                  \widetilde C_{b_i}(t)^2}{4\mu_i}.
\tag{21}
\]

Set \(z=\tan(t/2)\), \(D=1+z^2\). On a fixed-sign closed interval,
\(\sin t=2z/D\), \(\cos t=(1-z^2)/D\), and (7) is rational with
the same denominator. Consequently both numerator polynomials
\(\widehat C=D\widetilde C\) and \(\widehat L=DL\) have degree at
most two. The strict reverse of (21) is the positivity of

\[
P(z)=D\widehat L-QD^2\sum_i\mu_i-
\sum_i\frac{\widehat C_{a_i}(z)^2+
                  \widehat C_{b_i}(z)^2}{4\mu_i}.
\tag{22}
\]

This is again a quartic. Retaining the signed errors has introduced
neither extra continuous variables into the arithmetic table nor a
higher polynomial degree.

## 6. The finite table and the exact tilt tails

The full constants are in candidate_tilt_signed_error_hand_data.json.
There are 59 rational closed angle intervals. Each contains one common
seven-entry \(\lambda\) vector and exactly the 21 alternatives in
Section 4. Each alternative contains its nonzero indexed cone weights,
seven positive circle weights, and five positive Bernstein lower
numerators. All multiplier denominators are \(10^8\); all printed
coefficient denominators are \(10^{12}\).

Thus the table consists of 1,239 quartics and 6,195 positive coefficient
bounds. The elementary Bernstein conversion (24)–(25) of
HAND_CANDIDATE_MIXED_OWNERS_AND_TILT.md proves each quartic positive
on its whole closed interval. The interval union is exactly

\[
[-3/8,1001/20000]\ \cup\ [2/25,3/8].
\tag{23}
\]

The standalone companion verify_candidate_signed_error_tilt_duals.py
reconstructs the actual SAT formulas and their angular derivatives, checks
the derivative table, and reconstructs every row of (14), (18)–(22).
It binds one common edge-weight vector to all 21 alternatives in each
interval. It rejects missing or duplicate alternatives and checks the two
closed interval unions exactly. Finally it reconstructs every Bernstein
coefficient and the inverse transformation back to power coefficients.
No search, floating-point calculation, optimizer, sampled-state premise,
interval subdivision, or imported proof program is used by the replay.

Every alternative in the necessary disjunction is therefore impossible
when \(z\) lies in (23). Since \(|t|<7/10\) implies \(|z|<3/8\),
the actual \(z\) must lie strictly between \(1001/20000\) and \(2/25\).
The exact elementary comparisons

\[
2\left(\frac{1001}{20000}
-\frac13\left(\frac{1001}{20000}\right)^3\right)>\frac1{10},
\qquad
2\arctan(2/25)<2(2/25)=\frac4{25}
\tag{24}
\]

prove (3).

The conclusion is conditional only on the stated geometric cuts, the
intended owner sets and \(S\le1/1000\). Combining the already proved
owner gates at that threshold with this theorem supplies every
hypothesis of HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md. Its sharp lower
bound and its equality conditions can therefore be applied without any
additional local capture step.
