# A sharp terminal using the physical chain A,H,I,D

The seven-square weighted corner argument also works with three
physical horizontal links, without assuming any of them to be actual
coordinate-projection links. This provides a terminal for Cd402 near
the arrangement in which H and I lie between A and D.

## 1. Guard and conclusion

Retain seven distinct, pairwise interior-disjoint physical unit
squares A,H,I,D,E,F,G in the closed Q-disk, Q=1105/256.
Use their original canonical frames
u_P=(alpha_P,beta_P), v_P=(-beta_P,alpha_P), with alpha_P>0.
Suppose

\[
\begin{gathered}
 0\le\beta_A\le1/20,\qquad -1/20\le\beta_D\le0,\\
 |\beta_P|\le1/10\quad(P=H,I,E,F,G),\\
 x_A\le x_H\le x_I\le x_D,\\
 |y_H-y_A|\le1/20,\quad |y_I-y_H|\le1/20,
                  \quad |y_D-y_I|\le1/20,\\
 x_F-x_E\ge h_E+h_F,\qquad x_G-x_F\ge h_F+h_G,\\
 1/3\le x_E-x_A\le2/3,\qquad y_E>y_A,\\
 1/3\le x_D-x_G\le2/3,\qquad y_G>y_D.
\end{gathered}                                                  \tag{1}
\]

Then all seven beta_P vanish, and

\[
\begin{aligned}
 c_A&=(-3/2,-1/16),& c_D&=(3/2,-1/16),\\
 c_E&=(-1,15/16),& c_G&=(1,15/16),\\
 x_H&=-1/2,&x_I&=1/2,&x_F&=0.
\end{aligned}                                                  \tag{2}
\]

The full normalized 001/00 original is impossible in this guard:
its actual AB, BC and strictly weak CD contradict (2). This final
claim retains B and C as original physical squares with independent
frames. The guard alone is not a cover of the entire Cd402 original.

## 2. Uniform estimates already proved

Use the constants from
[the enlarged sharp terminal](CB882_ENLARGED_SHARP_TERMINAL.md):

\[
 a_0=497/500,\quad c=11/25,\quad
 \kappa_0=20/799,\quad\kappa_1=50/997.
\]

Its Section 2 applies without change after replacing its intermediate
original B by H. Thus alpha_P>=a_0, and

\[
 1-\alpha_P\le\kappa_0|\beta_P|\quad(P=A,D),\qquad
 1-\alpha_P\le\kappa_1|\beta_P|\quad(P=H,I,E,F,G).
\]

For either original owner of any physical side-axis separator,
the support threshold satisfies

\[
                  R_{PT}\ge1+c|\beta_P-\beta_T|.        \tag{3}
\]

The same terminal's Section 4, using exactly the endpoint gaps
in (1), supplies

\[
\begin{aligned}
 y_E-y_A&\ge1+(13/40)\beta_A-(1/4)|\beta_E|,\\
 y_G-y_D&\ge1+(13/40)\delta-(1/4)|\beta_G|,
 \qquad \delta=-\beta_D\ge0.
\end{aligned}                                                  \tag{4}
\]

Those proofs include both physical owners and every possible side
normal. They use no original B/H assumption.

## 3. All three horizontal links are physical

Consider any of the successive pairs AH, HI, ID in (1), with
center difference (Delta_x,Delta_y) toward the right. Its horizontal
gap is strictly positive: at zero gap, |Delta_y|<=1/20 would
contradict disjointness of the original incircles. Every center
coordinate difference has magnitude less than 2rho=91/30.

A nearly vertical side normal has absolute projection at most

\[
                  (1/10)(91/30)+1/20=53/150<1.
\]

A negative primary normal has projection at most
(1/10)(1/20)<1. Thus a physical separator toward the right must
be u_O=(alpha_O,beta_O) of one of the two original owners.
Divide its inequality by alpha_O and use (3) and alpha_O<=1:

\[
 \Delta_x\ge1+c|\beta_P-\beta_T|
                -\frac{\beta_O}{\alpha_O}\Delta_y.     \tag{5}
\]

Put a=beta_A>=0, b=beta_H, i=beta_I and

\[
                   T=|a-b|+|b-i|+|i+\delta|.
\]

The total variation along a,b,i,-delta satisfies T>=a+delta.
Every one of |a|,|b|,|i|,delta is at most T. Indeed, for a
nonnegative intermediate value its subpath to -delta has variation
at least that value; for a negative value the subpath from a does.
Hence the loss in each application of (5) is at most T/(20a_0).
Adding the three links gives

\[
 x_D-x_A\ge3+kT,
 \qquad k=c-\frac{3}{20a_0}=\frac{3592}{12425}>0.        \tag{6}
\]

Every possible original separating owner on each link is covered.

## 4. The weighted corner identity

Use precisely the four Q-circle points, original corners, and
positive weights in Section 5 of the enlarged sharp terminal.
Writing S for their weighted dot-product sum, its exact identity is

\[
\begin{aligned}
 S={}&23(x_D-x_A)+(27/4)(x_G-x_E)\\
 &+(207/32)((y_E-y_A)+(y_G-y_D))\\
 &+(943/64)(\alpha_A+\alpha_D)-(529/64)(a+\delta)\\
 &+(423/64)(\alpha_E+\alpha_G)+(9/64)(\beta_E-\beta_G)
 \le32Q.
\end{aligned}                                                  \tag{7}
\]

Substitute (6), (4), the actual EFG span from (1), and the alpha
estimates of Section 2. The constant terms are exactly 32Q.
Since T>=a+delta and beta_E-beta_G>=-|beta_E|-|beta_G|,

\[
\begin{aligned}
 S-32Q\ge{}&K_0(a+\delta)+K_1(T-a-\delta)\\
           &+K_E(|\beta_E|+|\beta_G|)+K_F|\beta_F|.
\end{aligned}                                                  \tag{8}
\]

All four coefficients are positive rational numbers:

| Coefficient | Formula | Exact value |
|---|---|---:|
| K_0 | 23k+(13/40)(207/32)-529/64-kappa_0(943/64) | 297537269/2541459200 |
| K_1 | 23k | 82616/12425 |
| K_E | 27/8-(1/4)(207/32)-9/64-kappa_1(639/64) | 142479/127616 |
| K_F | (27/4)(1-kappa_1) | 25569/3988 |

Thus S<=32Q forces a=delta=0, T=0, and beta_E=beta_F=beta_G=0.
The definition of T then forces beta_H=beta_I=0. Every loaded
original is aligned.

Equality in the four positively weighted corner inequalities gives
the four anchor centers in (2), by the same Cauchy--Schwarz equality
argument as Section 6 of the enlarged terminal. Each now-aligned
physical pair AH, HI, ID has height gap at most 1/20<1, so its
horizontal gap is at least one. Their sum is x_D-x_A=3;
all three gaps equal one and x_H=-1/2, x_I=1/2. The actual EFG
links similarly give x_F=0. This proves (2).

## 5. Contradiction with the unchanged weak link

Restore the full original caller, including B and C. The actual
AB and BC links and the aligned A anchor give

\[
 x_C\ge x_A+h_A+2h_B+h_C=-1+2h_B+h_C\ge h_C.
\]

The CD center cone forces its original aligned insets to separate
horizontally. The aligned D anchor therefore gives
x_C<=x_D-g_D-g_C=1-g_C. Since h_C+g_C>=1, equality is forced,
so h_C=g_C=1/2 and x_C=1/2. Then

\[
                    x_D-x_C=1=h_C+h_D,
\]

contradicting the retained strictly weak CD bit. This excludes the
entire guard (1), including all contact and tilt-sign boundaries.
