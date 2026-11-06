# A larger sharp terminal for the original physical frames

This chapter enlarges the orientation guard of the
[sharp local terminal](CB882_LOCAL_SHARP_TERMINAL.md). It permits twice
as much tilt for B,I,E,F,G while retaining the smaller A,D tilt bounds.
The original physical squares, center-gap hypotheses, weighted corner
identity, and equality conclusion are unchanged.

## 1. The complete guard and conclusion

Put Q=1105/256 and rho=91/60. Retain seven distinct physical unit
squares A,B,I,D,E,F,G, pairwise interior-disjoint, with all original
corners in the closed Q-disk. Write

\[
 u_P=(\alpha_P,\beta_P),\quad v_P=(-\beta_P,\alpha_P),
 \quad \alpha_P>0,\quad \alpha_P^2+\beta_P^2=1,
 \quad h_P=(\alpha_P+|\beta_P|)/2.
\]

The complete guard is

\[
\begin{gathered}
 0\le\beta_A\le1/20,\qquad -1/20\le\beta_D\le0,\\
 |\beta_P|\le1/10\quad(P=B,I,E,F,G),\\
 x_A\le x_B\le x_I\le x_D,\qquad x_B-x_A\ge h_A+h_B,\\
 x_F-x_E\ge h_E+h_F,\qquad x_G-x_F\ge h_F+h_G,\\
 -1/20\le y_I-y_B\le1/2,\qquad |y_D-y_I|\le1/10,\\
 1/3\le x_E-x_A\le2/3,\quad y_E>y_A,\\
 1/3\le x_D-x_G\le2/3,\quad y_G>y_D.
\end{gathered}                                                   \tag{1}
\]

**Theorem.** Every beta_P in this guard is zero, and

\[
\begin{aligned}
 c_A&=(-3/2,-1/16),&c_D&=(3/2,-1/16),\\
 c_E&=(-1,15/16),&c_G&=(1,15/16),\\
 x_B&=-1/2,&x_I&=1/2,&x_F&=0.
\end{aligned}                                                   \tag{2}
\]

The full original Cb882 caller is therefore impossible in (1),
including at closed Q: its retained original BC link and strictly
weak CD bit contradict (2), as verified in Section 6 below.

## 2. Uniform support estimates

Use the rational constants

\[
 a_0=497/500,\quad c=11/25,\quad
 \kappa_0=20/799,\quad\kappa_1=50/997.
\]

For every original in (1), alpha_P>=a_0; the squared comparison is
1-(1/10)^2-a_0^2=491/250000>0. Moreover

\[
 1-\alpha_P\le
 \begin{cases}
 \kappa_0|\beta_P|,&P=A,D,\\
 \kappa_1|\beta_P|,&P=B,I,E,F,G.
 \end{cases}                                                   \tag{3}
\]

For A,D use alpha_P>=399/400 and
beta_P^2/(1+alpha_P)<=|beta_P|/(20(1+399/400)).
For the other originals use alpha_P>=a_0 and
beta_P^2/(1+alpha_P)<=|beta_P|/(10(1+a_0)).

For two originals put b=beta_P, e=beta_T, and s=1/10.
The derivative of sqrt(1-z^2) gives

\[
 |\alpha_P-\alpha_T|\le(s/a_0)|b-e|.
\]

Consequently

\[
 |\sin(\theta_P-\theta_T)|
       \ge(a_0-s^2/a_0)|b-e|.
\]

Also the squared distance between their unit frame vectors gives

\[
\begin{aligned}
 1-\cos(\theta_P-\theta_T)
 &\le\frac12\left(1+(s/a_0)^2\right)|b-e|^2\\
 &\le s\left(1+(s/a_0)^2\right)|b-e|.
\end{aligned}
\]

The relative cosine is positive under (1). Hence the common support
threshold on either original's side axes satisfies

\[
 R_{PT}=\frac{1+\cos(\theta_P-\theta_T)
                  +|\sin(\theta_P-\theta_T)|}{2}
                 \ge1+c|b-e|.                              \tag{4}
\]

The exact reserve in the coefficient comparison is

\[
 \frac{a_0-s^2/a_0-s(1+(s/a_0)^2)}2-c
                  =\frac{361563}{247009000}>0.
\]

## 3. The two horizontal physical links

The horizontal gaps BI and ID are positive. If either were zero,
its height bound in (1) and the original incircles would contradict
physical disjointness. Every absolute center-coordinate difference
is less than 2rho=91/30.

On either pair a nearly vertical side normal has absolute projection
at most

\[
                 (1/10)(91/30)+1/2=241/300<1.
\]

A negative primary normal has projection at most (1/10)(1/2)<1.
Thus an actual separating normal toward the right must be the
positive primary u_O of one of the two physical owners. Its signed
slope t_O=beta_O/alpha_O gives

\[
 \Delta x\ge1+c|\beta_P-\beta_T|-t_O\Delta y.            \tag{5}
\]

Put delta=-beta_D>=0, b=beta_B, i=beta_I, and

\[
 T=|b|+|i-b|+|i+\delta|,\qquad
 P=\max\{b,i,0\},\qquad Z=\max\{|i|,\delta\}.
\]

The one-dimensional path 0,b,i,-delta gives

\[
                         T\ge\delta+2P,\qquad T\ge Z.
\]

For BI, the nonnegative-height loss is at most P/(2a_0) and
the negative-height loss is at most T/(20a_0). For ID the
loss is at most Z/(10a_0). These nonnegative bounds may be added,
so their total is at most

\[
                    \frac{T-\delta}{4a_0}+\frac{3T}{20a_0}.
\]

Combining (5) for both links with the actual AB link therefore gives

\[
\begin{aligned}
 x_D-x_A\ge{}&2+(\alpha_A+\alpha_B)/2+\beta_A/2
                    +(1/2-c)|b|\\
             &+k_D\delta+k_T(T-\delta),\\
 k_D={}&c-3/(20a_0),\qquad k_T=c-2/(5a_0).
\end{aligned}                                                   \tag{6}
\]

Every possible original owner of BI and ID was included.

## 4. The two vertical physical links

For A,E, a primary normal has absolute projection at most

\[
                 2/3+(1/10)(91/30)=97/100<1.
\]

A downward secondary normal has projection at most (1/10)(2/3)<1.
Thus the upward physical separator is v_O=(-beta_O,alpha_O),
owned by A or E. Put d=x_E-x_A in [1/3,2/3] and eta=1/200.
Its inequality and (4) give

\[
 y_E-y_A\ge1+c|\beta_E-\beta_A|
                   +d\beta_O-\eta|\beta_O|.              \tag{7}
\]

The normalization error is justified by

\[
 \eta-(2/3)(1/a_0-1)=97/99400>0.
\]

For O=A, the last two terms in (7) are at least
(1/3-eta)beta_A>=(13/40)beta_A.
For O=E and beta_E>=0,
c|beta_E-beta_A|+d beta_E>=(1/3)beta_A;
the remaining loss eta beta_E is at most |beta_E|/4.
For O=E and beta_E<0, the angular terms are at least

\[
 c\beta_A-(2/3-c+\eta)|\beta_E|
             \ge(13/40)\beta_A-(1/4)|\beta_E|.
\]

The two coefficient reserves are

\[
 1/3-\eta-13/40=1/300,\qquad
 1/4-(2/3-c+\eta)=11/600.
\]

Thus all cases give

\[
 y_E-y_A\ge1+(13/40)\beta_A-(1/4)|\beta_E|.              \tag{8}
\]

Reflecting the D,G pair in the vertical coordinate axis converts
beta_D into delta and beta_G into -beta_G. The same proof gives

\[
 y_G-y_D\ge1+(13/40)\delta-(1/4)|\beta_G|.               \tag{9}
\]

## 5. The exact weighted corner identity

Use the four Q-circle points

\[
 P_A=(-2,-9/16),\quad P_D=(2,-9/16),\quad
 P_E=(-3/2,23/16),\quad P_G=(3/2,23/16)
\]

and actual original corners

\[
 p_A=c_A-(u_A+v_A)/2,\quad p_D=c_D+(u_D-v_D)/2,
\]
\[
 p_E=c_E+(-u_E+v_E)/2,\quad p_G=c_G+(u_G+v_G)/2.
\]

Each P_P dot p_P<=Q. With the same positive weights as the smaller
terminal, put

\[
 S=(23/2)(P_A\cdot p_A+P_D\cdot p_D)
       +(9/2)(P_E\cdot p_E+P_G\cdot p_G)\le32Q.
\]

Direct expansion gives

\[
\begin{aligned}
 S={}&23(x_D-x_A)+(27/4)(x_G-x_E)\\
 &+(207/32)((y_E-y_A)+(y_G-y_D))\\
 &+(943/64)(\alpha_A+\alpha_D)-(529/64)(\beta_A+\delta)\\
 &+(423/64)(\alpha_E+\alpha_G)+(9/64)(\beta_E-\beta_G).
\end{aligned}                                                   \tag{10}
\]

Substitute (6), (8), (9), the actual EFG span, and (3), using
beta_E-beta_G>=-|beta_E|-|beta_G|. The constant terms are exactly
32Q. The remaining inequality is

\[
\begin{aligned}
 S-32Q\ge{}&K_A\beta_A+K_B|\beta_B|+K_D\delta\\
 &+K_E(|\beta_E|+|\beta_G|)+K_F|\beta_F|
                                  +K_T(T-\delta).       \tag{11}
\end{aligned}
\]

Every coefficient has the following positive rational value.

| Coefficient | Exact value |
|---|---:|
| K_A | 4786369/1022720 |
| K_B | 40043/49850 |
| K_D | 297537269/2541459200 |
| K_E | 142479/127616 |
| K_F | 25569/3988 |
| K_T | 10741/12425 |

For verification, with L=23 and J=207/32 the six entries are

\[
\begin{gathered}
 L/2+(13/40)J-529/64-\kappa_0(1679/64),\\
 L(1/2-c)-\kappa_1L/2,\\
 Lk_D+(13/40)J-529/64-\kappa_0(943/64),\\
 27/8-(1/4)J-9/64-\kappa_1(639/64),\\
 (27/4)(1-\kappa_1),\qquad Lk_T.
\end{gathered}                                                   \tag{12}
\]

Since every term on the right of (11) is nonnegative, S<=32Q
forces every displayed beta to vanish and T=delta=0. The definition
of T then forces beta_I=0 as well.

## 6. Equality and the unchanged original caller

All four nonnegative corner deficiencies Q-P_P dot p_P have positive
weights. Equality S=32Q forces each to be zero. Equality in
Cauchy--Schwarz gives p_P=P_P, and the aligned frames now give the
four anchor centers in (2).

The span x_D-x_A=3 is the sum of three horizontal gaps, each at
least one: AB is actual, and BI,ID now have aligned frames and
height gaps strictly below one. Their original disjointness forces
horizontal separation. Thus all three gaps equal one, giving
x_B=-1/2 and x_I=1/2. The actual EFG links similarly give x_F=0.
This proves the theorem.

Finally retain the full original Cb882 conditions, including originals
C,H. Its actual BC link gives x_C>=h_C. Its CD cone and contained
insets give x_C<=1-g_C, since D is aligned at x_D=3/2. But
h_C+g_C>=1, with equality only at h_C=g_C=1/2. Consequently
x_C=1/2 and x_D-x_C=1=h_C+h_D, contradicting the original strict
weak CD bit.

The larger terminal is therefore proved on the entire guard (1).
The complement of that guard still requires a complete separate cover;
this chapter alone does not exclude the whole Cb882 original.

## 7. Certifying the guard by linear inequalities

A finite cover need not bound each center separately tightly enough
to imply (1). It may instead prove the required center differences
directly. This retains the correlations between the same original
centers and uses the following ten linear targets:

| Linear expression | Upper bound |
|---|---:|
| x_B-x_I | 0 |
| x_I-x_D | 0 |
| y_B-y_I | 1/20 |
| y_I-y_B | 1/2 |
| y_D-y_I | 1/10 |
| y_I-y_D | 1/10 |
| x_A-x_E | -1/3 |
| x_E-x_A | 2/3 |
| x_G-x_D | -1/3 |
| x_D-x_G | 2/3 |

Here is an exact certificate rule for a target v dot z<=b, where
z contains the original center and frame variables in the
[physical-frame row chapter](CB882_PHYSICAL_FRAME_ROWS.md). Suppose
the current proved box is z_q in [L_q,U_q], and a nonnegative
rational combination of necessary rows gives A dot z<=B. For any
coefficient vector t put

\[
 \mathcal L(t)=\sum_q\min(t_q L_q,t_q U_q).
\]

For any positive rational M, the single rational comparison

\[
             Mb-\bigl(B-\mathcal L(A-Mv)\bigr)\ge0          \tag{13}
\]

proves the target: Mv dot z<=B-(A-Mv) dot z
<=B-\mathcal L(A-Mv)<=Mb. The row sum and every residual minimum
use the same already proved box. A target may also be checked
directly from its box maximum
sum_q max(v_q L_q,v_q U_q)<=b.

In the surviving Cb882 height arrangement, the whole-parent
theorems give y_E-y_A>=g_A+g_E>0 and
y_G-y_D>=g_D+g_G>0. The actual AB, EF and FG links, the signs
of A and D, and all physical pair and corner hypotheses are retained
in the caller. Thus the ten displayed targets, together with the
seven orientation bounds in (1), imply the entire guard. No
additional center-order or orientation assumption is needed.

Any finite use of this rule must print the actual row weights and
the nonnegative reserve in (13) for every target not supplied by
its proved box. A numerical objective value alone is insufficient.
