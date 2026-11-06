# A sharp local terminal using the actual AB link

This chapter proves a continuous hand terminal for the unchanged
original-nine `001/00` domain. It uses neither an endpoint tilt-toll
theorem nor an archived certificate. Its proof consists of elementary
separating-axis estimates and one explicit weighted sum of four corner
inequalities.

The terminal covers an open neighborhood of the relevant closed-Q
equality family, including the freedom to lower B. It does not by itself
prove that every Cb882 original enters that neighborhood. A complete
whole-original proof must also exclude its entire complement.

## 1. Precise closed-radius theorem

Put Q=1105/256 and rho=91/60. Retain seven distinct physical unit
squares A,B,I,D,E,F,G, pairwise interior-disjoint and with every
corner in the closed Q-disk. In the same fixed auxiliary frame write

\[
 u_P=(\alpha_P,\beta_P),\quad v_P=(-\beta_P,\alpha_P),\quad
 \alpha_P>0,\quad\alpha_P^2+\beta_P^2=1.
\]

Assume the following complete local guard:

\[
\begin{gathered}
 |\beta_P|\le1/20\quad(P=A,B,I,D,E,F,G),\qquad
 \beta_A\ge0,\quad\beta_D\le0,\\
 x_A\le x_B\le x_I\le x_D,\qquad
 x_B-x_A\ge h_A+h_B,\\
 x_F-x_E\ge h_E+h_F,\qquad x_G-x_F\ge h_F+h_G,\\
 -1/20\le y_I-y_B\le1/2,\qquad |y_D-y_I|\le1/10,\\
 1/3\le x_E-x_A\le2/3,\quad y_E>y_A,\\
 1/3\le x_D-x_G\le2/3,\quad y_G>y_D,
 \qquad h_P=(\alpha_P+|\beta_P|)/2.
\end{gathered}                                                   \tag{1}
\]

**Theorem.** These hypotheses force all seven beta_P to be zero,
and force

\[
\begin{aligned}
 c_A&=(-3/2,-1/16),&c_D&=(3/2,-1/16),\\
 c_E&=(-1,15/16),&c_G&=(1,15/16),\\
 x_B&=-1/2,&x_I&=1/2,&x_F&=0.
\end{aligned}                                                   \tag{2}
\]

Consequently the full original `001/00` caller is impossible in this
guard, even at closed Q. Indeed BC is actual, CD is cone and strictly
weak; Section 7 shows that (2) forces CD to be actual instead.
The ninth original H and C keep all their physical constraints in
this application. The theorem does not replace them with seven new
packing objects.

## 2. A uniform support estimate near the coordinate frame

Set a_0=399/400 and kappa=20/799. The guard gives

\[
 \alpha_P\ge a_0,\qquad
                 1-\alpha_P\le\kappa |\beta_P|.                \tag{3}
\]

The second estimate is beta_P^2/(1+alpha_P)<=
(1/20)|beta_P|/(1+a_0). For two originals put
b=beta_P, e=beta_T. Then

\[
 |\alpha_P-\alpha_T|\le(20/399)|b-e|.
\]

It follows directly that

\[
 |\sin(\theta_P-\theta_T)|
 \ge(a_0-(1/400)/a_0)|b-e|\ge(99/100)|b-e|,
\]

and, using |b-e|<=1/10,

\[
 1-\cos(\theta_P-\theta_T)
 \le\frac1{20}(1+(20/399)^2)|b-e|
 \le(51/1000)|b-e|.
\]

Thus the common support threshold on either original's side axes is

\[
 R_{PT}=\frac{1+\cos(\theta_P-\theta_T)
                    +|\sin(\theta_P-\theta_T)|}{2}
            \ge1+c|b-e|,\qquad c=15/32.                       \tag{4}
\]

The scalar comparison reserves in this deduction are

| Comparison | Positive reserve |
|---|---:|
| a_0-(1/400)/a_0-99/100 | 797/159600 |
| 51/1000-(1/20)(1+(20/399)^2) | 139201/159201000 |
| 939/2000-15/32 | 3/4000 |

Both signed angles and the aligned endpoint are included.

## 3. The two horizontal physical links

The links BI and ID need not be actual projection links. Their
horizontal gaps are nevertheless positive: a zero gap and the
height bounds in (1) would violate their original incircles.
Every center difference has either coordinate smaller than
2rho=91/30 in absolute value. A nearly vertical side normal has
projection at most
(1/20)(91/30)+1/2=391/600<1 on either pair.
A negative primary normal has projection at most (1/20)(1/2)<1.
Hence a separating normal toward the right must be the positive
primary u_O of one of the two actual owners.

For its signed slope t_O=beta_O/alpha_O, physical separation gives

\[
 \Delta x\ge R_{PT}/\alpha_O-t_O\Delta y
                      \ge1+c|\beta_P-\beta_T|-t_O\Delta y.    \tag{5}
\]

Put delta=-beta_D>=0, b=beta_B, i=beta_I, and

\[
 T=|b|+|i-b|+|i+\delta|,\quad
 P=\max\{b,i,0\},\quad Z=\max\{|i|,\delta\}.
\]

The polygonal path 0,b,i,-delta gives

\[
             T\ge\delta+2P,\qquad T\ge Z.                    \tag{6}
\]

On the first edge, a nonnegative height difference contributes at
most P/(2a_0). A negative height difference has magnitude at most
1/20 and contributes at most T/(20a_0). These two nonnegative
bounds may be added to cover both signs. For the second, either actual
owner has absolute beta at most Z, and its height difference has
absolute value at most 1/10. Its slope term is at most Z/(10a_0).
Equations (5)--(6), together with the actual AB link, therefore give

\[
\begin{aligned}
 x_D-x_A\ge{}&2+(\alpha_A+\alpha_B)/2+\beta_A/2
                    +(1/2-c)|b|\\
              &+k_D\delta+k_T(T-\delta),                      \tag{7}\\
 k_D={}&c-3/(20a_0)=1355/4256,\\
 k_T={}&c-1/(4a_0)-3/(20a_0)=865/12768.
\end{aligned}
\]

To check the last step without an owner assumption, the sum of the
two losses is at most
(T-delta)/(4a_0)+3T/(20a_0). Subtract this from cT.
This covers all four BI/ID owner patterns. The term T-delta is
nonnegative and is retained in the sharp estimate.

## 4. The two vertical physical links

Consider A,E first. A primary side normal has projection at most
2/3+(1/20)(91/30)=491/600<1; a downward secondary normal has
projection at most (1/20)(2/3)<1. Hence an actual separator
toward E is v_O=(-beta_O,alpha_O), owned by A or E.
Write d=x_E-x_A in [1/3,2/3]. Equations (3)--(4) imply

\[
 y_E-y_A\ge1+c|\beta_E-\beta_A|+d\beta_O-\eta|\beta_O|,
 \qquad\eta=1/500.
\]

The normalization error is valid because
(2/3)(1/a_0-1)<1/500, with reserve 197/598500.
If O=A, the last two terms are at least (1/3-eta)beta_A.
If O=E and beta_E>=0, the first two angular terms are at least
(1/3)beta_A. If O=E and beta_E<0, they are at least
c beta_A-(2/3-c)|beta_E|. Since
2/3-c+eta<1/5, with reserve 1/12000, both owners and signs give

\[
 y_E-y_A\ge1+(33/100)\beta_A-(1/5)|\beta_E|.                  \tag{8}
\]

Reflecting the isolated D/G pair in the vertical coordinate axis
changes beta_D into delta and beta_G into -beta_G, and makes
its horizontal gap positive in [1/3,2/3]. The same proof gives

\[
 y_G-y_D\ge1+(33/100)\delta-(1/5)|\beta_G|.                   \tag{9}
\]

These are inequalities for the actual originals, not imposed vertical
projection separations. All physical separator owners were covered.

## 5. The four-corner weighted identity

Let

\[
 P_A=(-2,-9/16),\quad P_D=(2,-9/16),\quad
 P_E=(-3/2,23/16),\quad P_G=(3/2,23/16).
\]

Each has squared norm Q. Choose the actual original corners

\[
 p_A=c_A-(u_A+v_A)/2,\quad p_D=c_D+(u_D-v_D)/2,
\]
\[
 p_E=c_E+(-u_E+v_E)/2,\quad p_G=c_G+(u_G+v_G)/2.
\]

Corner containment and Cauchy--Schwarz give P_P dot p_P<=Q.
With weights 23/2 for A,D and 9/2 for E,G define

\[
 S=(23/2)(P_A\cdot p_A+P_D\cdot p_D)
       +(9/2)(P_E\cdot p_E+P_G\cdot p_G)\le32Q.
\]

Direct expansion is the exact identity

\[
\begin{aligned}
 S={}&23(x_D-x_A)+(27/4)(x_G-x_E)\\
 &+(207/32)((y_E-y_A)+(y_G-y_D))\\
 &+(943/64)(\alpha_A+\alpha_D)-(529/64)(\beta_A+\delta)\\
 &+(423/64)(\alpha_E+\alpha_G)+(9/64)(\beta_E-\beta_G).
\end{aligned}                                                   \tag{10}
\]

The actual EFG links give

\[
 x_G-x_E\ge(\alpha_E+2\alpha_F+\alpha_G
                    +|\beta_E|+2|\beta_F|+|\beta_G|)/2.
\]

Substitute this, (7)--(9), and 1-alpha<=kappa|beta| into
(10), and bound beta_E-beta_G below by
-|beta_E|-|beta_G|. The constant terms total exactly
1105/8=32Q. Collecting gives

\[
\begin{aligned}
 S-32Q\ge{}&K_A\beta_A+K_B|\beta_B|+K_D\delta\\
 &+K_E(|\beta_E|+|\beta_G|)+K_F|\beta_F|
                            +K_T(T-\delta),                    \tag{11}
\end{aligned}
\]

with the following complete rational coefficient table:

| Coefficient | Exact positive value |
|---|---:|
| K_A | 12048619/2556800 |
| K_B | 11017/25568 |
| K_D | 279812227/340054400 |
| K_E | 432279/255680 |
| K_F | 21033/3196 |
| K_T | 19895/12768 |

For direct verification, put J=207/32, L=23 and c=15/32.
The entries are respectively

\[
\begin{gathered}
 L/2+(33/100)J-529/64-\kappa(1679/64),\\
 L(1/2-c)-\kappa L/2,\\
 L k_D+(33/100)J-529/64-\kappa(943/64),\\
 27/8-(1/5)J-9/64-\kappa(639/64),\\
 (27/4)(1-\kappa),\qquad L k_T.
\end{gathered}                                                   \tag{12}
\]

Every quantity on the right of (11) is nonnegative. Together with
S<=32Q this proves equality and forces beta_A=beta_B=beta_D=
beta_E=beta_F=beta_G=0 and T=delta=0. The definition of T
then forces beta_I=0 too.

## 6. The equality consequences needed for the terminal

Each of the four nonnegative quantities Q-P_P dot p_P has
positive weight in S. Hence each is zero. Since |p_P|<=sqrt(Q)
and |P_P|=sqrt(Q), the equality case of Cauchy--Schwarz gives
p_P=P_P. With the now aligned frames, this proves the four
anchor centers in (2).

The horizontal span x_D-x_A is three. Each of AB,BI,ID has
horizontal gap at least one: AB is actual, and the other two
aligned pairs have vertical gap strictly below one by (1), so
their physical nonoverlap must be horizontal. Thus all three
horizontal gaps are exactly one, giving x_B=-1/2 and x_I=1/2.
The actual EFG links similarly give x_F=0.

No assumption that B must have the same height as the outer anchors
was made. In particular this terminal includes the closed-Q family
in which B moves downward while I has the outer-anchor height.

## 7. Application to the unchanged nine-original weak-CD caller

In the original `001/00` domain, BC is actual. Since B is aligned
at x_B=-1/2, this gives x_C>=h_C. D is aligned at x_D=3/2,
and the original CD cone gives its inset comparison
x_D-x_C>=g_C+1/2. Therefore

\[
                    h_C\le x_C\le1-g_C.
\]

But h_C+g_C>=1, with equality only at h_C=g_C=1/2.
Consequently x_C=1/2 and x_D-x_C=1=h_C+h_D, which violates
the original strict weak CD bit. This is a contradiction even at
closed Q, and hence in particular below Q.

The local terminal is therefore complete for its exact guard (1).
Its complement remains part of the whole Cb882 proof obligation;
no whole original or mask is credited solely from this chapter.
All scalar arithmetic and identities are printed. Computation was
used to identify the weighted sum and check its rational constants;
no numerical feasibility result is a proof premise. No independent
review, Lean, Lake, CI or kernel verification is claimed.
