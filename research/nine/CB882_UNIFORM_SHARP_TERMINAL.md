# A uniform one-tenth sharp terminal

This chapter proves the sharp terminal with the same tilt allowance
for all seven loaded original squares. The extra estimate retains
the variation of absolute tilt along the physical B,I,D path.
It does not exclude the complement of the complete guard below.

## 1. Complete guard and conclusion

Let A,B,I,D,E,F,G be seven distinct, pairwise interior-disjoint
physical unit squares, with all original corners in the closed disk
of squared radius Q=1105/256. Use their canonical original frames
u_P=(alpha_P,beta_P), v_P=(-beta_P,alpha_P), with alpha_P>0,
alpha_P^2+beta_P^2=1 and h_P=(alpha_P+abs(beta_P))/2.
Assume the complete guard

\[
\begin{gathered}
 0\le\beta_A\le1/10,\qquad -1/10\le\beta_D\le0,\\
 |\beta_P|\le1/10\quad(P=B,I,E,F,G),\\
 x_A\le x_B\le x_I\le x_D,\qquad x_B-x_A\ge h_A+h_B,\\
 x_F-x_E\ge h_E+h_F,\qquad x_G-x_F\ge h_F+h_G,\\
 -1/16\le y_I-y_B\le3/4,\qquad |y_D-y_I|\le1/10,\\
 1/3\le x_E-x_A\le2/3,\quad y_E>y_A,\\
 1/3\le x_D-x_G\le2/3,\quad y_G>y_D.
\end{gathered}                                                    \tag{1}
\]

**Theorem.** All seven beta_P vanish, and

\[
 c_A=(-3/2,-1/16),\quad c_D=(3/2,-1/16),\quad
 c_E=(-1,15/16),\quad c_G=(1,15/16),
 \qquad x_B=-1/2,\ x_I=1/2,\ x_F=0.                 \tag{2}
\]

In the full original Cb882 caller, these equalities contradict its
retained actual BC link and strictly weak CD bit. This statement
includes closed Q; it uses no strict deficit from the containing disk.

## 2. Physical pair support retains absolute-tilt variation

Put a_0=497/500, kappa=50/997, c=11/25 and e=3/100.
Every frame in (1) satisfies

\[
 \alpha_P\ge a_0,\qquad
                 1-\alpha_P\le\kappa|\beta_P|.          \tag{3}
\]

Indeed 1-1/100-a_0^2=491/250000>0, and
beta_P^2/(1+alpha_P)<=abs(beta_P)/(10(1+a_0)).
For two original squares with signed tilts b,f in [-1/10,1/10],
the common support threshold on either original's side axes is

\[
 R(b,f)=\frac{1+\cos(\theta_b-\theta_f)
                   +|\sin(\theta_b-\theta_f)|}{2}.
\]

We claim the stronger estimate

\[
 R(b,f)\ge1+c|b-f|+e\bigl||b|-|f|\bigr|.                 \tag{4}
\]

Here is a direct continuous proof. Let p=max(abs(b),abs(f)),
q=min(abs(b),abs(f)), and a=sqrt(1-p^2). If p=0 the assertion
is immediate. For fixed p>0 and 0<=q<=p, the quantity R-1 is
one of the following concave functions of q:

\[
 F_\sigma(q)=\frac{(a+p)\sqrt{1-q^2}
                          +\sigma(a-p)q-1}{2},          \tag{5}
\]

where sigma=-1 for equal signs and sigma=1 for opposite signs.
Thus its graph lies above the chord from q=0 to q=p. At q=0,

\[
 F_\sigma(0)=\frac{p-(1-a)}2\ge(47/100)p,
\]

because

\[
 \frac{1-(1/10)/(1+a_0)}2-47/100=491/99700>0.
\]

For equal signs F_{-1}(p)=0; for opposite signs

\[
 F_1(p)=p(a-p)\ge(22/25)p,
 \qquad (a_0-1/10)/2-11/25=7/1000>0.
\]

The chord therefore gives (47/100)(p-q) in the equal-sign
case and (47/100)(p-q)+(22/25)q in the opposite-sign case.
These are exactly the right side of (4) minus one, since c+e=47/100.
No choice of a common physical separating owner was made here.

## 3. A strengthened horizontal path inequality

Put b=beta_B, i=beta_I, delta=-beta_D>=0 and

\[
\begin{aligned}
 T&=|b|+|i-b|+|i+\delta|,\\
 V&=|b|+\bigl||i|-|b|\bigr|+\bigl||i|-\delta\bigr|.
\end{aligned}
\]

Both are lengths of paths on the real line, from 0 to -delta
and from 0 to delta respectively. Hence T>=delta and V>=delta.
Also put P=max(b,i,0), N=max(-b,-i,0), and
Z=max(abs(i),delta). Visiting the highest and lowest points of
the signed path gives T>=delta+2P and T>=2N-delta. Thus

\[
 P\le(T-\delta)/2,\qquad
 N\le(T+\delta)/2,\qquad Z\le(T+\delta)/2.
\]

For the last inequality, abs(i)<=N or abs(i)<=P according to
its sign, and delta<=(T+delta)/2.

The incircles force both horizontal gaps BI,ID to be positive.
Actual AB gives x_B>=x_A+1>1-rho, where rho=91/60 is the
proved universal center bound. Since x_B<=x_I<=x_D<rho, both
horizontal gaps are smaller than 2rho-1=61/30. Therefore a
secondary normal has absolute projection at most
(1/10)(61/30)+3/4=143/150<1. A negative primary normal has
projection at most 3/40<1. The actual separator is therefore a
positive primary normal of one of the two physical owners. Its
inequality implies

\[
 \Delta x\ge R(b,f)-t_O\Delta y,
                    \qquad t_O=\beta_O/\alpha_O.        \tag{6}
\]

For BI the slope loss is at most
max((3/4)P,(1/16)N)/a_0. Each of these two quantities is at
most ((3/8)(T-delta)+delta/16)/a_0. For ID the loss is at
most Z/(10a_0)<=((T-delta)/20+delta/10)/a_0. Thus the
total loss is at most

\[
       \frac{17(T-\delta)}{40a_0}+\frac{13\delta}{80a_0}.
\]

Combine the two instances of (4), these losses, and actual AB.
The result is

\[
\begin{aligned}
 x_D-x_A\ge{}&2+(\alpha_A+\alpha_B)/2+\beta_A/2
                              +(1/2-c-e)|b|\\
 &+k_D\delta+k_T(T-\delta)+e(V-\delta),\\
 k_D={}&c+e-13/(80a_0),\qquad k_T=c-17/(40a_0).
\end{aligned}                                                    \tag{7}
\]

This includes every possible physical owner of the two separators.

## 4. Vertical links and the weighted corner sum

The vertical argument in Section 4 of the larger terminal also
uses only abs(beta)<=1/10 and alpha>=a_0; its sign assumptions
are exactly beta_A>=0 and beta_D<=0. A primary separator is
excluded by 2/3+(1/10)(91/30)=97/100<1, and the downward
secondary separator is excluded by (1/10)(2/3)<1. The remaining
upward physical separators, with either original owner, give

\[
\begin{aligned}
 y_E-y_A&\ge1+(13/40)\beta_A-(1/4)|\beta_E|,\\
 y_G-y_D&\ge1+(13/40)\delta-(1/4)|\beta_G|.              \tag{8}
\end{aligned}
\]

For completeness, normalization costs at most eta=1/200 per
absolute beta because eta-(2/3)(1/a_0-1)=97/99400>0.
The endpoint-gain and opposing-tilt comparisons have reserves
1/3-eta-13/40=1/300 and
1/4-(2/3-c+eta)=11/600. Thus enlarging A,D's allowed tilt
does not alter (8).

Use the same four original corners and positive weighted sum S
as Section 5 of the larger terminal. Its exact identity is

\[
\begin{aligned}
 S={}&23(x_D-x_A)+(27/4)(x_G-x_E)\\
 &+(207/32)((y_E-y_A)+(y_G-y_D))\\
 &+(943/64)(\alpha_A+\alpha_D)-(529/64)(\beta_A+\delta)\\
 &+(423/64)(\alpha_E+\alpha_G)+(9/64)(\beta_E-\beta_G)
 \le32Q.                                                       \tag{9}
\end{aligned}
\]

Substituting (3), (7), (8), and the actual EFG span gives

\[
\begin{aligned}
 S-32Q\ge{}&K_A\beta_A+K_B|b|+K_D\delta
        +K_E(|\beta_E|+|\beta_G|)+K_F|\beta_F|\\
 &+K_T(T-\delta)+K_V(V-\delta).                         \tag{10}
\end{aligned}
\]

Every coefficient is positive:

| Coefficient | Exact value |
|---|---:|
| K_A | 5131507/1276160 |
| K_B | 11293/99700 |
| K_D | 468467151/3171257600 |
| K_E | 142479/127616 |
| K_F | 25569/3988 |
| K_T | 7107/24850 |
| K_V | 69/100 |

These entries are obtained, respectively, from

\[
\begin{gathered}
 23/2+(13/40)(207/32)-529/64-\kappa(1679/64),\\
 23(1/2-c-e)-\kappa(23/2),\\
 23k_D+(13/40)(207/32)-529/64-\kappa(943/64),\\
 27/8-(1/4)(207/32)-9/64-\kappa(639/64),\\
 (27/4)(1-\kappa),\qquad23k_T,\qquad23e.
\end{gathered}
\]

The constant term is exactly 32Q. Inequality (10) forces all its
nonnegative terms to vanish. In particular beta_A,b,delta,beta_E,
beta_F,beta_G vanish and T=0, which also forces i=0.

## 5. Equality, the original weak bit, and certified guards

All four corner deficiencies in S have positive weights. Equality
in (9) forces each selected corner to equal its corresponding
Q-circle point. With aligned frames this gives the four anchors
in (2). The three horizontal gaps AB,BI,ID are each at least one
and sum to three, while the two EFG gaps are each at least one
and sum to two. Thus the remaining coordinates in (2) follow.

In the full Cb882 caller, actual BC now gives x_C>=h_C. The
retained CD cone and contained insets give x_C<=1-g_C.
Since h_C+g_C>=1, with equality only at h_C=g_C=1/2,
we obtain x_C=1/2. Then x_D-x_C=1=h_C+h_D, contradicting
the original strictly weak CD bit.

The ten center-difference targets and residual-certificate rule in
Section 7 of the larger terminal apply with two enlarged right sides:
the target y_B-y_I has upper bound 1/16, and y_I-y_B has
upper bound 3/4. The other eight right sides are unchanged. Together with
the seven uniform orientation bounds in (1), the original A,D
signs, actual AB/EF/FG, and the proved E/G upper inset orders,
they imply this entire guard. Any use of the enlarged terminal
must retain those hypotheses and print the exact weights for
targets not supplied by the proved box. This chapter alone makes
no claim about the guard's complement or the whole original.
