# One analytic stress excludes positive G1/E1

**Status: proved on paper on the whole forced positive arc.** Assume the hypotheses of `HAND_MIXED_OWNER_CHAIN_BOUNDS.md`, including S<=1/1000. Suppose that original G axis 1 and E axis 1 are both feasible and s=sin(t)>=0. We prove a contradiction without an angular cover or a list of owner certificates.

This is the difficult positive mixed-owner alternative. The preceding contraction to S<1/1000 remains an input, not a result of this note.

## 1. Geometric inputs and a single variable stress

Write c=cos(t), k=1001/1000 and W=(1+c+s)/2. The chain note proves

\[
 0\le s\le13/50,\qquad c^2+s^2=1,\qquad c\ge24/25,
 \qquad1-c\le(25/49)s^2.
\tag{1}
\]

It also proves the oblique corner support a_E+b_E/4<=283/200 and the lower bound a_G>=7/12.

Define the following explicit functions, without choosing any numerical subinterval:

\[
\begin{aligned}
 p&=24/41-s/4,& b&=1-3s/4,\\
 e&=36/31-3s/2,& d&=e(c+s/4),\qquad h=c.
\end{aligned}
\tag{2}
\]

Give H,G,A,B,T,D,E the weights (h,1,p,b,b,d,e). All are nonnegative on (1). The equal B/T weights cancel the T transverse coordinate. The H coefficient c cancels the G transverse coordinate. The D choice in (2) leaves exactly e s(a_E+b_E/4), which is bounded by (283/200)e s. Thus the oblique support, rather than an independent upper bound on a_E, is essential here.

The weighted demand is

\[
 D=c+p+2b+d+(1+e)W.
\tag{3}
\]

The four remaining corner forces on A,B,D,H are respectively

\[
 (1,p),\qquad(b,p),\qquad(d,b),\qquad(e,c).
\tag{4}
\]

The only other terms are at most (283/200)e s-(7/12)s. This follows directly from the original G1 and E1 projections in (2) of the chain note.

Use the four positive circle masses

\[
 \mu_A=12/41-s/32,\quad
 \mu_B=12/41-3s/16,\quad
 \mu_D=12/31-s/3,\quad
 \mu_H=12/31-s/4.
\tag{5}
\]

Each is positive for s<=13/50. The constants at zero are the exact four-circle stress of the aligned configuration; their variations and (2) are fixed rational formulas on the complete arc.

For any force (x,y) and mass mu, use only the square-completion bound

\[
 T_q(x,y;\mu)=\mu q+\frac{x^2+y^2}{4\mu}-\frac{x+y}{2}
 \ge xa_i+yb_i.
\tag{6}
\]

Because all masses are positive, q<=Q0 allows replacing q by Q0 in the upper bound. Define

\[
 \Psi(c,s)=D-
 T_{Q_0}(1,p;\mu_A)-T_{Q_0}(b,p;\mu_B)
 -T_{Q_0}(d,b;\mu_D)-T_{Q_0}(e,c;\mu_H)
 -(283/200)e s+(7/12)s.
\tag{7}
\]

At zero sine this is

\[
 \Psi_0=\frac{1728}{1271}\left(\frac{2257}{576}-Q_0\right)
       =\frac{3027}{794375}.
\tag{8}
\]

We next prove Psi>=Psi0 everywhere on (1), not merely near zero.

## 2. Removing the cosine by one circle chord

After substituting c^2=1-s^2 into (7), the resulting expression is affine in c. Its coefficient simplifies to

\[
 C(s)=\frac{25947s^3-132432s^2+255616s-154368}
            {992(31s-36)}.
\tag{9}
\]

This coefficient is positive. Indeed 31s-36<0. Since s<=13/50<1/3, the numerator is bounded above by

\[
 25947/27+255616/3-154368
 =961+255616/3-154368<0.
\]

Discarding the negative quadratic term made this a weaker upper bound. We may therefore replace c by 1-25s^2/49 in the **affine expression obtained after c^2=1-s^2**, obtaining a lower bound Psi_low(s). This order matters: it is not a substitution into unreduced squared cosine terms.

Put

\[
 \mathcal D(s)=24403200(31s-48)(31s-36)(41s-384)(41s-64).
\tag{10}
\]

All four linear factors are negative on (1), so Dcal(s)>0. Direct expansion of the four squares in (7), followed by the chord substitution just described, gives the single identity

\[
 \mathcal D(s)\bigl(\Psi_{\rm low}(s)-\Psi_0\bigr)
        =\frac{41s}{1225}P(s),
\tag{11}
\]

where the degree-seven polynomial is

\[
\begin{aligned}
P(s)={}&572973160660992
 -2792011665242112s
 +7763147347411264s^2\\
&-23886014191560008s^3
 +36828016239390074s^4
 -25192477325149800s^5\\
&+7050055775259375s^6
 -507046543875000s^7.
\end{aligned}
\tag{12}
\]

Equations (9)–(12) are one algebraic identity derived from the displayed stress. They are not imported polynomial data or an interval certificate. They can be checked by clearing the four positive masses in (5) and multiplying out four quadratic norms. No root isolation is needed.

## 3. A short whole-interval positivity proof

Let A0=572973160660992. Comparing the seven nonconstant integer coefficients in (12) gives the coefficientwise lower bound, for s>=0,

\[
 \frac{P(s)}{A0}\ge
 1-5s+13s^2-42s^3+64s^4-44s^5+12s^6-s^7.
\tag{13}
\]

For completeness, the positive differences establishing these comparisons in increasing degree are

\[
\begin{aligned}
&72854138062848,\quad314496258818368,\quad178858556201656,\\
&157733957086586,\quad18341743933848,\quad174377847327471,\quad65926616785992.
\end{aligned}
\]

These are simply the coefficient differences between P and A0 times the displayed small-integer polynomial, not a table of domain tests.

Group the right side of (13) as

\[
 1-5s+s^2\{13-42s+s^2(64-44s)\}+s^6(12-s).
\]

On [0,13/50], 64-44s>=52. The quadratic 13-42s+52s^2 is decreasing there and its right-end value is 3497/625>11/2. Also 12-s>0. Therefore

\[
 P(s)/A0\ge1-5s+(11/2)s^2\ge359/5000>0.
\tag{14}
\]

The last quadratic is also decreasing on this interval, and 359/5000 is its exact value at 13/50. This proves positivity on the complete continuous interval with no subdivision. By (10)–(11), Psi_low>=Psi0, and by (9) so does Psi(c,s).

## 4. The common error budget is smaller than the gap

All aligned weights are at most e0=36/31. In particular

\[
 d=e(c+s/4)\le(e0-3s/2)(1+s/4)\le e0,
\]

because e0/4<3/2. The E weight e is also at most e0. Thus the shared nominal loss is at most

\[
 (k+2)e0 S\le\frac{3001}{1000000}\frac{36}{31}
             =\frac{27009}{7750000}.
\]

But (8), (11) and (14) give the strictly positive reserve

\[
 \Psi-(k+2)e0S\ge
 \frac{3027}{794375}-\frac{27009}{7750000}
 =\boxed{\frac{103431}{317750000}}>0.
\]

This contradicts the weighted sum of the original feasible inequalities. Hence positive G1/E1 is impossible, including s=0 and every simultaneous feasible-axis tie.

## Verification boundary

This proof uses one tilt-dependent circle stress, one degree-seven algebraic remainder, and a short monotonicity argument on the entire forced arc. The larger coefficients in (12) arise only from clearing the four simple denominators in (5); no mesh, list of fitted interval multipliers, generated quartic row, or external numerical acceptance statement is used. Exploratory numerical work suggested the formulas; the explicit identities and inequalities above are independently sufficient for the proof. No Lean source was changed or compiled and no CI was run.
