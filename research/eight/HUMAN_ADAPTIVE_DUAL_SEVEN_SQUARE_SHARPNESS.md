# Orientation-robust sharp SEVEN-square conditional radius bound: adaptive support dual

**2026-10-13. Complete nonlinear LOCAL-TILT, arbitrary-CENTER
hand theorem, with independently rotated square frames.**
This substantially improves the end-frame assumption in
[HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md](HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md)
near the exact attaining tilt. It implements the
**independent-angle support penalty and angle-only
comparison** from Queuingtheorydotcom/11SquaresOptimal,
but with a crucial improvement: **the positive dual weights
adapt to the common tilt parameter**.

**IMPORTANT:** The theorem STILL REQUIRES the exact seven
directed true-square support separators, a small interval of
the free global oblique separator angle, and a small orientation
box around the two frame clusters. It makes NO assumption
about the locations of the seven square centers. It is NOT
the unrestricted eight-square sharp theorem and does not
supply the missing global separator/capture implication.

## 1. Main theorem

Write \(q_*=\widehat R^2\) and let
\((q_*,y_*,t_*)\) be the exact unique stationary
five-corner solution from
[FIVE_CORNER_REDUCTION.md](FIVE_CORNER_REDUCTION.md),
where \(0<t_*<\pi/4\).
Take fixed orthonormal coordinates \(a=(1,0),b=(0,1)\).
Let \(e_t=\cos t\,a+\sin t\,b\) and
\(f_t=-\sin t\,a+\cos t\,b\).

**Theorem.** There exists \(\delta>0\) such that
any SEVEN genuine unit squares
\[
A,B,T,D,E,H,G\subseteq D_R
\]
with **independent, arbitrary actual frames**
and the following properties satisfy
\[
\boxed{R^2\ge q_*=\widehat R^2.}                 \tag{1}
\]

* There is \(t\) with \(|t-t_*|<\delta\);
* their seven **actual directed center support inequalities**
  all hold (not necessarily as contacts):
  \[
  \begin{split}
  b\cdot(p_B-p_A)&\ge h_B(b)+h_A(b),\\
  a\cdot(p_B-p_T)&\ge h_B(a)+h_T(a),\\
  a\cdot(p_T-p_D)&\ge h_T(a)+h_D(a),\\
  b\cdot(p_D-p_E)&\ge h_D(b)+h_E(b),\\
  e_t\cdot(p_A-p_G)&\ge h_A(e_t)+h_G(e_t),\\
  e_t\cdot(p_G-p_H)&\ge h_G(e_t)+h_H(e_t),\\
  f_t\cdot(p_E-p_H)&\ge h_E(f_t)+h_H(f_t).
  \end{split}                                   \tag{2}
  \]
* Using continuous angle representatives modulo quarter
  turns, all five frames A,B,T,D,E have
  \(|\theta_i|\le1/100\) radians and both H,G have
  \(|\theta_i-t|\le1/100\) radians.

There is **no requirement A and E have the same frame**,
and no center proximity/contact graph or extra eighth
square requirement.

In fact there is a positive continuous algebraic
weight \(m_H(t)>0\), and a real analytic position
choice \(y(t)\), such that the **quantitative bound**
\[
\boxed{
R^2\ge q_*+m_H(t)F(q_*,y(t),t)
+\frac1{200}\left(
\sum_{i=A,B,T,D,E}|\sin\theta_i|
 +|\sin(\theta_H-t)|+|\sin(\theta_G-t)|
\right),}                                       \tag{3}
\]
holds throughout this neighborhood.
The previously proved full-domain conditional
family theorem gives \(F(q_*,y(t),t)\ge0\).
Its unique equality position forces \(t=t_*\)
if \(R^2=q_*\). Thus equality also forces
the seven actual frame orientations into the
two exact candidate orientation clusters.

This is a **finite-neighborhood sharp theorem**,
not merely a nonnegative first variation.
All seven center positions are unrestricted.

## 2. Fix the exact q* pseudo-chain at a nearby free tilt

For a sufficiently small tilt interval about \(t_*\),
the strict nondegenerate stationary minimum in
[HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md)
and the implicit-function theorem give a real
analytic function \(y(t)\) with
\[
y(t_*)=y_*,\qquad F_y(q_*,y(t),t)=0.
\]
All four nested square roots below remain
strictly positive in that neighborhood.
Put
\[
\begin{aligned}
x_1&=\sqrt{q_*-y^2},&
x_2&=\sqrt{q_*-(y+2)^2},&
x_3&=x_2-3,\\
y_3&=\sqrt{q_*-x_3^2},&
y_4&=y_3-2,&
x_4&=-\sqrt{q_*-y_4^2},\\
h_1&=c x_1+s y-2-c,&
h_2&=-s x_4+c y_4-1-s,
\end{aligned}
\]
where \(c=\cos t,s=\sin t,y=y(t)\).
The five *algebraic reference points* are
\[
P_1=(x_1,y),\quad
P_2=(x_2,y+2),\quad
P_3=(x_3,y_3),\quad
P_4=(x_4,y_4),\quad
P_5=h_1e_t+h_2f_t .
\]
By construction,
\(|P_j|^2=q_*\) for \(j=1,\ldots,4\), while
\[
|P_5|^2=q_*+F(q_*,y(t),t).                       \tag{4}
\]

These are **algebraic pseudo-points**:
for \(t\ne t_*\), P5 may lie OUTSIDE the sharp
disk. We use them to construct a *dual inequality*,
not to assert that the pseudo-points form a feasible packing.

The pseudo-centers are
\(p_A^0=P_1-(a-b)/2\),
\(p_B^0=P_2-(a+b)/2\),
\(p_D^0=P_3-(-a+b)/2\),
\(p_E^0=P_4+(a+b)/2\),
\(p_H^0=P_5+(e_t+f_t)/2\).
Choose \(p_T^0\) anywhere with x-coordinate
midway between B,D, and \(p_G^0=p_H^0+e_t\).
Every one of the seven *directed support
projections (2)* is exactly tight
on this pseudo-chain with standard
A,B,T,D,E frames and e_t,f_t frames for H,G.

## 3. A positive adaptive algebraic contact/circle dual

Introduce unnormalized oblique edge multiplier \(W=1\).
The following formulae define the other seven
positive edge multipliers and five circle weights:
\[
\begin{array}{lll}
\mu_A^0=\dfrac{c}{2x_1},&
\lambda_{AB}^0=s-\dfrac{cy}{x_1},&
\mu_B^0=\dfrac{\lambda_{AB}^0}{2(y+2)},\\[5pt]
\lambda_{TB}^0=\lambda_{DT}^0
=\dfrac{\lambda_{AB}^0x_2}{y+2},&
\mu_D^0=-\dfrac{\lambda_{TB}^0}{2x_3},&
\lambda_{ED}^0=2\mu_D^0 y_3,\\[5pt]
\mu_H^0=-\dfrac1{2h_1},&
\lambda_{HE}^0=\dfrac{h_2}{h_1},&
\mu_E^0=-\dfrac{s\lambda_{HE}^0}{2x_4},\\[5pt]
\lambda_{GA}^0=\lambda_{HG}^0=1.&&
\end{array}                                                 \tag{5}
\]
Divide ALL weights by
\(M=\mu_A^0+\mu_B^0+\mu_D^0+\mu_E^0+\mu_H^0>0\).
Denote the normalized values by \(\mu_i,\lambda_{ij}\),
and set \(W=\lambda_{GA}=\lambda_{HG}=1/M\).
In particular \(\sum_{i=A,B,D,E,H}\mu_i=1\).

All these weights are **strictly positive** near
the sharp candidate: \(x_1,x_2,y_3,c,s>0\),
\(x_3,x_4,h_1,h_2<0\), \(y+2>0\), and
\(s-cy/x_1>0\).

Their true center force-balance equations are
\[
\begin{aligned}
2\mu_A P_1+\lambda_{AB}b-We_t&=0,\\
2\mu_B P_2-\lambda_{AB}b-\lambda_{TB}a&=0,\\
2\mu_D P_3+\lambda_{DT}a-\lambda_{ED}b&=0,\\
2\mu_E P_4+\lambda_{ED}b-\lambda_{HE}f_t&=0,\\
2\mu_H P_5+We_t+\lambda_{HE}f_t&=0.
\end{aligned}                                             \tag{6}
\]
At T,G the two opposing directed normal weights
cancel identically.

All but E's vertical equation follow directly
from (5). For E, differentiating the reference
radical chain gives
\[
y_4'=\frac{x_3(y+2)}{y_3x_2},\quad
h_{1,y}=s-\frac{cy}{x_1},\quad
h_{2,y}=(c+s\,y_4/x_4)y_4'.
\]
Its residual is exactly
\[
2\mu_Ey_4+\lambda_{ED}-c\lambda_{HE}
=-\frac{W}{2h_1y_4'}F_y(q_*,y,t)=0,             \tag{7}
\]
not an approximate numerical stationarity claim.

## 4. The global-in-centers dual lower bound

Let \(v_A,v_B,v_D,v_E,v_H\) be the five
selected TRUE vertices of the arbitrary
actual squares in (1): the actual-frame
corners corresponding respectively to the
pseudo reference offsets
\[
o_A=(a-b)/2,\quad o_B=(a+b)/2,\quad
o_D=(-a+b)/2,\quad o_E=-(a+b)/2,\quad
o_H=-(e_t+f_t)/2.
\]
Each offset rotates with its own actual square frame.

Let \(g_{AB},g_{TB},g_{DT},g_{ED},
g_{GA},g_{HG},g_{HE}\ge0\) be the seven
TRUE directed support gaps (2).
Disk containment yields \(R^2\ge|v_i|^2\).
Because the circle weights sum to one and
all \(\lambda_{ij}>0\),
\[
R^2\ge
\sum_i\mu_i|v_i|^2-\sum_{ij}\lambda_{ij}g_{ij}
=:\mathcal D_t(p,\boldsymbol\theta).            \tag{8}
\]

Write \(c_i(t)\) for the actual weighted
outgoing-minus-incoming separator normal
sum at label i, using the seven directed
directions from (2). The two unanchored
labels T,G have \(c_T=c_G=0\).
For each circle-anchored label
\(i=A,B,D,E,H\),
complete the square:
\[
\mu_i|p_i+o_i(\theta_i)|^2+c_i(t)\cdot p_i
=\mu_i\left|p_i+o_i+\frac{c_i}{2\mu_i}\right|^2
-\frac{|c_i|^2}{4\mu_i}
-c_i\cdot o_i.
\]
Hence **for EVERY actual center vector p**,
\[
\boxed{R^2\ge
\Phi_t(\boldsymbol\theta):=
\sum_{\rm seven\ labels} S_i(\theta_i,t)
-\sum_{i=A,B,D,E,H}
\left(\frac{|c_i(t)|^2}{4\mu_i}
+c_i(t)\cdot o_i(\theta_i)\right),}             \tag{9}
\]
where \(S_i\) is the sum of the positive
weighted true square support half-widths
of all incident separators.

The algebraic reference centers satisfy
\(c_i(t)=-2\mu_iP_i\) by (6). Their seven
separator residuals vanish, and the five
reference squared vertex norms are
\(q_*,q_*,q_*,q_*,q_*+F\).
Thus the completed-square bound is
**exactly sharp at the reference angles**:
\[
\boxed{\Phi_t(0,0,0,0,0,t,t)
=q_*+\mu_H(t)F(q_*,y(t),t).}                    \tag{10}
\]
There is **no center-neighborhood hypothesis**
in (8)--(10). The center-square completion
is the decisive improvement over a mere
candidate linearization.

## 5. Strict finite angular inequality for seven freely rotated frames

For the five standard-frame labels put
\(\delta_i=\theta_i\). For H,G put
\(\delta_i=\theta_i-t\).
Within \(|\delta_i|\le1/100\) and t
sufficiently near \(t_*\), the absolute
support functions have a fixed sign pattern
apart from their true frame alignment cusps.

For each of the **seven independent** angle
variables, direct expansion of the exact
square support half-widths in (9) yields
\[
\Phi_{t,i}(\delta_i)-\Phi_{t,i}(0)
=A_i(t)(\cos\delta_i-1)
+B_i(t)\sin\delta_i+
\Gamma_i(t)|\sin\delta_i|.                       \tag{11}
\]

The coefficients are explicit. Write
\((\lambda_{AB},\lambda_{TB},\lambda_{DT},
\lambda_{ED},W,W,\lambda_{HE})\) for the
seven positive directed weights, and use
\(\lambda_{TB}=\lambda_{DT}\).
In label order A,B,T,D,E,H,G:
\[
\begin{array}{c|c|c|l}
i&\Gamma_i&B_i&A_i\\\hline
A&\lambda_{AB}/2&
 \mu_A(x_1+y)-W(c-s)/2&
 \Gamma_A+\mu_A(x_1-y)+W(c+s)/2\\
B&(\lambda_{AB}+\lambda_{TB})/2&
 \mu_B(y+2-x_2)&
 \Gamma_B+\mu_B(x_2+y+2)\\
T&\lambda_{TB}&0&\Gamma_T\\
D&(\lambda_{DT}+\lambda_{ED})/2&
 -\mu_D(x_3+y_3)&
 \Gamma_D+\mu_D(-x_3+y_3)\\
E&\lambda_{ED}/2&
 \mu_E(x_4-y_4)-\lambda_{HE}(c-s)/2&
 \Gamma_E+\mu_E(-x_4-y_4)+\lambda_{HE}(c+s)/2\\
H&(W+\lambda_{HE})/2&
 \mu_H(h_1-h_2)&
 \Gamma_H-\mu_H(h_1+h_2)\\
G&W&0&\Gamma_G
\end{array}                                                 \tag{12}
\]

At the EXACT isolated sharp stationary root,
an independent rational interval audit
[verify_adaptive_seven_square_dual.py](verify_adaptive_seven_square_dual.py)
establishes
\[
\boxed{\Gamma_i-|B_i|>\frac1{40}
\quad\text{and}\quad |A_i|<2
\quad\text{for every one of the seven labels}.}   \tag{13}
\]
The limiting margin occurs at label E:
\(\Gamma_E-|B_E|\approx0.0273680292>0.025\).
The audit works over the **entire exact rational
candidate root box** already certified in
FIVE_CORNER_REDUCTION.md; it does not
substitute a rounded stationary root.

Because the \(\mu,\lambda,y(t)\)
depend continuously on t and the
margins in (13) are strict,
there exists a smaller \(\delta>0\)
for which (13) remains true
for all \(|t-t_*|<\delta\).

For any \(|\delta_i|\le1/100\),
the elementary inequality
\[
\frac{1-\cos\delta_i}{|\sin\delta_i|}
=\tan(|\delta_i|/2)\le1/100
\]
holds when \(\delta_i\ne0\).
Applying (13) to (11),
\[
\begin{aligned}
\Phi_{t,i}(\delta_i)-\Phi_{t,i}(0)
&\ge(\Gamma_i-|B_i|)|\sin\delta_i|
  -|A_i|(1-\cos\delta_i)\\
&\ge\left(\frac1{40}-\frac2{100}\right)
  |\sin\delta_i|
=\boxed{\frac1{200}|\sin\delta_i|}.            \tag{14}
\end{aligned}
\]
The same inequality holds trivially at \(\delta_i=0\).
Summing (14), then using (9)--(10), proves
the quantitative inequality (3).
Finally \(F(q_*,y(t),t)\ge0\) near the
sharp stationary solution by the existing
global conditional family theorem,
so \(R^2\ge q_*\), with equality rigidity
in the seven actual frame angles and the
common tilt. QED.

## 6. A precise warning: the FROZEN dual is not enough

If one instead fixes all \(\mu_i,\lambda_{ij}\)
at their t=t* values, and completes the
centers' squares as in (9), the aligned-frame
dual function at a VARIABLE tilt t is
\[
\Phi_{\rm frozen}(t)=C_0+
K_c\cos t+K_s\sin t,
\]
where
\[
\begin{aligned}
K_c&=W+\frac{\lambda_{ED}\lambda_{HE}}{2\mu_E}>0,\\
K_s&=\lambda_{HE}
  +\frac{\lambda_{AB}W}{2\mu_A}>0.
\end{aligned}
\]
The exact five-corner t-stationarity identity
\(F_t(q_*,y_*,t_*)=0\) is equivalent to
\(K_s/K_c=\tan t_*\).
Thus at the sharp t* the FROZEN dual
has a **strict local MAXIMUM**:
\[
\boxed{\Phi_{\rm frozen}(t)
=q_*+K(\cos(t-t_*)-1)<q_*
\quad(t\ne t_*),}
\]
where
\(K=K_c\cos t_*+K_s\sin t_*>0\)
(numerically \(K\approx13.1090\)).
Therefore fixed candidate multipliers alone
**CANNOT** prove finite-neighborhood sharpness
by this center-completion bound. This is a
precise mathematical obstruction to the naive
linearized dual approach.

The t-DEPENDENT weights in (5), together
with the *true five-corner positive defect*
\(F(q_*,y(t),t)\ge0\), fix that
curvature problem and make the fully
nonlinear bound (3) valid.

## 7. Exactly what remains to finish unrestricted n=8

This hand theorem achieves an important conditional goal:
**near the attaining common tilt, equal A/E end frames
are no longer required, and the five standard plus two
tilted square frames may all rotate independently**.

But this alone cannot force *arbitrary* competitive
eight-square packings into the small orientation box,
or force the seven directed separator projections (2).
Those are the only major still-missing hypotheses for
the global bridge. They must follow from a true global
capture/separator theorem or be bypassed by
another sharp orientation-independent inequality.
The known equality-bearing seven-outer contact ring
is included in this local theorem.

No global \(R_8\ge\widehat R\), no all-equality
classification, and no Lean 4 formalization
is claimed here. The result is an analytic
finite-neighborhood sharp **seven-square** theorem
conditional on (2) and the two small frame clusters.
