# The exceptional E-aligned positive-GA endpoint outside the critical strip

## 1. Statement and exact domain

Use the actual owners, signs, contact and variation hypotheses of
[the critical-strip theorem](HAND_G5_POSITIVE_GA_EXCEPTIONAL_E_ALIGNED_SHARP_CRITICAL_STRIP.md),
but replace its radius ceiling by
\[
 q\le Q_1=1957767069/500000000,\qquad R=\sqrt{Q_1},
 \qquad h=.7,
\tag{1}
\]
and assume
\[
                   t=x+e\in[0,.1]\ \cup\ [.16,h].
\tag{2}
\]
In particular E has signed tangent \(y_E\ge0\), DE3 has error
\(e\ge0\), EH0 is aligned with the exact actual contact
\(a_H+y_E=1\), HG2 and GA1 with \(x\ge0\) are retained,
and the remaining owners are either AB, BT2 and arbitrary TD0.
The H,A signs are positive, the B,D signs negative, and G,T may
have either sign. All squares are sorted and contained at q.
No radial-boundary assumption is required in this stress proof.

**Theorem.** No such system exists. This is a strict exclusion
at Q1, including x=0 and all weak ties, on the two closed
intervals (2). Together with the critical-strip theorem it
excludes every exceptional endpoint with x>0 at q<=q*.
The critical interval itself is handled sharply, retaining
its genuine hard-chain zero.

## 2. Three explicit weight families

On the two low intervals \([0,.1]\) and \([.16,.18]\), use
\[
\begin{aligned}
 k&=.86265+.67t+.27t^2,&l&=.50521+.84t+.5t^2,\\
 c&=.86265+.72t+.30t^2,&\eta&=.262+.19t+.08t^2.
\end{aligned}
\tag{3}
\]
For \(.18\le t\le.35\), use
\[
 k=1,\quad l=.551+.67t+.21t^2,\quad
 c=.891+.64t+.02t^2,\quad \eta=.305-.02t+.035t^2.
\tag{4}
\]
For \(.35\le t\le h\), use
\[
                  k=1,\qquad l=.70+.32t,\qquad
                  c=1.13,\qquad\eta=.27+.08t.
\tag{5}
\]
Each choice is fixed while splitting its given total t. Put
\[
 n(x)=k(\cos x+\eta\sin x),\qquad
 p(e)=\cos e+\eta\sin e,
\tag{6}
\]
and give the actual seven inequalities the weights
\[
                            (n,k,l,c,c,1,p).
\tag{7}
\]
The exact forces, zero-error pairs and actual negative indices
are those in Sections 3--4 of the critical-strip theorem.
G has circle support \(k\sigma_\eta\sin x\), T cancels, and
E has force \(\sin e(a_E+\eta y_E)\).

Throughout (3)--(5), \(.862<k\le1\),
\(.262\le\eta<.327\) and \(\sigma_\eta-.5<.935\).
The exact EH contact cancels the varying-p residual. Keeping
E's actual coordinates before the split gives second derivative
at most
\[
 k\{-.435\cos x+.957\sin x\}-.5\cos e+.915\sin e.
\tag{8}
\]
For x+e=t<=h the values at x=0 and x=t are less than -.16
and -.21, respectively. The same affine-in-tangent argument
as in the critical proof makes (8) negative on the entire
split. We therefore need only the E endpoint (0,t) and the
G endpoint (t,0).

## 3. The complete ordinary-angle envelopes

Use the functions U and \(V^\nu\) defined in (20) of the
critical-strip theorem. At an E endpoint the four pairs are
\[
                         (p(t),k),(k,l),(l,c),(1,c),
\tag{9}
\]
and at a G endpoint they are
\[
                         (1,kp(t)),(k,l),(l,c),(1,c).
\tag{10}
\]
The respective negative coefficients are \((k,l,c,c)\)
and \((kp(t),l,c,c)\). Only B can have both signs; H,A,D
each have one ordinary angle. All ratios are at least one
half, so the ordinary-angle concentration used in the
critical proof applies without any restriction on individual
ordinary error signs.

### 3.1 The low family

The following bounds hold on the larger interval [0,.18]:
\[
\begin{gathered}
 k<1,\quad c<1.002,\quad l<.673,\quad \eta<.299,\\
 c-l>.329,\quad l/k<.72,\quad l/c>.585+.35t,\\
 c-k=.05t+.03t^2\le.0555t,\quad
 1\le p(t)<1.05.
\end{gathered}
\tag{11}
\]
The last lower bound is strict for t>0. All larger pair
coefficients are below 1.05; the H/D rectangle paths from
(.86265,1) have ratios above .82.

Exactly as in Section 4 of the critical proof, the complete
envelope is at least \(V_B(t)=V_{l,c}^{c}(t)\). Here are explicit
reserves for the comparisons, so the use of the larger interval
in (11) is harmless.

First, the H,D pure charges exceed 1.17t, whereas the initial
B slope is below 1.15. For A, the integral derivative of its
norm gain is below .55t on ratios at most .72 and t<=.2.
Hence its difference from B is at least
\[
 \{.329(.5-.18^2/24)-.55(.0555)\}t^2>.133t^2.
\tag{12}
\]
At t=0 all pure charges agree. The same-block B inequality
follows from the positive function
\[
 (.585+.35t)\{\cos(h-t)+\sin(h-t)-1\}-\cos t+\cos h
\tag{13}
\]
on [0,.2]. It has value greater than .004 at 0, first
derivative greater than .07 and .06 at the two endpoints,
and third derivative below -1. Thus its first derivative is
concave and positive throughout.

At h, H,D exceed .79, B is below .72, and the A-minus-B
comparison has reserve
\(.329(1-\cos h)-.01>.067\).
Every positive charge satisfies
\[
                         U_i(P)\ge-.545(1.05)P.
\tag{14}
\]
For the B chord, monotonicity in its ratio and scale yields
\[
 V_B(h)-V_B(t)
 \ge .86265\{V_{.585,1}^{1}(h)-V_{.585,1}^{1}(t)\}
 >.86265(.7)(h-t).
\tag{15}
\]
To verify the last step, subtract .7(h-t) from the bracket.
The resulting function decreases on [0,.18] and its value
at .18 exceeds .005. Positive-side squaring proves both
claims. The fixed-ratio derivative is positive on [0,h],
which justifies its scale comparison in (15). Since
\[
                   .86265(.7)-.545(1.05)>.031,
\tag{16}
\]
every separated charge exceeds \(V_B(t)\). This covers all
three endpoint types of the ordinary-angle concentration.

### 3.2 The middle and high families

In (4)--(5), every pair ratio is at least 2/3 and every
coefficient is below 1.131. In particular
\[
 2/3<l<1,\quad l/c>2/3,\quad 1<c<1.131,
 \qquad .97<p(t)<1.053.
\tag{17}
\]
For a common bound at both primary endpoints, replace H's
negative coefficient by 1.06. This only decreases its V
charge, because \(\cos s-1\le0\), and still gives a concave
one-angle function. Keep the actual negative coefficients
l,c,c at A,B,D. Denote these four common charges by
\(\widehat V_H,V_A,V_B,V_D\).

The mixed B same-block term dominates its pure charge by the
standard ratio-2/3 comparison. For separated terms the exact
balanced derivative bound is
\[
                  (V_{a,b}^{\max(a,b)})'>.674\max(a,b)
\tag{18}
\]
for ratio at least 2/3 and angle in [0,h]. The increased H
coefficient subtracts at most .06 sin h from this bound.
A's actual coefficient is smaller than its larger pair
coefficient, so it improves the bound. All larger pair
coefficients are at least 1, and therefore
\[
 \min(\widehat V_H',V_A',V_B',V_D')
          >.674-.06(.6443)>.545(1.131)+.018.
\tag{19}
\]
This pays the uniform positive cost
\(U_i(P)\ge-.545(1.131)P\). The complete ordinary-angle
envelope is consequently at least
\[
                     \min(\widehat V_H(t),V_A(t),V_B(t),V_D(t)).
\tag{20}
\]

## 4. Endpoint scalars and the exact G/E comparison

Set
\[
 C_\eta(t)=1+2\cos t+
                \{1+2\eta-R\sqrt{1+\eta^2}\}\sin t.
\tag{21}
\]
The E and G baselines are respectively
\[
\begin{aligned}
 B_E={}&3k+2l+3c+C_\eta(t)\\
 &-R\{\sqrt{p(t)^2+k^2}+\sqrt{k^2+l^2}
                   +\sqrt{l^2+c^2}+\sqrt{1+c^2}\},\\
 B_G={}&3+2l+3c+kC_\eta(t)\\
 &-R\{\sqrt{1+k^2p(t)^2}+\sqrt{k^2+l^2}
                   +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{aligned}
\tag{22}
\]
Their exact difference is
\[
 B_G-B_E=(1-k)(3-C_\eta(t))
       +R\{\sqrt{p(t)^2+k^2}-\sqrt{1+k^2p(t)^2}\}.
\tag{23}
\]
On the low family, k<1, p(t)>=1 and C_eta(t)<=3, so this
difference is nonnegative, strictly positive for t>0.
On the other two families k=1 and the baselines are identical.
The common charge in (20) was chosen to cover both H indices.
Thus the only scalar assertions needed are
\[
 B_E+V_B>0\quad\text{on }[0,.1]\text{ and }[.16,.18],
\tag{24}
\]
and
\[
 B_E+\widehat V_H>0,\quad B_E+V_A>0,\quad
 B_E+V_B>0,\quad B_E+V_D>0
             \quad\text{on }[.18,.35]\text{ and }[.35,h].
\tag{25}
\]
These ten full-interval assertions are certified next. They
complete the strict contradiction via Sections 2--3.

## 5. Explicit rational polynomial certificate

Use the same Taylor polynomials, positive-mass radical
inequality and coefficient-norm operator as Section 6 of
[the sole-EH theorem](HAND_G5_POSITIVE_GA1_POSITIVE_EH1_WITH_TD0_EXCLUSION.md):
\[
 S=\sum_{j=0}^7\frac{(-1)^jt^{2j+1}}{(2j+1)!},\quad
 C=\sum_{j=0}^8\frac{(-1)^jt^{2j}}{(2j)!},\quad
 R_+=1.978770866>R.
\tag{26}
\]
Use a local variable z=t-a, with the four full domains
\[
                (a,D)=(0,.1),(.16,.02),(.18,.17),(.35,.35).
\tag{27}
\]
Substitute (3), (4) or (5), set p=C+eta S, and start with
\[
\begin{gathered}
 A=3k+2l+3c+1+2C+(1+2\eta)S,\\
 (v_H,v_A,v_B,v_D)=(p^2+k^2,k^2+l^2,l^2+c^2,1+c^2).
\end{gathered}
\tag{28}
\]
For the selected negative index i, add \(\nu_i(C-1)\) to A
and subtract \(2b_iS\) from its squared norm, where
\[
                 (\nu_H,\nu_A,\nu_B,\nu_D)=(1.06,l,c,c),
 \qquad(b_H,b_A,b_B,b_D)=(pk,kl,lc,c).
\tag{29}
\]
Only index B is used on the low intervals. All four norms
have weight 1; append the fifth weighted norm
\((1+\eta^2,S)\).

For each squared norm v, define its mass by three rational
Newton steps at z=0 and a cubic truncation:
\[
\begin{gathered}
 \rho_0=1,\quad\rho_{j+1}=(\rho_j+v(0)/\rho_j)/2
                    \quad(j=0,1,2),\\
 w=([v]_{\le3}-v(0))/v(0),\qquad
 m_v=[\rho_3(1+w/2-w^2/8+w^3/16)]_{\le3}.
\end{gathered}
\tag{30}
\]
For the five resulting weighted norms \((v_j,w_j)\), put
\[
 P=2A\prod_jm_{v_j}
       -R_+\sum_jw_j(v_j+m_{v_j}^2)\prod_{r\ne j}m_{v_r}.
\tag{31}
\]
The identity
\((v+m^2)/(2m)-\sqrt v=(\sqrt v-m)^2/(2m)\ge0\)
shows that \(P/(2\prod m)\) bounds the scalar below. All
masses are above .81 and below 3 on their complete intervals.
The maximum degree of P is 46.

Let L and U be the whole-interval coefficient-norm operators
(37) of the critical-strip note, with the appropriate D in
(27). The following compact bounds certify (24)--(25):

- On [0,.1], \(U(P_B')<-.05\) and \(P_B(.1)>.00061\).
  Thus this complete numerator is decreasing and positive.
- On [.16,.18], \(L(P_B)>.00155\).
- On [.18,.35], the H,A,D numerators have respectively
  \(L(P_H)>.334\), \(L(P_A)>.0312\), \(L(P_D)>.317\).
  The B numerator satisfies
  \(P_B(0)>.0043\) and
  \(L((P_B-P_B(0))/z)>.203\).
- On [.35,.7], the H,A,B,D numerators have respectively
  coefficient-norm lower bounds .126, .0574, .0625 and .451.

Here a zero argument in a numerator means the local z=0.
Each statement is one rational coefficient-norm calculation
on its whole interval; no angle subdivision or sampled value
is used. Keeping the positive masses fixed, the same input
partial bounds as in the sole-EH theorem make the total Taylor
substitution error less than \(10^{-8}\), below every displayed
reserve.

The coefficient and angular inequalities (11)--(19) have equally
short positive-side checks. For example, (12) uses
\[
 Q_1(.72)^6<(.55)^2\{1+.72^2-2(.72)(.2)\}^3.
\tag{32}
\]
The chord in (15) uses r=.585 and a=.18. Its endpoint is
\[
 \sqrt{q_L}\{\sqrt{1+r^2-2r\sin a}
                  -\sqrt{1+r^2-2r\sin h}\}
                 +\cos h-\cos a-.7(h-a)>.005.
\tag{33}
\]
Its derivative sign follows by positive squaring from
\[
 q_Lr^2\cos^2a>(.7+\sin a)^2(1+r^2).
\tag{34}
\]
For (18), put r=2/3 and v=sin s. The cubic
\[
 Q_1r^2(1-v^2)-(v+.674)^2(1+r^2-2rv)
\tag{35}
\]
decreases on \([0,.6443]\) and its value at .6443 exceeds
.00048. The remaining fixed trigonometric and radical bounds
use alternating Taylor polynomials and positive squaring.
This supplies a finite exact certificate for every continuous
inequality used in the proof.
