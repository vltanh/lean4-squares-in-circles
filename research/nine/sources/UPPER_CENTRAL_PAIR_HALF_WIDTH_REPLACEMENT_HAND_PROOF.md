# Two upper central outsiders within half a unit supply a replacement floor

Complete hand proof, freshly and independently reviewed on 5 November
2026. No mathematical script, coefficient certificate, Lean, Lake, or CI
is a proof input.

Retain an actual horizontal four-chain of physical unit squares in
the closed disk of squared radius Q=1105/256, and assume each
consecutive main-center comparison is also an x-cone comparison.
All physical nonoverlap predicates are retained. Put rho=91/60
and l=29/60.

An **upper central outsider** here means a physical outsider A with
\[
 |x_A|<l,\qquad y_A>\max(y_{M_1},y_{M_2}).
\]

**Theorem.** If two upper central outsiders have horizontal center
gap at most 1/2, the one with higher center lies wholly above
\[
                \frac{2807}{24000}>\frac7{60}.       \tag{1}
\]

Consequently, three upper central outsiders cannot all have whole
floors at most 7/60: otherwise their pairwise horizontal center
gaps would exceed 1/2 inside a strip of width 29/30<1.

The theorem is independent of any designated short-chain link or side
occupancy. No separator owner is assumed in the theorem below. The basic
actual-four endpoint bands and transverse budget are the hand results in
[UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md](UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md);
the sharper endpoint resource needed here is proved in Section 1.

## 1. A sharper diagonal resource for each actual-four endpoint

For either outer endpoint E put
\[
 X=|x_E|,\quad Y=|y_E|,\quad h=h_E,\quad
 k=\sqrt{1/2-h^2},\quad a=h+k,\quad e=h-1/2.
\]
The actual chain and the opposite endpoint's center bound give
\[
 X>89/60+e,\qquad 1/2\le h<8/15.
\]
We claim
\[
 \boxed{X+Y-a<49/80,\qquad X+Y<129/80.}              \tag{2}
\]

An actual outward-quadrant corner has offsets (h,k) or (k,h).
Call its positive coordinate magnitudes X',Y'. Then
\[
 X'>a+59/60,\qquad X'+Y'=X+Y+a,
 \qquad (X')^2+(Y')^2\le Q.
\]
The first inequality uses X'>=X+k. Also a>399/400. Indeed a(h)
decreases on the endpoint orientation interval, and at its upper
endpoint a=(16+sqrt(194))/30; the required comparison follows from
194*1600-557^2=151>0.

On the relevant circular arc, u+sqrt(Q-u^2) decreases with u,
because u>=a+59/60>sqrt(Q/2). Thus
\[
 X+Y-a<59/60-a+\sqrt{Q-(a+59/60)^2}.
\]
The last expression is less than 49/80. To check this without
approximation, both candidate square-root bounds are positive and
\[
 (a+59/60)^2+(a-89/240)^2>Q.
\]
Both squared quantities increase with a; at a=399/400 the exact
positive numerator is
\[
 2377^2+752^2-1105\cdot5625=8
\]
over denominator 1440000. This proves the first part of (2).
The second follows from a<=1.

## 2. A uniform center-height bound for every upper central outsider

For a physical unit A write its larger and smaller absolute side
components as alpha>=beta>=0, with alpha^2+beta^2=1, and put
\[
 h=(\alpha+\beta)/2,\quad k=(\alpha-\beta)/2,
 \quad v=\beta/\alpha,\quad g=1/(4h).
\]
We prove
\[
 \boxed{y_A>\frac1{2\alpha}-\frac{151}{240}.}         \tag{3}
\]

Recall the physical proxy-clearance formula. If a unit lies above
an aligned inset of halfwidth g_i, with horizontal center gap D,
write delta=g_i-D. Whenever the horizontal axis cannot separate
the two and 1/2+delta(alpha+beta)>0, physical separation gives
\[
 y_A-y_i\ge g_i+
     \min\left\{h,\frac1{2\alpha}+v\delta\right\}.    \tag{4}
\]
This follows by considering the coordinate axes and the unit's two
physical side axes. Their ordering follows from the sign of
(alpha-beta){1/2+delta(alpha+beta)}. In every use in this section
delta>=-1/30; hence this sign is nonnegative, and horizontal
separation is impossible. Formula (4) includes aligned units.

The inner-main x-bands give
\[
 x_{M_2}+g_{M_2}>59/60,\qquad
 -x_{M_1}+g_{M_1}>59/60,
\]
\[
 g_{M_2}-x_{M_2}\ge-1/60,\qquad
 g_{M_1}+x_{M_1}\ge-1/60.                           \tag{5}
\]

If x_A>=1/60, use the right inner main. Its inset margin in (4)
is nonnegative. Since h>=1/(2alpha), that clearance is at least
g_{M_2}+1/(2alpha). The right outer main's cone link to M_2 gives
\[
 y_{M_2}\ge y_{M_3}-x_{M_3}+x_{M_2}.
\]
Combine this with (2),(5):
\[
 y_A>\frac1{2\alpha}+\frac{59}{60}-\frac{129}{80}
      =\frac1{2\alpha}-\frac{151}{240}.
\]
Horizontal reflection proves the same statement for x_A<=-1/60.

If |x_A|<=1/60, both inset margins in (4) are at least -1/30.
Thus both clearances are at least
\[
 g_i+\frac1{2\alpha}-\frac v{30}.
\]
Average the two resulting outer-endpoint inequalities. The retained
endpoint budget and center strip imply
\[
 \frac{(X_0-y_0)+(X_3-y_3)}2
 \le\frac{X_0+X_3+|y_0|+|y_3|}{2}
 <\rho+1/16=379/240.
\]
Consequently
\[
 y_A>\frac1{2\alpha}-\frac v{30}-\frac{143}{240}
      \ge\frac1{2\alpha}-\frac{151}{240},
\]
because 0<=v<=1. This completes (3), including the two boundaries.

## 3. Two orientation inequalities, proved on the entire interval

For every physical unit A and every 0<=w<=1,
\[
 \boxed{\frac1{2\alpha_A}+(1+w)g_A
       >\frac{59}{64}+\frac{3033}{8000}w.}            \tag{6}
\]
To prove this, put t=beta_A/alpha_A, L=sqrt(1+t^2), so
g_A=L/[2(1+t)] and 1/(2alpha_A)=L/2. It suffices to prove
\[
 \frac{(t+2)L}{2(t+1)}>59/64,\qquad
 \frac{(t+3)L}{2(t+1)}>1301/1000.                    \tag{7}
\]
The positive-squared difference for the first inequality is
\[
 P(t)=1024t^4+4096t^3+1639t^2-2866t+615.
\]
It has P''>0 on [0,1] and P'(1/4)=-2429/2<0, so it decreases
up to 1/4. On [1/4,1] it has P''>=10190>10000. At t=1/3,
\[
 P=496/81>6,\qquad P'=-6920/27,\qquad |P'|<257.
\]
The tangent quadratic therefore gives, throughout that latter interval,
\[
 P(t)>6-257^2/20000>0.
\]
Its earlier decreasing interval has values no smaller than at 1/4,
so the first inequality in (7) is proved everywhere.

For the second inequality, the positive-squared difference is
\[
 Z(t)=250000t^4+1500000t^3+807399t^2-1885202t+557399.
\]
Here Z''>1600000 on [0,1], while at t=1/2,
\[
 Z=79091/4>19000,\qquad Z'=172197<173000.
\]
The same tangent-quadratic argument gives
\[
 Z(t)>19000-173000^2/3200000>9000>0.
\]
This proves (7). The left side of (6) is the convex combination
with weights 1-w,w of the two left sides in (7). Their right-side
difference is exactly 3033/8000, proving (6).

## 4. One exact concave maximum

For 0<=w<=1, set
\[
 J(w)=\frac{w(1-w)}{2\sqrt{1+w^2}}+\frac{967}{8000}w.
\]
We need the uniform bound
\[
                              J(w)<703/4000.          \tag{8}
\]
Direct differentiation gives
\[
 J''(w)=\frac{w^2-3w-2}{2(1+w^2)^{5/2}}<-1/4.
\]
For the displayed comparison, use
(1+w^2)^(5/2)<=(1+w^2)^2(1+w^2/2)<=1+5w^2.
The remaining difference is 3+6w-7w^2>=2>0 on [0,1].

At w=3/5,
\[
 J=\frac3{5\sqrt{34}}+\frac{2901}{40000}<351/2000,
 \qquad J'=967/8000-\frac{13}{17\sqrt{34}}.
\]
The first bound follows from sqrt(34)>583/100 and the exact
cross-product comparison 4119*583-60*40000=1377>0.
For the derivative,
\[
                         -11/1000<J'<0.
\]
The upper sign follows from sqrt(34)<6; the lower bound follows
again from sqrt(34)>583/100, using
211*9911-1300*1600=11221>0.

The concave tangent quadratic has maximum at most
J(3/5)+2J'(3/5)^2. It is strictly smaller than
\[
 351/2000+2(11/1000)^2<351/2000+1/4000=703/4000.
\]
This proves (8) without a sampled value or unexamined subinterval.

## 5. The physical two-unit clearance and the replacement floor

Let A,B be upper central outsiders with |x_B-x_A|<=1/2, and label
them so y_B>y_A. Equal center heights would already contradict
their disjoint radius-1/2 disks.

Use A's contained aligned square, of halfwidth g_A, and the
physical upper unit B. The horizontal axis cannot separate them,
and its inset margin is at least g_A-1/2>=1/(2sqrt(2))-1/2.
The side-axis ordering condition in (4) remains strictly positive.
Put w=beta_B/alpha_B, k_B=(alpha_B-beta_B)/2. The exact
whole-floor form of (4) gives
\[
 y_B-h_B\ge y_A+g_A
       -\max\{0,w(k_B-g_A+1/2)\}.                   \tag{9}
\]
If the maximum is zero, (3),(7) already give a whole floor greater
than 59/64-151/240>2807/24000. Thus this branch already exceeds
the exact claimed threshold. Otherwise, (3),(6),(9) yield
\[
 \begin{aligned}
 y_B-h_B
 &>\frac1{2\alpha_A}+(1+w)g_A-wk_B-w/2-151/240\\
 &>59/64-\{wk_B+(967/8000)w\}-151/240.
 \end{aligned}
\]
Since k_B=(1-w)/(2sqrt(1+w^2)), the expression in braces
is exactly J(w). Apply (8):
\[
 y_B-h_B>59/64-703/4000-151/240
          =\frac{2807}{24000}
          =\frac7{60}+\frac7{24000}.                 \tag{10}
\]
This proves the theorem. All possible separating side axes,
orientations, and chiralities have been included in the two proxy
clearances; neither is an asserted physical vertical projection edge.

## 6. Recovered scope

This recovery retains the complete universal theorem and its proof in Sections 1--5. The prior fixed-mask caller is omitted. The theorem requires only the original actual cone four-chain and the two original upper central outsiders with horizontal center gap at most one half. No short-chain actual link or side occupancy is a premise. Its geometry, quartic identities, curvature bounds, rational anchors and boundary cases were independently read by hand on 5 November 2026.
