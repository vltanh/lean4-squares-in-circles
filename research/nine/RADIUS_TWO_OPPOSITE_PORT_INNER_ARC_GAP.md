# A uniform inner-circle gap bound for two opposite application vertices

Date: October 26, 2026.

**Status: complete hand scalar and geometric theorem, accepted after
full-source reviews in
REVIEW_RADIUS_TWO_OPPOSITE_PORT_GAP_AND_CAP2_ROOT_2026_10_26.md and
REVIEW_C6_OPPOSITE_PORT_GAP_AND_CAP_2_C6_2026_10_26.md.** No optimization, sampled inequality, root isolation,
orientation partition or computational certificate is a premise.

Put
\[
 K=79/40,\qquad \rho=5/4,\qquad
 \Lambda=2\arcsin(2/5),\qquad
 u=\sin\Lambda=4\sqrt{21}/25,\quad v=\cos\Lambda=17/25.
\tag{1}
\]
The theorem concerns actual unit squares and their actual application
vertices. It does not replace a shared mean by a vertex, choose a different
circle corner, or assert a routing statement for an arbitrary subgraph.

## 1. The uniform endpoint projection inequality

Let
\[
 K\le R\le2,\qquad a\ge b\ge1/2,\qquad a^2+b^2=R^2.
\tag{2}
\]
In an actual orthonormal own frame write the square as
\[
 [a-1,a]\times[b-1,b].
\]
Its physical circle corner is \((a,b)\), and its opposite vertex is
\(P=(a-1,b-1)\). Define
\[
 w=b-1,\qquad t=\sqrt{\rho^2-w^2},\qquad
 F=\frac{(a-1)t+w^2}{\rho},\qquad
 G=\frac{w(t-a+1)}{\rho}.
\tag{3}
\]

**Projection theorem.** On the entire domain (2),
\[
 \boxed{\qquad F\sin g+G\cos g>\frac12
       \quad\text{for every }\Lambda\le g\le\pi/2.\qquad}
\tag{4}
\]
The weak own-coordinate endpoint \(b=1/2\) is included.

First, \(a\ge R/\sqrt2\ge K/\sqrt2>\rho\). Also the opposite
vertex lies strictly inside the inner circle. To see the latter, put
\(q=R^2\). For fixed q the minimum of a+b under the ordered conditions
in (2) occurs at b=1/2; consequently
\[
 \begin{split}
 |P|^2&=q-2(a+b)+2\\
 &\le q+1-2\sqrt{q-1/4}
 \le5-\sqrt{15}<5/4<\rho^2.
 \end{split}
\tag{5}
\]
The middle function increases for \(q\ge K^2\), and the strict
comparison uses \(\sqrt{15}>15/4\). Thus
\[
                     0<a-1<t<a,\qquad F>0,
\tag{6}
\]
and G has the sign of w.

### 1.1. The endpoint g=Lambda has a uniform positive reserve

For fixed b the expression at g=Lambda increases with a, because its
coefficient of a is
\[
                    (ut-vw)/\rho>0.
\tag{7}
\]
For w<0 this is immediate. For \(0\le w\le\sqrt2-1<5/12\),
one has \(t>7/6\), \(u>7/10\), and
\((7/10)(7/6)-(17/25)(5/12)>0\). Hence it suffices to replace
a by the smaller quantity
\[
 A(w)=\sqrt{K^2-(w+1)^2},\qquad -1/2\le w\le\sqrt2-1.
\]
This radical is positive throughout this whole interval, whether or
not \(A(w)\ge w+1\). Define
\[
 f(w)=\frac{(A(w)-1)(ut-vw)+w(vt+uw)}{\rho}.
\tag{8}
\]
We prove a single strong-convexity bound on its whole interval:
\[
                              f''(w)>3/20.
\tag{9}
\]
Let a denote A(w) only within the following derivative calculation.
Since
\[
 a'=-(w+1)/a,\quad a''=-K^2/a^3,\qquad
 t'=-w/t,\quad t''=-\rho^2/t^3,
\]
direct differentiation gives
\[
 \rho f''=uU+vV,
\]
\[
 U=2-\frac{K^2t}{a^3}
       +\frac{2w(w+1)}{at}
       -\frac{(a-1)\rho^2}{t^3},
\qquad
 V=\frac{K^2w}{a^3}+\frac{2(w+1)}a
       -\frac{2w}t-\frac{w\rho^2}{t^3}.
\tag{10}
\]
The following three elementary ranges prove the same uniform bounds
\(U>-1/5\), \(V>1/2\). They are ordinary rational curvature
estimates, not point evaluations of f or a parameter certificate.

For \(-1/2\le w\le0\), use
\[
 17/10<a<1911/1000,\qquad229/200<t\le5/4.
\]
The squared reserves at the relevant radical endpoints are respectively
\(17/1600\), \(81/62500\), and \(59/40000\). Therefore
\[
 \begin{split}
 U&>2-\frac{K^2(5/4)}{(17/10)^3}
       -\frac{1/2}{(17/10)(229/200)}
       -\frac{(911/1000)(25/16)}{(229/200)^3}\\
  &=-\frac15+\frac{23186977239}{9440026073120}>-1/5.
 \end{split}
\tag{11}
\]
Moreover \(K^2/a^3<4/5\le\rho^2/t^3\). Since w<=0,
\[
 V=2((w+1)/a-w/t)+w(K^2/a^3-\rho^2/t^3)
       >1000/1911>1/2.
\tag{12}
\]

For \(0\le w\le1/4\), use
\[
 a>3/2,\quad a<12/7,\quad a-1<71/100,
                  \qquad6/5<t\le5/4.
\]
Dropping only nonnegative terms in (10) gives
\[
 \begin{split}
 U&>2-\frac{K^2(5/4)}{(3/2)^3}
           -\frac{(71/100)(25/16)}{(6/5)^3}
      =-\frac15+\frac{2611}{23040}>-1/5,\\
 V&>\frac76-\frac5{12}
           -\frac{(1/4)(25/16)}{(6/5)^3}
      =\frac12+\frac{331}{13824}>1/2.
 \end{split}
\tag{13}
\]
All displayed bounds on a,t follow directly by positive squaring from
\(K^2=6241/1600\) and \(\rho^2=25/16\).

For \(1/4\le w\le\sqrt2-1<5/12\), use
\[
 11/8<a<31/20,\quad a-1<11/20,
                         \qquad7/6<t\le5/4.
\]
Here \(a^2\ge K^2-2>(11/8)^2\), with reserve1/100,
and \(t^2>25/16-(5/12)^2=25/18>(7/6)^2\).
Equation (10) yields
\[
 \begin{split}
 U&>2-\frac{K^2(5/4)}{(11/8)^3}
       +\frac{5/8}{(31/20)(5/4)}
       -\frac{(11/20)(25/16)}{(7/6)^3}\\
  &=-\frac15+\frac{59903451}{566100920}>-1/5,\\
 V&>\frac{50}{31}-\frac57
       +\frac{K^2/4}{(31/20)^3}
       -\frac{(5/12)(25/16)}{(7/6)^3}\\
  &=\frac12+\frac{20477343}{81746504}>1/2.
 \end{split}
\tag{14}
\]
Thus, using \(0<u<3/4\),
\[
 f''>\frac{-(3/4)/5+(17/25)/2}{5/4}
       =\frac{19}{125}=\frac3{20}+\frac1{500}.
\tag{15}
\]
This proves (9) on the full interval, including the three joining
points by the same smooth formula.

One fixed tangent now suffices. At \(w_*=1/8\),
\[
       a=\sqrt{1054}/20,\qquad t=\sqrt{99}/8.
\]
The following coarse rational intervals follow by positive squaring:
\[
 \frac{1623}{1000}<a<\frac{1624}{1000},\qquad
 \frac{1243}{1000}<t<\frac{1244}{1000},\qquad
 \frac{733}{1000}<u<\frac{734}{1000}.
\tag{16}
\]
For clarity, the lower/upper squared reserves for a,t,u are respectively
\[
 \left(\frac{871}{10^6},\frac{2376}{10^6}\right),\quad
 \left(\frac{1826}{10^6},\frac{661}{10^6}\right),\quad
 \left(\frac{311}{10^6},\frac{1156}{10^6}\right).
\tag{17}
\]
Substitution in (8) and its first derivative gives
\[
 f(w_*)>\frac{101}{200}+\frac{265131}{625000000},
 \qquad
 -\frac1{50}<f'(w_*)<\frac1{50}.
\tag{18}
\]
The derivative enclosures can be checked without any hidden radical
arithmetic. If a0,a1,t0,t1,u0,u1 denote the six rational endpoints
in (16), and
\(Q_0=u_0t_0-vw_*\), \(Q_1=u_1t_1-vw_*\), then
\[
 \begin{split}
 \rho f'(w_*)&>
   -\frac{w_*+1}{a_0}Q_1
   -(a_1-1)(u_1w_*/t_0+v)
   +vt_0-vw_*^2/t_0+2u_0w_*,\\
 \rho f'(w_*)&<
   -\frac{w_*+1}{a_1}Q_0
   -(a_0-1)(u_0w_*/t_1+v)
   +vt_1-vw_*^2/t_1+2u_1w_*.
 \end{split}
\tag{19}
\]
After division by rho, the lower expression exceeds -1/50 by
\(37584071/84057875000\), and the upper expression is below 1/50
by \(662757413/18038000000\).

The integrated whole-interval bound (9), with \(y=w-w_*\), now gives
\[
 \begin{split}
 f(w)&>\frac{101}{200}-\frac{|y|}{50}+\frac3{40}y^2\\
 &\ge\frac{101}{200}-\frac1{750}
   =\frac12+\frac{11}{3000}>\frac12.
 \end{split}
\tag{20}
\]
Equations (7)--(8) prove (4) at g=Lambda for every original a,b,R.

### 1.2. The endpoint g=pi/2 and the complete angular interval

For fixed R, F decreases with b on \([1/2,R/\sqrt2]\). Indeed
\[
 \rho\frac{dF}{db}=-\frac{bt}{a}-\frac{(a-1)w}{t}+2w.
\tag{21}
\]
If w<=0 this is negative by \(0<a-1<t\). If w>=0, multiplying
the negative of (21) by at gives
\[
 bt^2+a(a-1)w-2atw
 \ge bt^2+a(a-1)w-w(a^2+t^2)
 =t^2-aw>0.
\tag{22}
\]
Here \(2at\le a^2+t^2\), \(a\le2\),
\(w<5/12\), and \(t^2>25/18>5/6\ge aw\).
Thus F is minimized at a=b=R/sqrt(2).

On that diagonal put \(w=R/\sqrt2-1\). Then
\[
 F=\frac{w(t+w)}\rho,
\]
which increases with w on the relevant positive interval, since
\(t+2w-w^2/t>0\). The inequality \(R\ge K\) therefore
reduces the lower bound to \(w\ge K/\sqrt2-1>99/250\).
The last positive-square reserve is \(2993/2000000\).
At \(w=99/250\) one has \(t>237/200\), with squared reserve
\(1459/1000000\). Consequently
\[
 F>\frac{(99/250)(99/250+237/200)}{5/4}
       =\frac12+\frac{269}{312500}>\frac12.
\tag{23}
\]

Finally, if G<0, the function \(F\sin g+G\cos g\) is increasing
on \([\Lambda,\pi/2]\). If G>=0, it is concave there and is
at least the lesser of its endpoint values. Equations (20),(23)
therefore prove (4) on the entire angular interval.

## 2. Exact geometric consequence for an actual port pair

Consider two actual boundary units satisfying (2), with actual opposite
application vertices \(P_-,P_+\) at distance exactly one. Suppose their
two facing inner-circle endpoints \(Q_-,Q_+\) are the lower-small-coordinate
face intersections described in (3), and the actual intervening free
interval has length \(\Gamma\in(0,\pi)\). The order is that the first
unit's interior arc ends at Q_-, and the second unit's interior arc begins
at Q_+. These are physical face and interval hypotheses, not a choice of
the complementary gap.

In the positively oriented own frame of the second unit,
\[
 P_+=F_+Q_+/\rho+G_+JQ_+/\rho.
\]
The first unit has the opposite own-frame orientation at its facing
endpoint, so
\[
 P_-=F_-Q_-/\rho-G_-JQ_-/\rho.
\tag{24}
\]
Both identities follow directly by dotting \(P=(a-1,w)\) with
\(Q=(t,w)\) and its perpendicular. Thus they retain the actual
application vertices exactly.

Rotate the midpoint direction of this actual interval to the upward
vertical and put \(g=\Gamma/2\). The horizontal component of
\(P_--P_+\), with the labels ordered from right to left, is
\[
 F_-\sin g+G_-\cos g+F_+\sin g+G_+\cos g.
\tag{25}
\]
If \(\Gamma\ge2\Lambda\), both summands exceed1/2 by (4),
because \(g\in[\Lambda,\pi/2)\). Hence
\(|P_--P_+|>1\), contradicting the actual unit channel reserve.
We have proved the strict whole-domain gap bound
\[
 \boxed{\qquad\Gamma<2\Lambda=4\arcsin(2/5).\qquad}
\tag{26}
\]

When every actual pocket extra lies above its actual channel height
H>1/4 and its full inner-circle arc is routed into this same interval,
RADIUS_TWO_CAP_INNER_ARC_SHARP_BOUND.md now excludes two extras.
This last inference requires those actual cap and routing premises.
The complete remaining-C6 join is supplied separately in
SIX_CYCLE_REMAINING_CAP_2_CAPACITY_ONE.md.

No Lean compilation or CI was run. The only computations displayed
above are fixed rational arithmetic and positive-square comparisons;
the signs over the continuous domain follow from the proved calculus
and geometric identities.
