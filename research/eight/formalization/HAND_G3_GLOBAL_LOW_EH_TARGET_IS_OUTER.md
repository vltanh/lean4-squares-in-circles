# Global outer-target rigidity for low EH witnesses

## 1. Statement and scope

Work on the actual G0--G2 boundary seven-cycle at
\(Q=9789/2500\), with its original separating-axis witnesses,
common real frame spread less than \(7/10\), and the established
normalization \(y_E\le0\).

**Theorem.** Every original EH witness of index 0 or 1 forces
H to be an outer boundary state.

There is no assumption on GA, on any other quarter owner, on
the signs of G,A,B,T, on the mismatch sum, or on an ordering
of the frames. Tied original witnesses are included.

The proof uses the original common G1 marker and proves, for
a putative core H, the stronger local charge
\[
 \frac\pi2+r-F_E-F_H+\frac9{50}h(r)
 >\frac{23459}{20000}>1,
 \qquad h(x)=\frac{\sin x+\cos x-1}{2}.                 \tag{1}
\]
The only possible core-H branch has \(r=d_{EH}>0\), as shown
below. Six unchanged complementary G1 edges then contradict
the angular budget.

## 2. A core target leaves just one branch

Write \(y_E=-b_E\). A low-index quarter witness forces
\(y_H=b_H>0\) by the global quarter-sign theorem. The two
original EH projections are
\[
 P_0=-b_E+a_H\cos r+b_H\sin r,
 \qquad
 P_1=a_H+a_E\sin r-b_E\cos r.                         \tag{2}
\]
Their common threshold is
\[
 W(r)=\frac{1+\cos r+|\sin r|}{2}\ge1.
\]

Suppose H is core. Then \(a_H\le7/12\), \(b_H\le a_H\),
so \(a_H^2+b_H^2\le49/72<1\). Thus \(P_0<1\), which
excludes EH0. If EH1 holds and \(r\le0\), positivity of
\(\cos r\) gives \(P_1\le a_H<1\). Hence \(0<r<7/10\).

E must be outer. Otherwise \(a_E\le7/12\) and
\(\sin r<13/20\) give
\[
 P_1\le\frac7{12}\left(1+\frac{13}{20}\right)
       =\frac{77}{80}<1.                              \tag{3}
\]
All remaining work therefore concerns EH1, positive error,
outer E and core H. No radial kind was changed to obtain
this reduction.

## 3. The original markers and a single circle support

Set
\[
 L=\frac{447}{800},\quad
 a_0=\sqrt{Q-1/4}-\frac12,\quad R=\sqrt Q,
 \quad\eta=\frac25,\quad m=\frac{111}{100}.
\]
The original outer G1 marker obeys the established plane
\[
 F_E\le\eta(a_E-a_0)+m b_E.                           \tag{4}
\]
For core H its exact marker and \(a_H>L\), \(b_H\le a_H\)
give
\[
\begin{aligned}
 F_H+a_H
 &=7.506931(7/12-a_H)+1.077372b_H+a_H\\
 &<7.506931(7/12-L)+2.077372L\\
 &=\frac{3228664781}{2400000000}<\frac{27}{20}.         \tag{5}
\end{aligned}
\]
The last rational reserve is
\(11335219/2400000000\). Each decimal in (5) is the exact
rational from the common G1 marker.

Put \(s=\sin r\), \(c=\cos r\), and
\[
 u=\eta+s,\qquad v=m-c,\qquad N(r)=\sqrt{u^2+v^2}.
\]
In fact both coefficients are positive, since
\(u\ge2/5\), \(v\ge11/100\). The actual E corner circle
therefore gives the usual Cauchy support bound
\[
 u a_E+v b_E
 \le R N(r)-\frac{u+v}{2}.                            \tag{6}
\]
Combine the original weak witness \(P_1\ge W\) with
(4)--(6). This gives the strictly valid lower bound
\[
\begin{aligned}
 C&:=\frac\pi2+r-F_E-F_H+\frac9{50}h(r)\\
 &>\frac\pi2+r+W(r)-\frac{27}{20}
        +\eta a_0+\frac{u+v}{2}-RN(r)+\frac9{50}h(r)\\
 &=\frac\pi2+\frac{251}{200}+\eta a_0-\frac{27}{20}
      -RN(r)+r+\frac{109}{100}\sin r
                  +\frac9{100}(\cos r-1).            \tag{7}
\end{aligned}
\]
No independent endpoint rectangle has replaced the retained
E circle.

## 4. A whole-interval norm estimate

The vector defining N changes by \((\sin r,1-\cos r)\)
from its value at zero. Consequently
\[
 N(r)\le N(0)+2\sin(r/2)\le N(0)+r,
 \qquad
 N(0)^2=\frac{1721}{10000}<\left(\frac{21}{50}\right)^2.
                                                               \tag{8}
\]
Use \(R<2\), \(a_0>7/5\), and \(\pi/2>157/100\) in
(7)--(8). The square reserve for \(a_0>7/5\) is
\(Q-1/4-(19/10)^2=139/2500>0\); the norm reserve in (8)
is \(43/10000>0\). Thus
\[
 C>\frac{239}{200}-r+\frac{109}{100}\sin r
                         +\frac9{100}(\cos r-1).      \tag{9}
\]
On the entire interval \([0,7/10]\), the elementary Taylor
bounds give
\[
 \sin r\ge r-r^3/6\ge\frac{551}{600}r,
 \qquad \cos r-1\ge-r^2/2\ge-\frac{49}{200}.
\]
Moreover
\[
 \frac{109}{100}\frac{551}{600}-1
   =\frac{59}{60000}>0.
\]
Substituting in (9) proves the advertised uniform estimate
\[
 C>\frac{239}{200}-\frac9{100}\frac{49}{200}
     =\frac{23459}{20000}>1.                           \tag{10}
\]

## 5. Closing the cycle

The complementary six real frame errors sum to \(-r\).
Their total variation is at least r. The established
G1 return compression therefore gives
\[
 \sum_{\text{six return edges}}h(|d_i|)\ge h(r).
\]
Apply the unchanged G1 edge lower bounds with
\(\Gamma=8833/10000\) and \(\beta=9/50\). Their
same-vertex signed markers telescope against the EH charge,
so (10) implies
\[
 2\pi>1+6\Gamma.
\]
This is impossible, since
\[
 1+6\Gamma-\frac{710}{113}
   =\frac{9387}{565000}>0,
 \qquad 2\pi<\frac{710}{113}.
\]
Thus H is outer whenever an original EH0/1 witness is
present. Together with the already established reflected
zero--quarter radial theorem, the remaining GA2/3,
EH0/1 branch has H,G,B all outer. The statement concerns
the witness-preserving boundary representatives; it makes
no claim that the original untranslated centers already
touch the containing circle.

The proof is a single whole-interval circle-support estimate.
It invokes no state or angle mesh, numerical acceptance
oracle, generated coefficient inventory, Lean compilation,
or CI result.
