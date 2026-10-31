# A unit cannot fit beside an occupied corner under three linked cuts

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_S_C5_TOP_VERTEX_FEATURE_THREE_CUT_CENTRAL_C6_RECOVERY_2026_10_26.md. An earlier review
of the lost version is not acceptance evidence for this file.

This is a geometric theorem for complete unit squares of arbitrary
orientation. Its parameters are linked by the stated equations; none
of the cuts may be chosen independently.

## 1. Statement and two uniform margins

Let
\[
\begin{gathered}
x,t,u,v,k,l>0,\qquad x^2+t^2=u^2+v^2=k^2+l^2=1,\\
x>19/20,\qquad t<3/10,\qquad
0<\lambda<1,\qquad 0<\ell<19/25,\\
\eta=l-\lambda,\qquad
u=x+\ell t-\eta,\qquad v=1+t-\ell x+k,\\
\alpha=xu+tv,\qquad \beta=xv-tu>0,\qquad ul>vk,\\
\lambda>\frac{29}{60}+\frac{37}{50}k.
\end{gathered}
\tag{1}
\]
The occupied root is \(A=[-1,0]\times[0,1]\).
There is no unit square E, interior-disjoint from A, all of whose
points satisfy
\[
\begin{gathered}
X\ge-\lambda,\qquad -k\le Y\le1+t,\\
-tX+x(Y-1)\le0,\qquad xX+tY\le1+t,\\
vX-uY\le v\eta+uk.
\end{gathered}
\tag{2}
\]
All inequalities defining the allowed region are weak.

Put \(X_Q=x+\ell t\), \(Y_Q=1+t-\ell x\).
Thus \(Y_Q>6/25+t\), \(X_Q-1<19t/25\), \(u=X_Q-\eta<1\),
and \(v=Y_Q+k\). In particular,
\[
\begin{split}
v\lambda-uk
&>\left(\frac6{25}+k\right)
       \left(\frac{29}{60}+\frac{37}{50}k\right)-k\\
&=\frac{29}{250}-\frac{2543}{7500}k+\frac{37}{50}k^2\\
&>\frac7{10}\left(k-\frac14\right)^2+\frac{57}{800}>0.
\end{split}
\tag{3}
\]
The difference in the last strict comparison is
\[
\frac1{1000}+\frac{41}{3750}k+\frac1{25}k^2>0.
\]
A second linked margin is
\[
\begin{split}
M&:=v(1-\eta)-uk\\
 &=Y_Q(1-l+\lambda)-k(X_Q-1)\\
 &>\frac{29}{250}+\frac{29}{60}t+
       \left(\frac{111}{625}-\frac t{50}\right)k\\
 &>\frac{29}{250}+\frac{29}{60}t.
\end{split}
\tag{4}
\]
Here \(1-l>0\) and the omitted coefficient exceeds \(429/2500\).
These estimates use the complete ranges in (1).

## 2. Exact separating-axis localization: the whole unit lies at X >= 0

For two squares with disjoint interiors, a weak separating line has
normal parallel to a side axis of one of them. Apply this to A and E.
If a coordinate normal separates them, the right-hand case gives
\(X\ge0\) for E. The left-hand case would put E between
\(-\lambda\) and \(-1\); the upper case has vertical width at most t;
and the lower case has vertical width at most k. They are impossible
because \(\lambda,t,k<1\), whereas every unit square has coordinate
width at least one.

It remains to check the possible side axes of E. Write their
nonzero absolute components as \(\xi,\zeta>0\), with
\(\xi^2+\zeta^2=1\), and let
\[
H_0=(\xi+\zeta)/2,\qquad J_0=(\xi-\zeta)/2.
\]
The coordinate half-widths of E are both \(H_0\). Orient a separating
normal from A toward E, so the minimum on E is at least the maximum
on A.

For a southwest normal \((-\xi,-\zeta)\), the bounds in (2)
make its minimum on E at most
\[
\xi\lambda+\zeta k-1<\xi,
\]
whereas its maximum on A is \(\xi\). For a northwest normal
\((-\xi,\zeta)\), that minimum is at most
\[
\xi\lambda+\zeta(1+t)-1<\xi+\zeta,
\]
again less than its maximum on A. In these bounds, the exact
additional term \(-\xi\zeta\) was harmlessly discarded.

Suppose next that a northeast normal \((\xi,\zeta)\) separates,
and that E has a point with \(X<0\). Its center \((X_c,Y_c)\)
then has \(X_c<H_0\). The separating inequality gives
\[
\xi X_c+\zeta Y_c-\frac12\ge\zeta,
\qquad Y_c>1-J_0.
\]
The half-width for the actual first cut in (2) is
\[
H_U=\frac{|x\zeta-t\xi|+t\zeta+x\xi}{2}.
\]
Its exact comparison is
\[
H_U-tH_0-xJ_0
=\frac{|x\zeta-t\xi|+x\zeta-t\xi}{2}\ge0.
\]
Consequently the maximum of \(-tX+xY\) on E is strictly
larger than x, contradicting that first cut.

Finally suppose the separating normal is southeast,
\(p=(\xi,-\zeta)\), and put \(j=(\zeta,\xi)\).
Write
\[
E=[\rho,\rho+1]p+[\tau,\tau+1]j.
\]
Separation from A gives \(\rho\ge0\). If E has \(X<0\), then
\(\tau<0\). Its minimum Y is then smaller than \(-\zeta\),
so (2) implies \(\zeta<k\), and therefore \(\xi>l\).
For \(N=(v,-u)\),
\[
N\cdot p=v\xi+u\zeta>0,\qquad
N\cdot j=v\zeta-u\xi<vk-ul<0.
\]
Its maximum on E is
\[
(\rho+1)(v\xi+u\zeta)+\tau(v\zeta-u\xi)
>v\xi>v\eta+uk,
\]
where the last comparison follows from (3) and \(\xi>l\).
This violates the final cut in (2).

The separating-axis cover is exhaustive, including equality
separators and directions parallel to a coordinate axis. Thus
every possible E would lie wholly in \(X\ge0\).

## 3. Reduction of all orientations to three support alignments

Set \(Y'=Y+k\). The supposed E lies in the first quadrant in
these coordinates and obeys
\[
xX+tY'\le1+t+tk,\qquad vX-uY'\le v\eta.
\tag{5}
\]
Represent its orientation by \(\phi\in[0,\pi/2]\). Write
\[
\begin{gathered}
H_0(\phi)=\frac{\cos\phi+\sin\phi}{2},\\
H_N(\phi)=
\frac{|v\cos\phi-u\sin\phi|+v\sin\phi+u\cos\phi}{2},\\
H_C(\phi)=
\frac{x\cos\phi+t\sin\phi+|t\cos\phi-x\sin\phi|}{2},
\qquad r=v/u.
\end{gathered}
\]
If \((X_c,Y_c')\) is its center, the quadrant and the second
cut in (5) imply
\[
X_c\ge H_0,\qquad
Y_c'\ge rX_c+H_N/u-r\eta.
\]
Therefore its support in direction \((x,t)\) is at least
\[
\mathcal F(\phi)=
(x+tr)H_0(\phi)+(t/u)H_N(\phi)+H_C(\phi)-tr\eta.
\tag{6}
\]
The sign changes in the absolute values occur at
\[
\phi_C=\arctan(t/x),\qquad
\phi_N=\arctan(v/u),\qquad
0<\phi_C<\phi_N<\pi/2,
\]
with the strict ordering supplied by \(\beta>0\).
On each interval cut out by these angles, the second derivative
of \(\mathcal F\) is the negative of the positive sum
\((x+tr)H_0+(t/u)H_N+H_C\). Hence it is strictly concave there.
Its minimum occurs at one of \(0,\phi_C,\phi_N,\pi/2\).
The values at 0 and \(\pi/2\) agree because they describe the
same axis-aligned square. Only three exact values remain.

### Coordinate alignment

Direct substitution gives the excess over the allowed support:
\[
\mathcal F(0)-(1+t+tk)
=t\left(\frac Mu-\frac t{1+x}\right).
\tag{7}
\]
Using (4), \(u<1\), \(1+x>39/20\), and
\[
\frac{20}{39}-\frac{29}{60}
=\frac{23}{780}<\frac1{30},
\]
the parenthesis is greater than
\[
\frac{29}{250}-\frac t{30}>\frac{53}{500}.
\tag{8}
\]

### Alignment with the C cut

At \(\phi_C\), exact substitution gives
\[
\mathcal F(\phi_C)-(1+t+tk)
=t\{r(x+t-\eta)-(1+t-x)-k\}.
\tag{9}
\]
Since \(x+t-1>0\), \(r>v>6/25+t\), and
\(1-x=t^2/(1+x)\), the expression in braces is greater than
\[
\frac{29}{250}-\frac{83}{300}t+
t^2\left(1-\frac{31/25+t}{1+x}\right).
\tag{10}
\]
The coefficient of \(t^2\) is positive: its numerator comparison
uses \(31/25+t<77/50<39/20<1+x\).
Thus (10) is greater than \(33/1000\), using \(t<3/10\).

### Alignment with the return cut

At \(\phi_N\), the exact excess is
\[
\begin{split}
\mathcal F(\phi_N)-(1+t+tk)
&=x(u+v)-1+t\{v+r(v-\eta)-k-1\}\\
&=\frac{\alpha}{u}(v-\eta).
\end{split}
\tag{11}
\]
For an explicit check of the identity, multiply its first line by
u and subtract \(\alpha(v-\eta)\). The remainder is
\[
u\{x(u+\eta)+t(v-k-1)-1\}
=u(x^2+t^2-1)=0
\]
by the two endpoint equations in (1).

Here \(u>x-1+\lambda>13/30>2/5\) and \(v>6/25\).
On the positive unit quarter-circle these imply \(u+v>6/5\).
Indeed the minimum of the sum on the intervening arc is at an
endpoint; the two endpoint comparisons reduce to
\(\sqrt{21}>4\) and \(\sqrt{589}>24\), with squared reserves
5 and 13.
Also \(\sqrt{1-t^2}+(19/25)t\) increases on \(0<t<3/10\).
Consequently
\[
X_Q<\frac{\sqrt{91}}{10}+\frac{57}{250}
<\frac{24}{25}+\frac{57}{250}=\frac{297}{250},
\]
where \((24/25)^2-91/100=29/2500\). Therefore
\[
v-\eta=u+v-X_Q>\frac3{250}>0.
\tag{12}
\]

All three support alignments have strictly positive excess.
Concavity on the complete intervening orientation intervals
proves the same for every orientation, contradicting (5).
This proves the theorem without an angular grid or a sign packet.

## 4. Scope

The theorem concerns a whole unit, all its boundary points,
weak geometric cuts, and interior-disjointness from the original
occupied root. It makes no circle-mask or force assignment.
In applications, each equation and inequality in (1)--(2) must
be obtained from the same actual contact geometry.
