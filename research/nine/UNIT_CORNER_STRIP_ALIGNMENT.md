# A unit cannot fit beside an occupied corner in a linked unit-width strip

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_S_C5_DOUBLE_AXIS_STRIP_CENTRAL_BC_RECOVERY_BLOCK_2026_10_26.md.

Let
\[
\begin{gathered}
0<\lambda\le1,\quad u,v,k,l>0,\quad
u^2+v^2=k^2+l^2=1,\quad ul>vk,\\
\eta=l-\lambda,\qquad
v\lambda-uk>0,\qquad v(1-\eta)-uk>0.
\end{gathered}
\tag{1}
\]
There is no unit square E, of any orientation, interior-disjoint
from \(A=[-1,0]\times[0,1]\), all of whose points satisfy
\[
-\lambda\le X\le1,\qquad -k\le Y\le1,\qquad
vX-uY\le v\eta+uk.
\tag{2}
\]
The endpoint \(\lambda=1\) is included.

## 1. Every separating axis forces the whole E into X >= 0

The separating-axis theorem supplies a weak separator parallel to
a side axis of A or E, oriented from A toward E.

A rightward coordinate separator gives \(X\ge0\), as desired.
A leftward one would place E between \(-\lambda\ge-1\) and \(-1\);
an upward one would place it at the single height 1; and a downward
one would give vertical width at most \(k<1\). These alternatives
are impossible for a unit square.

For a noncoordinate side axis of E, use absolute components
\(\xi,\zeta>0\), \(\xi^2+\zeta^2=1\), and coordinate half-width
\(H_0=(\xi+\zeta)/2\). A southwest normal has minimum on E
at most
\[
\xi\lambda+\zeta k-1<\xi=\max_A(-\xi,-\zeta)\cdot z.
\]
A northwest normal has minimum at most
\[
\xi\lambda+\zeta-1<\xi+\zeta
=\max_A(-\xi,\zeta)\cdot z.
\]
The exact additional negative term \(-\xi\zeta\) was discarded.
Both strict comparisons hold even at \(\lambda=1\).

For a northeast normal \((\xi,\zeta)\), suppose E reaches \(X<0\).
Its center obeys \(X_c<H_0\). The separating inequality
\(\xi X_c+\zeta Y_c-1/2\ge\zeta\) yields
\[
Y_c>1-(\xi-\zeta)/2.
\]
Thus its maximum Y is greater than \(1+\zeta\), contradicting (2).

For a southeast normal \(p=(\xi,-\zeta)\), put \(j=(\zeta,\xi)\)
and write
\[
E=[\rho,\rho+1]p+[\tau,\tau+1]j.
\]
The separating inequality gives \(\rho\ge0\). If E reaches \(X<0\),
then \(\tau<0\), and its minimum Y is smaller than \(-\zeta\).
Equation (2) implies \(\zeta<k\), hence \(\xi>l\).
For \(N=(v,-u)\), one has \(N\cdot p>0\) and
\(N\cdot j=v\zeta-u\xi<vk-ul<0\). Its maximum on E is therefore
\[
(\rho+1)(v\xi+u\zeta)+\tau(v\zeta-u\xi)
>v\xi>v\eta+uk,
\]
where the last comparison is \(v\lambda-uk>0\).
This contradicts the last cut.

The four noncoordinate quadrants and coordinate endpoints exhaust
the exact separator cover. Hence \(E\subseteq\{X\ge0\}\).

## 2. The strip forces alignment, and the actual return cut excludes it

The whole E now has \(0\le X\le1\). Every unit square has horizontal
width \(|\cos\phi|+|\sin\phi|\ge1\), with equality only for an
axis-aligned square. Thus
\[
E=[0,1]\times[y_0,y_0+1],\qquad y_0\le0,
\]
the final inequality coming from \(Y\le1\).
Its maximum in direction \((v,-u)\) is at least v. But (1) gives
\(v>v\eta+uk\), contradicting the last cut in (2).
This proves the whole-unit theorem with weak containing half-planes
and all boundary contacts retained.

