# A sharp common point for squares with high centers

Let
\[
D=\{(x,y):x^2+y^2\le17/4\},\qquad
H=\frac3{\sqrt5},\qquad z=\frac{\sqrt5}{2},\qquad p=(0,z).
\]

**Theorem.** Every unit square \(T\subset D\) whose center height exceeds
\(H\) contains \(p\) in its open interior. Consequently at most one square
in a physical packing in \(D\) can have center height exceeding \(H\).
Reflection gives the corresponding assertion below height \(-H\).

The strict threshold is sharp. The two reflected radial squares with centers
\[
\left(\pm\frac3{2\sqrt5},\frac3{\sqrt5}\right)
\]
and frames given by their radial and perpendicular directions fit in \(D\),
lie on opposite sides of the vertical axis, and touch at \(p\).

## 1. Reduction to a side coordinate

For any square with center \(c\) and orthonormal side axes \(n,m\), put
\(P=n\cdot c\), \(Q=m\cdot c\). Its exact farthest-corner squared radius is
\[
F(P,Q)=(|P|+1/2)^2+(|Q|+1/2)^2.                    \tag{1}
\]
Thus \(F(P,Q)\le17/4\). In particular \(|c|\le3/2\).

Suppose \(p\) is not in the open interior of the square. One of its oriented
side axes then satisfies
\[
n\cdot(c-p)\ge1/2.
\]
Reflecting horizontally if necessary, write
\[
n=(a,b),\quad a\ge0,\quad a^2+b^2=1,\qquad m=(-b,a).
\]
The exceptional case \(a=0\) is immediate. If \(b=1\), the displayed
inequality would require center height at least \(z+1/2>3/2\), impossible.
If \(b=-1\), it gives center height at most \(z-1/2<H\).
Hence assume \(a>0\). We have
\[
P\ge P_0:=1/2+zb,\qquad c_y=bP+aQ.                \tag{2}
\]
For purposes of maximizing \(c_y\), replacing \(Q\) by \(|Q|\) preserves
(1)--(2) and can only increase the height. Thus take \(Q\ge0\).

Put \(R=\sqrt{17}/2\). For fixed \(P\), (1) bounds the height by
\[
f(P)=bP+a\left(\sqrt{R^2-(|P|+1/2)^2}-1/2\right).  \tag{3}
\]
This function is strictly decreasing over its feasible domain \(P\ge P_0\).
Here is a direct check covering both signs. If \(P\ge0\), its derivative is
\[
b-a\frac{P+1/2}{\sqrt{R^2-(P+1/2)^2}}.
\]
It is negative when \(b\le0\). When \(b>0\), it is negative because
\[
P+1/2\ge1+zb>Rb,
\]
using \(R-z<1\). If \(P\le0\), then necessarily \(b<0\), and the derivative is
\[
b+a\frac{1/2-P}{\sqrt{R^2-(1/2-P)^2}}<0,
\]
because \(1/2-P\le-zb<-Rb\). The derivative comparisons follow by squaring
positive quantities and using \(a^2+b^2=1\). They also apply by continuity
at the endpoints. The simple comparison \(R-z<1\) follows from
\(R<z+1\), or equivalently \(17/4<9/4+\sqrt5\).

Therefore the maximum possible height under (2) occurs at \(P=P_0\).
If \(P_0\) is infeasible there is nothing to prove. Otherwise \(|P_0|\le3/2\),
so in particular \(b\le2/\sqrt5\).

## 2. Exact inequality at the proposed height

Let
\[
Q_H=\frac{H-bP_0}{a}.
\]
This is nonnegative throughout \(-1<b\le2/\sqrt5\). We will prove
\[
(|P_0|+1/2)^2+(Q_H+1/2)^2\ge17/4.                \tag{4}
\]
Since the left side increases with \(Q_H\ge0\), (4) implies that the maximum
feasible height in (3) is at most \(H\), as required.

Set \(t=\sqrt5\,b\), so \(-\sqrt5<t\le2\), and put
\[
C=(2-t)(t+3)=6-t-t^2\ge0.
\]
Direct substitution gives
\[
P_0=(1+t)/2,\qquad
Q_H=\frac{C}{2\sqrt{5-t^2}}.
\]
After multiplying (4)'s left side minus \(17/4\) by
\(4(5-t^2)>0\), the expression becomes
\[
C^2+(5-t^2)\bigl((|1+t|+1)^2-16\bigr)
   +2C\sqrt{5-t^2}.                                    \tag{5}
\]

### 2.1 The range \(-1\le t\le2\)

Expression (5) factors as
\[
2(2-t)\left((t+3)\sqrt{5-t^2}-(3-t)(t+2)\right).
\]
The two terms within parentheses are nonnegative before subtraction, and
their squared difference is exactly
\[
(t+3)^2(5-t^2)-(3-t)^2(t+2)^2
=(t+1)^2(9-2t^2)\ge0.
\]
This proves (4) over the whole range. Equality is possible only at
\(t=-1\) or \(t=2\).

### 2.2 The range \(-\sqrt5<t\le-1\)

Write
\[
G=t^3+5t^2-6t-22.
\]
Expression (5) is now \(2(G+C\sqrt{5-t^2})\).
On \((-\sqrt5,-2]\), \(G\ge G(-2)=2\): its derivative
\(3t^2+10t-6\) is negative on that interval. Thus (5) is positive there.

For \(-2\le t\le-1\), put \(r=-t-1\in[0,1]\). Direct expansion gives
\[
\begin{aligned}
C^2(5-t^2)-G^2
&=r(192-177r-34r^2+33r^3-2r^5)\\
&=r\left[12+(1-r)(180+3r-31r^2+2r^3+2r^4)\right]\\
&\ge12r\ge0.
\end{aligned}
\]
The bracketed polynomial is positive because
\(180+3r-31r^2+2r^3+2r^4\ge149\).
If \(G\ge0\), positivity of (5) is immediate. If \(G<0\), the last squared
comparison gives \(C\sqrt{5-t^2}\ge|G|\), again proving (5) nonnegative.
It is strict unless \(r=0\), namely \(t=-1\).

This completes (4), hence proves that exclusion of \(p\) from the open
interior implies \(c_y\le H\). Taking the contrapositive proves the theorem.
\(\square\)

## 3. The numerical threshold needed for P coupling

The rational comparison
\[
\frac{27}{20}>\frac3{\sqrt5}
\]
is exact, since \(729/400>9/5=720/400\). Thus two disjoint unit squares in
\(D\) cannot both have center heights at least \(27/20\), nor can they both
have center heights at most \(-27/20\).

This lemma requires no terminal obstacles, half-plane containment, common
orientation, or prescribed separating axis. It does not by itself prove
P.ALL; that application still needs the proposed upper-pair bound on the
lower endpoint of the vertical-axis section.
