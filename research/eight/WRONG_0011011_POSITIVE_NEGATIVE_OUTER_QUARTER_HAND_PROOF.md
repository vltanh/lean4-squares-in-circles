# 0011011: the whole positive-to-negative outer edge-3 quarter row

**Theorem.** For an outer source with positive local tangent and an outer
target with negative local tangent on edge 3, every retained separating
axis and every
\[
 \pi/2-.7\le\phi\le\pi/2+.7
\]
give corrected cost \(C>.8986>.89765\). Reflected reversal gives the
edge-5 partner. The proof uses monotonicity, a sum of two transverse
coordinates, and a single scalar norm comparison.

Set
\[
 Q=\frac{9789}{2500},\quad
 d=\sqrt{Q/2}-\frac12,\quad
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\frac12,\quad a_0=a(0),
 \qquad 0\le b,B\le d,
\]
and write \(a=a(b),A=a(B)\). All decimals are exact rationals.
The labels and cost are
\[
\begin{aligned}
 R(b)&=-.01025a+.16031b+.63457ab,\\
 K(B)&=-.02112A+.29090B+.44642AB,\\
 C&=\phi+R(b)+K(B).
\end{aligned}                                                     \tag{1}
\]
With \(s=\sin\phi,c=\cos\phi,W=(1+s+|c|)/2\), the four possible
projections are
\[
 b+As+Bc,\qquad -ac+bs+A,\qquad as+bc+B,\qquad a-Ac+Bs.             \tag{2}
\]
At least one is at least \(W\).

## 1. The two label bounds

For \(F(b)=p a(b)+q b+t a(b)b\), put
\(u=a+1/2,r=(b+1/2)/u\). Then
\[
 F'=-pr+q+t(a-br),\qquad
 F''=-2tr-(p+tb)\frac Q{u^3}.
\]
Both labels in (1) have \(p<0,t>0\). Uniformly,
\[
 r>.261,\qquad
 F''\le-2t(.261)+|p|\,\frac Q{(d+1/2)^3}<0.
\]
Both endpoint derivatives \(F'(d)\) are positive, so \(R,K\) increase.
The two further endpoint comparisons are
\[
 R'(.2)>.8,\qquad K'(.2)>.8.
\]
By concavity and monotonicity,
\[
\begin{aligned}
 R(b)&\ge R(0)+.8\min(b,.2),\\
 K(B)&\ge K(0)+.8\min(B,.2).
\end{aligned}                                                     \tag{3}
\]
Let \(c_0=R(0)+K(0)\). If \(\phi\ge.943\), then immediately
\[
 C\ge.943+c_0>.8986.                                              \tag{4}
\]
Only \(\ell=\pi/2-.7\le\phi\le.943<\pi/2\) remains.

## 2. The transverse-coordinate split

If \(b+B\ge.2\), the sum of the two minima in (3) is at least \(.2\).
Therefore
\[
 C\ge\ell+c_0+.16>.986.                                          \tag{5}
\]
Suppose instead \(b+B\le.2\). Each coordinate is at most \(.2\), and
\[
 C\ge\phi+c_0+.8(b+B).                                           \tag{6}
\]

For either secondary projection in (2), \(a,A\le a_0\) and
\(0\le c\le1\) imply
\[
 b+B\ge W-a_0\sin\phi.
\]
Combining this with (6) gives
\[
 C\ge F(\phi)
 =\phi+c_0+.4+.4\cos\phi-(.8a_0-.4)\sin\phi.                      \tag{7}
\]
The scalar increases, because
\[
 .4^2+(.8a_0-.4)^2<1
 \quad\Longrightarrow\quad
 F'=1-.4\sin\phi-(.8a_0-.4)\cos\phi>0.
\]
At the left endpoint, \(\sin\ell=\cos(.7)\) and
\(\cos\ell=\sin(.7)\), and the fixed comparison gives
\(F(\ell)>.924\).

The two primary projections are impossible in this small-sum case.
Indeed \(a,A\ge a(.2)>1.35\), \(\cos\phi\ge\cos(.943)>.587\), and
\(a_0<1.415\). Either primary projection is at most
\[
 1.415-1.35(.587)+.2<1\le W.                                     \tag{8}
\]
Equations (4)--(8) cover the whole row and prove the stated strict reserve.

The companion contains 17 fixed rational comparisons. Square roots are
bounded by integer-square comparisons; sine and cosine by adjacent
alternating Taylor sums. The only \(\pi/2\) enclosure is derived directly
from the Machin identity and the indicated finite arctangent sums.
No numerical minimization or unlisted feasibility assumption enters.

