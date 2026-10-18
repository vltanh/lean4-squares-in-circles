# A hand inequality for the critical zero-quarter outer pair

This proves one named regime of the proposed common three-row transition
table. It is a continuous analytic argument. Its numerical content is the
two-row rational table below; no subdivision or optimization is a premise.

Let
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 p=\frac{13}{200},\quad q=\frac{203}{200},\quad
 \lambda=q-\frac7{10}p=\frac{1939}{2000}.
\]
An outer boundary state in the positive tangent half is a point
\[
 (a,b),\qquad 0\le b\le a,\qquad
 (a+\tfrac12)^2+(b+\tfrac12)^2=Q.
\]
Write its marker as
\[
 \ell_O(a,b)=-\frac9{100}+pa+qb.
\]
Consider two such states \((a,b),(A,B)\), and a relative frame angle
\(-7/10\le\phi\le7/10\). If their positive source secondary axis separates,
then
\[
 b+A\sin\phi-B\cos\phi\ \ge\
 W(\phi):=\frac{1+|\sin\phi|+|\cos\phi|}{2}.                 \tag{1}
\]
The conclusion is
\[
 \phi+\ell_O(a,b)-\ell_O(A,B)>\frac{391}{400}.             \tag{2}
\]
Reflection followed by reversal gives the corresponding target secondary
regime.

## 1. Necessary angle and source-coordinate bounds

The outer circle gives
\[
 b<\frac9{10},\qquad A<\frac{71}{50},\qquad R<2.
\]
Indeed \(b\le\sqrt{Q/2}-1/2<9/10\), and
\(A\le\sqrt{Q-1/4}-1/2<71/50\).

If \(\phi\le0\), the left side of (1) is at most \(b<9/10\),
whereas \(W\ge1\), so this is impossible. If \(0\le\phi\le1/10\),
the difference between the two sides of (1) is strictly smaller than
\[
 \frac25+\frac{23}{25}\sin\phi-\frac12\cos\phi
 \le \frac25+\frac{23}{250}-\frac{199}{400}
 =-\frac{11}{2000}<0.
\]
Consequently
\[
 \frac1{10}<\phi\le\frac7{10}.                            \tag{3}
\]

On this interval (1) also yields
\[
 b\ge W-A\sin\phi+B\cos\phi
 >\frac12+\frac12\cos\phi-\frac{23}{25}\sin\phi
 >\frac7{25}.                                           \tag{4}
\]
The middle expression decreases throughout the interval. At its right
endpoint, the elementary Taylor estimates
\[
 \cos(7/10)>\frac{19121}{25000},\qquad
 \sin(7/10)<\frac{16106}{25000}
\]
give the stronger lower bound \(362149/1250000>7/25\).

For \(7/25\le b\le9/10\) the convex quadratic
\[
 (b+\tfrac12)^2+(2-\tfrac7{10}b)^2
 =\frac{17}{4}-\frac95b+\frac{149}{100}b^2
\]
is at most its larger endpoint value. Its endpoint values are
\[
 \frac{603565}{156250}=3.862816,\qquad
 \frac{38369}{10000}=3.8369,
\]
both smaller than \(Q\). Since \(2-7b/10>0\), the outer circle identity
therefore implies
\[
 a+\frac7{10}b>\frac32.                                 \tag{5}
\]

## 2. The SAT multiplier removes both state variables

Multiply (1) by the positive number \(\lambda\). By (5),
\[
 pa+(q-\lambda)b
 =p(a+\tfrac7{10}b)>\frac{39}{400}.
\]
For the target state, allow the whole outer circle; this enlarges its
domain and hence gives a valid lower support bound:
\[
\begin{split}
 (-p-\lambda\sin\phi)A+(\lambda\cos\phi-q)B
 &\ge
 \frac{p+q+\lambda(\sin\phi-\cos\phi)}2-RN(\phi),\\
 N(\phi)^2
 &=p^2+q^2+\lambda^2
       +2\lambda(p\sin\phi-q\cos\phi).
\end{split}                                             \tag{6}
\]
Combining the source and target bounds, the left side of (2) is strictly
larger than
\[
 F(\phi)=\phi+\frac{4489}{4000}
               +\lambda\sin\phi-RN(\phi).               \tag{7}
\]

## 3. One concavity identity reduces the interval to its endpoints

The norm in (6) satisfies the exact identity
\[
 N''+\frac N4
   =\frac{(p^2+q^2-\lambda^2)^2}{4N^3}\ge0.             \tag{8}
\]
This follows by differentiating \(N^2=C+u\sin\phi+v\cos\phi\);
the numerator after clearing denominators is \(C^2-u^2-v^2\).

We next establish \(N<(7/4)\sin\phi\) on \([1/10,7/10]\). Use
\[
 \left(\frac{N}{\sin\phi}\right)^2
 =
 \left(\frac{q-\lambda\cos\phi}{\sin\phi}\right)^2
 +\left(\lambda+\frac p{\sin\phi}\right)^2.              \tag{9}
\]
The derivative of the first ratio is
\[
 \frac{\lambda-q\cos\phi}{\sin^2\phi}.
\]
Its numerator increases, so this ratio has no interior maximum. Its
values at both endpoints are less than \(11/20\), using the rational
sine and cosine bounds in the table below. Also
\(\sin\phi>\sin(1/10)>99/1000\), so the second ratio is less than
\[
 \frac{1939}{2000}+\frac{65}{99}<\frac{33}{20}.
\]
Both ratios are positive. Their squared bounds add to
\(1210/400<49/16\), proving the assertion.

Now (8), \(R<2\), and \(\lambda>7/8\) give
\[
 F''=-\lambda\sin\phi-RN''
 \le-\lambda\sin\phi+\frac R4N
 <(-\lambda+\tfrac78)\sin\phi<0.                        \tag{10}
\]
Thus \(F\) is concave, and its minimum on the closed interval is an
endpoint value.

## 4. The complete endpoint arithmetic

All entries below are rational. The sine and cosine estimates follow
from the alternating Taylor bounds of degrees \(7,5,6\), respectively
(lower sine, upper sine, lower cosine). Use \(R<1979/1000\).

| \(x\) | lower \(\sin x\) | upper \(\sin x\) | lower \(\cos x\) | upper \(N(x)\) | lower \(F(x)\) |
|---|---:|---:|---:|---:|---:|
| \(1/10\) | \(9983/100000\) | \(999/10000\) | \(199/200\) | \(17/100\) | \(196521037/200000000\) |
| \(7/10\) | \(3221/5000\) | \(16106/25000\) | \(19121/25000\) | \(371/500\) | \(9783839/10000000\) |

To check each \(N\) entry, substitute the upper sine and lower cosine
into (6) and compare with the square of the proposed upper bound.
To check each \(F\) entry, substitute the lower sine, the proposed
upper \(N\), and \(1979/1000\) into (7).
Both displayed lower \(F\) values exceed \(391/400\). This proves (2).

The accompanying short rational arithmetic file independently checks
every displayed comparison and the two quadratic endpoint values.
It is a reproducibility aid for the displayed arithmetic, not a
search or a hidden case cover.
