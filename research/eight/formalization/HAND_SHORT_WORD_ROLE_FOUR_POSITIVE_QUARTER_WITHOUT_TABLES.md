# All role-4 positive-sign quarter owners of the short word

At \(Q=9789/2500\), every outer/outer quarter-one pair on edge 4 of
\(0010111\), with original signs \((+,+)\), satisfies
\[
 C>.89765
\]
whenever one of the four retained original axes separates and
\(|\phi-\pi/2|\le.7\). All separating-owner ties are included.

Original axes 3 and 4, on both full angle halves, are proved with the
stronger bound \(C>.949\) in
[HAND_SHORT_WORD_SAME_SIGN_UNIT_SUPPORTS_WITHOUT_TABLES.md](HAND_SHORT_WORD_SAME_SIGN_UNIT_SUPPORTS_WITHOUT_TABLES.md).
This note proves both halves of original axes 1 and 2 and therefore
completes the entire eight-branch role-4 positive-sign family.

The only split below is the intrinsic transition at which the exact
circle support leaves the diagonal endpoint. There is no subdivision
into prescribed angle intervals or any table of coefficient signs.

## 1. Common constants and one scalar

All terminating decimals are exact rationals. Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\quad
 d=\sqrt{Q/2}-\tfrac12,
\]
and
\[
 \lambda=.71553,\qquad t=.86884,\qquad c=.03846.
\tag{1}
\]
Both outer states satisfy
\[
 a=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\quad 0\le b\le d,
\]
and the same equation holds for \(A,B\). We use
\[
\begin{gathered}
 1.414575671<a_0<1.414575672,\qquad
 .899214065109<d<.899214065110,\qquad R<1.978788,\\
 \sin u<.645,\quad\cos u>.764\qquad(0\le u\le.7),\\
 \sqrt{\tfrac14+(a_0-\tfrac12)^2}<1.043.
\end{gathered}
\tag{2}
\]
Write
\[
 \phi=\frac\pi2+ru,\quad s=\sin u,\quad k=\cos u,\quad
 W=\frac{1+k+s}{2},\qquad r\in\{-1,1\}.
\]

A scalar needed for both owners is
\[
 D(u)=\frac\pi2-u+c-td+\frac\lambda2+
          \lambda(\tfrac12-d)k+\lambda(\tfrac12+d)s.
\tag{3}
\]
Its derivative is
\[
 D'=-1+\lambda(d-\tfrac12)s+\lambda(d+\tfrac12)k,
\]
and
\[
 D'''=-\lambda(d-\tfrac12)s-\lambda(d+\tfrac12)k<0.
\tag{4}
\]
Thus \(D'\) is strictly concave. Direct fixed endpoint comparisons give
\[
 D'(0)>.00117,\qquad D'(.3)>.0408.
\tag{5}
\]
In particular, \(D\) increases on \([0,.3]\). Also \(D'\), once it
becomes negative, cannot return to zero: concavity and \(D'(0)>0\)
force its subsequent secant slopes to be negative. Hence the minimum
of \(D\) on \([0,.7]\) lies at an endpoint.

The fixed value bounds needed below are
\[
 D(0)>.90009,\qquad D(.7)>.91224.
\tag{6}
\]
They follow from (2), \(\pi/2>1.570795\), and the alternating-series
bounds
\[
\begin{gathered}
 .64421768723<\sin(.7)<.64421768724,\\
 .76484218728<\cos(.7)<.76484218729.
\end{gathered}
\tag{7}
\]
For example
\[
 D(0)=\frac\pi2+c-(\lambda+t)d+\lambda
 >\frac{9000972116616693}{10000000000000000}>.90009.
\tag{8}
\]
The derivative check at \(.3\) uses the same alternating series at
that single endpoint.

## 2. Original axis 1

The exact role-label difference and original separator are
\[
 C=\phi+c+\lambda b-tB,\qquad b+Ak+rBs\ge W.
\tag{9}
\]
Subtract \(\lambda\) times the weak separator margin. The source
coefficients vanish, and the target expression becomes
\[
 -\lambda k A-(t+r\lambda s)B.
\tag{10}
\]

### 2.1 The positive half

Here \(t+\lambda s>\lambda k\). The derivative of (10) in \(B\)
is negative throughout the outer arc, so its minimum is at \(A=B=d\).
Consequently
\[
 C\ge P(u):=\frac\pi2+u+c-td+\frac\lambda2+
                                \lambda(\tfrac12-d)(k+s).
\tag{11}
\]
Since \(k-s>0\) on \([0,.7]\),
\[
 P'=1-\lambda(d-\tfrac12)(k-s)
 >1-\lambda(d-\tfrac12)>.71.
\]
Its minimum is \(P(0)=D(0)>.90009\).

### 2.2 The negative half

The transition equation
\[
 \lambda(\cos u_d+\sin u_d)=t
\tag{12}
\]
has exactly one root \(u_d\) in \((0,.3)\).
Indeed \(k+s\) is strictly increasing on \([0,.7]\), its initial
value gives \(\lambda-t<0\), and the alternating series gives
\(\lambda(\cos(.3)+\sin(.3))-t>.026\).

For \(0\le u\le u_d\), the derivative of (10) in \(B\) is
nonpositive throughout the arc, so the diagonal support is valid and
\[
 C\ge D(u)\ge D(0)>.90009.
\tag{13}
\]
For \(u\ge u_d\), use the full-circle lower support. It gives
\[
 C\ge N_*(u):=\frac\pi2-u+c+\frac{\lambda+t}{2}
                       +\lambda k-RN(u),
 \qquad
 N(u)^2=\lambda^2+t^2-2\lambda ts.
\tag{14}
\]
At the transition the two target coefficients coincide. Their
full-circle minimum is exactly the diagonal point, and hence
\[
 N_*(u_d)=D(u_d).
\tag{15}
\]
The norm \(N\) is positive and decreasing. At the transition,
\(N(u_d)=\sqrt2\,\lambda\cos u_d\le\sqrt2\,\lambda\).
The exact differentiated norm identity is
\[
 N''+\frac N4=\frac{(t^2-\lambda^2)^2}{4N^3}\ge0.
\tag{16}
\]
It follows that on the whole intrinsic support interval
\[
 N_*''=-\lambda k-RN''
 \le-\lambda k+\frac{RN}{4}
 \le\lambda\left(-.764+\frac{R}{2\sqrt2}\right)<0.
\tag{17}
\]
Here \(R/(2\sqrt2)=\sqrt{Q/8}<.7\).
Therefore \(N_*\) is concave on \([u_d,.7]\), and its minimum is
at \(u_d\) or \(.7\).

The left value exceeds \(.90009\) by (13), (15). At the right endpoint,
(7) and squaring give \(N(.7)<.682546867\). Thus
\[
\begin{split}
 N_*(.7)&>
 1.570795-.7+.03846+\frac{.71553+.86884}{2}\\
 &\hspace{12mm}+.71553(.76484218728)
                     -1.978788(.682546867)\\
 &=\frac{561307487754539}{625000000000000}>.89809.
\end{split}
\tag{18}
\]
This completes both full halves of original axis 1.

## 3. Original axis 2

Exact reflection and reversal sends this owner to source axis 4 with
normalized signs \((-,-)\), preserving \(\phi\) and the corrected cost.
In the normalized coordinates, its cost and separator are
\[
 C=\phi+c-tb+\lambda B,\qquad a+rAs+Bk\ge W.
\tag{19}
\]
Use the same multiplier \(\lambda\). The source expression is
\[
 -\lambda a-tb.
\]
Since \(t>\lambda\), it is decreasing on the full outer arc and has
diagonal minimum
\[
 -(\lambda+t)d.
\tag{20}
\]
The target expression is
\[
 -r\lambda s A+\lambda(1-k)B.
\tag{21}
\]

For \(r=1\), it increases with \(B\), so the axial minimum gives
\[
 C\ge A_+(u):=\frac\pi2+u+c-(\lambda+t)d+
             \frac\lambda2+\frac{\lambda k}{2}
                              +\lambda(\tfrac12-a_0)s.
\tag{22}
\]
Its derivative satisfies the whole-angle estimate
\[
 A_+'\ge
 1-\lambda\sqrt{\tfrac14+(a_0-\tfrac12)^2}
 >1-.71553(1.043)>.25.
\tag{23}
\]
Thus \(A_+(u)\ge A_+(0)=D(0)>.90009\).

For \(r=-1\), the coefficient of \(A\) in (21) is nonnegative.
The target expression is concave in \(B\), so its minimum is at the
axial or diagonal endpoint. The diagonal scalar is precisely \(D(u)\)
from (3). The axial scalar is
\[
 A_-(u)=\frac\pi2-u+c-(\lambda+t)d+
             \frac\lambda2+\frac{\lambda k}{2}
                              +\lambda(\tfrac12+a_0)s.
\tag{24}
\]
It is concave on \([0,.7]\), because
\[
 A_-''=-\frac{\lambda k}{2}
                     -\lambda(\tfrac12+a_0)s<0.
\]
Its endpoint values satisfy
\[
 A_-(0)=D(0)>.90009,\qquad A_-(.7)>.99850,
\]
by (2) and (7). Together with (6) and the endpoint-minimum argument
following (5), this proves
\[
 C\ge\min\{A_-(u),D(u)\}>.90009.
\]
Original axis 2 is now covered on both full angle halves.

The two original owners established here and the two owners in the
unit-support note exhaust the entire role-4 \((+,+)\) original
separating-axis union. Every bound is strict at angle and state
endpoints, so the conclusion also includes all simultaneous owners.

