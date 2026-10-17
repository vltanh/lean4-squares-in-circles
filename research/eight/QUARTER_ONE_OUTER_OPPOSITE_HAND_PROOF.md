# A hand inequality for the opposite-sign outer pair near a quarter turn

This proves the source primary-axis regime with negative source tangent
and positive target tangent in the proposed common three-row transition
table. It uses a bound at exactly a quarter turn, elementary angle
comparisons, and two endpoint evaluations of a concave function.

All terminating decimals in this note denote rational numbers. Put

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 p=\frac{13}{200},\quad q=\frac{203}{200},
 \qquad \ell(a,b)=-\frac9{100}+pa+qb.
\]

Let \((a,b)\) and \((A,B)\) belong to the full positive outer arc:

\[
 0\le b\le a,\quad 0\le B\le A,\qquad
 (a+\tfrac12)^2+(b+\tfrac12)^2
 =(A+\tfrac12)^2+(B+\tfrac12)^2=Q.
\]

Write \(\phi=\pi/2+x\), where \(-7/10\le x\le7/10\).
The source negative primary axis separates the two signed states if

\[
 a+A\sin x-B\cos x
 \ge \frac{1+|\sin x|+\cos x}{2}.                         \tag{1}
\]

The transition cost is

\[
 \mathcal C=\phi-\ell(a,b)-\ell(A,B)
 =\frac\pi2+x+\frac9{50}-p(a+A)-q(b+B).
\]

**Theorem.** Every pair satisfying (1) obeys

\[
 \boxed{\mathcal C>\frac{157}{200}=.785.}                 \tag{2}
\]

No bound on the center-angle gap, other than that already encoded in
the named arc and frame domains, is needed here.

## 1. A uniform bound at exactly a quarter turn

The outer arc immediately gives

\[
 a,A<1.415,\qquad a,A>.899,\qquad b,B<.9,\qquad R<1.979.
                                                               \tag{3}
\]

Indeed its primary-coordinate extremes are
\(\sqrt{Q-1/4}-1/2\) and \(\sqrt{Q/2}-1/2\). The proposed
comparisons in (3) follow by squaring.

Temporarily define the quarter-turn cost

\[
 \mathcal C_0=\frac\pi2+\frac9{50}-p(a+A)-q(b+B).
\]

Subtract \(a-B-1\), and enlarge each outer arc to its whole circle.
The minimum of \(u a+v b\) on the circle of center
\((-1/2,-1/2)\) and radius \(R\) is
\(-(u+v)/2-R\sqrt{u^2+v^2}\). Consequently

\[
 \mathcal C_0\ge F_0+(a-B-1),                             \tag{4}
\]

where the constant is

\[
 F_0=\frac\pi2+2.26
 -R\left(\sqrt{(1+p)^2+q^2}+\sqrt{p^2+(q-1)^2}\right).
\]

The rational comparisons

\[
 \sqrt{(1+p)^2+q^2}<1.47121,\qquad
 \sqrt{p^2+(q-1)^2}<.06671,\qquad \pi>3.14159
\]

give

\[
 F_0>\frac{19681283}{25000000}>.787.                      \tag{5}
\]

Both root bounds are checked by squaring. The quoted lower bound
for \(\pi\) has the alternating Machin-series proof in
LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md.

## 2. All negative frame deviations and the first positive tenth

First let \(x=-z\), with \(0\le z\le.7\).
If \(z\ge.4\), (1) and (3) would imply

\[
 .915>1.399\sin z+\frac12\cos z.                           \tag{6}
\]

The right side increases on \([.4,.7]\), since its derivative is at
least \(1.399(1-.7^2/2)-.7/2>0\). At \(z=.4\), the lower Taylor
bounds \(\sin z\ge z-z^3/6\) and \(\cos z\ge1-z^2/2\) make it
at least \(188377/187500>.915\). This contradicts (6).
Thus only \(0\le z<.4\) is feasible.

On this remaining interval, (1) gives

\[
\begin{split}
 a-B-1
 &\ge (A+\tfrac12)\sin z-(B+\tfrac12)(1-\cos z)\\
 &\ge (A+\tfrac12)(\sin z+\cos z-1)\\
 &\ge \frac43z\left(1-\frac z2-\frac{z^2}{6}\right)
 \ge \frac{232}{225}z\ge z .
\end{split}                                                \tag{7}
\]

Here \(A\ge B\), \(A+1/2>4/3\), and the trigonometric
parenthesis is nonnegative. Equations (4) and (7) imply
\(\mathcal C=\mathcal C_0-z\ge F_0>.787\).

Now suppose \(0\le x\le.1\). Equation (1) instead gives

\[
 a-B-1\ge-(A-\tfrac12)\sin x-(B+\tfrac12)(1-\cos x).
\]

Using (3), \(\sin x\le x\), and \(1-\cos x\le x^2/2\), we obtain

\[
\begin{split}
 \mathcal C
 &\ge F_0+x-.915\sin x-1.4(1-\cos x)\\
 &\ge F_0+x(.085-.7x)
 \ge F_0+.015x>.787.
\end{split}                                                \tag{8}
\]

This proves (2) throughout \([-.7,.1]\).

## 3. The remaining interval has a concave lower envelope

For \(.1\le x\le.7\), multiply the nonnegative separator margin
in (1) by \(\lambda=39/40=.975\) and subtract it from the cost.
Enlarging both state arcs to their full circles gives
\(\mathcal C\ge F(x)\), where

\[
\begin{split}
 F(x)&=\frac\pi2+x+\frac{63}{50}+\lambda+\lambda\sin x
             -R(N_1+N_2(x)),\\
 N_1&=\sqrt{(p+\lambda)^2+q^2},\\
 N_2^2&=p^2+q^2+\lambda^2
                 +2\lambda(p\sin x-q\cos x).
\end{split}                                                \tag{9}
\]

The source coefficient pair after subtraction is
\((-p-\lambda,-q)\), and the target pair is
\((-p-\lambda\sin x,-q+\lambda\cos x)\). These show every sign
and constant in (9) directly.

The same elementary circle-norm identity as in
QUARTER_ZERO_OUTER_POSITIVE_HAND_PROOF.md gives

\[
 N_2''+\frac{N_2}{4}
 =\frac{(p^2+q^2-\lambda^2)^2}{4N_2^3}\ge0.              \tag{10}
\]

For completeness, square the norm, differentiate twice, and multiply
by \(4N_2^3\). The numerator is
\((p^2+q^2+\lambda^2)^2-4\lambda^2(p^2+q^2)\), the square in
(10).

We claim \(N_2<(7/4)\sin x\) on the whole interval. Indeed,

\[
 \left(\frac{N_2}{\sin x}\right)^2
 =\left(\frac{q-\lambda\cos x}{\sin x}\right)^2
  +\left(\lambda+\frac p{\sin x}\right)^2.
\]

The first ratio is positive and its derivative has the sign of
\(\lambda-q\cos x\), which increases with \(x\). Its maximum is
therefore an endpoint value. Both endpoint values are less than
\(11/20\), as verified by the sine and cosine bounds below.
The second ratio is less than
\(\lambda+65/99<33/20\), since \(\sin x>.099\).
Their squared bounds sum to \(1210/400<49/16\), proving the claim.

Since \(R<2\) and \(\lambda>7/8\), (10) now gives

\[
 F''=-\lambda\sin x-RN_2''
 \le-\lambda\sin x+\frac R4N_2
 <(-\lambda+\tfrac78)\sin x<0.                            \tag{11}
\]

Thus the minimum of \(F\) is at one of the two endpoints.

## 4. The complete endpoint comparisons

Use \(R<1.979\), \(N_1<1.45322\), and \(\pi>3.14159\).
The \(N_1\) bound follows by squaring. The following table contains
all remaining comparisons.

| \(x\) | Lower \(\sin x\) | Upper \(\sin x\) | Lower \(\cos x\) | Upper \(N_2(x)\) | Lower \(F(x)\) |
|---|---:|---:|---:|---:|---:|
| \(1/10\) | \(9983/100000\) | \(999/10000\) | \(199/200\) | \(337/2000\) | \(79374537/100000000\) |
| \(7/10\) | \(3221/5000\) | \(16106/25000\) | \(19121/25000\) | \(1859/2500\) | \(39319161/50000000\) |

The sine lower bound follows from the Taylor polynomial through
degree seven, the sine upper bound from degree five, and the cosine
lower bound from degree six. Substituting the upper sine and lower
cosine in \(N_2^2\), then squaring the proposed upper \(N_2\), checks
the fifth column. Substituting the lower sine and all root upper
bounds in (9) checks the last column.

Both endpoint lower values exceed \(.7863>.785\).
Equations (8) and (11) complete the proof of (2). The optional
verify_quarter_one_outer_opposite_hand.py reproduces these displayed
finite comparisons using rational arithmetic only. \(\square\)
