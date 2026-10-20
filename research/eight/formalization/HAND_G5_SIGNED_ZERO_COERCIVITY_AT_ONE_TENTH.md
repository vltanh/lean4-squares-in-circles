# A complete signed zero-edge charge at S <= 1/10

## 1. Exact theorem and forward hypotheses

Assume the G0--G2 candidate geometry at squared radius
\(q\le Q=9789/2500\), with roles \((H,G,A,B,T,D,E)\), quarter word
\(0101011\), and
\[
 S=|d_H|+|d_A|+|d_B|+|d_T|+|d_D|\le1/10.
\]
The already proved zero-edge sign theorem gives the strict signs
\((H,G,A,B,T,D)=(+,-,+,-,+,-)\). The global zero-primary theorem
retains exactly the original possible zero-edge axes \(0,2\).
Neither input uses a G/T/H/D tangent cut or a preferred witness.

For any one of the actual zero-quarter edges HG, AB, or TD, write its
original own-frame centers as \((a,-b)\) and \((A,B)\), with
\(a\ge b>0\), \(A\ge B>0\), and signed frame increment \(d\).
Then
\[
 \boxed{b+B+d\ \ge\ 1+\frac{|d|}{32}.}                 \tag{1}
\]
The estimate covers both complete sign intervals \(-1/10\le d\le0\)
and \(0\le d\le1/10\), both originally feasible transverse owners,
every radial state, and weak separating ties. In particular, putting
\(h(d)=(|\sin d|+\cos d-1)/2\),
\[
 \boxed{d-\frac1{16}h(d)+b-(1-B)\ge0.}                \tag{2}
\]
The inequality in (2) is strict when \(d\ne0\). At \(d=0\), equality
holds precisely when \(b+B=1\).

Thus the linear potential \(F(b)=b\) supplies a complete charged
zero-edge theorem at this middle threshold. The charge \(1/16\) is
proved for every currently possible original witness; it is not a
restriction to a contact, an outer receiver, or a chosen radial label.

This is a component for the G5 contraction from \(S\le1/10\). It does
not establish that threshold, construct compatible quarter/mixed-edge
potentials, or by itself prove \(S<3/200\).

## 2. Uniform original-center bounds

Core avoidance and corner containment imply
\[
 L:=\frac{447}{800}<a,A<U:=\frac{283}{200},
 \qquad 0\le b,B<\frac9{10}.                          \tag{3}
\]
For completeness, the distance from the origin to a square with nearest
axis coordinates \((a,-b)\), \(a\ge b\ge0\), is
\[
 \sqrt{(a-1/2)_+^2+(b-1/2)_+^2}
 \le\sqrt2\,(a-1/2)_+.
\]
Avoiding the open radius-\(1/12\) disk gives
\(a\ge1/2+\sqrt2/24>447/800\). The final comparison follows from
\(\sqrt2>141/100\). The same argument applies to A.
The farthest-corner inequality is
\[
 (a+1/2)^2+(b+1/2)^2\le Q.
\]
Substituting \(a=283/200\), \(b=0\) makes its left side exceed Q.
Also \(a\ge b\) and \(2(7/5)^2>Q\) imply \(b<9/10\).

## 3. Preserve the signed increment before estimating it

Write \(x=|d|\), \(c=\cos x\), and \(s=\sin x\). The support width
of either original transverse witness is
\[
 W=(1+c+s)/2.
\]
Its actual feasible projection is one of
\[
 b+A\sin d+B\cos d\ge W,
 \qquad a\sin d+b\cos d+B\ge W.                       \tag{4}
\]
These are the literal original axis-0 and axis-2 inequalities. Either
one yields, for its actual receiver coordinate \(X\in\{A,a\}\) and
its corresponding transverse coordinate \(Y\in\{B,b\}\),
\[
 b+B\ge1+\frac{s}{2}-X\sin d+(Y-1/2)(1-c).           \tag{5}
\]

If \(d\ge0\), add \(\sin d=s\) to (5), and use
\(3/2-X>3/2-U=17/200>47/800\). If \(d\le0\), add
\(\sin d=-s\), and use \(X-1/2>L-1/2=47/800\).
Since \(Y\ge0\), both full sign intervals give the same exact bound
\[
 \boxed{b+B+\sin d\ge
  1+\frac{47}{800}\sin x-\frac12(1-\cos x).}          \tag{6}
\]
Every receiver in (4) satisfies (3), so no owner change was made.
The positive and negative intervals agree at zero.

The signed linear term in (6) is essential. Replacing it initially by
an absolute error would discard the cancellation needed in a later
closed-cycle sum.

## 4. A single rational remainder on the full interval

For \(0\le x\le1/10\), use
\[
 \sin x\ge x-x^3/6,\qquad
 1-\cos x\le x^2/2,\qquad d-\sin d\ge-x^3/6.
\]
Applying these three inequalities to (6) gives
\[
 \begin{aligned}
 b+B+d-1
 &\ge\frac{47}{800}x-\frac{x^2}{4}
                         -\frac{847}{4800}x^3\\
 &\ge\left(\frac{47}{800}-\frac1{40}
                         -\frac{847}{480000}\right)x\\
 &=\frac{15353}{480000}x
  =\left(\frac1{32}+\frac{353}{480000}\right)x.
 \end{aligned}                                                     \tag{7}
\]
This proves (1), with a strictly positive additional reserve whenever
\(x>0\). No mesh or subinterval estimate appears in (7).

Finally \(0\le h(d)\le|d|/2\), since \(\sin x\le x\) and
\(\cos x\le1\). Therefore (7) implies
\[
 d-\frac1{16}h(d)+b+B-1
 \ge\frac{353}{480000}|d|,                            \tag{8}
\]
which proves (2), its nonzero-error strictness, and its equality
statement at zero.

## 5. One shared zero-edge budget, with no double spending

Apply (1) to the actual HG, AB, and TD edges and sum. With
\[
 Z=|d_H|+|d_A|+|d_T|,
\]
one obtains
\[
 \boxed{
 b_H+b_G+b_A+b_B+b_T+b_D
 +(d_H+d_A+d_T)\ge3+\frac{Z}{32}.}                   \tag{9}
\]
More generally, multiplying the three actual rows by any nonnegative
weights retains \(\sum\lambda_i d_i\) on the left and charges
\(\sum\lambda_i|d_i|/32\) on the right. Every shared vertex keeps its
actual signed coordinates and its original radial state.

The remaining G5 obligation is to combine a complete set of such rows
with compatible quarter and mixed-edge supports and the exact cyclic
angle sum. Three proved zero rows do not supply those missing four
edge estimates. In particular, replacing their potentials independently
on adjacent edges would invalidate a claimed telescoping argument.

The proof is elementary containment, both original projection identities,
and the single polynomial remainder (7). No Lean source or historical
certificate was changed, and no compilation or CI was run.
