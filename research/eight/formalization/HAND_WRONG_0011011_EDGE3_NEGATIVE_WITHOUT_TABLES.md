# The second negative outer quarter component without scalar tables

This note replaces the three primary-coordinate speed rows and six
zero-target scalar intervals in
`../WRONG_0011011_EDGE3_NEGATIVE_OUTER_QUARTER_HAND_PROOF.md`.
Together with that note's remaining analytic contact reductions, it proves
its complete edge-3 outer/outer negative-sign component:
\[
 \phi-T(b)+K(B)>.89777>.89765
 \qquad(\pi/2-.7\le\phi\le\pi/2+.7)
\]
for every original separating axis. Reflected reversal gives its edge-5
positive-sign component. Other components remain necessary for the
whole 0011011 exclusion.

All decimals are exact rationals. The proofs below use derivative signs,
circle tangents, and explicit point comparisons; they use neither a
continuous interval mesh nor a coefficient table.

## 1. Data and the two remaining scalar targets

Let
\[
 Q=9789/2500,\quad d=\sqrt{Q/2}-1/2,\quad
 a(b)=\sqrt{Q-(b+1/2)^2}-1/2,
\]
\[
 a_0=a(0),\qquad b_1=\sqrt{Q-9/4}-1/2,
\]
\[
 T(b)=.01670+2.42322b-.91744b^2-.95769a(b)b,
 \qquad K(B)=-.02112a(B)+.29090B+.44642a(B)B.
\]
The original analytic label proof gives
\[
 .609<T'<1.069,\quad T'''>1.6,\quad T'''>0\text{ increasing},
 \qquad K'>0,\quad K''<0.
\]
Define
\[
 M(a)=-T\left(\sqrt{Q-(a+1/2)^2}-1/2\right).
\]
The same scalar proof establishes \(M'(a)>.76\) on the full range
\(d\le a\le a_0\), by a positive lower bound for the second derivative
of \(T'(b)-.76(b+1/2)/(a(b)+1/2)\) and one completed square.

The two targets for replacing the rows are:

1. On the active lower-half axis-4 contact,
   \(M'(a)\,\partial_xa_*>1\) for the entire primary-coordinate range.
2. On the lower-half axis-3 zero-target contact,
   \(\pi/2-x-T(b(x))+K(0)>.9\) for its whole physical arc.

We prove both uniformly. All other original axis and boundary arguments
are retained exactly as stated in the cited note.

## 2. One strongly convex speed product

Put \(u=a+1/2\), \(w=\sqrt{Q-u^2}\), and write
\(B_0=3.819505\), \(k_0=.95769\). The third and fourth derivatives
of the primary-coordinate label satisfy
\[
 M'''=\frac{3Q(B_0u-k_0Q)}{w^5}>0,
 \qquad
 \frac{M''''}{M'''}=\frac{B_0}{B_0u-k_0Q}+\frac{5u}{w^2}>
 \frac92.                                                   \tag{1}
\]
Here \(u\ge w\), \(w<1.4\), so \(5u/w^2>25/7\).
The first summand exceeds one because \(u<1.915\) and
\(B_0(.915)<k_0Q\). Both denominators are positive.

At \(a=d\), exact endpoint comparisons give
\(M'<.774\), \(M''<0\), and \(M'''>3.49\).
Equation (1) shows successively that
\[
 M'''-2M''>0,\qquad M'''-2M'>0,\qquad
 M'''-2M''-2M'>0                                             \tag{2}
\]
on the whole interval. For detail, the derivative of the first expression
is greater than \((5/2)M'''>0\). Its sign then makes the derivatives
of the second and third expressions greater than
\((7/2)M'''\) and \((3/2)M'''\), respectively. All three initial
values are positive by the displayed endpoint bounds.
Consequently
\[
                      M'''>2M'+2\max(M'',0).                \tag{3}
\]

Set
\[
 C_0=Q-1.8,\quad z=a-1/2,\quad v=\sqrt{C_0-z^2},\quad
 A(a)=M'(a)v.
\]
Throughout the primary-coordinate range,
\[
 .399<z<.915,\qquad 1.278<v^2<1.96,\qquad
 v^2-z>0,\qquad 2v^4-C_0>1.15.
\]
Since
\[
 A''=M'''v-\frac{2M''z}{v}-\frac{M'C_0}{v^3},
\]
(3) gives, if \(M''\ge0\),
\[
 A''>\frac{M'(2v^4-C_0)}{v^3}
                    +\frac{2M''(v^2-z)}v
 >\frac{.76(1.15)}{1.4^3}>.3.
\]
If \(M''<0\), its middle term in the formula for \(A''\) is
positive, and \(M'''>2M'\) gives the same lower bound. Therefore
\[
                             A''>.3                         \tag{4}
\]
on the full interval, with no primary-coordinate subdivision.
At the single reference \(a=1\),
\[
                     A(1)>1.057,\qquad |A'(1)|<.1.
\]
Integrating (4) and completing a square proves
\[
                   A(a)>1.057-\frac{.1^2}{.6}>1.04>1.        \tag{5}
\]

For the actual active axis-4 contact,
\[
 (\partial_xa_*)^2=Q-2B-(a-1/2)^2
                  >Q-1.8-(a-1/2)^2=v^2,
\]
since \(B\le d<.9\). Both speeds and \(M'\) are positive.
Thus (5) proves \(M'\partial_xa_*>1\) everywhere. The three
former speed rows are replaced by this one strongly convex product.
The original argument now reduces the whole axis to alignment and the
source-diagonal transition; their analytic bounds remain unchanged.

## 3. A linear upper bound for the whole zero-target contact angle

On the zero-target boundary of the remaining lower-half axis, the
contact equation is
\[
 (a(b)-1/2)\cos x-(b+1/2)\sin x=1/2,
 \qquad 0\le b\le b_1.                                     \tag{6}
\]
We prove the useful whole-arc estimate
\[
                         x<.571-.72b.                       \tag{7}
\]
Put \(k=.72\), \(C(b)=.571-kb\), \(v=b+1/2\),
\(u=\sqrt{Q-v^2}\), and
\[
 F(b)=(u-1)\cos C(b)-v\sin C(b).
\]
Here \(0<C(b)\le.571\), because \(.7905<b_1<.791\).
Differentiation gives
\[
 F''=\cos C\{A_0(b)-D_0(b)\tan C\},
\]
\[
 A_0=2k-Q/u^3-k^2(u-1),\qquad D_0=kv(2/u-k)>0.               \tag{8}
\]
We show that the brace is positive throughout \([0,b_1]\).

First,
\[
 A_0''(b)=\frac Q{u^7}\{k^2u^4-3Q-12v^2\}<0,
\]
since \(u<1.915\) and \(k^2(1.915)^4<3Q\).
Thus \(A_0\) is concave. Its endpoint values exceed
\(.407\) and \(.0206\), respectively. For \(y=b_1-b\), its chord
therefore gives
\[
 A_0(b)>.0206+\frac{.3864}{b_1}y>.0206+.488y.                \tag{9}
\]
Second, \(D_0'=2kQ/u^3-k^2>0\), so its right endpoint bounds it
above by \(.571\). Convexity of the tangent function, with the exact
comparison \(\tan(.571)<1.13(.571)\), gives
\[
 \tan C\le1.13C<1.13(.00184+.72y).
\]
Combining this with (9),
\[
 A_0-D_0\tan C
 >.0206+.488y-(.571)(1.13)(.00184+.72y)>0.                    \tag{10}
\]
Both the constant and linear coefficients on the right are positive.
Hence \(F''>0\) on the whole interval.

The left endpoint has \(F(0)<1/2\), by direct substitution at the
single angle \(.571\). At the right endpoint, \(u=3/2\) and
\(C(b_1)>0\), so
\(F(b_1)=\tfrac12\cos C(b_1)-(b_1+1/2)\sin C(b_1)<1/2\).
A convex function is bounded above by its endpoint chord; therefore
\(F(b)<1/2\) throughout the interval. The left side of (6) decreases
strictly with \(x\) on the relevant arc. Substitution of \(x=C(b)\)
therefore proves (7).

## 4. One scalar label bound finishes the zero-target curve

We next prove
\[
                     T(b)-.72b<.06918\qquad(0\le b\le b_1). \tag{11}
\]
On \([0,.5]\), the increasing second derivative of \(T\) is bounded
above by \(T''(.5)<-.336\). At the rational reference \(b=1/3\),
\[
 T(1/3)-.72/3<.069177,\qquad |T'(1/3)-.72|<.00016.
\]
Strong concavity and a completed square give on the whole first half
\[
 T(b)-.72b<.069177+\frac{(.00016)^2}{.672}<.06918.
\]
On \([.5,b_1]\), the function \(T'-.72\) is convex, because
\(T'''>0\). Both endpoint values are negative. It is therefore
negative throughout, so \(T-.72b\) decreases there. This proves
(11) on the full range.

Finally, (7) and (11), together with \(K(0)=-.02112a_0>-.02989\),
give on the entire zero-target boundary
\[
\begin{aligned}
 \pi/2-x-T(b)+K(0)
 &>1.57079-.571-.06918-.02989\\
 &=.90072>.9.                                                \tag{12}
\end{aligned}
\]
The six former midpoint/derivative rows are unnecessary.

## 5. Complete axis coverage and dependence

Equation (5) supplies the full primary-coordinate speed inequality needed
for axis 4 below alignment. Equation (12) supplies the entire zero-target
boundary of axis 3 below alignment. The other axis and boundary arguments
in the cited note use direct circle supports, monotonicity, negative
curvature at every possible stationary point, or whole-interval derivative
signs. In particular its fixed-endpoint-angle proof already uses
\(J'''<-.36\) on its whole domain and one strong-convexity reference;
it needs no replacement.

Those arguments exhaust all four original axes and both angle halves,
including their closed boundaries and ties. The component's least final
bound remains strictly greater than \(.89777\). The complete scope is
therefore as stated at the beginning, without the former three speed
rows or six scalar intervals.

All comparisons here follow from the printed rational formulas, squaring
positive radical bounds, and alternating Taylor inequalities at the
explicit angles. No verifier result, lookup table, or unproved scalar
minimum is a premise. No Lean or generated certificate has been changed
or run.
