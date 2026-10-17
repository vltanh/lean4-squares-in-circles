# Wrong word 0011011: asymmetric opposite-sign outer zero-quarter pairs

**Status.** This is a hand proof of the entire edge-0 outer/outer sign case
\((+,-)\), for every \(-7/10\le\phi\le7/10\), at
\(Q=9789/2500\). Reflected reversal also gives the corresponding edge-1 case.
All retained source and target axes are covered. The conclusion is the strict
bound \(C>.89778>.89765=17953/20000\). The proof uses monotonicity,
concavity, and 66 fixed rational comparisons. No contact search or adaptive
subdivision is an input.

## 1. States, labels, and the two axis orders

Put
\[
 Q=\frac{9789}{2500},\quad
 d=\sqrt{Q/2}-\frac12,\quad
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\frac12,\quad
 a_0=a(0),\qquad 0\le b\le d.
\]
Throughout, \(A=a(B)\). Every decimal is an exact terminating rational. The
two labels used here are
\[
 \begin{aligned}
 P(b)&=.02478+.93015b+.02363b^2-.11055\,a(b)b,\\
 J(b)&=-.00026a(b)+.83194b-.11864b^2+.17627\,a(b)b.
 \end{aligned}                                                   \tag{1}
\]
These are the positive edge-0 and negative edge-1 labels, respectively,
in the exact role table. The actual signed pair cost is
\[
 C=\phi+P(b)+J(B).
\]
The source centre has own-frame coordinates \((a(b),-b)\), the target
centre \((A,B)\), and the target frame is rotated by \(\phi\).

Let
\[
 W=\frac{1+|\cos\phi|+|\sin\phi|}{2}.
\]
The retained source secondary and primary separators are
\[
 b+A\sin\phi+B\cos\phi\ge W,                              \tag{2}
\]
\[
 a(b)-A\cos\phi+B\sin\phi\ge W.                           \tag{3}
\]
Reflected reversal exchanges the two squares, preserves \(\phi\), and
exchanges the two labels. It takes each retained target separator to one
of (2),(3). It is therefore enough to prove the claimed bound for
\[
 C_{F,G}=\phi+F(b)+G(B),\qquad
 (F,G)=(P,J)\ \hbox{or}\ (J,P),                          \tag{4}
\]
under either source inequality. This also explains why neither target-axis
case is omitted.

All subsequent contact deformations are made in the larger domain consisting
only of the two outer arcs, the stated signs, the angle interval, and the
chosen SAT inequality. No preservation of a centre-angle constraint is
assumed.

## 2. Scalar derivatives and the aligned bound

For any label
\[
 F(b)=c+p\,a(b)+q b+r b^2+s\,a(b)b,
\]
write \(u=a(b)+1/2\), \(v=b+1/2\). Direct differentiation gives
\[
 \begin{aligned}
 F'&=-p\,v/u+q+2rb+s(a-bv/u),\\
 F''&=2r-2s\,v/u-(p+s b)Q/u^3,\\
 F'''&=-3Q\{sQ+(p-s/2)v\}/u^5.
 \end{aligned}                                                   \tag{5}
\]
For \(P\), the last expression is positive: its brace is
\(-.11055[Q-v/2]\). Thus \(P''\) and \(P'\) increase, and
\[
 P''>0,\qquad .773<P'<.973.                              \tag{6}
\]
For \(J\), its brace is positive throughout \(v\le1.4\). Hence
\(J'''<0\), and fixed endpoint evaluations give
\[
 J''<-.329,\qquad .618<J'<1.082.                         \tag{7}
\]
Both labels are strictly increasing.

At \(\phi=0\), (2) is \(b+B\ge1\); its minimum has \(b+B=1\).
Put \(S(b)=P(b)+J(1-b)\), on \(1-d\le b\le d\). Then
\(S'''=P'''-J'''(1-b)>0\), so \(S'\) is convex. The fixed comparison
\(S'(d)<0\) implies that the nonpositive set of \(S'\) is an interval
containing the right endpoint. Consequently \(S\) can increase and then
decrease, but cannot have an interior minimum below both endpoints.
The two endpoint evaluations are
\[
 P(1-d)+J(d)>.89778,\qquad P(d)+J(1-d)>.89778.            \tag{8}
\]
This argument does not claim that \(S\) itself is concave.

We use the elementary radical enclosures
\[
 .899<d<.9,\qquad 1.4145<a_0<1.415,\qquad \sqrt Q<2.      \tag{9}
\]

## 3. Both primary orders have a large reserve

For \(\phi\le0\), the left side of (3) minus \(W\) is at most
\(a_0-d\cos(.7)-1<0\), so that case is impossible.

For \(0\le\phi\le.5\), the margin in (3) is bounded above by
\[
 a_0-\tfrac12-(d+\tfrac12)\cos\phi
                         +(d-\tfrac12)\sin\phi.
\]
Maximizing the target expression at \(B=d\) is valid because
\(-a(B)\cos\phi+B\sin\phi\) increases with \(B\). The displayed expression
increases with \(\phi\), and its value at \(.5\) is negative.
Thus any primary contact has \(\phi>.5\).

Such a contact also has \(B>.6\): otherwise its margin is at most
\[
 a_0-a(.6)\cos(.7)+.6\sin(.7)-1<0.
\]
Using label monotonicity,
\[
 \begin{aligned}
 C_{P,J}&>.5+P(0)+J(.6)>.99,\\
 C_{J,P}&>.5+J(0)+P(.6)>.99.
 \end{aligned}                                                   \tag{10}
\]
This settles both source primary orders, and hence the retained target
primary as well.

## 4. Secondary contacts and their exact speeds

In (2), the projection increases strictly with both \(b\) and \(B\).
Indeed its \(B\)-derivative is
\[
 \cos\phi-\frac{B+1/2}{A+1/2}\sin\phi>0
\]
because \(|\phi|\le.7<\pi/4\) and the quotient lies in \((0,1]\).
The labels also increase. We may therefore decrease the coordinates to
equality in (2). They cannot both reach zero first, since
\(a_0\sin(.7)<1\le W\).

For \(0\le\phi\le.7\), put \(s=\sin\phi,c=\cos\phi\).
Equality is
\[
 b=b_+(B,\phi)
   =\tfrac12+(\tfrac12-B)c-(A-\tfrac12)s.                \tag{11}
\]
It decreases with both \(B\) and \(\phi\). Write
\[
 r=\frac{B+1/2}{A+1/2},\qquad
 K=-b_\phi=(A-\tfrac12)c-(B-\tfrac12)s>0.
\]
For the last positivity one may use \(A\ge B\) and
\((d-\tfrac12)(c-s)>0\), with the case \(B<1/2\) even more direct.
Moreover
\[
 K^2\le(A-\tfrac12)^2+(B-\tfrac12)^2
      =Q-2(A+B),                                      \tag{12}
\]
and \(A+B\) increases with \(B\). In particular \(K<1.043\).
On a contact,
\[
 \frac{\partial C_{F,G}}{\partial\phi}=1-F'(b)K.        \tag{13}
\]

## 5. Positive angles when the source label is \(P\)

For \(\phi\le.3\),
\[
 K\le .915\cos\phi+\tfrac12\sin\phi
   \le .915\cos(.3)+\tfrac12\sin(.3).
\]
The last elementary function increases on the stated interval.
The fixed comparison
\[
 .973\{\,.915\cos(.3)+\tfrac12\sin(.3)\,\}<1
\]
and (6) prove that (13) is positive.

For \(\phi\ge.3\), monotonicity of (11) gives
\(b\le b_+(0,.3)<.708\), so \(P'(b)<P'(.708)<.907\).
Equation (12) now gives
\[
 1-P'(b)K>1-.907(1.043)>0.                             \tag{14}
\]
Thus, in this order, decreasing a positive angle strictly decreases
the contact cost.

## 6. Positive angles when the source label is \(J\)

First let \(0\le\phi\le.5\). If \(B\ge.2\), equation (12) gives
\(K<.903\), and \(J'K<1.082(.903)<1\).
If \(B\le.2\), then \(b\ge b_+(.2,.5)>.35\), so
\(J'(b)<J'(.35)<.947\). Thus \(J'K<.947(1.043)<1\).
This proves (13) positive on the first half interval.

For \(.5\le\phi\le.7\), put \(G(B,\phi)=J'(b_+(B,\phi))K\).
Every feasible contact has \(0\le b<.501\). Here the fixed estimates are
\[
 J'>.874,\quad |J''|<.514,\quad r>.261,\quad
 c-rs<.753,\quad rc+s>.679.
\]
Because \(b_B=-(c-rs)\) and \(K_B=-(rc+s)\),
\[
 G_B=-J''K(c-rs)-J'(rc+s)
 <.514(1.043)(.753)-.874(.679)<0.                      \tag{15}
\]
For a fixed angle, moving \(B\) toward zero only increases the contact
coordinate \(b\), which remains below \(.501<d\). Thus all intermediate
contacts used in (15) stay in the stated scalar range. Hence
\(G(B,\phi)\le G(0,\phi)\).

At \(B=0\), equation (11) gives
\(.293<b<.501\), while \(K>1.02\) and \(J'<.972\).
Since \(K_\phi=b-1/2\),
\[
 G_\phi=-J''K^2+J'(b)(b-\tfrac12)
 >.329(1.02)^2-.972(.207)>0.
\]
Finally the fixed endpoint evaluation is
\[
 G(0,.7)<.993<1.                                      \tag{16}
\]
Combining (15),(16) proves (13) positive on the entire positive-angle
domain for the second label order.

## 7. The source-diagonal exit for positive angles

In either order, decrease \(\phi\) along (11). The cost decreases until
\(\phi=0\), already covered by (8), or until \(b=d\).
The latter exit has \(0\le B<1-d\). We prove its entire cost is also
bounded by its two endpoints.

Let \(k=1/2-d\), so \(-.4<k<-.399\). On this source-diagonal contact,
\[
 \begin{gathered}
 Z=k+\sin\phi+\cos\phi,\quad Y=\sqrt{Q-Z^2},\\
 U=Z\sin\phi+Y\cos\phi=A+\tfrac12,\qquad
 V=Z\cos\phi-Y\sin\phi=B+\tfrac12.
 \end{gathered}                                                   \tag{17}
\]
These are the positive circle coordinates determined by the contact.
Writing \(m=\sin\phi+\cos\phi\), direct differentiation gives
\[
 f=1-\frac{\cos\phi-\sin\phi}{Y},\qquad
 U'=Vf,\quad V'=-Uf,
\]
\[
 f'=\frac{m(Q-2-k^2)-k m^2-2k}{Y^3}>0.                 \tag{18}
\]
The branch begins at \(\phi=0,B=1-d\) and ends at \(B=0\), at the unique
positive solution \(\phi_a\) of
\[
 (a_0-\tfrac12)\sin\phi_a-\tfrac12\cos\phi_a+d-\tfrac12=0.
\]
The defining function increases, and two rational point evaluations give
\[
 .10726<\phi_a<.108.                                  \tag{19}
\]
On this whole branch \(f>0\), and therefore \(B'=-Uf<0\) and
\[
 B''=-Vf^2-Uf'<0.                                     \tag{20}
\]

For target label \(J\), (7),(20) immediately make
\(\phi+P(d)+J(B(\phi))\) strictly concave.
For target label \(P\), the following uniform bounds suffice:
\[
 B<.101,\quad P''<.125,\quad U>1.8,\quad U<2,\quad
 f<.56,\quad f'>.36.
\]
Here \(B\le1-d<.101\). The \(f\) upper bound follows from (18), \(\phi<.108\),
and \(Y<\sqrt Q\). For the last lower bound in (18), use
\(m\ge1\), \(k^2<.16\), \(-k>.399\), and \(Y^3<8\):
its numerator exceeds \(Q-2-.16+3(.399)>8(.36)\).
Thus
\[
 \frac{d^2}{d\phi^2}\{\phi+J(d)+P(B(\phi))\}
 <.125(1.12)^2-.773(1.8)(.36)<0.                       \tag{21}
\]
Both orders attain their minima at endpoints. At \(\phi=0\) use (8).
At the other endpoint, (19) and the fixed label values give
\[
 \begin{aligned}
 \phi_a+P(d)+J(0)&>.10726+P(d)+J(0)>.89779,\\
 \phi_a+J(d)+P(0)&>.10726+J(d)+P(0)>.926.
 \end{aligned}                                                   \tag{22}
\]
This completes all nonnegative angles.

## 8. Negative angles when the source label is \(P\)

Write \(\phi=-x\), \(0\le x\le.7\), and use \(s=\sin x,c=\cos x\).
The secondary contact becomes
\[
 b=b_-(B,x)
 =\tfrac12+(\tfrac12-B)c+(A+\tfrac12)s.                 \tag{23}
\]
It increases with \(x\) and decreases with \(B\). Put
\[
 v=b_x=(A+\tfrac12)c+(B-\tfrac12)s>0,\qquad z=b-\tfrac12.
\]
The exact circle cancellation is
\[
 v^2=Q-2B-z^2.                                       \tag{24}
\]
Every contact has \(b\ge1-B\), so \(B\ge1-d\) and \(|z|<.4\).
By (6),(9),(24),
\[
 \bigl(P'(b)v\bigr)^2
 >.773^2(Q-1.8-.16)>1.
\]
Thus the derivative of \(-x+P(b_-(B,x))+J(B)\) is strictly positive.
Decreasing \(x\) reaches alignment and decreases the cost. Equation (8)
settles this half.

## 9. Negative angles when the source label is \(J\)

For fixed \(B\), let
\[
 H(x)=-x+J(b_-(B,x))+P(B).
\]
Since \(b_{xx}=-(b-1/2)\), equations (7),(24) give
\[
 H''=J''(b)v^2-J'(b)(b-\tfrac12)
 <-.329(Q-1.8-.16)+1.082(.4)<0.                        \tag{25}
\]
The feasible \(x\)-interval begins at zero. Its other endpoint has \(b=d\).
Indeed (23) decreases with \(B\), and even the contact at \(B=d\) is
infeasible by \(x=.56\), because
\[
 (d-\tfrac12)(1+\cos(.56))-(d+\tfrac12)\sin(.56)<0.
\]
Thus every negative-angle contact reaches \(b=d\) before \(x=.56<.7\).
Concavity (25) reduces the minimum to alignment or to this source-diagonal
boundary.

It remains to control that boundary without another curvature table.
Using \(k=1/2-d\), set
\[
 Z=\cos x+k,\quad Y=\sqrt{Q-Z^2},\quad
 U=Y\cos x-Z\sin x,\quad V=Y\sin x+Z\cos x.
\]
The contact equation \(b=d\) is exactly \(V\cos x-U\sin x=Z\);
hence \(U=A+1/2\), \(V=B+1/2\). Here
\[
 f=1-\frac{\sin x}{Y}>0,\quad
 U'=-Vf,\quad V'=Uf,
\]
\[
 f'=\frac{(1-Q+k^2)\cos x+k(1+\cos^2x)}{Y^3}<0.        \tag{26}
\]
Therefore \(B'=Uf>0\) and
\(B''=-Vf^2+Uf'<0\): the target coordinate is strictly increasing
and concave along the entire boundary.

At its two endpoints \(B_0=1-d\) and \(B_1=d\), the corresponding angles
are \(0\) and \(x_*<.56\). The inverse function \(x(B)\) is convex.
A convex function lies below its endpoint chord, so
\[
 0\le x(B)\le \frac{x_*}{2d-1}(B-(1-d))
 <.702(B-(1-d)),                                     \tag{27}
\]
where \(.56/(2(.899)-1)<.702\).
By \(P'>.773\),
\[
 \begin{aligned}
 -x(B)+J(d)+P(B)
 &\ge J(d)+P(1-d)+(.773-.702)(B-(1-d))\\
 &\ge J(d)+P(1-d)>.89778.
 \end{aligned}                                                   \tag{28}
\]
Together with (25), this settles every negative angle in the second order.

## 10. Arithmetic and coverage

The companion verify_wrong_0011011_asymmetric_opposite_outer_zero_hand.py
checks 66 fixed strict comparisons. It uses exact rational intervals,
integer-square-root enclosures with denominator \(10^{14}\), and alternating
sine/cosine Taylor bounds at the explicitly displayed rational arguments.
The derivative identities, monotonicity, concavity, and endpoint completeness
are proved above; no numerical minimum or sampled contact is used.

There are two axis orders, two source separator types, and two angle halves.
They cover all four retained axes for edge 0, OO, signs \((+,-)\), including
all closed boundaries. Reflected reversal supplies edge 1.
The distinct symmetric edge-4 \((+,-)\) case is already handled in
WRONG_0011011_SYMMETRIC_OUTER_WHOLE_ANGLE_HAND_PROOF.md.
The same-sign OO zero-quarter cases and the remaining quarter-one OO cases
are separate obligations; this note makes no assertion about them.

