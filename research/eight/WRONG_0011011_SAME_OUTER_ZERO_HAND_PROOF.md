# Wrong word 0011011: every same-sign outer zero-quarter pair

**Status.** This is a hand proof of all same-sign outer/outer zero-quarter
branches of the word 0011011. It covers the four retained axes, the complete
allowed frame-angle interval, and the physical centre-angle condition.
Every such corrected cost is strictly greater than
\(.89777>.89765=17953/20000\).
The companion verifies 133 fixed rational comparisons.
The continuous arguments are an endpoint-forcing derivative implication,
a negative-Hessian test on a stationary curve, and three one-variable
strong-convexity bounds. No contact search or adaptive subdivision is used.

## 1. The two representative rows

Write
\[
 Q=\frac{9789}{2500},\quad
 d=\sqrt{Q/2}-\frac12,\quad
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\frac12,\quad
 a_0=a(0),\qquad 0\le b\le d,
\]
and \(A=a(B)\). All decimals below are exact terminating rationals.
The four labels are
\[
 \begin{aligned}
 P(b)&=.02478+.93015b+.02363b^2-.11055a(b)b,\\
 J(b)&=-.00026a(b)+.83194b-.11864b^2+.17627a(b)b,\\
 L(b)&=.03965+3.85510b-1.49748b^2-1.89442a(b)b,\\
 K(b)&=-.02112a(b)+.29090b+.44642a(b)b.
 \end{aligned}                                                   \tag{1}
\]
They are exactly the declared role-table coefficients. The two representative
costs, both with signs \((++)\), are
\[
 C=\phi+F(b)-G(B),\qquad (F,G)=(P,J)\ \hbox{or}\ (L,K). \tag{2}
\]
They correspond respectively to edge 0 and edge 4. Reflected reversal
gives edge 1 with signs \((--)\), and the other same-sign half of edge 4.
These are all four same-sign zero-quarter edge/sign choices.

The source centre has own-frame coordinates \((a(b),-b)\) and the target
\((A,-B)\). Put \(W=(1+|\sin\phi|+|\cos\phi|)/2\).
The four retained separating projections are
\[
 \begin{array}{ll}
 \text{source }+f:& b+A\sin\phi-B\cos\phi,\\
 \text{target }+e:& -a(b)\cos\phi+b\sin\phi+A,\\
 \text{target }+f:& a(b)\sin\phi+b\cos\phi-B,\\
 \text{source }-e:& a(b)-A\cos\phi-B\sin\phi.
 \end{array}                                                   \tag{3}
\]
At least one must be at least \(W\).

We use the already proved physical centre-gap bound \(\delta>.76\).
In this same-sign case
\[
 \delta=\phi+\arctan(b/a)-\arctan(B/A),
\]
so a negative \(\phi\) satisfies
\(\phi>.76-\pi/4>-.026\).
For \(-.026<\phi\le0\), the secondary projections in (3) are at most
\(d<1\); the primary projections are bounded above by
\(a_0-d\cos(.026)+d\sin(.026)<1\).
Thus every feasible same-sign row has \(\phi>0\).
The conclusion is asserted for the physical domain; this use of the gap
hypothesis is explicit.

The elementary bounds
\[
 .899<d<.9,\quad 1.4145<a_0<1.415,\quad \sqrt Q<2        \tag{4}
\]
will be used throughout.

## 2. Three of the four axes have a direct reserve

For positive \(\phi\), the source-primary projection is at most
\(a_0-d\cos(.7)<1\), so it is impossible.

For the target-primary axis, maximizing its margin over the source at
\(b=d\) and over the target at \(B=0\) gives
\[
 a_0-\tfrac12-(d+\tfrac12)\cos\phi
                         +(d-\tfrac12)\sin\phi.
\]
This increases with \(\phi\) and is negative at \(.6\).
Thus \(\phi>.6\). The same margin, with \(b=.8,B=0,\phi=.7\), is still
negative, so \(b>.8\). With \(b=d,B=.3,\phi=.7\), it is again negative,
so \(B<.3\). Monotonicity in the coordinates justifies these maxima.
Both costs therefore satisfy
\[
 C>.6+F(.8)-G(.3)>.98.                                \tag{5}
\]

For the target-secondary axis,
\[
 B\le(a-\tfrac12)\sin\phi+(b-\tfrac12)\cos\phi-\tfrac12.
\]
The right side increases with both \(b\) and \(\phi\) on the stated
range. At \(b=d\) it equals
\((d-\tfrac12)(\sin\phi+\cos\phi)-1/2\).
Fixed evaluations imply
\[
 \phi>.3024,\qquad B<.063.
\]
The two point tests at \((b,\phi)=(.8,.5)\) and \((.624,.7)\) also give
\[
 b>.8\quad(\phi\le.5),\qquad b>.624\quad(\phi\ge.5).
\]
Consequently, in either label row,
\[
 \begin{cases}
 C>.3024+F(.8)-G(.063)>.93,&\phi\le.5,\\
 C>.5+F(.624)-G(.063)>.96,&\phi\ge.5.
 \end{cases}                                                   \tag{6}
\]
All label-monotonicity assertions used here are established next.
Only the source-secondary axis remains.

## 3. Scalar label facts

For a label \(H=c+p\,a+q b+r_2b^2+s_2ab\), put
\(u=a+1/2,\ v_b=b+1/2\). Its first three derivatives are
\[
 \begin{aligned}
 H'&=-p\,v_b/u+q+2r_2b+s_2(a-bv_b/u),\\
 H''&=2r_2-2s_2v_b/u-(p+s_2b)Q/u^3,\\
 H'''&=-3Q\{s_2Q+(p-s_2/2)v_b\}/u^5.
 \end{aligned}                                                   \tag{7}
\]
These give
\[
 .773<P'<.973,\quad P''>0,\quad P'''>0,\quad P''''>0,   \tag{8}
\]
\[
 J'>0,\quad J'<1.082,\quad J''<-.329,\quad J'''<0,      \tag{9}
\]
and \(K'>0,\ K''<0,\ K'(0)<.928,\ K'(.2)<.869\).
For the last assertion in (8), differentiating \(P'''\) leaves the positive
numerator
\[
 (5v_b-\tfrac12)Q-2v_b^2
 \ge2(3.9)-2(1.4)^2>0.
\]

Write \(D=L'\). Formula (7) gives
\[
 D''=1.89442\left(\frac{3Q}{u^3}
                   +\frac{3bQ(b+1/2)}{u^5}\right)>2.
\]
The fixed comparisons
\[
 D(.5)>.6248,\quad -.0311<D'(.5)<0,\quad
 D(0),D(d)<1.176
\]
and strong convexity give
\[
 .6245<D<1.176.                                       \tag{10}
\]
In particular all four labels increase strictly. We will also use
\[
 D(d)>1.16,\quad D(.293),D(.755)<.817,\quad
 D'(.755)>1.67.                                      \tag{11}
\]

## 4. The remaining contact surface

The source-secondary inequality is
\[
 b+A\sin\phi-B\cos\phi\ge W.
\]
At fixed \(B,\phi\), reducing \(b\) reduces the cost until equality.
The resulting contact is
\[
 b=\tfrac12+(B+\tfrac12)\cos\phi-(A-\tfrac12)\sin\phi.  \tag{12}
\]
It satisfies \(b>.293\), because its minimum is at \(B=0,\phi=.7\).
Every contact has \(\phi>.107\); even \(b=d,B=0\) is infeasible at
\(\phi=.107\). There is no contact at \(B=d\): the value of (12) at
\(B=d,\phi=.7\) already exceeds \(d\).

Set
\[
 U=A+\tfrac12,\quad V=B+\tfrac12,\quad r=V/U,\quad
 z=b-\tfrac12,\quad q=Q-2A.
\]
The two contact speeds are
\[
 v=-b_\phi=(A-\tfrac12)\cos\phi+(B+\tfrac12)\sin\phi>0,
 \qquad k=b_B=\cos\phi+r\sin\phi>0.                    \tag{13}
\]
They satisfy
\[
 v^2=q-z^2,\qquad
 \frac{k}{v}=\frac{Q-U}{Uq}+\frac{Vz}{Uqv}.            \tag{14}
\]
The cost derivatives on this surface are
\[
 C_\phi=1-F'(b)v,\qquad C_B=F'(b)k-G'(B).              \tag{15}
\]

One further speed bound is useful. From (12),
\[
 Z=b-\tfrac12-\sin\phi=V\cos\phi-U\sin\phi,\quad
 Y=U\cos\phi+V\sin\phi=\sqrt{Q-Z^2},
\]
and hence
\[
 v=Y-\cos\phi<\sqrt Q-\cos(.7)<1.215.                 \tag{16}
\]
At fixed \(b\), \(v\) increases with \(\phi\), since its derivative is
\(V/Y>0\).

The contact set is compact. Its only boundaries are \(B=0\), \(b=d\),
and \(\phi=.7\): we have excluded \(B=d\), \(b=0\), and \(\phi=0\).
This exact boundary description will be used in both rows.

## 5. The \(L,K\) row: an endpoint-forcing implication

We prove
\[
 C_\phi\le0\quad\Longrightarrow\quad C_B>0.            \tag{17}
\]
By convexity of \(D\) and (11), \(D<.817\) on
\([.293,.755]\). Thus (16) gives \(D v<.817(1.215)<1\)
on that interval. The premise in (17) consequently forces \(b>.755\),
or \(z>.255\), and \(D\ge1/v\). It remains to show
\(k/v>K'(B)\).

For \(B\le.2\), we have \(1.85<U<1.915\). Let
\(q_s=Q+1-2(1.85)\). The function \(U(Q+1-2U)\) decreases on this
range. Equation (14) gives the explicit lower bound
\[
 \frac{k}{v}>
 \frac{Q-1.915}{1.85\,q_s}
 +\frac{(.5)(.255)}{1.915\,q_s\sqrt{q_s}}
 >.928>K'(B).                                        \tag{18}
\]
For \(B\ge.2\), the first summand of (14) is uniformly greater than
\(.84\). Indeed, for every \(U>0\), the quadratic inequality
\[
 Q-U-.84\,U(Q+1-2U)>0
\]
follows by completing the square, because
\[
 Q-\frac{[1+.84(Q+1)]^2}{8(.84)}>0.
\]
In the physical range \(U<1.915,\ q<2.118,\ v<1.456,\ V\ge.7\).
Thus
\[
 \frac{k}{v}>
 .84+\frac{(.7)(.255)}{1.915(2.118)(1.456)}
 >.869>K'(.2)\ge K'(B).                               \tag{19}
\]
Equations (15),(18),(19) prove (17).

At \(b=d\), another strict comparison gives
\[
 \bigl(D(d)v\bigr)^2>
 1.16^2(Q-2a_0-.16)>1,
\]
so \(C_\phi<0\). Increasing \(\phi\) therefore decreases the cost at
this boundary, unless \(\phi=.7\). At that corner, (17) instead permits
decreasing \(B\), which again decreases the cost.

An interior minimum would have \(C_\phi=C_B=0\), contradicting (17).
At \(\phi=.7\), a minimum with \(B>0,b<d\) would have \(C_B=0\)
and \(C_\phi\le0\), again a contradiction. The preceding paragraph excludes
\(b=d\). Every minimum is therefore at \(B=0\).

## 6. The \(L,K\) target-zero boundary

Here
\[
 b_0(\phi)=\tfrac12+\tfrac12\cos\phi-(a_0-\tfrac12)\sin\phi,
 \quad
 v_0=(a_0-\tfrac12)\cos\phi+\tfrac12\sin\phi,
\]
and \(H(\phi)=\phi+L(b_0(\phi))-K(0)\).
When \(b_0\le.755\), equations (11),(14) give
\(H'>1-.817\sqrt{Q-2a_0}>0\).
On the remaining interval \(b_0\ge.755\),
\[
 H''=D'(b_0)v_0^2-D(b_0)(b_0-\tfrac12)
 >1.67(Q-2a_0-.16)-1.176(.4)>1.                       \tag{20}
\]
At the explicit rational point \(\phi_0=.15781\),
\[
 .755<b_0(\phi_0)<d,\quad
 H(\phi_0)>.8977797,\quad |H'(\phi_0)|<.000003.
\]
Strong convexity and completion of the square give
\[
 H>.8977797-\frac{(.000003)^2}{2}>.89777.              \tag{21}
\]
The later increasing portion cannot lower this bound.
This completes the entire \(L,K\) source-secondary row.

## 7. The \(P,J\) row: local coordinates at a possible critical point

We now show that an interior minimum is impossible in the other row.
Use \(b,B\) as local coordinates on (12), solving for \(\phi\).
This is legitimate because \(b_\phi=-v<0\). The cost is
\(\phi(b,B)+P(b)-J(B)\), and
\[
 C_b=P'(b)-1/v,\qquad
 C_B=\frac{k}{v}-J'(B).                               \tag{22}
\]
At a critical point, \(v=1/P'(b)\).

Every such point has \(b>.6\). For \(b\le.6\), equation (16), the
monotonicity of \(v\) in \(\phi\), and \(P''>0\) imply
\[
 P'(b)v\le P'(.6)
 \left[\sqrt{Q-(.1-\sin(.7))^2}-\cos(.7)\right]<1.
\]
In the square root, its argument increases with \(b\le.6\), so the use of
the right endpoint is valid.

Put \(p=P'(b)\) and
\[
 E(b)=P''(b)-(b-\tfrac12)p^3.
\]
On \([.6,.7]\),
\(E'<.45-(.876)^3<0\).
On \([.7,d]\), equation (8) and fixed derivative values give
\[
 E'<.779-(.903)^3-3(.2)(.903)^2(.293)<0.
\]
Also
\[
 E(d)>.043,\quad E(.6)<.187,\quad E(.75)<.124.         \tag{23}
\]
Thus \(E>0\) and decreases throughout the possible critical range.

Stationarity in (22) determines the target coordinate exactly:
\[
 q(b)=(b-\tfrac12)^2+\frac1{p^2},\quad
 U(b)=\frac{Q+1-q(b)}2,\quad
 B(b)=\sqrt{Q-U(b)^2}-\tfrac12.                       \tag{24}
\]
Since \(q'(b)=-2E(b)/p^3<0\), the last function decreases.
Three endpoint evaluations give
\[
 .2<B(b)<.32,\qquad
 B(b)>.242\quad\hbox{if }b\le.75.                     \tag{25}
\]
No critical point has been numerically located or assumed in deriving
these intervals.

## 8. A uniform negative Hessian determinant

Let
\[
 f_1(U)=\frac{Q-U}{U(Q+1-2U)},\quad q=Q+1-2U,\quad r=V/U.
\]
Differentiating (14) at fixed \(b\) gives
\[
 \phi_{BB}=-r f_1'(U)
 +\frac{z}{qv}
       \left(\frac{Q}{U^3}-\frac{2r^2}{q}
                              -\frac{r^2}{v^2}\right),           \tag{26}
\]
\[
 f_1'(U)=
 \frac{4QU-2U^2-Q(Q+1)}{[U(Q+1-2U)]^2}.
\]
On the rectangle (25), \(1.8<U<1.852,\ r>.378,\ .1<z<.4\).
Set
\[
 q_-=Q+1-2(1.852),\qquad q_+=Q+1-2(1.8),
\]
\[
 A_-=\frac{4Q(1.8)-2(1.8)^2-Q(Q+1)}{(1.8\,q_+)^2},
 \qquad
 B_+=\frac{Q}{1.8^3}-\frac{3(.378)^2}{q_+}.
\]
The numerator defining \(f_1'\) increases with \(U\), while \(Uq\)
decreases. Hence \(f_1'>A_->0\).
Since \(v^2=q-z^2\), equation (26) yields
\[
 \phi_{BB}<
 -.378A_-+
 \frac{.4B_+}{q_-\sqrt{q_--.16}}<-.05.                \tag{27}
\]
The displayed \(B_+\) is positive; thus this is a valid upper bound even
when the bracket in (26) is negative.

At a critical point, the Hessian entries in the \((b,B)\) chart are
\[
 C_{bb}=E(b),\qquad C_{bB}=r\,p^3,\qquad
 C_{BB}=\phi_{BB}-J''(B)<.386,                        \tag{28}
\]
using \(J''(.32)>-.436\). Equations (23),(25) and the fixed
radial-slope bounds give the following two complete rows.

| Source interval | Upper bound for \(C_{bb}\) | Lower bound for \(C_{bB}\) | Upper bound for \(C_{BB}\) |
|---|---:|---:|---:|
| \([.6,.75]\) | .187 | \(.404(.876)^3\) | .386 |
| \([.75,d]\) | .124 | \(.378(.918)^3\) | .386 |

In both rows
\[
 C_{bb}C_{BB}-C_{bB}^2<0.                             \tag{29}
\]
A twice differentiable function cannot have a local minimum at an interior
critical point with a negative Hessian determinant. Therefore the minimum
lies on one of the three contact boundaries already listed in Section 4.

## 9. The \(P,J\) target-zero boundary

At \(B=0\), the contact uses the same \(b_0,v_0\) as Section 6 and has
cost \(H_0(\phi)=\phi+P(b_0(\phi))-J(0)\).
For \(\phi\le.3\),
\[
 P'(b_0)v_0<
 .973[.915\cos(.3)+\tfrac12\sin(.3)]<1.
\]
For \(\phi\ge.3\), \(b_0<.708\), so
\(P'(b_0)<.907\), while \(v_0<1.043\); their product is again below one.
Thus \(H_0\) increases.

Its first point has \(b_0=d\), at a unique angle \(\phi_a>.10726\).
The inequality follows by evaluating
\[
 (a_0-\tfrac12)\sin\phi-\tfrac12\cos\phi+d-\tfrac12
\]
at \(.10726\); the expression increases on this interval. Hence
\[
 H_0>.10726+P(d)-J(0)>.8985.                          \tag{30}
\]

## 10. The \(P,J\) source-diagonal boundary

Put \(z_0=d-1/2\). On \(b=d\), the contact has the explicit coordinates
\[
 \begin{gathered}
 Z=z_0-\sin\phi,\quad Y=\sqrt{Q-Z^2},\\
 U=Y\cos\phi-Z\sin\phi=A+\tfrac12,\quad
 V=Y\sin\phi+Z\cos\phi=B+\tfrac12.
 \end{gathered}                                                   \tag{31}
\]
Let
\[
 f=1-\frac{\cos\phi}{Y},\qquad
 f'=\frac{\sin\phi(Q-1-z_0^2)+z_0(1+\sin^2\phi)}{Y^3}.
\]
Direct differentiation gives
\[
 B'=Uf,\qquad B''=-Vf^2+Uf'.                         \tag{32}
\]
The physical branch begins at \(B=0,\phi=\phi_a>.10726\), ends at
\(\phi=.7\) with \(B<d\), and lies in the following six fixed intervals.

| Angle interval | Lower bound for \(B'\) | Upper bound for \(B''\) |
|---|---:|---:|
| \([.107,.2]\) | .915 | .151 |
| \([.2,.3]\) | .914 | .190 |
| \([.3,.4]\) | .919 | .217 |
| \([.4,.5]\) | .924 | .238 |
| \([.5,.6]\) | .924 | .251 |
| \([.6,.7]\) | .924 | .248 |

Each row follows by direct outward substitution in (31),(32), with the
monotone sine and cosine endpoint enclosures; no smaller intervals are
generated. The first interval extends slightly below the physical starting
angle. Only the geometric derivative formulas are bounded there; the
following label inequalities are applied to physical \(B\ge0\).

For \(H_d(\phi)=\phi+P(d)-J(B(\phi))\), equations (9),(32) imply
\[
 H_d''>.329(B'_{\rm lower})^2
                 -1.082(B''_{\rm upper})>.009
\]
in every row. At \(\phi_0=.18909\), exact point evaluations give
\[
 0<B(\phi_0)<d,\quad H_d(\phi_0)>.89777605,\quad
 |H_d'(\phi_0)|<.000001.
\]
Completion of the square gives the global lower bound
\[
 H_d>.89777605-\frac{(.000001)^2}{.018}
             >.89777604>.89777.                      \tag{33}
\]

## 11. The \(P,J\) upper-angle boundary

At \(\phi=.7\), write \(b=b(B,.7)\) from (12). This increases with \(B\),
and
\[
 b_B=k,\qquad b_{BB}=(Q/U^3)\sin(.7)>0.
\]
Therefore
\[
 \frac{d^2}{dB^2}\{.7+P(b(B,.7))-J(B)\}
 =P''k^2+P'(Q/U^3)\sin(.7)-J''>.329.                  \tag{34}
\]
At the explicit rational reference \(B_0=.34621\), the source coordinate
lies strictly between 0 and \(d\), the cost is \(>.89778868\), and the
absolute first derivative is \(<.00001\). Consequently
\[
 C>.89778868-\frac{(.00001)^2}{.658}
             >.89778867>.89777.                      \tag{35}
\]
The reference belongs to the connected feasible boundary interval, so this
strong-convexity estimate applies to the whole boundary.

Sections 9–11 exhaust the \(P,J\) contact boundary. Combined with (29),
they complete its source-secondary row.

## 12. Exact arithmetic and complete scope

The self-contained companion verify_wrong_0011011_same_outer_zero_hand.py
checks 133 strict rational comparisons and writes the corresponding JSON.
It uses exact fractions, integer square roots with denominator \(10^{14}\),
and alternating sine/cosine Taylor bounds at the displayed rational arguments.
The only interval evaluations are the six fixed rows in Section 10.
The two Hessian rows are analytical bounds on the complete stationary curve,
not a sample of critical points.

The two representative rows each cover all four retained separating axes.
Reflected reversal supplies the other two same-sign edge/sign choices.
Thus all \(4\times4=16\) same-sign OO zero-quarter branches are proved, including
every closed endpoint and both physical angle signs.

The asymmetric opposite-sign OO zero rows are proved separately in
WRONG_0011011_ASYMMETRIC_OPPOSITE_OUTER_ZERO_HAND_PROOF.md, and the symmetric
opposite-sign edge-4 row in
WRONG_0011011_SYMMETRIC_OUTER_WHOLE_ANGLE_HAND_PROOF.md.
Together with the completed core/core and mixed-zero notes, every zero-quarter
branch of this word is now covered by hand arguments. The remaining
quarter-one rows still require their separate closure.

