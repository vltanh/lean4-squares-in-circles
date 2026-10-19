# The three remaining same-sign primary owners, on both whole angle halves

All terminating decimals in this note are exact rationals. This proves the
complete outer/outer families

\[
 (i,\sigma,\tau,j)=(2,-,-,4),\ (4,-,-,4),\ (6,+,+,2)
\]

of the short word 0010111. The last coordinate is the **original one-based
separating axis**. For every weak separating contact and every
\(|\phi-\pi/2|\le .7\), the original corrected cost is greater than .898.
In particular it exceeds both required assembly thresholds .8975 and .89765.
No near-aligned interval table or complementary scalar table is used.

The proof treats each entire angle half. On the negative half, a circle-speed
identity moves every active contact to alignment or the source diagonal;
the latter is one strictly concave curve. On the positive half, the actual
contact domain ends at an axial/diagonal event; one uniform angular curvature
bound controls the possible initial loss before that event.

## 1. Exact normalization and labels

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a(y)=\sqrt{Q-(y+1/2)^2}-1/2,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=a(0),\quad b_0=1-d.
\]
Both outer states have primary/secondary coordinates \((a,b)\), \((A,B)\),
where \(a=a(b), A=a(B)\) and \(0\le b,B\le d\). Write
\[
 r(y)=\frac{y+1/2}{a(y)+1/2},\qquad
 a'=-r,\qquad r'=\frac{Q}{(a+1/2)^3}.
\]
The exact reflection/reversal of original axis 2 in the last family leaves
the angle and corrected cost unchanged. All three cases then have the form
\[
 C=\pi/2+x+c+pa-qb-PA+tB,
 \qquad a+A\sin x+B\cos x\ge W,
 \quad W=\frac{1+\cos x+|\sin x|}{2}.                     \tag{1}
\]
Their coefficient tuples \((c,p,q,P,t)\), respectively, are
\[
\begin{aligned}
 &(-.53489,\ .09133,\ .88074,\ -.33147,\ 1.1336),\\
 &(-.53062,\ .19335,\ .76744,\ -.20967,\ .83048),\\
 &(-.20704,\ 0,\ .94766,\ -.21826,\ .83472).
\end{aligned}                                             \tag{2}
\]
These are the literal affine label differences in short_hand_labels.json.
For the reflected case, the rule on a positive-secondary tuple is
\((p,q,P,t)\mapsto(-P,t,-p,q)\), with both signs reversed.
Thus (1) is the stipulated original owner, not a newly selected separator.

In primary coordinates the source cost \(M(a)=pa-qb(a)\) has
\[
 M'(a)=p+q\frac{a+1/2}{b+1/2}=:L>0,\qquad
 M''(a)=\frac{qQ}{(b+1/2)^3}>0.                            \tag{3}
\]
The target cost \(-PA+tB\) increases strictly with \(B\), since its
 derivative is \(t+Pr(B)\ge t+P>0\).

The elementary radical bounds used below are
\[
\begin{gathered}
 .899<d<.9,\quad .1<b_0<.101,\quad a_0<1.415,\\
 a(b_0)+1/2>1.885,\quad
 \sqrt{Q-9/4}>1.29,\quad p+q\ge .94766.
\end{gathered}                                             \tag{4}
\]
For reproducible point comparisons one may use
\[
\begin{gathered}
1.414575671<a_0<1.414575672,\\
.899214065109<d<.899214065110,\\
1.29058126439213<\sqrt{Q-9/4}<1.29058126439214.
\end{gathered}
\]
They follow by squaring positive rational endpoints.

## 2. All aligned contacts

At \(x=0\), minimizing (1) first in \(a\), then in the increasing target
coordinate on any source-diagonal slack portion, leaves exactly
\(a+B=1\), \(0\le B\le b_0\). Its cost is
\[
 H(B)=\pi/2+c+p(1-B)-q\,a(1-B)-P\,a(B)+tB.                 \tag{5}
\]
For rows 2 and 3 of (2),
\[
 H'=-p-q\frac{1.5-B}{\sqrt{Q-(1.5-B)^2}}+Pr(B)+t
 \le -p-q+t<0.
\]
Their two minimum values \(H(b_0)\) are respectively greater than .89811
and .89810.

For row 1,
\[
 H''=\frac{qQ}{[a(1-B)+1/2]^3}
                  +\frac{PQ}{[a(B)+1/2]^3}
 >\frac{.88074Q}{1.4^3}-\frac{.33147Q}{1.885^3}>1.
\]
At the single rational reference \(B=517/10000\), direct substitution gives
\[
 H(B)-\frac{H'(B)^2}{2}>.89811.
\]
Integrating the preceding lower curvature bound and completing a square
therefore proves, for every row,
\[
                         H(B)>.8981.                      \tag{6}
\]

We record two further fixed comparisons for the positive half. Let
\(\eta=1/80\). Each \(H\) decreases on \([0,\eta]\), and
\[
                         H(\eta)>.89908.                  \tag{7}
\]
For row 1 the decrease follows from \(H''>0\) and \(H'(\eta)<0\);
for the other rows it was just proved. The three values of \(H(\eta)\)
exceed .89908, .91962, and .91937, respectively. All these comparisons
are direct evaluations of (5), not a continuous-domain cover.

## 3. The whole negative half

Write \(x=-u\), \(0\le u\le .7\), and \(s=\sin u,k=\cos u\).
The least source primary coordinate before imposing \(a\ge d\) is
\[
 a_c=\frac12+(\tfrac12-B)k+(A+\tfrac12)s.                  \tag{8}
\]
At fixed \(B,u\), reduce the source to \(a=\max\{d,a_c\}\).
If this leaves strict separation at \(a=d\), reduce \(B\) until contact.
This always reaches contact before \(B=0\), because
\(a_c(0,u)\ge a_c(0,0)=1>d\). Here \(a_c(0,u)\) increases on
\([0,.7]\). Thus it suffices to bound the active contacts (8).

Their speed is positive:
\[
 (a_c)_u=(A+\tfrac12)k+(B-\tfrac12)s
 >1.399(.764)-\tfrac12(.645)>0.
\]
More importantly, the exact circle identity gives
\[
 [(a_c)_u]^2=Q-2B-(a-\tfrac12)^2
                   >Q-1.8-.915^2.
\]
Together with (3)--(4), this gives **on every active contact in the
entire negative half**
\[
 L^2[(a_c)_u]^2>.94766^2(Q-1.8-.915^2)>1,
 \qquad C_u=-1+L(a_c)_u>0.                                 \tag{9}
\]
Decreasing \(u\) at fixed \(B\) consequently decreases the cost and stays
on its original feasible contact until alignment or \(a=d\).
An axial or target-diagonal endpoint of the target arc is included in
this same motion. The upper source endpoint also immediately enters the
arc under this motion; it introduces no additional minimum.

### 3.1. The complete source-diagonal contact is concave

Put \(k_0=1/2-d<0\), and define
\[
 Z=k+k_0,\quad Y=\sqrt{Q-Z^2},\quad
 U=Yk-Zs,\quad V=Ys+Zk,\quad B=V-1/2.
\]
These are the target coordinates on \(a=b=d\):
\(Vk-Us=k+k_0\) and \(U^2+V^2=Q\).
The physical contact starts at \(u=0,B=b_0\) and ends at the unique
\(u=u_*\) where \(B=d\). The contact height increases strictly in \(u\),
and substitution gives
\[
                         .5558<u_*<.5559.                 \tag{10}
\]
Equivalently, \(u_*\) is the unique zero of
\(\tfrac12+(	frac12-d)\cos u+(d+\tfrac12)\sin u-d\).
Its derivative is positive on \([0,.7]\), so the two point signs suffice.

Set \(f=1-s/Y\). Direct differentiation gives
\[
 U'=-Vf,\qquad V'=Uf,\qquad
 f'=\frac{(1-Q+k_0^2)k+k_0(1+k^2)}{Y^3}<0.                 \tag{11}
\]
Moreover \(f>0\), since
\(Y^2-s^2=Q-1-2k_0k-k_0^2>0\).
Along this entire physical curve, \(U\ge V>0\), and
\(tU+PV\ge(t+P)U>0\).
Its cost is
\[
 E(u)=\pi/2-u+c+(p-q)d-P(U-1/2)+t(V-1/2),
\]
so
\[
 E''=(PU-tV)f^2+(tU+PV)f'<0.                               \tag{12}
\]
Thus its minimum is at an endpoint. At zero it is the aligned value
\(H(b_0)>.8981\). At \(u_*\), its value is
\[
 \pi/2-u_*+c+(p-q-P+t)d>.9025                              \tag{13}
\]
for each of the three exact tuples. The weaker bound
\(\pi/2>1.570795\) and the upper bound in (10) already prove (13).

Equations (6), (9), and (12)--(13) exhaust the active contact and all
its boundaries. Therefore every original negative-half owner has
\(C>.8981\), with no short-angle or tail restriction.

## 4. The whole positive half

Write \(x\ge0\). Now
\[
 a_c=\frac12+(\tfrac12-B)\cos x-(A-\tfrac12)\sin x.        \tag{14}
\]
As before choose \(a=\max\{d,a_c\}\). On a source-diagonal slack
portion, reducing \(B\) decreases cost until contact or \(B=0\).
Thus it is enough to handle active contacts and the clamped axial
boundary after those contacts end.

The contact function is strictly decreasing in \(B\), because
\((a_c)_B=-\cos x+r(B)\sin x<0\) on \([0,.7]\).
If \(B\ge1/2\), (14) is at most \(1/2<d\) and hence inactive.
If \(B\le1/2\), then \(a_c\le1-B\).
Consequently every active contact satisfies
\[
 0\le B\le b_0,\qquad d\le a_c\le1.
\]
Its angle cannot exceed the unique axial/diagonal event \(x_a\) where
\[
 \tfrac12+\tfrac12\cos x_a-(a_0-\tfrac12)\sin x_a=d,
 \qquad .1072<x_a<.1073<.108.                              \tag{15}
\]
The left side decreases strictly, and its point signs at .1072 and
.1073 prove the bracket. For larger angles every least-source state
is clamped at \(a=d\), and its least target is \(B=0\); that cost
increases with slope 1. The entire original angle range beyond the
contact event is therefore accounted for, not discarded.

### 4.1. One angular curvature estimate on the entire contact domain

Put \(u=a_c+1/2, v=b+1/2\), and
\[
 h=-(a_c)_x=(A-\tfrac12)\cos x+(\tfrac12-B)\sin x>0.
\]
Then
\[
 C_x=1-Lh,\qquad
 C_{xx}=\frac{qQh^2}{v^3}-L(u-1).                          \tag{16}
\]
Throughout this domain,
\[
 1.29<v<1.4,\quad h>.879,\quad u\le1.5,\quad
 L<.19335+.94766(1.5)/1.29<1.3.
\]
For the speed bound, use \(A-1/2>.885\), \(x<.108\), and
\(\cos(.108)>.994\). Since \(q\ge.76744\), (16) gives uniformly
\[
 C_{xx}>\frac{.76744Q(.879)^2}{1.4^3}-.65>.19.             \tag{17}
\]

At zero its angular derivative is
\[
 e(B)=1-
 \left[p+q\frac{1.5-B}{\sqrt{Q-(1.5-B)^2}}\right]
 (a(B)-1/2).                                               \tag{18}
\]
Both positive factors subtracted in (18) decrease with \(B\), so
\(e\) increases strictly. Direct substitution into (18) gives for
all three tuples
\[
                        e(0)>-.02,\qquad e(1/80)>0.        \tag{19}
\]

If \(e(B)\ge0\), (17) shows that the cost increases from its aligned
value. If \(e(B)<0\), monotonicity and (19) force \(B<1/80\), and
(7) gives \(H(B)>.89908\). Integrating (17) from alignment and
completing one square now proves
\[
 C(B,x)>H(B)-\frac{.02^2}{2(.19)}
          >.89908-\frac{.0004}{.38}>.89802.                 \tag{20}
\]
The integration is valid on the whole segment from zero to the active
angle: at fixed \(B\), (14) decreases from \(1-B\) to its current
value in \([d,1]\). After it reaches \(d\), the actual clamped cost
has derivative 1 and cannot undo this bound.
The two alternatives above are the sign of the actual initial
angular derivative, not a table of target-coordinate intervals.

Equations (6), (15), and (17)--(20) prove \(C>.898\) on the whole
positive half, including the clamped axial ray and its transition.

## 5. Arithmetic, scope, and dependency substitution

The fixed comparisons in this note involve only the three coefficient
tuples (2), the displayed radicals, (5), and (18). Radical brackets
are checked by squaring positive rationals. Sine and cosine at the
four event-bracketing points use alternating Taylor inequalities;
Machin's identity supplies the stated rational lower bound for \(\pi/2\).
The only interior reference is the aligned row-1 strong-convexity
comparison following (5). No program result or sampled minimum is an
input to the argument.

This replaces **all six angle halves** of the three same-sign original
primary owners named at the start. In particular neither Section 3 of
SHORT_WRONG_WORD_OUTER_QUARTER_ALIGNED_HAND_PROOF nor their complementary
rows in SHORT_WRONG_WORD_OUTER_QUARTER_SCALAR_HAND_PROOF is needed.
All deformations preserve the stipulated original separator. Closed
state endpoints, weak separation, both copies of alignment, and
simultaneous feasible owners are included. The three companion
same-sign secondary owners are separate obligations.
