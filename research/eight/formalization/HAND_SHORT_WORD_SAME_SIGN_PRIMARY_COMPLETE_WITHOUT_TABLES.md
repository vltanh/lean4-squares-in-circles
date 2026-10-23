# Three same-sign primary owners, on both whole angle halves

Every terminating decimal in this note is an exact rational. For the
short word 0010111, this proves the complete outer/outer families
\[
 (i,\sigma,\tau,j)=(2,-,-,4),\ (4,-,-,4),\ (6,+,+,2).
\]
The last coordinate is the original one-based separating axis. Every
weak separating contact with \(|\phi-\pi/2|\le.7\) has corrected cost
\(C>.898\), including all state endpoints and simultaneous owners.
There is no near-aligned or complementary angle-table premise.

## 1. Exact normalization

Put
\[
 Q=9789/2500,\quad a(y)=\sqrt{Q-(y+1/2)^2}-1/2,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=a(0),\quad b_0=1-d.
\]
Both states are outer: \(a=a(b),A=a(B),0\le b,B\le d\). Write
\[
 r(y)=\frac{y+1/2}{a(y)+1/2},\qquad a'=-r,\qquad
 r'=Q/(a+1/2)^3.
\]
Exact reflection/reversal of original axis 2 in the last family preserves
the angle and corrected cost. All three cases become
\[
 C=\pi/2+x+c+pa-qb-PA+tB,\qquad
 a+A\sin x+B\cos x\ge W,
\]
\[
 W=(1+\cos x+|\sin x|)/2,\qquad - .7\le x\le.7.
\tag{1}
\]
Their literal adjacent-label tuples \((c,p,q,P,t)\) are
\[
\begin{aligned}
 &(-.53489,.09133,.88074,-.33147,1.1336),\\
 &(-.53062,.19335,.76744,-.20967,.83048),\\
 &(-.20704,0,.94766,-.21826,.83472).
\end{aligned}                                               \tag{2}
\]
The reflection rule on a paired positive-secondary tuple is
\((p,q,P,t)\mapsto(-P,t,-p,q)\), with both signs reversed.
Thus (1) is the stipulated original owner, not a new owner selection.

In primary coordinates the source cost \(M(a)=pa-qb(a)\) satisfies
\[
 M'=p+q\frac{a+1/2}{b+1/2}=:L>0,\qquad
 M''=\frac{qQ}{(b+1/2)^3}>0.
\tag{3}
\]
The target cost increases with \(B\), since
\((-PA+tB)'=t+Pr(B)\ge t+P>0\).
The circle equation gives the bounds
\[
\begin{gathered}
 .899214065109<d<.899214065110,\quad .1<b_0<.101,\\
 1.414575671<a_0<1.414575672,\quad a(b_0)+1/2>1.885,\\
 1.29058126439213<\sqrt{Q-9/4}<1.29058126439214,\quad
 p+q\ge.94766.
\end{gathered}                                               \tag{4}
\]
Every radical bound follows by squaring positive rational endpoints.

## 2. Every aligned contact

At \(x=0\), reduce the source coordinate and then the increasing target
coordinate on any diagonal slack portion. This leaves exactly
\(a+B=1\), \(0\le B\le b_0\), with cost
\[
 H(B)=\pi/2+c+p(1-B)-q\,a(1-B)-P\,a(B)+tB.
\tag{5}
\]
For rows 2 and 3,
\[
 H'=-p-q\frac{1.5-B}{\sqrt{Q-(1.5-B)^2}}+Pr(B)+t
                    \le-p-q+t<0.
\]
Their endpoint minima \(H(b_0)\) exceed .89811 and .89810, respectively.
For row 1,
\[
 H''>\frac{.88074Q}{1.4^3}-\frac{.33147Q}{1.885^3}>1.
\]
At the single reference \(B=517/10000\), direct evaluation gives
\(H(B)-H'(B)^2/2>.89811\). Integrating the curvature bound and
completing a square proves, for every row and every aligned state,
\[
                              H(B)>.8981.
\tag{6}
\]

Set \(\eta=1/80\). Each \(H\) decreases on \([0,\eta]\).
For row 1 this follows from \(H''>0\) and \(H'(\eta)<0\); for the
other rows it was just proved. The three values \(H(\eta)\) exceed
.89908, .91962, and .91937, respectively. In particular,
\[
                         H(B)>.89908\quad(0\le B\le\eta).
\tag{7}
\]
These are evaluations of (5), not a cover of its variable domain.

## 3. The complete negative half

Write \(x=-u\), \(0\le u\le.7\), \(s=\sin u,k=\cos u\).
The unclamped least source coordinate is
\[
 a_c=1/2+(1/2-B)k+(A+1/2)s.
\tag{8}
\]
First choose \(a=\max(d,a_c)\). On any remaining slack portion at
\(a=d\), reduce \(B\), decreasing cost, until contact. It reaches
contact before \(B=0\), because \(a_c(0,u)\ge a_c(0,0)=1>d\);
this last contact height increases with \(u\) on the whole range.
Thus every minimum is represented by an active contact (8).

Its speed is positive:
\[
 (a_c)_u=(A+1/2)k+(B-1/2)s
                 >1.399(.764)-.5(.645)>0.
\]
The exact circle identity retains both state coordinates:
\[
 [(a_c)_u]^2=Q-2B-(a-1/2)^2>Q-1.8-.915^2.
\]
Since \(L\ge p+q\ge.94766\), the single rational comparison
\[
 .94766^2(Q-1.8-.915^2)>1
\]
proves on every active contact
\[
                         C_u=-1+L(a_c)_u>0.
\tag{9}
\]
Decreasing \(u\) at fixed \(B\) stays on the original contact and
reduces cost until alignment or the source diagonal. An axial or
diagonal target endpoint is included in this motion; a source-axis
endpoint immediately moves into the outer arc.

### 3.1. The entire source-diagonal curve

Put \(k_0=1/2-d<0\) and
\[
 Z=k+k_0,\quad Y=\sqrt{Q-Z^2},\quad
 U=Yk-Zs,\quad V=Ys+Zk,\quad B=V-1/2.
\]
These are the target coordinates on \(a=b=d\), since
\(Vk-Us=k+k_0\), \(U^2+V^2=Q\). The physical curve starts at
\(u=0,B=b_0\) and ends at the unique \(u_*\) with \(B=d\).
Equivalently, \(u_*\) is the unique zero of
\[
 1/2+(1/2-d)\cos u+(d+1/2)\sin u-d.
\]
Its derivative is positive on \([0,.7]\). The two endpoint signs give
\[
                              .5558<u_*<.5559.
\tag{10}
\]
Let \(f=1-s/Y\). Direct differentiation gives
\[
 U'=-Vf,\quad V'=Uf,\quad
 f'=\frac{(1-Q+k_0^2)k+k_0(1+k^2)}{Y^3}<0.
\]
Also \(f>0\), because \(Y^2-s^2=Q-1-2k_0k-k_0^2>0\).
On the physical arc, \(U\ge V>0\) and \(tU+PV\ge(t+P)U>0\).
Its cost
\[
 E(u)=\pi/2-u+c+(p-q)d-P(U-1/2)+t(V-1/2)
\]
therefore has
\[
 E''=(PU-tV)f^2+(tU+PV)f'<0.
\tag{11}
\]
The minimum is at an endpoint. At zero it is (6). At the other endpoint,
\[
 E(u_*)=\pi/2-u_*+c+(p-q-P+t)d>.9025
\tag{12}
\]
for every tuple (2), using \(\pi/2>1.570795\), (4), and (10).
Equations (6), (9), and (11)--(12) prove the whole negative half.

## 4. The complete positive half

For \(0\le x\le.7\), the unclamped contact is now
\[
 a_c=1/2+(1/2-B)\cos x-(A-1/2)\sin x.
\tag{13}
\]
Choose \(a=\max(d,a_c)\). A diagonal slack portion reduces in cost
by decreasing \(B\) until contact or \(B=0\).
The contact is strictly decreasing in \(B\), since
\((a_c)_B=-\cos x+r(B)\sin x<0\).
If \(B\ge1/2\), it is below \(d\). If \(B\le1/2\), then
\(a_c\le1-B\). Thus every active contact has
\[
                     0\le B\le b_0,\qquad d\le a_c\le1.
\]
It can occur only before the unique axial/diagonal event \(x_a\):
\[
 1/2+(1/2)\cos x_a-(a_0-1/2)\sin x_a=d,\qquad
 .1072<x_a<.1073<.108.
\tag{14}
\]
The defining function decreases, and the two rational point signs prove
the bracket. After this event, the least source is diagonal for every
target; the least target is axial, and that cost increases with slope 1.
This accounts for the entire rest of the original angle range.

### 4.1. Uniform contact curvature

Set \(u=a_c+1/2,v=b+1/2\), and
\[
 h=-(a_c)_x=(A-1/2)\cos x+(1/2-B)\sin x>0.
\]
Then
\[
 C_x=1-Lh,\qquad
 C_{xx}=qQh^2/v^3-L(u-1).
\tag{15}
\]
Over the whole active domain, \(1.29<v<1.4\), \(u\le1.5\),
\(L<.19335+.94766(1.5)/1.29<1.3\), and \(h>.879\).
For the last bound use \(A-1/2>.885\), \(x<.108\), and
\(\cos(.108)>.994\). Hence one global curvature estimate is
\[
 C_{xx}>\frac{.76744Q(.879)^2}{1.4^3}-.65>.19.
\tag{16}
\]
At zero its angle derivative equals
\[
 e(B)=1-
 \left[p+q\frac{1.5-B}{\sqrt{Q-(1.5-B)^2}}\right]
                   (a(B)-1/2).
\tag{17}
\]
Both positive factors subtracted in (17) decrease with \(B\), so
\(e\) increases strictly. Direct evaluation gives in every row
\[
                              e(0)>-.02,\qquad e(1/80)>0.
\tag{18}
\]
If \(e(B)\ge0\), (16) makes the cost increase from alignment, covered
by (6). If \(e(B)<0\), (18) forces \(B<1/80\), and (7) applies.
Integration and a single square completion give
\[
 C(B,x)>H(B)-\frac{.02^2}{2(.19)}
             >.89908-\frac{.0004}{.38}>.89802.
\tag{19}
\]
At fixed \(B\), the entire segment from zero to an active angle stays
in \(d\le a_c\le1\), since (13) decreases from \(1-B\). After it
reaches the source diagonal, the actual clamped cost has derivative 1.
Thus this continuation cannot reduce the bound (19).
These are the two signs of the actual initial angular derivative,
not a target-coordinate partition.

## 5. Scope and arithmetic

Sections 2--4 prove all six original angle halves named at the start.
No theorem from the historical near-aligned note or its scalar-table tails
is used. Every deformation keeps its stipulated weak original separator,
so axis ties and all closed coordinate endpoints remain covered.

The point comparisons have explicit inputs (2), (5), (14), and (17).
Positive square comparisons prove the radical bounds; alternating Taylor
inequalities prove the event brackets and fixed trigonometric values.
Machin's identity supplies the rational bounds for \(\pi/2\).
The continuous inequalities are the circle speed (9), whole-curve
concavity (11), and uniform angular curvature (16). The only interior
reference is the row-1 aligned comparison following (5).
No verification-program result, continuous mesh, or coefficient-sign
table is a premise of this proof.
