# A whole quarter-turn strip for the mixed edge-2 transitions of 0011011

## Statement and dependencies

Use the exact states and labels of
\`WRONG_0011011_ALIGNED_MIXED_QUARTER_HAND_PROOF.md\`. This note proves
\[
 \phi-L_2^-(a,b)-\tau L_3^\tau(A,B)>.89765
\tag{1}
\]
for **every mixed core/outer edge-2 pair**, both target signs
\(\tau=\pm1\), all four retained true separating axes, and
\[
 |\phi-\pi/2|\le1/50.
\tag{2}
\]
Reflection followed by source/target reversal gives the corresponding
edge-6 transitions. The aligned theorem is a prerequisite; no
nonaligned numerical result is used. The companion checker performs
146 fixed rational comparisons, including the 85 aligned comparisons.

This is a closed strip, not a proof of the remaining angles
\(\pi/2-.7\le\phi<\pi/2-.02\) and
\(\pi/2+.02<\phi\le\pi/2+.7\).

Write
\[
 e=\phi-\pi/2,\quad u=\sin e,\quad v=\cos e,\quad
 W=(1+v+|u|)/2.
\]
Throughout the strip,
\[
 |u|\le.02,\quad .9998\le v\le1,\quad 1\le W\le1.01.
\tag{3}
\]
The sine estimate follows from \(|\sin e|\le|e|\), and the cosine
estimate from \(1-\cos e\le e^2/2\). Let \(c=7/12\).
For an outer state use
\[
 a=a(b),\quad r=-a',\quad
 .261<r\le1,\quad .899<d<.9,\quad a(0)<1.415.
\]
The source outer label and its derivative are
\[
 L=.02478+.93015b+.02363b^2-.11055ab,\qquad
 L'=.93015+.04726b-.11055(a-rb).
\]
The aligned proof establishes
\[
 L'>.773,\quad L'<1.073,\quad
 .972<L'/r<3.
\tag{4}
\]
For the ratio bounds, use its strict decrease on the outer arc:
at the diagonal \(L'/r=.93015+.04726d>.972\), and at the axis
\((.93015-.11055a(0))/r(0)<3\).

Whenever a core target is on its side, write
\[
 C_3^+=-.01449+1.0424B,\qquad
 C_3^-=c_-+.98439B-.05334B^2,\quad
 c_-=.22042-.34492c.
\]
Their derivatives \(g_\tau\) satisfy
\[
 .97<g_\tau\le1.0424
 \quad\text{if }0\le B<.13,
\tag{5}
\]
and \(g_+=1.0424\) for the entire side.

## 1. Outer source, core target: reduction to side contacts

The source sign is negative. In the present coordinates the four
retained separating projections minus their required width are
\[
\begin{array}{c|l}
1&-b+A v+\tau B u-W\\
2&a u-bv+A-W\\
3&a v+b u-\tau B-W\\
4&a+A u-\tau Bv-W.
\end{array}
\tag{6}
\]
For axes 1 and 2 the respective upper bounds
\(c+c_C(.02)-1<0\) and \(1.415(.02)+c-1<0\)
make separation impossible.

It remains to treat axes 3 and 4. Along the core boundary
\(-1\le A'\le0\). Both unsigned target labels increase there.
For \(\tau=+1\), increase \(B\); this decreases cost and decreases
the selected projection. It must reach contact before the core diagonal:
the projection at that diagonal is negative. For \(\tau=-1\), decrease
\(B\); this decreases cost and also decreases the selected projection.
It reaches contact unless \(B=0\) is reached first. In the latter event,
increase outer \(b\): cost decreases because \(L'>0\), and the selected
projection decreases because
\(-rv+u<0\) for axis 3 and \(a'=-r<0\) for axis 4.
At outer \(b=d\), its projection with \(B=0\) is negative. Thus a
contact is reached in either event.

Every such contact lies on the core side. From (3) and (6),
\[
\begin{array}{c|cc}
&\tau=+1&\tau=-1\\ \hline
\text{axis 3}&B<1.415+.9(.02)-1<.5&
 B\le1.01-.899(.9998)+.9(.02)<.13\\
\text{axis 4}&
 Bv\le1.415+c(.02)-1<.5(.9998)&
 Bv\le1.01-.899+c(.02)<.13(.9998).
\end{array}
\tag{7}
\]
The preceding slack reduction is therefore complete. It suffices to
bound side contacts \(A=c\). Notice that (7) also rules out an upper-side
endpoint during any contact deformation within the strip.

### 1.1. Axis 3, fixed outer state

On either open half of the strip set \(\epsilon=\operatorname{sign}(e)\).
The contact equation is
\[
 \tau B=F(e):=(a-\tfrac12)v+
                 (b-\tfrac{\epsilon}{2})u-\tfrac12.
\]
With outer \(b\) fixed, the contact cost satisfies
\[
 C_e=1-g_\tau F_e,\qquad
 F_e=-(a-\tfrac12)u+
                   (b-\tfrac{\epsilon}{2})v.
\tag{8}
\]

For \(e>0\), \(F_e\le\max(b-1/2,0)\le.4\), hence
\(C_e\ge1-1.0424(.4)>0\).

For \(e<0\), \(F_e\ge(b+1/2)v\).
If \(\tau=-1\), the nonnegative contact coordinate requires
\(av+bu\le W\). Therefore
\(a\le(1.01+.9(.02))/.9998<1.029\), which forces \(b>.75\):
the circle equation at \(b=.75\) gives \(a>1.03\).
Using (5),
\[
 g_-F_e>.97(1.25)(.9998)>1,
\]
so \(C_e<0\).
If \(\tau=+1\) and \(b\ge.49\), then
\[
 g_+F_e\ge1.0424(.99)(.9998)>1,
\]
again giving \(C_e<0\).

The remaining positive-target states have \(b\le.49\). For either sign
of \(e\), the formula for \(F\) gives \(B=F\le a-1\).
Their cost is consequently at least the aligned positive-target contact
cost at the same \(b\), minus .02. That aligned contact cost decreases
on \(0\le b\le b_0\), by the ratio comparison \(L'/r>1.0424\) from the
aligned proof. At \(b=.49\), direct radical substitution gives a
value greater than .942. Thus all these states have cost
greater than \(.942-.02>.89765\).

For every other interior side contact, moving \(e\) toward zero strictly
decreases cost by (8).

### 1.2. Axis 4, fixed outer state

Here
\[
 \tau B=F(e):=\frac{a-1/2}{v}-\frac12+
                    (c-\epsilon/2)\tan e,
\]
so
\[
 F_e=\frac{(a-1/2)u+c-\epsilon/2}{v^2},\qquad
 C_e=1-g_\tau F_e.
\tag{9}
\]
For \(e>0\),
\[
 F_e\le\frac{.915(.02)+1/12}{.9998^2}<.102,
\]
so \(C_e>0\). For \(e<0\),
\[
 F_e\ge13/12-.915(.02)>1.065,
\]
and (5) gives \(g_\tau F_e>.97(1.065)>1\), so \(C_e<0\).

Again, moving \(e\) toward zero decreases cost as long as \(B\ge0\).

### 1.3. Continuing through the endpoint \(B=0\)

If a fixed-outer-state deformation reaches \(B=0\), continue on the
unique zero-core-coordinate contact by varying outer \(b\). This
continuation exists for the full strip and does not leave the outer arc.

For axis 3, its equation is
\[
 av+bu=W.
\tag{10}
\]
The left side minus \(W\) is positive at outer \(b=0\), negative at
outer \(b=d\), and its derivative in \(b\) is \(-rv+u<0\). Hence (10)
has exactly one outer solution for each \(e\). Its bounds are
\[
 .982<a<1.029,\quad .75<b<.83,\quad .817<r<.9.
\tag{11}
\]
The first two \(a\)-bounds follow by (3); the \(b\)-bounds then follow
from the circle equation, and the \(r\)-bounds from its defining ratio.

Implicit differentiation gives
\[
 b_e=\frac{-(a-1/2)u+(b-\epsilon/2)v}{rv-u},
 \qquad C_e=1-L'b_e.
\]
For \(e<0\), the numerator is at least \(1.25(.9998)\), while the
denominator is at most .92. Therefore
\[
 L'b_e>.773(1.25)(.9998)/.92>1.
\]
For \(e>0\), the numerator is at most .33 and the denominator is greater
than \(.817(.9998)-.02\). Consequently
\[
 L'b_e<
 \frac{1.073(.33)}{.817(.9998)-.02}<1.
\]
The cost again decreases toward zero.

For axis 4, the zero-coordinate contact is explicit:
\[
 a=W-cu=\tfrac12+\tfrac12v+(\epsilon/2-c)u.
\]
It lies strictly between the diagonal and axis outer coordinates, by
(3). Its cost derivative is
\[
 C_e=1+(L'/r)a_e,\qquad
 a_e=-\tfrac12u+(\epsilon/2-c)v.
\]
For \(e>0\), \(a_e\ge-.01-1/12\), and (4) gives \(C_e>0\).
For \(e<0\),
\[
 a_e\le.01-(13/12)(.9998),\qquad
 C_e<1-.972[(13/12)(.9998)-.01]<0.
\]
This continuation also decreases cost toward zero.

All admissible contact paths therefore reach either an already
excluded small-\(b\) regime or an aligned state with no increase in
cost. The aligned theorem proves (1) for both outer-to-core signs.

## 2. Core source, outer target

The negative core-source label is
\[
 C_2^-=\ .00125+g_0b,\qquad g_0=1.03981.
\]

### 2.1. Negative outer target

The direct bounds from the aligned proof give
\(C_2^-<.583\) and \(O_3^-\ge.01670\). Therefore, throughout the strip,
\[
 \phi-C_2^-+O_3^-
 \ge3.14159/2-.02-.583+.01670>.89765.
\tag{12}
\]
No separating-axis condition is needed.

### 2.2. Positive outer target: all contacts are on the side

The target label is
\[
 O_3^+(A,B)=-.01025A+.16031B+.63457AB.
\]
Axes 3 and 4 have respective upper bounds
\(c+c_C(.02)-1<0\) and \(c+1.415(.02)-1<0\).
For axis 1 a feasible pair satisfies
\[
 b\le Av+Bu-W\le1.415+.9(.02)-1<.5.
\]
For axis 2,
\[
 bv\le A+au-W\le1.415+c(.02)-1<.5(.9998).
\]
Hence every feasible source state is on the core side, \(a=c\).
Increasing \(b\) decreases cost and reaches the selected contact before
the side endpoint. It therefore suffices to consider side contacts.

For axis 1, with the outer target fixed,
\[
 b=(A-\tfrac12)v+(B-\epsilon/2)u-\tfrac12,
\]
and its cost derivative is the formula (8) with \(g_\tau\) replaced by
\(g_0\) and \((a,b)\) there replaced by \((A,B)\).
On the positive half it is positive. On the negative half it is negative
whenever \(B\ge.462\), because
\[
 1.03981(.962)(.9998)>1.
\tag{13}
\]

For \(B\le.462\), the aligned contact function \(H_2(B)\) from the
aligned proof satisfies \(H_2''>.5\) and \(H_2'(.462)<0\).
It is thus decreasing up to .462, and radical evaluation gives
\(H_2(.462)>.9093\). On the negative half the contact derivative is at
most
\[
 1-g_0(B+1/2)v\le1-g_0(.5)(.9998)<.481.
\]
Integration from \(e=0\) therefore gives
\[
 C(e)\ge H_2(B)-.02(.481)
       >.9093-.00962>.89765.
\tag{14}
\]
The positive half increases cost, so (14) covers it as well.

For axis 2 the contact equation is
\[
 b=(A-\tfrac12)/v-\tfrac12+(c-\epsilon/2)\tan e.
\]
The derivative calculation (9) applies with \(g_0\). The same bounds
\(F_e<.102\) for the positive half and \(F_e>1.065\) for the negative
half prove that its cost decreases toward the aligned state.

### 2.3. The endpoint \(b=0\)

If one of these fixed-target contact paths reaches \(b=0\) before
\(e=0\), it may stop there. The target label increases on the outer arc:
\[
 (O_3^+)'=.01025r+.16031+.63457(A-rB)>.16031,
\]
because \(A\ge B\) and \(r\le1\).
At the diagonal its exact value is
\[
 O_3^+(d,d)=.15006d+.63457d^2<.64805.
\]
Thus every zero-source-coordinate endpoint throughout the strip has
\[
 C>\ 3.14159/2-.02-.00125-.64805>.89765.
\tag{15}
\]
There is no upper-side endpoint by the bounds in section 2.2.
The deformation hence reaches either (15), (14), or an aligned state,
all of which establish (1).

## 3. Scope accounting

Outer-to-core transitions use the two possible separating axes 3 and 4;
axes 1 and 2 are impossible. Core-to-positive-outer transitions use
axes 1 and 2; axes 3 and 4 are impossible. Core-to-negative-outer
transitions use a direct bound independent of the axis.
Every core side and corner state is included before the exact
monotonic contact reduction; no core corner is silently discarded.

Together with the already proved aligned theorem this closes every
mixed edge-2 sign/owner branch on the full strip (2). The two remaining
nonaligned angle ranges are explicitly outside this result.
