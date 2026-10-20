# Every nonpositive primary at an outer E is already secondary

## 1. Exact same-state statement

Let E be sorted and outer at the **actual common q**, with
\[
 q\le Q=9789/2500<4,\qquad
 a_E\ge |y_E|,\qquad
 (a_E+1/2)^2+(|y_E|+1/2)^2=q.
\tag{1}
\]
Let D,H be their sorted contained anchors at that same q,
with their normal signs D negative and H positive. Write their
nonnegative magnitudes as \((a_D,b_D),(a_H,b_H)\). Thus
\[
 a_i\ge b_i\ge0,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le q\quad(i=D,H).
\tag{2}
\]
The anchors need not be on the outer circle for this lemma.
Put \(h=7/10\) and \(W(v)=(1+\cos v+|\sin v|)/2\).

**Theorem.** For either sign of E and every \(0\le s\le h\),
the following are implications between actual weak witnesses
at their original states and frames:
\[
 DE3\text{ at }-s\ \Longrightarrow\ DE2\text{ at }-s,
\]
\[
 EH1\text{ at }-s\ \Longrightarrow\ EH0\text{ at }-s.
\tag{3}
\]
No state, frame, captured error, cyclic gap, or variation changes.
In particular every selected nonpositive E primary may be
replaced by its secondary while retaining all other witnesses.

This is independent of GA, HG, AB, BT, and TD. It therefore
applies to the reflected positive-BT entry as well as the
original positive-GA entry, without assuming a sign for the
reflected E tangent. The outer equality in (1) is at q, not at
the upper comparison ceiling Q.

## 2. A signed-coordinate comparison with one anchor

Write \(A=a_E\), \(Y=|y_E|\), and let \((a,b)\) be either
anchor in (2). Actual containment implies the exact comparison
\[
 (A-b)(A+b+1)\ge(a-Y)(a+Y+1).
\tag{4}
\]
It follows by subtracting the two shifted squared norms in
(1)--(2) and rearranging. Sorting and \(q<4\) give the simple
strict bounds
\[
                    A,a<3/2,\qquad Y,b<1.
\tag{5}
\]
For example \((A+1/2)^2\le q-1/4<4\), and
\(2(Y+1/2)^2\le q<4<9/2\). The same bounds hold for a,b.

For \(0<s\le h\),
\[
 \tan(s/2)\le\tan(7/20)
 <\frac{7/20}{1-(7/20)^2/2}
 =\frac{280}{751}<\frac25.
\tag{6}
\]
Only \(\sin u<u\) and \(\cos u>1-u^2/2\) are used in (6).

Consider first
\[
 \Delta_-=(A-b)\sin s-(a-Y)(1-\cos s).
\tag{7}
\]
If a at most Y, then \(A\ge Y\ge a\ge b\), so both terms
in (7), as written with their signs, are nonnegative. If a>Y,
(4) gives
\[
 \frac{A-b}{a-Y}
 \ge\frac{a+Y+1}{A+b+1}
 \ge\frac{a+1}{A+a+1}
 >\frac{a+1}{a+5/2}\ge\frac25.
\tag{8}
\]
Together with \(1-\cos s=\sin s\tan(s/2)\), this proves
\[
                             \Delta_-\ge0.
\tag{9}
\]
The inequality is strict in the a>Y case; strictness is not
needed in the other case.

The second comparison is
\[
 \Delta_+=(A-b)\sin s-(a+Y)(1-\cos s).
\tag{10}
\]
Suppose its associated unfavorable primary is feasible:
\[
                         a-A\sin s-Y\cos s\ge W(s).
\tag{11}
\]
Since A at least Y, \(\sin s>1-\cos s\), and \(W(s)>1\),
\[
 a-Y\ge W(s)+A\sin s-Y(1-\cos s)>1.
\tag{12}
\]
In particular \(Y<a-1<1/2\), and hence \(a+Y<2\).
Equation (4) and (5) now give
\[
\begin{split}
 \frac{A-b}{a+Y}
 &\ge\frac{(a-Y)(a+Y+1)}{(a+Y)(A+b+1)}\\
 &>\frac{3/2}{7/2}=\frac37>\frac25.
\end{split}
\tag{13}
\]
Here \(a-Y>1\), \(1+1/(a+Y)>3/2\), and
\(A+b+1<7/2\). Equations (6), (10), and (13) imply
\[
                              \Delta_+>0.
\tag{14}
\]

## 3. Apply the comparisons to the actual two projections

At error −s, the two DE projections are
\[
 \begin{split}
 P_{DE3}&=a_D-A\sin s-y_E\cos s,\\
 P_{DE2}&=a_D\cos s-b_D\sin s-y_E.
 \end{split}
\tag{15}
\]
Their difference is
\[
 P_{DE2}-P_{DE3}
       =(A-b_D)\sin s-(a_D+y_E)(1-\cos s).
\tag{16}
\]
If \(y_E\le0\), this is (7), with the D anchor, and is
nonnegative without any additional feasibility assumption.
If \(y_E\ge0\), it is (10), and the retained DE3 witness
is precisely (11). It is therefore positive for s>0.
Both cases prove the first implication in (3).

At the same negative error, the two EH projections are
\[
 \begin{split}
 P_{EH1}&=a_H-A\sin s+y_E\cos s,\\
 P_{EH0}&=a_H\cos s-b_H\sin s+y_E.
 \end{split}
\tag{17}
\]
Their difference is
\[
 P_{EH0}-P_{EH1}
       =(A-b_H)\sin s-(a_H-y_E)(1-\cos s).
\tag{18}
\]
If \(y_E\ge0\), this is (7), with the H anchor. If
\(y_E\le0\), it is (10), and the actual EH1 witness is
(11). The second implication in (3) follows.

At s=0 the two projections in each pair coincide exactly.
Thus all zero-error weak ties are included. If E is on its
true core instead of outer at q, (4) is unavailable and the
theorem does not assert reselection; genuine negative core
primaries remain in their separate core-E reduction.

Consequently, after same-state reselection at an outer E of
either tangent sign, every retained E primary has strictly
positive error. The remaining choices are both secondary,
sole positive DE3, sole positive EH1, or two positive primaries.
This is the complete nonpositive-error portion of the signed
outer-E owner gate.
