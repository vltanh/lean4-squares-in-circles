# A diagonal-center exclusion at squared radius 17/4

**Status:** complete hand proof of the local lemmas stated here. These
lemmas do not by themselves settle the unrestricted nine-square theorem.
They allow arbitrary orientations and physical interior-disjointness.
Written against PR #11 head `6b235bda64b1064a89835eeef8b18634e213a061`.
No Lean compilation or CI has been run.

Let

\[
D=\{(x,y):x^2+y^2\le17/4\},\qquad
E=[1,2]\times[-1/2,1/2],\qquad W=-E.
\]

## 1. Exact corner formula and center bound

Write a closed unit square as

\[
T=c+[-1/2,1/2]u+[-1/2,1/2]v,
\]

where \(u,v\) are an orthonormal frame. Its farthest corner has squared
norm

\[
F(T)=|c|^2+\frac12+|c\cdot u|+|c\cdot v|.                 \tag{1}
\]

Consequently \(T\subset D\) is equivalent to \(F(T)\le17/4\).
The inequality
\(|c\cdot u|+|c\cdot v|\ge|c|\) gives

\[
|c|^2+|c|+\frac12\le\frac{17}{4},
\qquad\text{hence}\qquad |c|\le\frac32.                  \tag{2}
\]

Every unit square contains the open disk of radius \(1/2\) centered
at its center. Physical nonoverlap with a fixed closed square therefore
requires distance at least \(1/2\) from the center to that fixed square.

## 2. Two unavoidable points for a diagonal center

**Lemma 1.** If \(T\subset D\) has center \(c=(x,y)\) with
\(x\ge1\) and \(y\ge1\), then both

\[
p=(1,1/2),\qquad p'=(1/2,1)
\]

belong to the open interior of \(T\).

**Proof.** Put \(x=1+s\), \(y=1+t\), where \(s,t\ge0\). Let
\(a\ge b\ge0\) be the absolute coordinate magnitudes of a side axis;
then \(a^2+b^2=1\) and \(a\ge1/\sqrt2\). Reflections and quarter-turns
of the frame leave its square unchanged. Thus its corner-support sum

\[
L(c)=|c\cdot u|+|c\cdot v|
\]

has \(L(1,1)=2a\). A supporting linear form at \((1,1)\) has coefficients
\((a-b,a+b)\), or those coefficients interchanged. In either case both
coefficients are nonnegative. Explicitly, the two possible frame forms
are \((a,b),(-b,a)\) and \((a,-b),(b,a)\), up to swapping and changing
signs of the frame vectors. At \((1,1)\), choosing their nonnegative
dot products gives the asserted supporting form. It follows that

\[
L(1+s,1+t)\ge2a.                                         \tag{3}
\]

Equations (1) and (3) imply

\[
\begin{aligned}
\frac{17}{4}
&\ge (1+s)^2+(1+t)^2+\frac12+L(c)\\
&\ge \frac52+2a+2(s+t),
\end{aligned}
\]

so

\[
s+t\le\frac78-a.                                        \tag{4}
\]

For either \(q=p\) or \(q=p'\), both coordinates of \(c-q\) are
nonnegative and their sum is \(s+t+1/2\). Since every coordinate
magnitude of \(u,v\) is at most \(a\), equation (4) gives

\[
\begin{aligned}
|(c-q)\cdot u|, |(c-q)\cdot v|
&\le a(s+t+1/2)\\
&\le a(11/8-a)\\
&\le \frac{11}{8\sqrt2}-\frac12
 <\frac12.                                               \tag{5}
\end{aligned}
\]

The quadratic \(a(11/8-a)\) is decreasing for
\(a\ge1/\sqrt2>11/16\), which proves the third inequality.
The strict final inequality is equivalent to \(121<128\).
Both coordinates in the square's own frame are strictly between
\(-1/2\) and \(1/2\). Thus both points are in \(\operatorname{int}T\).
\(\square\)

Reflections of Lemma 1 give the analogous two points in every diagonal
quadrant. No common orientation between different squares is assumed.

## 3. A single terminal screens the corresponding center coordinate

**Lemma 2.** If \(T\subset D\) is physically interior-disjoint from
\(E\), then its center \((x,y)\) satisfies \(x<1\).

**Proof.** Suppose \(x\ge1\). By (2), \(1\le x\le3/2\). At these
horizontal coordinates, the distance of \((x,y)\) to \(E\) is
\(\max\{|y|-1/2,0\}\). The open radius-\(1/2\) disk inside \(T\)
therefore forces \(|y|\ge1\).

If \(y\ge1\), Lemma 1 places \((1,1/2)\) in
\(\operatorname{int}T\). If \(y\le-1\), its reflected version places
\((1,-1/2)\) in \(\operatorname{int}T\). Both points belong to the
closed square \(E\), and every open neighborhood of either point meets
\(\operatorname{int}E\). Either possibility contradicts physical
interior-disjointness. Thus \(x<1\). \(\square\)

**Corollary 3.** A square \(T\subset D\) physically interior-disjoint
from both \(E\) and \(W\) has center satisfying

\[
-1<x<1.                                                  \tag{6}
\]

This assertion requires no half-plane containment of \(T\). It follows
from Lemma 2 and its reflection in the vertical axis.

Equivalently, for a unit direction \(e\), let
\(S(e)=(3/2)e+[-1/2,1/2]e+[-1/2,1/2]e^\perp\).
A square in \(D\) avoiding \(S(e)\) has center projection
\(c\cdot e<1\); avoiding both antipodal terminals gives
\(|c\cdot e|<1\). This is a statement about centers. It does not
assert that every point of the whole square has that projection bound.
