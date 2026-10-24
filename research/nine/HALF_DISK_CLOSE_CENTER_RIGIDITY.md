# Close horizontal centers in a half-disk force the north terminal

**Status:** complete hand proof of the local pair theorem below. The
squares may have independent orientations; only physical
interior-disjointness is assumed. This does not establish the full
three-square half-pocket theorem or P.ALL. No Lean compilation or CI
has been run.

Put
\[
D=\{(x,y):x^2+y^2\le17/4\}.
\]

**Theorem 1.** Let \(A,B\) be closed unit squares contained in
\(D\cap\{y\ge0\}\), with disjoint open interiors. If their center
horizontal coordinates differ by at most \(1/2\), then both squares
are axis-aligned. After naming the higher one \(B\), their centers are
\[
 c_B=(0,3/2),\qquad c_A=(x,1/2),\qquad |x|\le1/2.          \tag{1}
\]
Conversely, every pair in (1) satisfies the stated hypotheses.

## 1. Support widths and a separating axis

For a square \(S\) with orthonormal side axes \(u_S,v_S\), let
\[
H_S(n)=\frac12\bigl(|n\cdot u_S|+|n\cdot v_S|\bigr)
\]
be its support halfwidth in a unit direction \(n\). Thus
\(H_S(n)\ge1/2\), with equality when \(n\) is a side axis.
Whole upper-half-plane containment gives
\[
                        (c_S)_y\ge H_S(e_y).              \tag{2}
\]
The exact corner formula, proved in
[DIAGONAL_CENTER_EXCLUSION.md](DIAGONAL_CENTER_EXCLUSION.md), gives
\[
                              |c_S|\le3/2.                 \tag{3}
\]

Physical nonoverlap of two squares supplies a separating axis owned by
one of them. One direct justification is to consider their Minkowski
difference: it is a convex polygon whose edge normals are side axes
of the two squares. The origin is not in its interior, so one of its
edge inequalities separates the origin. Equivalently, after orienting
that axis \(n\) suitably,
\[
 n\cdot(c_B-c_A)\ge H_A(n)+H_B(n)\ge1.                    \tag{4}
\]
This includes touching sides, touching vertices, and every equality
case. It assumes no shared orientation or prescribed separator.

Order the centers so that \((c_B)_y\ge(c_A)_y\). If \(n_y\le0\),
the horizontal-gap assumption would make the left side of (4) at most
\(1/2\), a contradiction. Hence we may write
\[
a=n_y>0,\qquad b=|n_x|\ge0,\qquad a^2+b^2=1.
\]
Writing the center heights as \(y_A,y_B\), (4) implies
\[
 a y_B\ge a y_A+H_A(n)+H_B(n)-b/2.                         \tag{5}
\]
We show that \(b>0\) contradicts \(y_B\le3/2\).

## 2. When the lower square owns the separator

If \(n\) is a side axis of \(A\), then
\[
H_A(n)=1/2,\qquad H_A(e_y)=(a+b)/2,
\qquad H_B(n)\ge1/2.
\]
Equations (2) and (5) therefore give
\[
\begin{aligned}
y_B
&\ge\frac{a+b}{2}+\frac{1-b/2}{a}\\
&=\frac32+\frac{b^2(2-a-b)}{2a(1+a)}.                     \tag{6}
\end{aligned}
\]
The identity follows from \(1-a=b^2/(1+a)\).
Since \(a+b\le\sqrt2<2\), the final term is strictly positive
when \(b>0\), contrary to (3).

## 3. When the upper square owns the separator

Now suppose \(n\) is a side axis of \(B\), so \(H_B(n)=1/2\).
For every orientation of \(A\) we have
\[
aH_A(e_y)+H_A(n)
\ge\min\left\{a+b/2,\ \frac{a(a+b)+1}{2}\right\}.          \tag{7}
\]

Here is a proof retaining every orientation. Parameterize the frame of
\(A\) by an angle modulo \(\pi/2\), and split the parameter circle at
the finitely many angles where a frame vector is perpendicular to
\(e_y\) or \(n\). On each resulting closed interval the left side of
(7) is a positive function of the form \(K\cos\phi+L\sin\phi\).
Its second derivative is its negative, so it is concave and attains
its minimum at an endpoint. The endpoint frames are exactly those
aligned to \(e_y\) or \(n\). Their values are the two expressions in
(7). This proves (7) by a two-direction support calculation, without
an orientation grid.

Subtract \(3a/2+b/2-1/2\) from the respective expressions on the
right of (7). The differences are
\[
\frac{1-a}{2},\qquad
\frac{b^2(2-a-b)}{2(1+a)}.                                 \tag{8}
\]
Both are strictly positive if \(b>0\). Using (2), (5), and
\(H_B(n)=1/2\), equations (7)--(8) imply
\(a y_B>3a/2\), again contradicting (3).

## 4. Equality and the complete pair classification

We have proved \(b=0\), hence \(a=1\). Equations (2), (3), and (5)
then force equality throughout:
\[
y_A=H_A(e_y)=1/2,\qquad H_B(e_y)=1/2,
\qquad y_B=3/2.
\]
A unit square has vertical halfwidth \(1/2\) only when it is
axis-aligned: if its vertical axis components are \(r,s\), then
\(r^2+s^2=1\) and \(|r|+|s|=1\) force \(rs=0\).
Thus both squares are aligned. Equation (3) forces \((c_B)_x=0\),
and the assumed horizontal gap gives \(|(c_A)_x|\le1/2\).
These are exactly (1). Their containment and physical disjointness
are immediate from the coordinate rectangles, proving the converse.
\(\square\)

## 5. Two consequences used in completion reductions

**Corollary 2.** At most two pairwise physically interior-disjoint unit
squares contained in \(D\cap\{y\ge0\}\) can have all center horizontal
coordinates in \((-1,0)\). The same holds for \((0,1)\), and by
reflection for the lower half-disk.

Indeed, three center coordinates in an open interval of length one
have two consecutive coordinates differing by less than \(1/2\).
Theorem 1 would give a square centered at \((0,3/2)\), which lies in
neither permitted center strip.

For the next consequence, put
\[
E=[1,2]\times[-1/2,1/2],\quad W=-E,\quad
N=[-1/2,1/2]\times[1,2].
\]

**Corollary 3.** Suppose three arbitrary unit squares lie in the upper
half-disk, avoid \(E,W\) physically, and have pairwise disjoint open
interiors. If any two centers differ horizontally by at most \(1/2\),
then the triple is exactly
\[
[-1,0]\times[0,1],\quad [0,1]\times[0,1],\quad N.           \tag{9}
\]

Theorem 1 first supplies \(N\). Consider another center \((x,y)\)
with \(x\ge0\). Its radius-\(1/2\) inscribed disk must avoid \(E,N\).
The elementary center-region calculation gives
\[
0\le x,y\le1/2\quad\text{or}\quad x,y\ge1.                 \tag{10}
\]
For completeness, \(x>1/2,y\le1/2\) puts the center within distance
strictly less than \(1/2\) of \(E\); the transposed case uses \(N\).
Here (3) ensures \(x,y\le3/2\). If both exceed \(1/2\) and just one
is at least one, its corresponding terminal is again too close. If
both are in \((1/2,1)\), put \(u=x-1/2,v=y-1/2\). Avoidance would
require \(u^2+v^2\ge u,v\), while
\[
u^2+v^2<(u+v)/2\le\max\{u,v\},
\]
a contradiction. This proves (10), including its boundary alternatives.

The diagonal alternative is excluded by Lemma 1 of
[DIAGONAL_CENTER_EXCLUSION.md](DIAGONAL_CENTER_EXCLUSION.md).
Whole upper-half-plane containment then gives
\(1/2\ge y\ge H(e_y)\ge1/2\). Hence this square is aligned with
center \((x,1/2)\), where \(0\le x\le1/2\). Reflection deals with
\(x\le0\). The two remaining aligned squares have center heights
\(1/2\), horizontal coordinates in \([-1/2,1/2]\), and horizontal
separation at least one. Their centers must be \((-1/2,1/2)\) and
\((1/2,1/2)\), proving (9).

**Remaining proof boundary.** Corollary 3 does not classify triples
whose sorted center coordinates satisfy both adjacent gaps
\(x_2-x_1>1/2\) and \(x_3-x_2>1/2\). That entire residual remains
open here; the pair theorem must not be cited as full half-pocket
rigidity or as P.ALL.
