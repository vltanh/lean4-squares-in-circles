# Parallel enclosed units force boundary-center diameter at least three

**Status: complete hand implication; independent full hand audit passed.**
Let \(P\) be a convex polygon whose edges have length at most
\(\sqrt2\). Suppose two parallel unit squares \(T,U\), with disjoint
open interiors, are contained in \(P\), and every vertex of \(P\) is
at distance at least \(1/2\) from each unit. Then the vertex diameter of
\(P\) is at least three.

There is no bound on the number of polygon vertices and no assumption
that the inner units are in the same row or actually touch. The result
applies to C7 through `C7_CENTER_POLYGON_LOCALIZATION.md`; the known
strict center-diameter upper bound then excludes all parallel inner
pairs. The independently oriented case remains separate.

## 1. A missing far-face zone forces a short corner-to-corner crossing

First put

\[
T=[-1,0]\times[-1/2,1/2].
\]

Call

\[
Z_L=\{(x,y):x\le-3/2,\ -1/2\le y\le1/2\}
\]

its left middle zone. Suppose \(P\) has no vertex in \(Z_L\). The
leftward ray from \((-1/2,0)\) meets the boundary of \(P\) at a point
\((x,0)\) with \(x\le-1\). This point is not a polygon vertex:
clearance from \(T\) would require \(x\le-3/2\). It therefore lies
inside an edge with one endpoint above and one below the horizontal
axis. Write those endpoints as \(A,B\), respectively.

Both endpoints have first coordinate strictly less than \(-1\). To
see this, one endpoint must have first coordinate at most \(-1\),
because the edge crosses that leftward ray. Say it is the lower one
\(B\). Absence of \(Z_L\) and clearance force \(B_y<-1/2\).
If the other endpoint \(A\) had \(-1\le A_x\le0\), then its
clearance would force \(A_y\ge1\), contradicting edge length at most
\(\sqrt2\). If \(A_x\ge0\) and \(A_y\le1/2\), clearance would
force \(A_x\ge1/2\), giving horizontal difference at least \(3/2\).
If \(A_x\ge0\) and \(A_y>1/2\), the horizontal difference is at
least one and the vertical difference exceeds one. This also contradicts
the edge-length bound. Interchanging upper and lower endpoints covers
the other possibility. Equality at first coordinate \(-1\) is ruled
out by the same argument.

Consequently the endpoints have the form

\[
A=(-1-u,1/2+v),\qquad B=(-1-w,-1/2-z),
\]

where \(u,w,v,z>0\), and

\[
u^2+v^2\ge1/4,\quad w^2+z^2\ge1/4,\qquad
v+z\le\sqrt2-1<1/2.
\tag{1}
\]

Moreover

\[
u>1/4,\qquad w>1/4.
\tag{2}
\]

Indeed each of \(v,z\) is at most \(\sqrt2-1<\sqrt3/4\),
so the clearance inequalities in (1) give (2). The displayed comparison
follows by squaring from \(\sqrt2>45/32\).

The reflected and translated assertion holds at the right middle zone
of any translated parallel unit.

## 2. No opposite-side point can be within three of both endpoints

Keep the endpoints from Section 1. If \(C_x\ge3/2\), at least one
of \(|C-A|,|C-B|\) is strictly greater than three.

Suppose otherwise. The horizontal differences are at least
\(5/2+u\) and \(5/2+w\), so \(u,w\le1/2\). For
\(1/8\le u\le1/2\),

\[
9-(5/2+u)^2\le9(1/4-u^2)\le9v^2.
\]

The first comparison is exactly
\((1/2-u)(8u-1)\ge0\); the second is clearance. Thus
\(|C_y-A_y|\le3v\), and similarly \(|C_y-B_y|\le3z\).
The triangle inequality would give

\[
1+v+z=A_y-B_y\le3(v+z),
\]

contradicting \(v+z<1/2\) in (1). This proves the claim, including
all closed equality cases for the assumed distances.

## 3. Two missing zones force a cross diagonal longer than three

After a rigid motion and, if necessary, an interchange of coordinate
axes and the two units, any two parallel interior-disjoint units have
the form

\[
T=[-1,0]\times[-1/2,1/2],\qquad
U=[g,g+1]\times[t-1/2,t+1/2],\qquad g\ge0.
\tag{3}
\]

Their relative vertical displacement \(t\) is arbitrary. Suppose both
the left middle zone of \(T\) and the right middle zone of \(U\)
are empty of polygon vertices. Section 1 supplies the left endpoints
\(A,B\) and right endpoints

\[
C=(g+1+p,t+1/2+q),\qquad
D=(g+1+r,t-1/2-s),
\]

with each excess pair \((u,v),(w,z),(p,q),(r,s)\) satisfying

\[
x>1/4,\quad y\ge0,\quad x^2+y^2\ge1/4.
\tag{4}
\]

Every such pair obeys

\[
2x+y>9/10.
\tag{5}
\]

For \(x\ge1/2\) this is immediate. For \(1/4\le x\le1/2\),
the concave function \(2x+\sqrt{1/4-x^2}\) has minimum at an
endpoint. Those endpoint values are \(1\) and
\(1/2+\sqrt3/4>9/10\).

If \(t\ge0\), use the cross diagonal \(BC\). Its horizontal and
vertical absolute coordinate differences are at least
\(2+w+p\) and \(1+z+q\), respectively. Therefore

\[
\begin{aligned}
|B-C|^2
&\ge (2+w+p)^2+(1+z+q)^2\\
&=5+2\bigl((2w+z)+(2p+q)\bigr)
 +(w+p)^2+(z+q)^2\\
&>5+18/5+1/2=91/10>9.
\end{aligned}
\]

The last squared sum is at least
\(w^2+z^2+p^2+q^2\ge1/2\), and (5) handles the linear terms.
If \(t<0\), the same computation uses \(AD\); the negative stagger
increases its vertical gap. Thus arbitrary stagger cannot evade the
strict diameter bound in the two-empty-zone case.

## 4. Exhaustion of all zone cases

If both middle zones contain vertices, their horizontal coordinate
difference is at least \(g+3\ge3\), giving the desired diameter.
If only the left zone is empty, a vertex in the right zone has first
coordinate at least \(g+3/2\ge3/2\), and Section 2 gives an even
strict diameter bound. Reflection handles the case in which only the
right zone is empty. If both are empty, Section 3 applies.

These cases exhaust (3), proving the theorem.

For a physical C7, the center-polygon localization theorem supplies all
its hypotheses for any parallel extra pair. The theorem would give
center diameter at least three, contradicting
`BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md`. Hence the remaining C7
completion problem has two genuinely nonparallel inner frames.
