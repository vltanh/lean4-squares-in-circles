# A connected nine-eighths arc outside the one-eighth disk

Date: October 27, 2026.

Status: reconstructed after the workspace snapshot reset from the complete
previously independently accepted proof. The mathematical statement and
every exact estimate are unchanged; this restored wording has a new byte
pin and awaits independent readback.

Put \(Q=1105/256\), \(\rho=9/8\), and
\(\gamma=\arccos(4/5)\), so \(\sin\gamma=3/5\).

## 1. Whole physical statement and actual coordinates

Let \(E\) be any actual closed unit square contained in the closed disk
of squared radius \(Q\). If
\[
 \operatorname{dist}(O,E)>1/8,                         \tag{1}
\]
then \(\operatorname{int}E\) meets the radius-\(\rho\) circle in exactly
one connected open arc of angular length strictly greater than \(\gamma\).
This arc contains the point in the actual center direction. The statement
includes arbitrary orientations and all physical side and corner endpoints;
there are no force, contact-normal, graph-degree or circle-mask assumptions.

Only reorder and change the signs of the actual orthonormal own axes,
retaining the original circle origin. Write
\[
 E=[A,a]\times[B,b],\qquad A=a-1,\ B=b-1,
 \qquad a\ge b\ge1/2,\quad a^2+b^2\le Q.
\]
In particular
\[
 A<61/60,\qquad B<1/2.
\]
The actual squared distance in (1) is
\(\max(A,0)^2+\max(B,0)^2\). Retain separately both possible comparisons
of the actual far coordinate \(a\) with \(\rho\).

## 2. The complete domain with \(a>\rho\)

In this domain \(1/8<A<61/60\). Sections 1--3 of
`NINE_EIGHTHS_INNER_ARC_AWAY_FROM_CENTRAL_DISK.md` apply directly.
The stronger distance assumption in that source is used only to establish
\(a>\rho\); the rest of its proof uses precisely the actual coordinate
inequalities just stated. For completeness its full interval and estimate
are as follows:
\[
 \alpha=\arccos(A/\rho),\quad
 \beta=\arcsin(B/\rho),\quad
 \eta=\arcsin(\min(b/\rho,1)),
\]
and the complete closed intersection is
\[
 [\max(-\alpha,\beta),\ \min(\alpha,\eta)].          \tag{2}
\]
For fixed \(q=a^2+b^2\) and \(t=a+b\),
\[
 A^2+B^2+(6/5)AB
 =(2/5)q+(3/5)t^2-(16/5)t+16/5.
\]
Convexity in \(t\) reduces the upper bound to the enlarged endpoints
\(b=1/2\) and \(a=b\). At the first, the convex quadratic in
\(A_0=\sqrt{q-1/4}-1\in(1/8,61/60)\) has endpoint values
\(61/320\) and \(97/144\). At the second, \(a=b=v\in(3/4,3/2)\)
gives \((16/5)(v-1)^2<4/5\). Consequently
\[
 A^2+B^2+(6/5)AB<4/5<81/100=\rho^2(4/5)^2.
\]
This implies \(\alpha-\beta>\gamma\). The unchanged half-angle bounds
\(A/\rho<122/135<\cos(\gamma/2)\) and
\(\eta\ge\arcsin(4/9)>\gamma/2\) give
\(2\alpha,\alpha+\eta>\gamma\). The full unit-strip difference
\(\eta-\beta\) has minimum \(2\arcsin(4/9)>\gamma\) for
\(b\le\rho\), and is greater than \(\pi/3\) when \(b>\rho\).
Thus all four upper-minus-lower differences in (2) exceed \(\gamma\).
The open-interior intersection is its one open interval. In particular
the formal \(\eta=\pi/2\) endpoint for \(b\ge\rho\) creates no
additional point or arc, since \(\alpha<\pi/2\).

## 3. The complete outer-face domain with \(a\le\rho\)

Now (1) forces
\[
 0<B\le A\le1/8,\qquad A^2+B^2>1/64.
\]
Indeed, if \(B\le0\), the actual distance is at most \(A\le1/8\).
Since \(A\ge B>0\),
\[
 A>1/(8\sqrt2)>1/12,\qquad a>13/12,\qquad b>1.
\]
The actual square and its intersection lie in the first quadrant. Define
\[
 \alpha=\arccos(A/\rho),\quad\beta=\arcsin(B/\rho),
 \quad\theta=\arccos(a/\rho),\quad\eta=\arcsin(b/\rho).
\]
The complete closed intersection is exactly
\[
 [\max(\beta,\theta),\ \min(\alpha,\eta)].           \tag{3}
\]
This expression includes \(a=\rho\) and \(b=\rho\); the corresponding
zero or right-angle endpoint is superseded by the other actual strict
inner-face inequality. We compare all four endpoint differences.

First,
\[
 \alpha-\beta\ge\pi/2-2\arcsin(1/9)>\gamma,
\]
because the cosine of the middle angle is \(8\sqrt5/81<4/5\).
Each full unit-strip difference satisfies
\[
 \alpha-\theta\ge\arcsin(8/9)>\gamma,
 \qquad\eta-\beta\ge\arcsin(8/9)>\gamma.
\]
For instance the first difference is
\(\arccos(A/\rho)-\arccos((A+1)/\rho)\), which is increasing for
\(A\in[0,1/8]\), with initial value \(\arcsin(8/9)\). The sine-strip
argument is identical. Endpoint equalities are retained.

For the two outer faces, \(\eta-\theta\in[-\pi/2,\pi/2]\), and
\[
\begin{split}
 \sin(\eta-\theta)
 &=\frac{ab-\sqrt{(\rho^2-a^2)(\rho^2-b^2)}}{\rho^2}\\
 &>\frac{13/12-31/192}{81/64}=\frac{59}{81}>\frac35.
\end{split}                                                   \tag{4}
\]
Here
\[
 (\rho^2-a^2)(\rho^2-b^2)
 <(53/576)(17/64)=901/36864<(31/192)^2.
\]
The sine is strictly increasing on the full stated difference interval,
so (4) gives \(\eta-\theta>\gamma\). All four differences in (3) are
strictly greater than \(\gamma\). Thus (3) gives one nonempty open
interior arc of the required length throughout this remaining domain.

## 4. Actual center point and capacity export

The actual incircle of radius \(1/2\), centered at \(c_E\), is contained
in \(E\). Hence (1) implies
\[
 |c_E|>5/8=\rho-1/2.
\]
The actual farthest-corner formula gives
\[
 |c_E|^2+|c_E|+1/2\le Q.
\]
At \(91/60\) its left side exceeds \(Q\) by \(31/57600\).
Thus \(|c_E|<91/60<\rho+1/2\), and the point
\(\rho c_E/|c_E|\) lies strictly inside that actual incircle. It is on
the unique open arc established above.

Distinct squares with disjoint open interiors give disjoint open arcs.
After a caller proves that their complete actual arcs lie in a particular
free interval, an interval of length at most \(n\gamma\) can contain at
most \(n-1\) such arcs. In particular a gap at most \(\gamma\) contains
none, and a gap at most \(3\gamma\) contains at most two. The strict
arc lengths retain equality in the gap-length assumptions. Actual closed
occupied arcs and their endpoints must be established by the caller.

## 5. The strict clearance threshold is necessary

The actual contained unit
\[
 [1/8,9/8]\times[-1/2,1/2]
\]
has distance exactly \(1/8\) from the origin. Its interior intersects
the radius-\(9/8\) circle in two nonempty open arcs, one above and one
below the positive horizontal axis. The point \((9/8,0)\) lies on its
outer side and separates them. Thus the assertion of one connected open
arc cannot extend to the non-strict clearance hypothesis. No selected
force or numerical pose is used in this theorem or this equality example.
