# Exact projection clipping before a circular-support pair bound

This is a hand reduction for the affine-marker pair inequalities. It does
not assert that a particular fitted marker family satisfies those
inequalities. In particular, it does not identify the convex support
dual with the exact nonconvex contact minimum.

## The exact coordinate projections of a separating pair

Let \(D_s,D_t\subset\mathbb R^2\) be nonempty compact state domains.
Fix vectors \(u,v\), and suppose separation on a chosen signed square
axis is

\[
 u\cdot x+v\cdot y\ge W,\qquad x\in D_s,\quad y\in D_t.
\tag{1}
\]

Write

\[
 m_s=\max_{D_s}u\cdot x,\qquad m_t=\max_{D_t}v\cdot y.
\]

If \(m_s+m_t<W\), the branch is impossible. Otherwise define

\[
 D_s'=D_s\cap\{u\cdot x\ge W-m_t\},\qquad
 D_t'=D_t\cap\{v\cdot y\ge W-m_s\}.
\tag{2}
\]

**Projection lemma.** The sets in (2) are exactly the two coordinate
projections of the feasible pair set (1).

Indeed, every feasible pair satisfies both inequalities in (2).
Conversely, for any \(x\in D_s'\), choose a maximizer of
\(v\cdot y\) in \(D_t\), which exists by compactness. Then (1)
holds. The argument for \(D_t'\) is identical.

The original maximizers remain in the clipped sets, since
\(m_s+m_t\ge W\). Hence their separate maximum projections remain
\(m_s,m_t\). Repeating this same clipping operation cannot sharpen
(2); improving a bound beyond it requires retaining more than these
two separate projection maxima.

## A cost bound with any linear frame charge

Suppose the corrected cost has the form

\[
 C(\phi,x,y)=a\phi+b-\beta h(\phi)
             +p\cdot x+q\cdot y,
\tag{3}
\]

where \(a,b,\beta\) and the coefficient vectors may depend on the
named pair regime, but are fixed when that regime is considered.
For every \(\lambda\ge0\), subtracting \(\lambda\) times the
nonnegative margin in (1) gives

\[
\begin{split}
 C\ge{}&a\phi+b-\beta h(\phi)+\lambda W\\
 &+\min_{x\in D_s'}(p-\lambda u)\cdot x
  +\min_{y\in D_t'}(q-\lambda v)\cdot y.
\end{split}
\tag{4}
\]

This is valid for any explicitly chosen nonnegative function
\(\lambda(\phi)\). There is no restriction on the real coefficient
\(a\). Thus it applies, in particular, to the additional quarter-word
charge \(a=1-\nu\), \(b=\nu k\pi/2\), as well as the original
coefficient \(a=1\).

In square-frame coordinates the source \(+f\) case has

\[
 u=(0,\sigma),\quad v=(\sin\phi,-\tau\cos\phi),
\]

and the source \(-e\) case has

\[
 u=(1,0),\quad v=(-\cos\phi,-\tau\sin\phi).
\]

All these projection vectors are unit vectors. The affine marker
coefficients and constants in (3) are exactly those in
`AFFINE_MARKER_SUPPORT_REDUCTION.md`.

## The clipped circle support has finitely many explicit candidates

Consider a circle arc of radius \(R\) and centre \(c_0\), clipped
by the half-plane \(u\cdot x\ge k\), where \(|u|=1\). To minimize
a linear functional \(p\cdot x\) on the resulting closed set, it
suffices to inspect:

1. The original arc endpoints that remain in the half-plane.
2. The intersections of the clipping line with the circle that lie on
   the arc.
3. The ordinary interior minimum of the linear functional on the
   circle, if it lies on the arc and in the half-plane.

For the second candidates put \(d=k-u\cdot c_0\). When
\(|d|\le R\), they are the explicit points

\[
 c_0+d u\ \pm\sqrt{R^2-d^2}\,Ju,
\tag{5}
\]

where \(J\) is rotation through \(\pi/2\). There are no such
intersections when \(|d|>R\). For \(p\ne0\), the third candidate is

\[
 c_0-R\frac p{|p|}.
\tag{6}
\]

If \(p=0\), its minimum is zero whenever the clipped set is nonempty.
These candidates are exhaustive: on each open component left after
clipping, any interior extremum of a linear functional on a circle is
one of its two stationary points, and only (6) can be a minimum. All
remaining extrema are boundary points from (1) or (2) above. The argument
also covers a clipped set with more than one connected component.

The outer arcs have \(c_0=(-1/2,-1/2)\), \(R=\sqrt Q\). The core
corner arc has \(c_0=(1/2,1/2)\), \(R=1/12\). The core side segment
\(a=7/12\), \(0\le b\le1/2\) needs only its retained endpoints and,
when present, its intersection with the clipping line. For a union of
side and corner, take the smaller of these two exact minima.

Thus every support in (4) is a finite formula involving only endpoint
values and square roots. No subdivision of the two tangent variables
is needed for this reduction.

## A direct contact alternative when the support dual loses information

There is a useful exact coordinate form for analyzing the remaining
one-dimensional contact problem. On a circle arc, use the signed SAT
projection \(z=u\cdot x\) as parameter. Split the arc at a projection
stationary point if necessary. On either resulting branch,

\[
 x=c_0+(z-z_0)u+s\sqrt{R^2-(z-z_0)^2}\,Ju,
 \qquad z_0=u\cdot c_0,\quad s\in\{-1,1\}.
\]

Every affine label is then

\[
 f(z)=A z+B\sqrt{R^2-(z-z_0)^2}+C_0,
\tag{7}
\]

with explicit coefficients. In the interior,

\[
 f''(z)=-\frac{BR^2}{[R^2-(z-z_0)^2]^{3/2}}.
\tag{8}
\]

Hence the convexity sign of a label on each branch is simply the
opposite sign of \(B\). If the two labels increase in their projection
coordinates, a minimum subject to (1) occurs either at a domain boundary
or on the exact contact line \(z+w=W\). On contact the objective is
\(f(z)+g(W-z)\), with second derivative given by the sum of two
expressions (8). This permits direct endpoint or strict-convexity
arguments in regimes where (4) has a convex-hull loss. The low/high
aligned-contact proof is an explicit example of that method.

Equations (4)--(8) supply the analytic formulas; a complete pair theorem
must still prove its required scalar inequalities in all the named
relative-angle regimes.
