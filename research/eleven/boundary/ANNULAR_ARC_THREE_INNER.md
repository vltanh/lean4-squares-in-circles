# Every eleven-square packing in the certified window has three inner centers

Let eleven unit squares with disjoint open interiors lie in a disk centered at
the origin with squared radius `q<=5`. Put

\[
\rho=\sqrt2,\qquad r_0=2-\frac{\sqrt2}{2},\qquad
\gamma=2\arcsin\frac1{2\sqrt2}.
\]

**Theorem.** At most eight square centers have Euclidean norm at least `r_0`.
Consequently at least three centers have norm strictly less than `r_0`.
This applies in particular to `q<=49013/10000`. Squares may have independent
orientations; no square is assumed to contain the origin.

The proof gives the following individual-square statement.

**Arc lemma.** A unit square contained in the radius-`sqrt(5)` disk, with
center norm at least `r_0`, meets the circle of radius `rho` in one connected
arc of angular length at least `gamma`. Its open interior has the same
angular measure on that circle.

## 1. Own-frame coordinates and the complete arc formula

Use reflections and quarter-turn choices of one square's orthonormal frame
to write its center in that frame as `(a,b)`, with `a>=b>=0`. These choices
are only for computing its intersection measure on the rotationally invariant
circle. Its four sides are the coordinate lines at `a+-1/2,b+-1/2`.
Write `r=sqrt(a^2+b^2)` and set

\[
x=a-1/2,\quad y=b-1/2.
\]

Containment implies

\[
(a+1/2)^2+(b+1/2)^2\le5.                         \tag{1}
\]

Since `a>=r/sqrt(2)` and `r>=r_0`,

\[
a+1/2\ge\rho,\qquad x\ge\sqrt2-1>0.             \tag{2}
\]

Thus the far primary side does not cut the radius-`rho` circle, while the
near primary side restricts its intersection to the right open half-plane.
Also `a<=sqrt(19)/2-1/2`, by (1) and `b>=0`, so
`x<=sqrt(19)/2-1<sqrt(2)`. We have `y>=-1/2`.

The near corner `(x,y)` is strictly inside the radius-`rho` disk. Indeed the
usual farthest-corner estimate gives

\[
r\le C=\frac{\sqrt{19}-1}{2},\qquad
x^2+y^2=r^2-a-b+1/2\le r^2-r+1/2.
\]

The last polynomial is increasing for `r>=1/2`, and `r>=r_0>1/2`.
Consequently

\[
x^2+y^2\le C^2-C+1/2=6-\sqrt{19}<2.              \tag{3}
\]

Parameterize the right circle semicircle as
`rho(cos(phi),sin(phi))`, `-pi/2<phi<pi/2`. The square conditions are
`rho cos(phi)>=x` and `y<=rho sin(phi)<=y+1`. By (3), the lower endpoint is

\[
\phi_-=\arcsin(y/\rho).
\]

The upper endpoint is

\[
\phi_+=
\begin{cases}
\min\{\arccos(x/\rho),\arcsin((y+1)/\rho)\},&y+1\le\rho,\\
\arccos(x/\rho),&y+1\ge\rho.
\end{cases}                                                       \tag{4}
\]

At `y+1=rho` these formulas agree. Equation (3) ensures
`phi_-<arccos(x/rho)` and `phi_->-arccos(x/rho)`, so no lower primary-side
branch or disconnected component is omitted. The upper horizontal side has
larger coordinate than the lower one and therefore gives a strictly larger
angle whenever it is active. The intersection is exactly this one closed
arc. It remains to bound each possible upper-endpoint difference in (4).

## 2. An arc cut by the two parallel sides

When `b+1/2<=rho`, the side-to-side difference is

\[
L_s(b)=\arcsin\frac{b+1/2}{\rho}
       -\arcsin\frac{b-1/2}{\rho}.
\]

For `b>=0`, its derivative is nonnegative because
`(b+1/2)^2>=(b-1/2)^2`. Continuity covers the upper endpoint at which the
first derivative becomes unbounded. Hence

\[
L_s(b)\ge L_s(0)=\gamma.                         \tag{5}
\]

## 3. An arc cut by the two near perpendicular sides

The other possible arc length is

\[
L_c(a,b)=\arccos(x/\rho)-\arcsin(y/\rho)
       =\pi/2-\arcsin(x/\rho)-\arcsin(y/\rho).   \tag{6}
\]

For fixed `b`, enlarge `a` until equality holds in (1). This increases
`arcsin(x/rho)`, so it can only decrease `L_c`. The enlarged `a` still
satisfies `a>=b`, because the original `a>=b` was feasible. On that boundary
write

\[
x+1=\sqrt5\cos\theta,\qquad
y+1=\sqrt5\sin\theta,\qquad
\arcsin\frac1{2\sqrt5}\le\theta\le\pi/4.
\]

Both `x,y` lie strictly between `-rho` and `rho`. Define

\[
S(\theta)=\arcsin(x/\rho)+\arcsin(y/\rho),\qquad
H(z)=(z+1)\sqrt{2-z^2}.
\]

Direct differentiation gives

\[
S'(\theta)=
\frac{H(x)-H(y)}{\sqrt{2-x^2}\sqrt{2-y^2}}.        \tag{7}
\]

The crucial exact factorization, using `(x+1)^2+(y+1)^2=5`, is

\[
H(x)^2-H(y)^2=(x-y)\bigl((x+y)^2+1\bigr).        \tag{8}
\]

Here `x>=y`, both `x+1,y+1` are positive, and both square roots are positive.
Thus `H(x)>=H(y)` and `S` is nondecreasing. Its maximum is at `x=y`, giving

\[
L_c\ge\frac\pi2
-2\arcsin\frac{\sqrt{5/2}-1}{\sqrt2}.            \tag{9}
\]

This lower bound exceeds `gamma`. One exact verification is

\[
\frac{\sqrt5-\sqrt2}{2}<\frac{\sqrt7-1}{4}
=\sin\left(\frac\pi4-\arcsin\frac1{2\sqrt2}\right).
\]

The inequality is equivalent to `1+2sqrt(5)<2sqrt(2)+sqrt(7)`. Squaring
positive quantities reduces this to `sqrt(14)-sqrt(5)>3/2`, then to
`sqrt(70)<67/8`, which follows from `4480<4489`. The angles are in
`(0,pi/2)`, so sine and arcsine are strictly increasing there. This proves
`L_c>gamma`. Together with (4) and (5), it proves the arc lemma.

Each square boundary is a union of four straight segments. Its intersection
with the circle is finite, so replacing the closed square by its open interior
does not change angular measure. All side/corner tangencies and the endpoints
of (4) are thereby retained.

## 4. Summing the arcs

The eleven open square interiors are pairwise disjoint, so their intersections
with the radius-`rho` circle are pairwise disjoint measurable sets. Their total
angular measure is at most `2pi`. Every square whose center norm is at least
`r_0` contributes at least `gamma`.

Finally

\[
\gamma>\frac1{\sqrt2}>\frac7{10},\qquad
9\gamma>\frac{63}{10}>\frac{44}{7}>2\pi.
\]

The first strict inequality follows from `arcsin(t)>t` for `0<t<1`; the last
uses the standard elementary bound `pi<22/7`. Nine qualifying squares are
therefore impossible. At least three of eleven centers lie strictly inside
the radius-`r_0` disk.

## Scope for the finite classification

This is a new unrestricted radial split: inner centers have norm `<r_0`,
outer centers have norm `>=r_0`, and there are at most eight outer labels.
It does not assert that there are exactly three inner squares, that their
interiors contain the disk center, or that the outer labels form a
neighbor-cycle sufficient for nonoverlap. It does not deform the packing
or discard any of the 55 physical pair constraints. Sharp lower bounds and
the classification of the residual geometry remain open.
