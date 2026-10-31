# Parallel transmissions in the mixed five-cycle

**Status:** independently reviewed exact conditional hand proof. This
excludes the parallel-direction subcase of the remaining three-loaded
five-cycle. It does not exclude nonparallel transmission directions or
close the unrestricted ten-square problem.

Use the selected physical positive-stress certificate of
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md), and assume

\[
                         79/40\le R\le3/\sqrt2.             \tag{1}
\]

Suppose an entire positive component is the cycle

\[
                         A-U-C-V-B-A,                       \tag{2}
\]

where precisely A, B, C are circle-loaded. The unloaded degree-two bodies
U and V transmit along straight lines, with respective widths in
\(\{1,\sqrt2\}\), as proved in
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md).

**Theorem.** The two transmission directions from C toward A and B cannot
be parallel.

The selected-certificate convention matters in one explicitly identified
vertex-contact case below. All other exclusions are geometric or follow
from force balance.

## 1. A sign lemma for a loaded square

Let a unit square have minimum horizontal coordinate l, with l>−1/2 and
positive horizontal center coordinate. If a farthest vertex lies in the
opposite closed vertical half-plane from its center, then its norm is at
most

\[
                              l+\sqrt2.                    \tag{3}
\]

If the center has vertical coordinate zero, every farthest vertex satisfies
the same bound.

To prove this, first suppose the center's vertical coordinate is nonnegative.
Write the square's rotation, modulo quarter-turns, as an angle of absolute
value at most pi/4, and put

\[
 c=\cos|\theta|,\quad s=\sin|\theta|,\quad
 w=c+s,\quad h=w/2,\quad t=(c-s)/2.
\]

For positive tilt the four center-relative vertices, in order from right
to top, left and bottom, are

\[
                   (h,-t),\ (t,h),\ (-h,t),\ (-t,-h).
\]

The top vertex strictly dominates the left vertex and weakly dominates
the bottom vertex in its dot product with the center. The latter comparison
can be an equality only when t=0 and the vertical center coordinate is zero;
then the right vertex strictly dominates both. Thus a farthest vertex with
nonpositive vertical coordinate must be the right vertex. For negative tilt, the corresponding
list is

\[
                   (h,t),\ (-t,h),\ (-h,-t),\ (t,-h).
\]

The right vertex dominates the bottom vertex, strictly except when s=0
and the center's vertical coordinate is zero. The left vertex cannot be
farthest. Therefore an eligible farthest vertex is again rightmost; the
exception at s=0 is also rightmost. If the center's vertical coordinate
is zero, its positive horizontal coordinate directly makes every farthest
vertex rightmost. In all these cases its absolute vertical coordinate is
at most t, and its horizontal coordinate is l+w. Consequently

\[
 \begin{aligned}
 |p|^2
 &\le(l+w)^2+t^2\\
 &=(l+w)^2+\frac{2-w^2}{4}
 \le(l+\sqrt2)^2.                                         \tag{4}
 \end{aligned}
\]

The final expression before the inequality has derivative
\(2l+3w/2>0\) on \(1\le w\le\sqrt2\). Reflection in the horizontal
axis handles a negative vertical center coordinate.

In particular, if a square is contained in the radius-R disk, is loaded,
and R>l+sqrt(2), then its vertical center coordinate is nonzero and all
its circle vertices have that same strict vertical sign.

## 2. Reduction of the central loaded square

If the transmission directions are opposite, rotate so one points right
and the other left. The endpoint squares lie beyond the two support faces
of C, with an additional gap at least one on each side. Their horizontal
projections are therefore separated by at least three. They cannot touch,
contradicting the edge A--B in (2).

It remains to consider two directions pointing the same way. Rotate so
both point right. The two forces into C are parallel and point left.
Aggregate them at their positively weighted mean contact point on C's
right support face. Torque balance makes that effective force line radial.
The loaded-leaf calculation from
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md) applies to this
aggregate. Set

\[
                  a=\sqrt{R^2-1/4}-1,\qquad b=R-\sqrt2.
\]

The square C is a radial side type S or radial diagonal type D, on the
negative horizontal ray. Its inward support coordinate is respectively
−a or −b.

If C is D, its two contacts use its unique rightmost vertex. A diagonal
transmitter starting there occupies both sides of the outgoing horizontal
ray locally, and therefore overlaps either a side or another diagonal
transmitter starting at that point. If both transmitters are side type,
their interiors can be disjoint only when one occupies the upper-right
quadrant at the point and the other the lower-right quadrant. Both contacts
are then point-only vertex/vertex contacts at the nonzero point (−b,0).
Their positive force normals are horizontal, hence radial. This is ruled
out by the stipulated nonradial normal choice at off-origin point-only
vertex/vertex contacts. Thus C must be S.

Its right support face is

\[
                      \{(-a,y): |y|\le1/2\}.              \tag{5}
\]

Both transmitters cannot be diagonal. Their centers would have the same
horizontal coordinate and vertical separation at most one, while two
unit diamonds with horizontal diagonals and equal horizontal center
coordinates require vertical separation at least sqrt(2). Their interiors
would overlap. Relabel if necessary so U is a side transmitter.

Writing l_A and l_B for the minimum horizontal coordinates of A and B,
the exact transmission widths now give

\[
                 l_A=1-a,\qquad
                 l_B\in\{1-a,\sqrt2-a\}.                 \tag{6}
\]

## 3. The endpoint loads lie above and below the horizontal axis

The radius window gives a>9/10 and a<9/8. The horizontal halfwidth of
any unit square lies between 1/2 and sqrt(2)/2, so (6) implies positive
horizontal center coordinates and l_A,l_B>−1/2. Also

\[
 l_A+\sqrt2,\ l_B+\sqrt2
 \le2\sqrt2-a
 <39/20<79/40\le R,                                      \tag{7}
\]

using sqrt(2)<57/40 and a>9/10. Section 1 therefore shows that the vertical
center coordinates of A and B are nonzero, and every circle load on each
has the strict sign of that center coordinate.

The total circle load on C is horizontal, by its own force equation.
Summing the five body force equations cancels all contact forces, leaving
zero total circle load. Thus the centers of A and B lie on opposite sides
of the horizontal axis.

## 4. The endpoint centers are too far apart to touch

Every loaded square has center norm at least R−sqrt(2)/2. Since
sqrt(2)<99/70, define

\[
 r_0=\frac{71}{56}=\frac{79}{40}-\frac{99}{140};
 \qquad |c_A|,|c_B|>r_0.                                  \tag{8}
\]

Moreover a>91/100: indeed

\[
 \frac{5841}{1600}-\left(\frac{191}{100}\right)^2
   =\frac{101}{40000}>0.
\]

The halfwidth bound and (6) give, for the horizontal center coordinates
x and z,

\[
 0<x<x_0:=\frac{279}{350},\qquad
 0<z<z_0:=\frac{212}{175},\qquad x_0,z_0<r_0.              \tag{9}
\]

Their vertical coordinates have opposite signs, so

\[
 \begin{aligned}
 |c_A-c_B|^2
 &>(x-z)^2+
       \left(\sqrt{r_0^2-x^2}+\sqrt{r_0^2-z^2}\right)^2\\
 &=2r_0^2-2xz+2\sqrt{(r_0^2-x^2)(r_0^2-z^2)}.              \tag{10}
 \end{aligned}
\]

For positive x,z<r_0 the last expression strictly decreases in either
variable. Substitute x_0,z_0 and use the exact inequalities

\[
 r_0^2-x_0^2-\left(\frac{49}{50}\right)^2
       =\frac{93}{8000}>0,
 \qquad
 r_0^2-z_0^2-\left(\frac{37}{100}\right)^2
       =\frac{1177}{392000}>0.
\]

This yields

\[
 \begin{aligned}
 |c_A-c_B|^2
 &>2r_0^2-2x_0z_0+2\left(\frac{49}{50}\right)
                              \left(\frac{37}{100}\right)\\
 &=2+\frac{1717}{196000}>2.                                \tag{11}
 \end{aligned}
\]

Touching unit squares have center distance at most sqrt(2), because each
contact point is at distance at most sqrt(2)/2 from either center. This
contradicts the positive edge A--B and proves the theorem.
