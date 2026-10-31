# n=9: an unconditional triple-transversal lemma

**Status:** a proved global G2 input, but **not** the desired
seven-anchor extraction or unrestricted lower bound.

This argument works for arbitrary individual square rotations.
It is useful as a guaranteed starting point for a structural
classification; a three-square line transversal is far weaker
than full vertical layer separation.

## Theorem (every direction has a line meeting three squares)

Let nine unit squares with disjoint open interiors fit in a
closed disk of radius \(R\le\sqrt{1105}/16\).
For **every unit vector** \(e\) there is a line perpendicular
to \(e\) that meets the open interiors of at least three
of these squares.

*Proof.* Fix a unit vector \(e\), and write
\(t=p\cdot e\) for projection onto it. A unit square
whose side axes are the orthonormal vectors \(u,v\)
has projection interval length
\[
 w_e(S)=|e\cdot u|+|e\cdot v|\ge
 \sqrt{(e\cdot u)^2+(e\cdot v)^2}=1. \tag{1}
\]
Every interval lies inside the projected disk segment
\([-R,R]\).

Let \(N_e(t)\) be the number of the nine open projection
intervals containing \(t\). Since endpoints are a finite
set of measure zero, elementary interval-length
additivity gives
\[
 \int_{-R}^{R}N_e(t)\,dt
  =\sum_{i=1}^9 w_e(S_i)\ge9. \tag{2}
\]
But
\[
 R^2\le1105/256<81/16=(9/4)^2,
 \qquad\text{so}\qquad 4R<9. \tag{3}
\]
If \(N_e(t)\le2\) for all \(t\), its integral would be
at most \(2(2R)=4R<9\), contradicting (2).
Thus \(N_e(t)\ge3\) for some \(t\).

For a convex square, a \(t\) strictly inside its
projection interval is realized by a point in its
open interior (take a convex combination of two
interior points on opposite sides of the line).
Hence the line \(p\cdot e=t\) meets three
square interiors. Their cross-sections on that
line are disjoint open intervals, since square
interiors are disjoint. \(\square\)

The same argument proves the general result:
if \(n\) unit squares fit in a disk of radius R,
some perpendicular line in each direction meets
at least \(\lceil n/(2R)\rceil\) square interiors
when \(n/(2R)\) is not an integer; if it is
an integer, the obvious weak bound applies
with equality care.

## Role in G2 and limitation

This result is unconditional and uses the original
packing assumptions, unlike the stratified terminal
theorems. In particular it provides a vertical stack
of at least three non-overlapping *cross-sections*
for **any chosen frame**.

It does **not** prove that the three entire squares
have disjoint vertical projection intervals, nor
that the other six squares can be split into
horizontally separated 4+3 groups. Tilted squares
may be disjoint even when both coordinate
projections overlap. Therefore it does not close
G2 or imply the sharp global n=9 bound by itself.

A useful next structural question is whether a
choice of line transversal with maximal angular/
projection obstruction forces an additional
four-square projection-separated chain, or whether
nonstratified topological arrangements survive
and require their own analytic G3 obstruction.
No such implication is asserted here.
