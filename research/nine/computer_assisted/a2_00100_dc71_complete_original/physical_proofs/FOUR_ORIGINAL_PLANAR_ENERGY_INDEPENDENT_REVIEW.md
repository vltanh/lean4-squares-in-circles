# Independent review: the four-center squared-distance capacity bound

**Accepted as a complete elementary theorem.** If four distinct points in the Euclidean plane have all six mutual distances at least one, then

\[
\sum_{i<j}\|p_i-p_j\|^2\ge 8.
\]

This uses planarity beyond separate pair distances and a generic positive-semidefinite moment relaxation. It applies to centers of any four original nonoverlapping unit squares, since their open incircles of radius one-half are disjoint. It is not itself a whole-cell or mask closure.

## Stronger complete three-matching cover

For any numbering of the four points, at least one of the following three alternatives holds:

\[
\begin{aligned}
|p_1-p_2|^2+|p_3-p_4|^2&\ge4,\\
|p_1-p_3|^2+|p_2-p_4|^2&\ge4,\\
|p_1-p_4|^2+|p_2-p_3|^2&\ge4.
\end{aligned}
\]

In the convex case below, use the matching of the two diagonals. In the strict interior-point case, the edge with squared length at least three and its disjoint complementary edge form a matching with squared sum at least four. In a boundary or collinear case, the analogous matching has sum at least five. These cases exhaust all configurations, so this is a complete finite cover, with shared equality faces included.

The total-energy bound follows because the four distances outside the selected matching each have square at least one. The diameter bound follows because at least one of the two matching distances has square at least two. The matching cover is generally stronger than either consequence alone. It permits three closed alternatives; a cell is discharged only after all applicable alternatives have complete proofs.

## Convex quadrilateral case

Label the four hull vertices cyclically A,B,C,D, and let O be the intersection of the diagonals. Write

\[
A=xe,\quad C=-ye,\quad B=zf,\quad D=-wf,
\qquad x,y,z,w>0,\quad \|e\|=\|f\|=1.
\]

(The origin in this calculation is O, not the containing-circle origin; only translation-invariant pair distances are used.) Assign to AB,BC,CD,DA the positive weights

\[
\frac{yw}{(x+y)(z+w)},\quad
\frac{xw}{(x+y)(z+w)},\quad
\frac{xz}{(x+y)(z+w)},\quad
\frac{yz}{(x+y)(z+w)}.
\]

They sum to one. Expansion of all four squared edge distances cancels every coefficient of e·f and gives their weighted average exactly xy+zw. Since each edge has squared length at least one, xy+zw≥1. Meanwhile

\[
|AC|^2+|BD|^2=(x+y)^2+(z+w)^2
\ge4xy+4zw\ge4.
\]

The four boundary edges have total squared length at least four, so all six distances have total at least eight. The weights and the two AM–GM identities include every nondegenerate convex quadrilateral, without any ordering of side lengths or assumption on the angle between diagonals.

## One point in the triangle or a boundary segment

If the four points are not the four vertices of a strictly convex quadrilateral, choose P in the convex hull of the other three. When P is strictly inside their triangle, the three consecutive angles around P sum to 2π, so one is at least 2π/3. The angle is at most π because P is inside the triangle. For its two endpoints U,V, put a=|PU| and b=|PV|; then a,b≥1 and

\[
|UV|^2=a^2+b^2-2ab\cos\angle UPV
\ge a^2+b^2+ab\ge3.
\]

The remaining five squared distances are each at least one, proving the same bound eight.

If P lies on the boundary of the triangle, or if all four points are collinear, choose two other points U,V for which P lies on their segment. Distinctness gives a,b≥1 and angle UPV=π, hence |UV|≥2 and the sum of all six squared distances is at least 4+5=9. Thus all degenerate hull cases are covered. No coincident-point case can occur because of the unit-distance hypothesis.

## Useful equivalent and affine forms

For the four-point mean m=(p_1+p_2+p_3+p_4)/4, the identity

\[
\sum_{i<j}\|p_i-p_j\|^2=4\sum_i\|p_i-m\|^2
\]

gives the equivalent planar spread inequality \(\sum_i\|p_i-m\|^2\ge2\).

If a *certified* coordinate difference d lies in [l,u], then

\[
d^2\le(l+u)d-lu.
\]

Adding this secant upper bound for the twelve coordinate differences gives an affine necessary row with right side at least eight. All interval guards must already hold on the unchanged parent before the row is installed. The quadratic inequality itself can be inserted directly in a common-moment model; planarity is its geometric justification, not an inference from PSD alone.

The statement is sharp: any unit-side rhombus whose two diagonals are at least one has sum eight, including the unit square. Consequently a stronger universal constant would be false.

No Lean, Lake, CI, human, or proof-kernel verification was performed. This independent mathematical review changes zero ledger counts until a complete original parent is excluded.
