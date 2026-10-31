# n=9 G2.C4.2b — large zigzag excludes a perpendicular four-chain

**Status: complete exact structural hand proof for the
common-coordinate-separable branch.**
No local tilt bounds or computed positional subdivision.
This is a statement about an entire *crossed-chain*
structural possibility; it does NOT yet exclude every
nine-square packing with a zigzag.

## Theorem

Let nine independently oriented unit squares fit in a
disk of squared radius \(q\le1105/256\). Suppose there
exists a fixed orthonormal frame \((e,f)\) in which
**every pair** of squares has disjoint open projections
on at least one of \(e,f\).

Suppose four of the squares form a chain with pairwise
disjoint e-projections, ordered \(M_1,M_2,M_3,M_4\),
and their centers contain a vertical gap \(\ge2\)
(in the f-coordinate).

Then **no four-square chain with pairwise
disjoint f-projections exists**.

Consequently, in the common-frame poset notation
of ORTHOGONAL_RANK_DICHOTOMY.md, the longest
horizontal chain has length \(a=4\), while
the longest vertical chain has \(b\le3\).
Since nine squares require \(9\le ab\),
we in fact have
\[
                           \boxed{(a,b)=(4,3).} \tag{1}
\]

*Proof.* The exact chain normal form
[FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md](FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md)
gives
\[
\begin{aligned}
|c_S|&<61/40\quad\text{for every square},\\
 |x_2|,|x_3|&<21/40,\\
 \text{one of }y_2,y_3&>1/2,\quad
 \text{the other }<-1/2,\quad
 |y_2-y_3|\ge2.
\end{aligned} \tag{2}
\]

Write \(M_H\) for the higher inner-chain square,
\(M_L\) for the lower one. Since their vertical
gap is at least 2, **either**
\[
                         y_H\ge1
                 \qquad\text{or}\qquad y_L\le-1.
                 \tag{3}
\]
Indeed the alternative \(y_H<1\) and \(y_L>-1\)
would give \(y_H-y_L<2\).

Suppose, toward contradiction, that the packing
also contains four squares with pairwise disjoint
*f*-projections. Apply the same quantized-chain
lemma with axes exchanged. Its top endpoint
square \(T\) and bottom endpoint square \(B\)
then have
\[
 \begin{aligned}
 y_T&>59/40,& |x_T|&<2/5,\\
 y_B&<-59/40,& |x_B|&<2/5 .
 \end{aligned}\tag{4}
\]

If \(y_H\ge1\), compare \(M_H\) with T.
By (2)--(4),
\[
 |x_H-x_T|<21/40+2/5=37/40<1,\qquad
 |y_H-y_T|<61/40-1=21/40<1. \tag{5}
\]
(The second inequality uses \(1\le y_H<61/40\)
and \(59/40<y_T<61/40\).)
Both coordinate center differences are strictly
less than 1. But each oriented unit square has
projection halfwidth at least 1/2 along *each*
frame axis. Thus two squares whose center
coordinate differences both have magnitude <1
cannot be separated by either coordinate
projection. This contradicts the assumed
common-coordinate separability.

If \(y_L\le-1\), compare \(M_L\) with B
and obtain the same inequalities by reflection,
again contradicting coordinate separability.

Thus no vertical four-chain exists. The absence
of five-chains follows from the universal
radius bound, while the given horizontal
four-chain forces \(a=4\). The rank injection
\(9\le ab\), with \(b\le3\), then yields
\(b=3\). \(\square\)

## Consequence and limitation

The large-zigzag branch of G2.C4 no longer
has an additional 4×4 rank case: it lives
entirely in a 4×3 rank rectangle with
exactly nine occupied distinct rank cells.
The 3×3 fully occupied rank grid has already
been excluded by GRID_FOUR_CORNER_STRESS.md.

**Still open:** prove that the nine occupied
cells in the 4×3 rank rectangle and the
middle-pair zigzag (2) are incompatible with
\(q\le q_*\), or derive a new compact sharp
stress certificate for every possibility.
An arbitrary oblique-separated packing does
not satisfy the premise of this theorem and
is handled under G2.O2/O3.

This result is a finite structural exclusion,
not a small tightening of an angle or radius
parameter. No Lean compilation or CI was run.
