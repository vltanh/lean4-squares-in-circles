# Whole six-body two-load completion at squared radius 17/4

**Status: TL.COMPLETE6 CLOSED by a hand proof.** Every six-square
parallel-layer skeleton supplied by
[TWO_LOAD_RECIPROCAL_RIGIDITY.md](TWO_LOAD_RECIPROCAL_RIGIDITY.md)
admits at most two further unit squares in the disk, even when those
additional squares have independent orientations and only physical
interior-disjointness is imposed. Thus such a skeleton cannot occur
in a nine-square packing in that disk.

This closes the entire six-body two-load family, including its simple
six-cycle and theta examples. The separate five-body theorem now reduces
that family to P.ALL; the four-body P completion remains open. A coarse
cyclic cell that also permits unresolved stresses with three or more
loaded bodies stays open. No Lean compilation or CI has been run.

## 1. Statement and inputs

Let
\[
 D=\{(x,y):x^2+y^2\le17/4\},\qquad
 E=[1,2]\times[-1/2,1/2],\quad W=-E.
\]
For \(j=L,R\), choose heights
\[
 -1<l_j<0<u_j<1,\qquad u_j-l_j\ge1.                        \tag{1}
\]
The six core squares are \(E,W\) and the four axis-aligned unit
squares with centers
\[
 (-1/2,l_L),\ (-1/2,u_L),\ (1/2,l_R),\ (1/2,u_R).
\]
Assume these core squares lie in \(D\) and have pairwise disjoint open
interiors. Any additional unit squares must lie in \(D\), be physically
interior-disjoint from the core, and be pairwise physically
interior-disjoint. No alignment assumption is imposed on them.

**Theorem.** There are at most two additional squares.

We use three proved local facts:

1. Every unit-square center in \(D\) satisfies \(|c|\le3/2\), and a
   square avoiding \(E,W\) has center \(-1<c_x<1\). Both are proved
   in [DIAGONAL_CENTER_EXCLUSION.md](DIAGONAL_CENTER_EXCLUSION.md).
2. The outer-face screen puts every point of a square avoiding \(E,W\)
   strictly between the lines \(x=-2\) and \(x=2\). This is the
   radial-terminal outer-face lemma in
   [RADIAL_SECTOR_POCKET_CAPACITY.md](RADIAL_SECTOR_POCKET_CAPACITY.md).
3. At most two independent squares fit in \(D\cap\{y\ge1/2\}\), and
   if there are two their center horizontal coordinates have strictly
   opposite signs. This is
   [HALF_CAP_CENTER_SEPARATION.md](HALF_CAP_CENTER_SEPARATION.md),
   with the reflected statement for \(y\le-1/2\).

## 2. Every extra center is above or below its entire core column

Let \((x,y)\) be the center of an additional square. Its open center
disk of radius \(1/2\) lies in its open interior. Consequently its
distance to every closed core square is at least \(1/2\).

If \(-1<x\le0\), the center's horizontal coordinate lies in the
horizontal span \([-1,0]\) of both left core squares. The distance
condition for the square at height \(l_L\) says
\(|y-l_L|\ge1\); for the square at height \(u_L\) it says
\(|y-u_L|\ge1\). Since \(u_L-l_L<2\), the two forbidden open
intervals overlap, and together these inequalities imply
\[
                   y\le l_L-1\quad\text{or}\quad y\ge u_L+1. \tag{2}
\]
The same argument for \(0\le x<1\) gives
\[
                   y\le l_R-1\quad\text{or}\quad y\ge u_R+1. \tag{3}
\]
At \(x=0\) both conclusions hold. Because \(l_j<0<u_j\), every
additional square has \(y<-1\) or \(y>1\). Call these the lower and
upper squares, respectively.

## 3. The core routes the whole squares into two caps

The union of the six core squares contains each of the full segments
\[
 [-2,2]\times\{1/2\},\qquad [-2,2]\times\{-1/2\}.            \tag{4}
\]
For the upper segment the internal left and right parts are covered by
the squares at heights \(u_L,u_R\), since \(0<u_j<1\). The terminal
edges supply the two end parts. The lower segment is covered similarly
by the squares at heights \(l_L,l_R\) and by the terminal edges.

An upper extra square cannot contain a point below height \(1/2\).
Otherwise its convexity, together with its interior center above height
one, would give an interior point on the upper segment in (4). To see
the interior assertion even if the point below is a boundary point,
every nontrivial convex combination of that point with the interior
center is interior. The outer-face screen ensures that the crossing
has \(-2<x<2\). It belongs to a closed core square, and every open
neighborhood of it meets that core square's open interior. This is a
physical overlap, a contradiction.

Thus every upper square lies wholly in \(y\ge1/2\); by reflection,
every lower square lies wholly in \(y\le-1/2\). Boundary points on the
two lines are allowed; they do not affect the argument.

## 4. A pair in one cap excludes the other cap

Each cap holds at most two additional squares. Suppose the upper cap
holds two. Their center horizontal coordinates have strictly opposite
signs by the cap theorem. For the negative one, (2) and the strict
center inequality \(y<3/2\) give
\[
                  u_L+1\le y<3/2,\qquad u_L<1/2.           \tag{5}
\]
The strict inequality follows from \(x\ne0\) and
\(x^2+y^2\le9/4\). The positive center similarly gives \(u_R<1/2\).
Together with (1), these bounds imply
\[
                             l_L<-1/2,\qquad l_R<-1/2.     \tag{6}
\]
Any lower additional center must use the lower alternative in (2) or
(3), so (6) would force \(y<-3/2\), contradicting its center bound.
Hence two upper squares exclude every lower square. Reflection proves
that two lower squares exclude every upper square.

If neither cap holds two, the total is at most one plus one. If a cap
holds two, the other is empty. In all cases there are at most two
additional squares, proving the theorem. \(\square\)

## 5. Application to positive physical stress

[TWO_LOAD_RECIPROCAL_RIGIDITY.md](TWO_LOAD_RECIPROCAL_RIGIDITY.md)
reduces every six-body component with exactly two circle-loaded bodies,
in the declared working radius window, to \(R^2=17/4\) and the two
terminals \(E,W\). The four remaining bodies are axis-aligned, with
two centers in each of the layers \(x=\pm1/2\). Their heights lie
strictly in \((-1,1)\), and the two heights in a layer differ by at
least one. Ordering them therefore gives exactly (1).

The theorem applies to the whole resulting family without using the
chosen contact edges, degrees, cycle lengths, or reciprocal-flow
weights. In particular it includes every admitted six-cycle and theta
graph. Since six core squares leave room for at most two additional
squares, a nine-square packing cannot contain such a component.

Combined with the existing exclusion of seven through nine bodies
with exactly two loads and the whole five-body reduction in
[FIVE_BODY_TWO_LOAD_REDUCTION.md](FIVE_BODY_TWO_LOAD_REDUCTION.md),
this leaves P.ALL as the only two-load completion obligation. No
statement about a component with three or more loads is inferred from
these completion results.
