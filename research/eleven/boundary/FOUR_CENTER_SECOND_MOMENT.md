# Exact second-moment bound for four centers

For any four points `p_i` in the plane with all six mutual distances at
least one, and their centroid `m`,

\[
 \sum_{i=1}^4 |p_i|^2\ge 2+4|m|^2.              \tag{1}
\]

Equality in the centered bound means that the four points are the vertices
of a unit-side rhombus with both diagonals at least one. If they are centers
of four pairwise open-interior-disjoint unit squares, equality forces a
common orientation and a two-by-two square arrangement.

## Proof

Translate the centroid to zero and write the resulting points as `c_i`.
Set

\[
 x=c_1+c_2,\quad y=c_1+c_3,\quad z=c_1+c_4.
\]

The six mutual differences, up to sign, are `x+y`, `x-y`, `x+z`, `x-z`,
`y+z`, `y-z`. Moreover,

\[
 S:=\sum_i|c_i|^2=|x|^2+|y|^2+|z|^2.
\]

Let `G` be the three-by-three Gram matrix of `x,y,z`, with diagonal
entries `a,b,c`. The six distance inequalities imply

\[
 |G_{ij}|\le (G_{ii}+G_{jj}-1)/2.
\]

Therefore the sum of the absolute off-diagonal entries in the row with
diagonal `a` is at most `(a+S-2)/2`, and likewise in the other rows.

Suppose `S<2`. None of `a,b,c` is zero: for example `a=0` would force
`b>=1` and `c>=1`. Each row is consequently strictly diagonally dominant
with positive diagonal, since `(a+S-2)/2<a/2<a`. The symmetric matrix
`G` is then positive definite. Explicitly, `2|u_i u_j|<=u_i^2+u_j^2`
bounds its quadratic form below by

\[
 \sum_i\left(G_{ii}-\sum_{j\ne i}|G_{ij}|\right)u_i^2>0
\]

for every nonzero vector `u`. This is impossible for the Gram matrix of
three planar vectors, whose rank is at most two. Hence `S>=2`, and
adding back the centroid gives (1).

If `S=2` and all three diagonal entries were positive, the same argument
would still make `G` positive definite. Thus one is zero, say `z=0`.
The distances involving `z` imply `a,b>=1`, so `a=b=1`. The four centers
are then `+(x+y)/2`, `+(x-y)/2`, `-(x-y)/2`, `-(x+y)/2`: a unit-side
rhombus, with the remaining two distance inequalities asserting that its
diagonals have length at least one.

For square centers, any pair at center distance one must have a common
frame with the center displacement along one of its axes. Indeed every
separating-axis support threshold is at least one, while its displacement
projection is at most one. Equality forces the separating axis to be the
center direction and both support half-widths to be `1/2`. Applying this
to all four unit-length sides of the rhombus forces one common square
frame and orthogonal adjacent rhombus sides. The rhombus is a square.

## Scope and discovery limitation

This is a rigorous necessary condition available in the four-core case.
It does not exclude that case. In a sampled forty-circle angular-budget
linear program, adding the weaker consequence `sum |p_i|^2>=2` receives
zero dual weight and does not improve the bound. Thus the moment theorem
alone does not resolve the missing core-to-ring interaction. The script
`four_core_moment_discovery.py` is numerical discovery only and is not an
exhaustive certificate.
