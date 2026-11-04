# A shared normal and center-gap square

Let `d=center_j-center_i` for two retained original squares. A selected physical
separating alternative has one original-owned signed unit normal `n`. Its two
existing auxiliary products are `z0=n_x d_x` and `z1=n_y d_y`, so the physical
projection is exactly `n·d=z0+z1`.

For proved closed bounds `lo_k <= d_k <= hi_k`, nonnegative rectangle slack gives

\[
d_k^2\le (lo_k+hi_k)d_k-lo_k hi_k.
\]

Write the sum of these two affine secants as `D`. For arbitrary rational
`q=(x,y,a,b)`, the following expression is nonnegative:

\[
\begin{aligned}
0&\le\|(x,y)+a n+b d\|^2\\
 &\le x^2+y^2+a^2+b^2D
 +2a(x n_x+y n_y)+2b(x d_x+y d_y)+2ab(z0+z1).
\end{aligned}
\]

The second inequality is valid because `b²>=0`. Thus the final affine expression
is nonnegative. Moving its variable terms to the left gives a rational
necessary row. The selected owner, axis and sign express `n_x,n_y` linearly in
that same original's alpha and beta. This never substitutes a freely chosen
normal or mixes distinct physical realizations.

The independent checker expands the Gram matrix of `e_x,e_y,n,d` and replaces
only the final diagonal by the proved upper secant `D`. It reconstructs the
owner, signed axis and auxiliary slot from the retained physical SAT path. It
uses the independently propagated Cartesian difference bounds for that same
record. The exact row name records the four rational parameters.

Every parameter vector is valid. Numerical negative Gram eigenvectors merely
suggest useful parameters and play no role in arithmetic replay. The identity
also holds on every interval endpoint, so no closed face is omitted. No extra
variable, original, branch assumption or original-cell conclusion is added.

The companion control replay independently rebuilds 184 rows and checks 13,800
exact rational physical evaluations, including all 8 owner/axis/sign choices
and all four endpoint combinations of the difference rectangle. It rejects8
damaged right sides. The checked slack equals the physical squared norm plus
`b²` times the two nonnegative interval-product slacks.
