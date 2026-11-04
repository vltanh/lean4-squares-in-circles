# Shared physical frame square inequalities

Fix two distinct retained original squares with canonical oriented unit vectors
`u_i=(alpha_i,beta_i)` and `u_j=(alpha_j,beta_j)`. Their positively rotated
vectors are `v_i=(-beta_i,alpha_i)` and `v_j=(-beta_j,alpha_j)`. All four vectors
belong to the same physical realization as the original centers and corners.

A selected physical separating alternative already introduces six auxiliary
products. The last four equal

`z2=alpha_i alpha_j`, `z3=beta_i beta_j`,
`z4=alpha_i beta_j`, `z5=beta_i alpha_j`.

Write `C=z2+z3` and `S=z4-z5`. The exact dot products are

| Vectors | Dot product |
| --- | --- |
| u_i, u_j | C |
| v_i, v_j | C |
| u_i, v_j | -S |
| v_i, u_j | S |
| u_i, v_i | 0 |
| u_j, v_j | 0 |

Every vector has squared norm one. For any six rational numbers
`q=(x,y,a,b,c,d)`, nonnegativity of an ordinary squared Euclidean norm gives

\[
0\leq\|(x,y)+a u_i+b v_i+c u_j+d v_j\|^2
 = x^2+y^2+a^2+b^2+c^2+d^2
 +2(xa+yb)\alpha_i+2(ya-xb)\beta_i
 +2(xc+yd)\alpha_j+2(yc-xd)\beta_j
 +2(ac+bd)C+2(bc-ad)S.
\]

Moving the affine terms to the left gives a necessary rational linear row in
the existing variables. There is no sign restriction on the six rational
parameters, no division, no additional variable, no restriction of the caller,
and no dependence on an optimizer's conclusion. The proof uses the original
unit frames; it does not identify independent relaxed auxiliary values with
actual frames during discovery.

The producer `physical_pair_frame_squares.row(choices,slot,weights)` expands the
displayed identity. The independent checker reconstructs the complete sparse
off-diagonal Gram matrix instead and expands `-2 q_a q_b G_ab` entry by entry.
It derives the auxiliary slot from the retained path's ordered SAT choices,
checks both original indices, and validates every printed coefficient and
right side. The row name records the exact six rational parameters. The
generic nonnegative multiplier replay then treats the validated row exactly
like every other physical necessary inequality.

Numerical eigenvectors may suggest rational parameters; their approximation
quality affects only whether a useful inequality is found. Every rational
vector gives a valid inequality, so no numerical eigenvalue or eigenvector is
trusted by the proof. All nine originals, all 36 corners and pairs, strict CD,
and all previously retained closed faces stay in the enclosing caller.

The source-bound control replay independently rebuilds 376 rows and checks
18,424 exact physical evaluations across all eight separating alternatives.
It also rejects eight altered right sides. These identity checks give no new
original-cell or mask closure by themselves.
