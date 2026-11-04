# Complete B6ad original-cell proof

The certificate excludes the complete original cell
`negative-6ad5eef3b91c1fbd` in mask `001/00`. It earns one original-cell
closure and no whole-mask closure. The original path, all nine physical
unit squares, their 36 corners, all 36 pairs, and the strict CD predicate
are retained throughout.

## 1. Physical configuration and certified ancestor

Write the nine original centers as \(c_0,\ldots,c_8\), with labels
\(A,\ldots,I\). For square \(i\), use the same original orthonormal frame
\[
u_i=(\alpha_i,\beta_i),\qquad v_i=(-\beta_i,\alpha_i),
\qquad \alpha_i^2+\beta_i^2=1.
\]
Its four original corners are
\(c_i+(s u_i+t v_i)/2\), for \(s,t\in\{-1,1\}\). The physical scalar
variables additionally include \(z_i=|\beta_i|\) and
\(g_i=1/(2(\alpha_i+z_i))\). These are functions of the same original
frame. The certificate does not assign a different frame to a different
corner or pair.

The immutable original path is the one whose compact JSON SHA-256 prefix
is `6ad5eef3b91c1fbd`. The ancestor checker reconstructs it and verifies
34 coordinate deductions, followed by all 13 exact bound rounds:
837 deductions and 3,376 printed rows. Every bound is a nonnegative
rational sum of independently reconstructed physical inequalities with
an exact residual correction. Bounds from a round are installed only
after their premises from the preceding state have been checked.

Consequently every physical configuration in the original cell has
the following certified I-center rectangle:
\[
\begin{aligned}
L_x&=\frac{45713}{524288},&
U_x&=\frac54,\\
L_y&=-\frac{41615}{524288},&
U_y&=\frac{725451}{1048576}.
\end{aligned}
\]
These bounds are deductions about the whole original cell, rather than
new assumptions defining a smaller original cell.

## 2. A finite cover with all boundary faces retained

For \(r,s\in\{0,1,2,3\}\), define
\[
X_r=\left[L_x+\frac r4(U_x-L_x),
              L_x+\frac{r+1}4(U_x-L_x)\right],
\quad
Y_s=\left[L_y+\frac s4(U_y-L_y),
              L_y+\frac{s+1}4(U_y-L_y)\right].
\]
The sixteen closed rectangles \(X_r\times Y_s\) cover the entire
certified I-center rectangle. Adjacent rectangles share their common
face. No equality case is discarded. The other eight original centers
and all original frames retain their certified ancestor domains.

The table gives the contradiction for every rectangle. An exact reserve
floor means that the rational reserve stored in the certificate is at
least the listed positive rational number. `COVER_TABLE.json` contains
the same table and is checked against the exact replay outputs.

| Tile | I rectangle indices \(r,s\) | Contradiction | Used terminal rows | Exact reserve floor |
|---:|:---:|---|---:|---:|
| 0 | (0,0) | All four F–I original inset alternatives impossible | 0 | — |
| 1 | (0,1) | All four F–I original inset alternatives impossible | 0 | — |
| 2 | (0,2) | Affine rational sum | 10 | 1/64 |
| 3 | (0,3) | Quadratic rational sum | 1523 | 1/1024 |
| 4 | (1,0) | Affine rational sum | 3 | 1 |
| 5 | (1,1) | Affine rational sum | 29 | 1/512 |
| 6 | (1,2) | Quadratic rational sum | 1524 | 1/512 |
| 7 | (1,3) | Quadratic rational sum | 1537 | 1/1024 |
| 8 | (2,0) | Affine rational sum | 25 | 1/64 |
| 9 | (2,1) | Quadratic rational sum | 1535 | 1/512 |
| 10 | (2,2) | Quadratic rational sum | 13 | 1/32 |
| 11 | (2,3) | Affine rational sum | 3 | 1 |
| 12 | (3,0) | All four D–I original inset alternatives impossible | 0 | — |
| 13 | (3,1) | Affine rational sum | 3 | 1 |
| 14 | (3,2) | Affine rational sum | 3 | 1 |
| 15 | (3,3) | All four G–I original inset alternatives impossible | 0 | — |

The affine and interval checker recomputes every rectangle directly from
the independently proved ancestor, then repeats the exact interval
propagation and reconstructs each used physical row. The seven affine
terminals use 76 rows in total; the four interval terminals are exact
geometric interval contradictions.

## 3. The five remaining quadratic certificates

For each of the five remaining rectangles, let \(x\in\mathbb R^{54}\) consist of the
18 center coordinates and the 36 physical scalar variables above.
Introduce only the products \(x_i x_j\) with \(i\le j\). There are
1,539 linear and quadratic entries in this representation. Every
physical configuration defines these products simultaneously.

The five final certificates contain 6,132 nonzero weighted rows in total.
The independent checker reconstructs them from the original physical
variables: 187 affine premises for interval-factor products, counted
per certificate, and 96 explicit negative rational squares, together
with the required original corner and frame equations, exact interval
product inequalities, radial bounds and original owner-axis separation
rows. The final rectangle (2,2) needs only 13 quadratic rows and no
negative-square row.

For a proved affine row \(a\cdot x\le b\) and a proved scalar interval
\(l\le x_k\le u\), the two product inequalities are
\[
(x_k-l)(a\cdot x-b)\le0,
\qquad
(u-x_k)(a\cdot x-b)\le0.
\]
Both factors asserted nonnegative are checked in this same rectangle.
The checker reconstructs the affine premise before expanding either
quadratic product.

Each rational square row is simply
\[
-\left(q_0+\sum_{i=0}^{53}q_{i+1}x_i\right)^2\le0
\]
for an explicitly stored rational vector \(q\). Its coefficients are
expanded with exact rational arithmetic. Numerical eigenvalues and the
numerical semidefinite solver are not premises of this proof.

The fixed owner-axis rows use actual `sat` choices in the immutable
original path. If \(n\) is the chosen original owner axis and
\(\sigma\in\{-1,1\}\) its sign, physical separation implies
\[
2\sigma(c_j-c_i)\cdot n
\ge 1+|u_i\cdot u_j|+|\det(u_i,u_j)|
\ge 1+u_i\cdot u_j+\varepsilon\det(u_i,u_j)
\]
for either \(\varepsilon\in\{-1,1\}\). The checker requires that the
owner, axis and sign in each such row occur at the indicated position
of the original path. No new separation choice is assumed.

Two certificates also use the complete owner-axis union for the
original A–B pair. The checker enumerates all eight alternatives: either
original owner, either axis, and either sign. It removes an alternative
only after an exact physical interval contradiction. If the remaining
signed projections are \(p_a\ge l_a\), with \(l_a<1\), at least one
has \(p_a\ge1\), while every summand below is nonnegative. Therefore
\[
\sum_a\frac{p_a-l_a}{1-l_a}\ge1.
\]
This is a necessary inequality for the full surviving union. It does
not select an unproved separation alternative.

All radial rows used here are upper bounds. They follow directly from
original square containment: if \(r=\lVert c_i\rVert\), one original
corner has squared radius at least \(r^2+r+1/2\). Since
\((91/60)^2+91/60+1/2-1105/256=31/57600>0\), it follows that
\(r<91/60\). The checker uses the weaker non-strict squared bound,
intersected with the exact center-box bound.

Although four-center and square-area inequalities helped the numerical
discovery model, none occurs in these five final quadratic terminals.

## 4. Exact arithmetic contradiction and complete-parent conclusion

For each rational terminal, write the independently rebuilt rows as
\(a_r\cdot m\le b_r\), where \(m\) is the corresponding vector of
physical variables and, when used, their products. The stored weights
are positive integers divided by \(2^{40}\). Let
\[
c=\sum_r\lambda_r a_r,
\qquad b=\sum_r\lambda_r b_r,
\qquad R=-b-\sum_k B_k|c_k|,
\]
where \(|m_k|\le B_k\) follows from the checked scalar bounds.
For a product entry, \(B_{ij}=B_i B_j\). The exact checker verifies
every coefficient, every positive weight, the weighted right-hand side,
and the strictly positive rational number \(R\).

A physical configuration would imply both
\(c\cdot m\le b\) and \(c\cdot m\ge-\sum_kB_k|c_k|\).
The inequality \(R>0\) makes these incompatible. Every quadratic
rectangle has exact reserve at least \(1/1024\). The stronger per-tile
rational floors in the table are checked separately.

Every one of the sixteen closed rectangles is therefore impossible.
Their exhaustive cover excludes the complete original cell.

## 5. Replay boundary

Run `python -B -S verify_all.py` from this directory. The standard-library
runner checks the frozen byte manifest, replays the original ancestor,
reconstructs all sixteen rectangles, checks their exact contradictions,
and matches every entry of the table. Its audit hook disallows reads
from any external workspace path. Historical absolute paths in the raw
records are resolved through explicit frozen source bindings.

The final report is `COMPLETE_REPLAY.json`. A successful report grants
exactly one original-cell closure and zero mask closures. It does not
claim a Lean kernel proof; no Lean, Lake or CI was run.
