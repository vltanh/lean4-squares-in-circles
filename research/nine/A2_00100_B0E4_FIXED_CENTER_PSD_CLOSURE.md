# Complete B0e4 original-cell proof

The certificate excludes the complete original cell
`negative-0e4fa3209b6f7b12` in mask `001/00`. It earns one original-cell
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
is `0e4fa3209b6f7b12`. The ancestor checker reconstructs it and verifies
34 coordinate deductions, followed by all 13 exact bound rounds:
746 deductions and 3,053 printed rows. Every bound is a nonnegative
rational sum of independently reconstructed physical inequalities with
an exact residual correction. Bounds from a round are installed only
after their premises from the preceding state have been checked.

Consequently every physical configuration in the original cell has
the following certified I-center rectangle:
\[
\begin{aligned}
L_x&=\frac{49758149082743}{70368744177664},&
U_x&=\frac54,\\
L_y&=\frac{91857}{524288},&
U_y&=\frac{188833794117659}{140737488355328}.
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

| Tile | I rectangle indices \((r,s)\) | Contradiction | Used terminal rows | Exact reserve floor |
|---:|:---:|---|---:|---:|
| 0 | (0,0) | Affine rational sum | 47 | 1/256 |
| 1 | (0,1) | Affine rational sum | 3 | 1 |
| 2 | (0,2) | Affine rational sum | 3 | 1 |
| 3 | (0,3) | Quadratic rational sum | 1535 | 1/512 |
| 4 | (1,0) | Affine rational sum | 3 | 1 |
| 5 | (1,1) | All four G–I original inset alternatives impossible | 0 | — |
| 6 | (1,2) | All four G–I original inset alternatives impossible | 0 | — |
| 7 | (1,3) | Affine rational sum | 5 | 1/32 |
| 8 | (2,0) | Affine rational sum | 3 | 1 |
| 9 | (2,1) | All four G–I original inset alternatives impossible | 0 | — |
| 10 | (2,2) | All four G–I original inset alternatives impossible | 0 | — |
| 11 | (2,3) | Affine rational sum | 3 | 1 |
| 12 | (3,0) | Affine rational sum | 3 | 1/8 |
| 13 | (3,1) | All four G–I original inset alternatives impossible | 0 | — |
| 14 | (3,2) | All four G–I original inset alternatives impossible | 0 | — |
| 15 | (3,3) | Empty propagated original center interval | 0 | — |

The affine and interval checker recomputes every rectangle directly from
the independently proved ancestor, then repeats the exact interval
propagation and reconstructs each used physical row. The eight affine
terminals use 70 rows in total; the seven interval terminals are exact
geometric interval contradictions.

## 3. The remaining quadratic certificate

For rectangle \((0,3)\), let \(x\in\mathbb R^{54}\) consist of the
18 center coordinates and the 36 physical scalar variables above.
Introduce only the products \(x_i x_j\) with \(i\le j\). There are
1,539 linear and quadratic entries in this representation. Every
physical configuration defines these products simultaneously.

The final certificate contains 1,535 nonzero weighted rows. The
independent checker reconstructs them from the original physical
variables, including 33 distinct affine premises used in products
with nonnegative interval factors, 21 explicit negative rational
squares, the original corner and frame equations, exact interval
product inequalities, two all-nine radial bounds, and two original
owner-axis separation rows.

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

Although four-center and square-area inequalities helped the numerical
discovery model, no such row occurs in this final quadratic terminal.

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
The inequality \(R>0\) makes these incompatible. In the quadratic
rectangle, the exact reserve is approximately 0.0026751930416154235,
and the simpler exact floor \(R\ge1/512\) is checked separately.

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
