# Complete B5d7 original-cell proof

November 4, 2026. This complete original-cell exclusion advances the same
231-cell register from **200 CLOSED / 31 OPEN to 201 CLOSED / 30 OPEN**.
The remaining original families are **A5, B14, C8, D3**. The full-mask
ledger remains **8 CLOSED / 24 OPEN**. Mask `001/00`, its reversal
`100/00`, A.2, the unrestricted bound and global equality remain OPEN.

[Source-bound packet and root fresh replay](computer_assisted/a2_00100_b_5d7_psd_manifest.json) ·
[Fixed original register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Physical caller and coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md)

The root reviewer read the additional all-nine central-arc premise,
including its weak-clearance endpoints, and repeated the complete
standard-library replay from a relocated copy. The run passed with all
workspace reads confined to the packet. This is an exact rational replay
and written physical argument; no human or proof-kernel verification is
claimed. No Lean, Lake or CI was run.

The certificate excludes the complete original cell
`negative-5d7c9f118e060b2a` in mask `001/00`. It earns one original-cell
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
is `5d7c9f118e060b2a`. The ancestor checker reconstructs it and verifies
32 coordinate deductions, followed by all 13 exact bound rounds:
684 deductions and 2,095 printed rows. Every bound is a nonnegative
rational sum of independently reconstructed physical inequalities with
an exact residual correction. Bounds from a round are installed only
after their premises from the preceding state have been checked.

Consequently every physical configuration in the original cell has
the following certified I-center rectangle:
\[
\begin{aligned}
L_x&=-\frac{1}{1048576},&
U_x&=\frac54,\\
L_y&=-\frac{62903}{1048576},&
U_y&=\frac{91}{60}.
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

The original H center has the same certified coordinate intervals
\([L_x,U_x]\times[L_y,U_y]\). Only inside I rectangle \((2,3)\),
cover H by its two closed equal x halves and four closed equal y
quarters. These eight products exhaust the entire H rectangle, again
retaining common faces. The other fifteen I rectangles do not restrict
H beyond its ancestor bounds. This gives twenty-three complete
conditional rectangles and no deeper refinements.

The table gives the contradiction for every final rectangle. A pair
\((r,s)\) denotes an I rectangle; a four-tuple \((r,s,h_x,h_y)\)
adds the indicated H half and quarter. An exact reserve
floor means that the rational reserve stored in the certificate is at
least the listed positive rational number. `COVER_TABLE.json` contains
the same table and is checked against the exact replay outputs.

| I indices; optional H indices | Contradiction | Used terminal rows | Exact reserve floor |
|:---:|---|---:|---:|
| (0,0) | All four F–I original inset alternatives impossible | 0 | — |
| (0,1) | Affine rational sum | 3 | 1/16 |
| (0,2) | Affine rational sum | 3 | 1 |
| (0,3) | Affine rational sum | 3 | 1/8 |
| (1,0) | Affine rational sum | 3 | 1 |
| (1,1) | Quadratic rational sum | 1536 | 1/2048 |
| (1,2) | Quadratic rational sum | 19 | 1/128 |
| (1,3) | Quadratic rational sum | 1500 | 1/256 |
| (2,0) | Affine rational sum | 33 | 1/512 |
| (2,1) | Affine rational sum | 5 | 1/128 |
| (2,2) | Quadratic rational sum | 1507 | 1/512 |
| (2,3,0,0) | Affine rational sum | 3 | 1 |
| (2,3,0,1) | Quadratic rational sum | 1501 | 1/256 |
| (2,3,0,2) | Quadratic rational sum | 1517 | 1/512 |
| (2,3,0,3) | Affine rational sum | 11 | 1/128 |
| (2,3,1,0) | Affine rational sum | 30 | 1/128 |
| (2,3,1,1) | Affine rational sum | 3 | 1/32 |
| (2,3,1,2) | Empty propagated original center interval | 0 | — |
| (2,3,1,3) | All four H–I original inset alternatives impossible | 0 | — |
| (3,0) | Affine rational sum | 10 | 1/16 |
| (3,1) | Affine rational sum | 3 | 1 |
| (3,2) | All four G–I original inset alternatives impossible | 0 | — |
| (3,3) | Affine rational sum | 3 | 1 |

The affine and interval checker recomputes every rectangle directly from
the independently proved ancestor, then repeats the exact interval
propagation and reconstructs each used physical row. The thirteen affine
terminals use 113 rows in total; the four interval terminals are exact
geometric interval contradictions.

## 3. The six quadratic certificates

For each of the six quadratic rectangles, let \(x\in\mathbb R^{54}\) consist of the
18 center coordinates and the 36 physical scalar variables above.
Introduce only the products \(x_i x_j\) with \(i\le j\). There are
1,539 linear and quadratic entries in this representation. Every
physical configuration defines these products simultaneously.

The six final certificates contain 7,580 nonzero weighted rows in total.
The independent checker reconstructs them from the original physical
variables: 194 affine premises for interval-factor products, counted
per certificate, and 58 explicit negative rational squares, together
with the required original corner and frame equations, exact interval
product inequalities, radial bounds and a complete original owner-axis
union. I rectangle (1,2) needs only nineteen quadratic rows and no
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

One certificate uses the complete owner-axis union for the
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

The radial upper bounds follow directly from
original square containment: if \(r=\lVert c_i\rVert\), one original
corner has squared radius at least \(r^2+r+1/2\). Since
\((91/60)^2+91/60+1/2-1105/256=31/57600>0\), it follows that
\(r<91/60\). The checker uses the weaker non-strict squared bound,
intersected with the exact center-box bound.

One terminal also uses the all-nine radial lower bound
\(\lVert c_F\rVert>27/100\), weakened to the non-strict squared
inequality. This is an unconditional consequence of the included,
independently reviewed central-arc theorem. Every square in the closed
Q disk whose clearance from the origin is at least \(23/100\)
occupies more than \(\pi/4\) angular measure of the circle of radius
\(123/100\) through its open interior. If one original center had
norm at most \(27/100\), that square would contain the closed central
disk of radius \(23/100\), since each own coordinate of its center
has absolute value at most \(27/100\). Its eight companions would
then all have clearance at least \(23/100\); their disjoint
open-interior circle subsets would have total measure exceeding
\(8\pi/4=2\pi\), a contradiction. The complete arc proof, endpoint
treatment, and accepted independent review are frozen in
`ancestry/proofs/`. All nine original labels are essential to this
particular lower bound.

Although four-center and square-area inequalities helped the numerical
discovery model, none occurs in these six final quadratic terminals.

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
rectangle has exact reserve at least \(1/2048\). The stronger per-tile
rational floors in the table are checked separately.

Every one of the twenty-three final closed rectangles is therefore
impossible. The sixteen I rectangles and the exhaustive eight-piece H
cover inside I(2,3) exclude the complete original cell.

## 5. Replay boundary

Run `python -B -S verify_all.py` from this directory. The standard-library
runner checks the frozen byte manifest, replays the original ancestor,
reconstructs all twenty-three final rectangles, checks their exact contradictions,
and matches every entry of the table. Its audit hook disallows reads
from any external workspace path. Historical absolute paths in the raw
records are resolved through explicit frozen source bindings.

The final report is `COMPLETE_REPLAY.json`. A successful report grants
exactly one original-cell closure and zero mask closures. It does not
claim a Lean kernel proof; no Lean, Lake or CI was run.


## 6. Preserved interrupted numerical discovery

The numerical discovery for HI(2,3,0,1) stopped after saving its complete
numerical state and before writing its final square-export diagnostic.
The raw `interrupted_diagnostics.json` and `complete_numerical_state.npz`
are retained byte for byte. A separately source-bound continuation,
`recover_psd_square_export.py`, proposed rational square vectors from
that saved state. The completed diagnostic explicitly identifies this
recovery and records the raw-record, state and continuation hashes.

No numerical completion or numerical infeasibility status is claimed
for that stopped run. Every proposed vector defines a universal
negative-square inequality regardless of its origin. The independent
checker expands the actual rational vectors and verifies the exact
positive rational weighted sum. The complete runner also verifies all
preserved recovery-source bindings; it never imports a numerical
package or uses a floating-point state as a mathematical premise.
