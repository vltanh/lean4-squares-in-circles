# Complete B347 original-cell proof

November 4, 2026. This complete original-cell proof advances the same
231-cell register from **205 CLOSED / 26 OPEN to 206 CLOSED / 25 OPEN**.
The remaining original families are **A4, B10, C8, D3**. The full-mask
ledger remains **8 CLOSED / 24 OPEN**. Mask `001/00`, its reversal
`100/00`, A.2, the unrestricted bound and global equality remain OPEN.

[Source-bound packet and root fresh replay](computer_assisted/a2_00100_b_347_bound_manifest.json) ·
[Current fixed register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Physical caller and coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md)

The separate independent checks and the complete original-cell assembly
passed. The root then repeated the whole proof from a relocated frozen
packet. All source hashes remained unchanged. This is independent exact
rational arithmetic and a complete written physical argument; no human
or proof-kernel verification is claimed. No Lean, Lake or CI was run.

The complete original cell negative-3475db94338c355f in mask 001/00
is impossible. This certificate earns one original-cell closure and
zero mask closures. The proof retains all nine physical original unit
squares, their 36 original corners, all 36 original pairs, the immutable
original path and its strict CD predicate.

## 1. Original variables and exact ancestor

For each original square, use its one actual center \(c_i\) and frame
\[
u_i=(\alpha_i,\beta_i),\qquad v_i=(-\beta_i,\alpha_i),
\qquad \alpha_i^2+\beta_i^2=1.
\]
Its four corners are \(c_i+(s u_i+t v_i)/2\), \(s,t\in\{-1,1\}\).
The quantities \(z_i=|\beta_i|\) and
\(g_i=1/[2(\alpha_i+z_i)]\) refer to this same frame.
The 18 center coordinates and 36 scalar quantities give 54 original
variables.

The immutable original path has compact JSON hash prefix
3475db94338c355f. It already contains one actual C–D separating-axis
choice, using the positive second axis of original D. The affine model
also uses six derived products for this one original pair: the two
normal-component times center-difference products and the four frame
products \(\alpha_C\alpha_D,\beta_C\beta_D,\alpha_C\beta_D,
\beta_C\alpha_D\). Every physical configuration supplies their actual
values. Their product bounds and separation rows are independently
reconstructed, giving 60 physical and derived coordinates in the
affine certificate.

The independent whole-cell ancestor replay checks 31 coordinate
deductions followed by all 11 exact bound rounds, containing 592 further
deductions and 1,957 printed rows. It reconstructs the original path,
same actual frames and all used physical rows before the cover begins.

## 2. Complete finite cover with all faces retained

Both original centers H and I have the certified ancestor rectangle
\[
[-1/1048576,\;5/4]\times[-20825/262144,\;91/60].
\]
Divide each I coordinate interval \([L,U]\) into the four closed pieces
\[
[L+j(U-L)/4,\;L+(j+1)(U-L)/4],\qquad j=0,1,2,3.
\]
Retain all sixteen products and every common face.

Only inside I(2,3), divide the entire ancestor H rectangle into two
equal closed x halves and four equal closed y quarters. The other
fifteen I rectangles retain H's full ancestor domain. The resulting
cover has \(15+8=23\) rectangles, with no deeper subdivisions.
Every other original coordinate retains its certified ancestor domain
unless an exact bound deduction proves a stronger statement inside
that whole listed rectangle.

A pair in the table gives the I quarter indices. Four indices add the
H half and quarter. Each reserve floor is a positive rational lower
bound on the exact stored reserve and is checked by the complete runner.

| I indices; optional H indices | Contradiction | Used terminal rows | Exact reserve floor |
|:---:|---|---:|---:|
| (0,0) | All four F–I inset alternatives impossible | 0 | — |
| (0,1) | Original D unit-frame norm below one | 0 | — |
| (0,2) | Direct affine rational sum | 2 | 1/2 |
| (0,3) | Direct affine rational sum | 17 | 1/64 |
| (1,0) | Direct affine rational sum | 29 | 1/128 |
| (1,1) | Affine rational sum after proved bounds | 38 | 1/512 |
| (1,2) | Affine rational sum after proved bounds | 21 | 1/32 |
| (1,3) | Affine rational sum after proved bounds | 31 | 1/64 |
| (2,0) | Affine rational sum after proved bounds | 31 | 1/64 |
| (2,1) | Empty G–I inset union after proved bounds | 0 | — |
| (2,2) | Affine rational sum after proved bounds | 9 | 1 |
| (2,3,0,0) | Direct affine rational sum | 36 | 1/128 |
| (2,3,0,1) | Affine rational sum after proved bounds | 24 | 1/256 |
| (2,3,0,2) | Affine rational sum after proved bounds | 5 | 1/32 |
| (2,3,0,3) | Direct affine rational sum | 13 | 1/128 |
| (2,3,1,0) | Original D unit-frame norm below one | 0 | — |
| (2,3,1,1) | Direct affine rational sum | 3 | 1/32 |
| (2,3,1,2) | empty propagated original center interval | 0 | — |
| (2,3,1,3) | All four H–I inset alternatives impossible | 0 | — |
| (3,0) | Direct affine rational sum | 3 | 1 |
| (3,1) | Direct affine rational sum | 3 | 1 |
| (3,2) | All four G–I inset alternatives impossible | 0 | — |
| (3,3) | Direct affine rational sum | 3 | 1 |

The final weighted contradictions use 268 rows. The ten local
bound inductions add 3,516 printed premise rows, counted once
within each round, and prove 2,293 bounds in 14 rounds.
The complete final proof uses affine rational sums and exact interval
contradictions.

## 3. Exact finite bound induction

Let \(m\) be the vector of original quantities and the six actual
derived products. At a round, the preceding proved state supplies
physical inequalities \(a_r\cdot m\le b_r\) and absolute bounds
\(|m_k|\le B_k\). For a target \(v\cdot m\), positive rational multipliers
give
\[
w=\sum_r\lambda_r a_r,\qquad b=\sum_r\lambda_r b_r,\qquad
v\cdot m\le b+\sum_k B_k|w_k-v_k|.
\]
The checker independently rebuilds every used physical row and verifies
all multipliers, the weighted coefficients and the exact residual
correction. The proposed dyadic bound is checked to round upward.
Only original scalar coordinates and original center differences are
targets.

Every proposal within a round uses the same preceding state. After those
proofs pass, the checker intersects the bounds, verifies physical frame
inferences, and intersects the exact analytic frame bounds. It then
reconstructs the next round in that proved state. These deductions
restrict no uncovered configuration: they are consequences valid
throughout the whole listed rectangle.

In I(0,1), the exact bound round proves the following bounds on
original D's actual frame:
\[
\alpha_D\in\left[\frac{495463}{524288},\frac{1014131}{1048576}\right],\qquad
\beta_D\in\left[-\frac{244207}{1048576},-\frac{52893}{262144}\right].
\]
The independently computed deficit is
\[
1-\left(\frac{1014131}{1048576}\right)^2
 -\left(\frac{244207}{1048576}\right)^2
=\frac{5706441883}{549755813888}>0.
\]
This contradicts the original unit-frame identity
\(\alpha_D^2+\beta_D^2=1\). All 220 preceding weighted deductions
and the four recorded partial frame inferences are checked exactly.

The producer stopped during that terminal round. Its saved final-state
fields consequently still describe the preceding state. The independent
checker reconstructs the new deductions and the actual empty angle
interval; it does not treat those saved fields as a new derived state.
The elementary squared-norm deficit above is also independently checked.

The same type of terminal excludes HI(2,3,1,0). Its 229 exact bound
deductions give
\[
\alpha_D\in\left[\frac{247253}{262144},\frac{1011705}{1048576}\right],\qquad
\beta_D\in\left[-\frac{126157}{524288},-\frac{102349}{524288}\right].
\]
Consequently
\[
1-\left(\frac{1011705}{1048576}\right)^2
 -\left(\frac{126157}{524288}\right)^2
=\frac{12302266155}{1099511627776}>0,
\]
again contradicting the same original D unit frame. The checker verifies
the four recorded partial frame inferences and this exact deficit before
accepting the terminal.

In I(2,1), the independently recomputed post-induction state makes all
four original G–I inset alternatives impossible. Each original square
contains its axis-aligned inset square of half-side \(g_i\). Disjoint
open interiors therefore require one of the four signed coordinate
gaps to be at least \(g_G+g_I\). All four alternatives are excluded
by exact interval bounds, retaining the weak-contact boundary cases.

## 4. Shared physical-square area rows used by the induction

Three used printed rows follow from the physical-square area moment theorem.
For a subset of \(k\) original unit squares, write \(\bar c\) for their
average center and let \(B\) be the fixed rational \(2\times2\) matrix
specified by the row. Their interiors are disjoint, so their union
has area \(k\). A unit square in any orthonormal orientation has second
moment matrix \(I/12\) about its center. Thus
\[
\int_S\|B(x-\bar c)\|^2\,dx
=\sum_i\|B(c_i-\bar c)\|^2+\frac{k}{12}\|B\|_F^2.
\]
Under the linear image by \(B\), the equal-area disk minimizes the
integral of squared radius. For nonsingular \(B\), this gives the
lower bound \(k^2|\det B|/(2\pi)\) for the integral above.
Using the pair-energy identity and \(\pi<22/7\),
\[
\sum_{i<j}\|B(c_i-c_j)\|^2
\ge\frac{7k^3}{44}|\det B|-\frac{k^2}{12}\|B\|_F^2.
\]
If \(B\) is singular, the displayed lower bound is nonpositive and the
claim follows directly. The complete area argument is frozen in the
included physical-square area moment hand proof.

These area inequalities give necessary affine rows through the exact
secant inequality
\[
t^2\le(a+b)t-ab,\qquad a\le t\le b.
\]
Every coordinate difference or projected difference uses a proved
interval in the same round. The independent checker reconstructs the
area secants from those intervals and the explicit
original label subset and matrix. No numerical sample selects a new
geometric premise.

## 5. Exact terminal contradiction and full-cell conclusion

For a weighted terminal, combine its independently reconstructed
inequalities \(a_r\cdot m\le b_r\) with the stored positive integer
multipliers divided by \(2^{40}\). Write
\[
c=\sum_r\lambda_r a_r,\qquad b=\sum_r\lambda_r b_r,\qquad
R=-b-\sum_k B_k|c_k|.
\]
The checker verifies all coefficients, physical absolute bounds, weights,
the exact rational reserve \(R>0\), and the table's reserve floor.
The six derived product coordinates use their physically justified
absolute bounds.

A physical configuration would imply both \(c\cdot m\le b\) and
\(c\cdot m\ge-\sum_kB_k|c_k|\), which are incompatible when \(R>0\).
The other terminals are the independently recomputed exact interval
contradictions. Every one of the twenty-three closed rectangles is
therefore impossible. Their exhaustive coverage excludes the entire
immutable original cell.

## 6. Portable replay and common ancestor

Run python -B -S verify_all.py from this packet. The standard-library
runner checks the frozen byte inventory, reconstructs the original
ancestor and all cover rectangles, verifies all bound rounds and final
contradictions, and compares every table entry with the exact results.

The ancestor certificate hash in every bound leaf and every conditional
H cover must equal the hash used by the coarse I cover. These explicit
gates prevent mixing quarter grids computed from different certified
ancestor boxes. The audit hook also rejects external workspace reads;
historical source paths resolve only to explicit frozen copies.

The packet retains the unused coarse I(2,3) OPEN bound record as frozen
provenance. The final INDEX selects the full H cover there and exactly
ten closed bound records; the OPEN record contributes no terminal or
induction credit to the final cover.

No numerical producer or optimizer is imported. The generated
COMPLETE_REPLAY.json grants exactly one original-cell closure and
zero mask closures. No Lean, Lake or CI was run; no Lean kernel claim
is made.


## Reconstruct the committed packet

From `research/nine/computer_assisted`, run:

```sh
cat a2_00100_b_347_bound_checkpoint.tar.gz.part01 a2_00100_b_347_bound_checkpoint.tar.gz.part02 > a2_00100_b_347_bound_checkpoint.tar.gz
printf '%s  %s\n' 9144aec45ce793d50c3173429a54b53d3319e50353eb70d83adefdc7580415e6 a2_00100_b_347_bound_checkpoint.tar.gz | sha256sum -c -
tar -xzf a2_00100_b_347_bound_checkpoint.tar.gz
cd b_347_bound_package
python -B -S verify_all.py
```
