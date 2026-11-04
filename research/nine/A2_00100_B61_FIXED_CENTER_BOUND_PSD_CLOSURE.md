# Complete B61 original-cell proof

November 4, 2026. This complete original-cell proof advances the same
231-cell register from **207 CLOSED / 24 OPEN to 208 CLOSED / 23 OPEN**.
The remaining original families are **A4, B9, C7, D3**. The full-mask
ledger remains **8 CLOSED / 24 OPEN**. Mask `001/00`, its reversal
`100/00`, A.2, the unrestricted bound and global equality remain OPEN.

[Source-bound packet and root fresh replay](computer_assisted/a2_00100_b_61_bound_manifest.json) ·
[Current fixed register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Physical caller and coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md)

The separate independent checks and the complete original-cell assembly
passed. The root then repeated the whole proof from a relocated frozen
packet. All source hashes remained unchanged. This is independent exact
rational arithmetic and a complete written physical argument; no human
or proof-kernel verification is claimed. No Lean, Lake or CI was run.

The complete original cell negative-61b796e2fa1d59e4 in mask 001/00 is
impossible. The proof earns one original-cell closure and zero mask closures.
It retains all nine physical original unit squares, their 36 original corners,
all 36 original pairs, the immutable original path, and its strict CD predicate.

## 1. Same original geometry and exact ancestor

Original square \(i\) has one actual center \(c_i\) and one frame
\[
u_i=(\alpha_i,\beta_i),\qquad v_i=(-\beta_i,\alpha_i),\qquad
\alpha_i^2+\beta_i^2=1.
\]
Its corners are \(c_i+(s u_i+t v_i)/2\), \(s,t\in\{-1,1\}\).
The quantities \(z_i=|\beta_i|\) and
\(g_i=1/[2(\alpha_i+z_i)]\) use that same frame. The eighteen center
coordinates and these thirty-six scalar quantities give 54 original variables.
All induced bounds concern these same original quantities and center differences.
The certified canonical frame intervals have \(\alpha_i>0\), so the actual
frame slope is \(t_i=\beta_i/\alpha_i\).

The source-bound original path has compact JSON hash prefix 61b796e2fa1d59e4.
The independent ancestor replay checks 31 coordinate
deductions and 10 exact rounds containing 418
further deductions and 1453 printed rows. Its original frames, pair
predicates, coordinate and frame bounds, and physical rows are reconstructed
before any cover rectangle is attached.

## 2. Complete fixed cover

The certified original centers H and I both lie in
\[
[-1/1048576,\;5/4]\times[-111499/1048576,\;91/60].
\]
For each coordinate interval \([L,U]\), retain all four closed quarters
\([L+j(U-L)/4,L+(j+1)(U-L)/4]\), \(j=0,1,2,3\).
Their sixteen products cover the entire I domain, including shared faces.
Only inside I(2,3), divide the entire original-parent H rectangle into two
closed x halves and four closed y quarters. This replaces one coarse member
by all eight products and gives exactly \(15+8=23\) final rectangles.
Every other coordinate retains its full certified domain until a proved
bound deduction strengthens it throughout that whole rectangle.

Two indices below specify I; four indices also specify H. Each positive
reserve floor is checked against the independently replayed exact reserve.

| I indices; optional H indices | Contradiction | Used terminal rows | Exact reserve floor |
|:---:|---|---:|---:|
| (0,0) | All four F–I inset alternatives impossible | 0 | — |
| (0,1) | Contradictory original D g bounds | 0 | — |
| (0,2) | Direct affine rational sum | 2 | 1/2 |
| (0,3) | Direct affine rational sum | 16 | 1/64 |
| (1,0) | Direct affine rational sum | 24 | 1/128 |
| (1,1) | Quadratic rational sum after proved bounds | 1534 | 1/2048 |
| (1,2) | Affine rational sum after proved bounds | 3 | 1 |
| (1,3) | Affine rational sum after proved bounds | 31 | 1/64 |
| (2,0) | Affine rational sum after proved bounds | 35 | 1/128 |
| (2,1) | Affine rational sum after proved bounds | 3 | 1 |
| (2,2) | Affine rational sum after proved bounds | 5 | 1 |
| (2,3,0,0) | Direct affine rational sum | 30 | 1/128 |
| (2,3,0,1) | Affine rational sum after proved bounds | 28 | 1/512 |
| (2,3,0,2) | Affine rational sum after proved bounds | 30 | 1/256 |
| (2,3,0,3) | Direct affine rational sum | 13 | 1/256 |
| (2,3,1,0) | All four G–H inset alternatives impossible | 0 | — |
| (2,3,1,1) | Direct affine rational sum | 3 | 1/32 |
| (2,3,1,2) | Empty propagated original center interval | 0 | — |
| (2,3,1,3) | All four H–I inset alternatives impossible | 0 | — |
| (3,0) | Direct affine rational sum | 3 | 1/32 |
| (3,1) | Direct affine rational sum | 3 | 1 |
| (3,2) | All four G–I inset alternatives impossible | 0 | — |
| (3,3) | Direct affine rational sum | 3 | 1 |

The final contradictions use 1766 printed terminal rows. The ten
local affine records prove 2379 bounds in 15 rounds using
3507 printed induction rows. Nine records end in exact affine or
interval contradictions. The I(1,1) record is certified OPEN and supplies
the proved state for its separate quadratic contradiction.

## 3. Exact affine bound induction and interval terminals

Suppose the preceding proved state supplies physical inequalities
\(a_r\cdot x\le b_r\) and absolute bounds \(|x_k|\le B_k\).
For a target \(v\cdot x\), positive rational multipliers give
\[
w=\sum_r\lambda_r a_r,\quad b=\sum_r\lambda_r b_r,\qquad
v\cdot x\le b+\sum_kB_k|w_k-v_k|.
\]
The checker reconstructs every used physical row and verifies the exact
weighted coefficients, residual correction and upward rounding of each
proposed dyadic bound. Every proposal in a round uses the same preceding
state. Only after all proposals pass are intervals intersected, physical
frame inferences checked, and analytic frame bounds intersected. Thus every
later round is a consequence for the same complete rectangle.

In I(0,1), the exact weighted deductions and same-frame analytic bounds give
\[
g_D\ge \frac{445015}{1048576},\qquad
g_D\le \frac{115962941438211}{281474976710656}.
\]
Their exact positive gap is \(\frac{3494863013629}{281474976710656}\).

When the producer exits during an empty frame intersection, its saved final
fields still describe the preceding state. The independent checker verifies
the new deductions and the actual empty intersection directly; those saved
fields are never treated as a newly derived state.

Direct inset terminals are also recomputed exactly. Each square contains
its axis-aligned inset square of half-side \(g_i\). Disjoint open interiors
force one of four signed coordinate gaps to be at least \(g_i+g_j\).
An inset terminal excludes all four alternatives by exact interval bounds.
An empty propagated center interval is checked by the same exact propagation.
Weak-contact cases remain in the closed cover.

## 4. Physical-square area rows

The local bound proofs use 4 printed physical-square area rows.
For a subset of \(k\) original unit squares, let \(\bar c\) be the average
center and let \(B\) be the rational two-by-two matrix printed in the row.
The union \(S\) has area \(k\), and every oriented unit square has second
moment matrix \(I/12\) about its center. Hence
\[
\int_S\|B(x-\bar c)\|^2\,dx
=\sum_i\|B(c_i-\bar c)\|^2+\frac{k}{12}\|B\|_F^2.
\]
For nonsingular \(B\), the equal-area disk bound applied after the linear
map gives a lower bound \(k^2|\det B|/(2\pi)\) for this integral.
The pair-energy identity and \(\pi<22/7\) therefore imply
\[
\sum_{i<j}\|B(c_i-c_j)\|^2
\ge\frac{7k^3}{44}|\det B|-\frac{k^2}{12}\|B\|_F^2.
\]
For singular \(B\), the right side is nonpositive and the claim is immediate.
The full area proof is frozen under ancestry/proofs. The exact secant
\(t^2\le(a+b)t-ab\) for \(a\le t\le b\) converts this necessary energy
bound into affine rows using the same round's proved projected-difference
intervals. Every subset, matrix, interval and coefficient is reconstructed.

## 5. Quadratic certificate on the proved I(1,1) state

The OPEN affine record for I(1,1) is independently replayed first. With the
same original 54 coordinates \(x\), introduce all simultaneous products
\(x_i x_j\), \(i\le j\), giving 1,539 entries. Every physical configuration
assigns them their actual values. No original corner or pair acquires another
frame. The certificate uses 1534 terminal rows, 45 rebuilt affine
antecedents, and 23 explicit rational negative squares.

Corner-circle, point-circle, unit-frame, absolute-frame, reciprocal-frame,
support and pair-distance inequalities are expanded in these same original
variables. The point-circle rows use points of the same original squares.
Every two original centers have distance at least one, since their unit
squares contain open center disks of radius one half. Product bounds follow
from nonnegative products such as \((x_i-l_i)(x_j-l_j)\ge0\), with all
factor endpoints taken from proved intervals. For a
checked affine premise \(a\cdot x\le b\) and \(l\le x_k\le u\), the products
\[
(x_k-l)(a\cdot x-b)\le0,\qquad (u-x_k)(a\cdot x-b)\le0
\]
are valid. The checker rebuilds the premise before expanding each such row.
For each explicit rational vector \(q\), it also expands the universal row
\[
-\left(q_0+\sum_{k=0}^{53}q_{k+1}x_k\right)^2\le0.
\]
Numerical eigenvalues and solver statuses are not proof premises.

One used A–B projection lower bound concerns their actual difference and
original A frame. For a fixed frame slope \(t\), the projection is linear
in the difference coordinates, so its extrema on a rectangle occur at
vertices. At each vertex it has the form
\((X+tY)/\sqrt{1+t^2}\); its extrema on a slope interval occur at endpoints
or at \(t=Y/X\) when that stationary point is defined and belongs to the
interval. Exact rational comparisons with these finitely many radical
values verify the printed bound. This introduces no chosen separating-axis
case. The independent replay also reconstructs all 288 original pair-axis
alternatives used to certify the supplied projection-guard inventory.

The used original-D radial upper row follows directly from its four corner
containment inequalities. For \(r=\|c_D\|\), one corner has squared radius
at least \(r^2+r+1/2\), because the frame is orthonormal. Since
\[
(91/60)^2+91/60+1/2-1105/256=31/57600>0,
\]
one has \(r<91/60\). The checker uses the weak squared upper bound,
intersected with the exact coordinate-box upper bound, and independently
checks the guard metadata.

## 6. Rational terminal sums and whole-original conclusion

For each weighted terminal, write its physical rows as
\(a_r\cdot m\le b_r\), where \(m\) denotes original variables or their
simultaneous quadratic products. Positive integer multipliers divided by
\(2^{40}\) give
\[
c=\sum_r\lambda_r a_r,\quad b=\sum_r\lambda_r b_r,\quad
R=-b-\sum_kB_k|c_k|.
\]
All coefficients, weights, physical absolute bounds and the exact reserve
\(R>0\) are independently checked. A product's absolute bound is the
product of its factors' proved absolute bounds. A physical configuration
would imply both \(c\cdot m\le b\) and
\(c\cdot m\ge-\sum_kB_k|c_k|\), contradicting \(R>0\).
The other leaves have the exact interval contradictions above.
All twenty-three closed rectangles are therefore impossible, and their
complete coverage excludes the immutable original cell.

## 7. Portable complete replay

Run python -B -S verify_all.py from this packet. The standard-library master
checks the frozen byte inventory, original ancestor, complete I cover,
complete conditional H cover, every bound proof and quadratic expansion,
and every table entry and reserve floor. Each bound or PSD result must name
the same original path, full tile and ancestor certificate hash as the
coarse affine cover. The PSD antecedent's OPEN bound-state replay must also
have that same ancestor hash. These gates prevent combining quarter grids
from differently tightened original boxes.

An audit hook rejects external workspace reads. Historical source paths
resolve only to explicitly bound frozen copies. No producer or optimizer
is imported. COMPLETE_REPLAY.json grants exactly one original-cell closure
and zero mask closures. No Lean, Lake or CI was run, and no Lean kernel
claim is made.


## Reconstruct the committed packet

From `research/nine/computer_assisted`, run:

```sh
cat a2_00100_b_61_bound_checkpoint.tar.gz.part01 a2_00100_b_61_bound_checkpoint.tar.gz.part02 > a2_00100_b_61_bound_checkpoint.tar.gz
printf '%s  %s\n' 41c5b9dfd85d7659719454d99033bda566aec4547a845c0194ce3c6f4d5e73f6 a2_00100_b_61_bound_checkpoint.tar.gz | sha256sum -c -
tar -xzf a2_00100_b_61_bound_checkpoint.tar.gz
cd b_61_bound_package
python -B -S verify_all.py
```
