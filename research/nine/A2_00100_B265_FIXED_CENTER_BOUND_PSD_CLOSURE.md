# Complete B265 original-cell proof

November 4, 2026. This complete original-cell exclusion advances the same
231-cell register from **201 CLOSED / 30 OPEN to 202 CLOSED / 29 OPEN**.
The remaining original families are **A5, B13, C8, D3**. The full-mask
ledger remains **8 CLOSED / 24 OPEN**. Mask `001/00`, its reversal
`100/00`, A.2, the unrestricted bound and global equality remain OPEN.

[Source-bound packet and fresh root replay](computer_assisted/a2_00100_b_265_psd_manifest.json) ·
[Fixed original register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Physical caller and coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md)

All thirteen quadratic certificates and all five local bound-induction
proofs passed separate independent reconstruction. The root then repeated
the entire assembly from a relocated packet: every original ancestor,
every closed cover rectangle and every exact terminal passed. This is an
exact rational replay and complete written physical argument. No human
or proof-kernel verification is claimed. No Lean, Lake or CI was run.

This packet excludes the complete original cell negative-2652afcd308ef1ea
in mask 001/00. It earns one original-cell closure and zero mask closures.
All nine original physical unit squares, their 36 original corners,
all 36 original pairs, the immutable original path and its strict CD
predicate are retained.

## 1. Physical variables and certified ancestor

For each original label \(i\in\{A,\ldots,I\}\), write its center as \(c_i\)
and its one actual orthonormal frame as
\[
u_i=(\alpha_i,\beta_i),\qquad v_i=(-\beta_i,\alpha_i),
\qquad \alpha_i^2+\beta_i^2=1.
\]
The four original corners are \(c_i+(s u_i+t v_i)/2\), with
\(s,t\in\{-1,1\}\). The scalar variables
\(z_i=|\beta_i|\) and \(g_i=1/[2(\alpha_i+z_i)]\)
refer to this same frame. These 18 center coordinates and 36 scalar
variables form one vector \(x\in\mathbb R^{54}\).

The original path is independently reconstructed and its compact JSON
hash prefix is checked against 2652afcd308ef1ea. The frozen whole-cell
ancestor has 33 coordinate deductions followed by 13 exact bound rounds,
923 further deductions, and 2,341 printed rows. Every installed bound is
proved from the preceding state. Its geometry and exact rational arithmetic
are replayed before the finite cover is considered.

The resulting original center rectangles are
\[
\begin{aligned}
c_I&\in[-25101/131072,\;5/4]\times[-77491/1048576,\;91/60],\\
c_H&\in[-25101/131072,\;0]\times[362967/524288,\;91/60].
\end{aligned}
\]
They are deductions about the complete original cell.

## 2. Complete closed-rectangle cover

Divide each coordinate interval of \(c_I\) into four consecutive equal
closed parts. For an interval \([L,U]\), part \(j\) is
\([L+j(U-L)/4,\;L+(j+1)(U-L)/4]\).
All sixteen products are retained, including their shared boundary faces.

Inside each of the two I rectangles (1,1) and (2,3), cover the entire
original H rectangle by two equal closed x halves and four equal closed
y quarters. Those H cuts are taken from the same certified ancestor
rectangle, without discarding any surviving H position. The other
fourteen I rectangles retain the full ancestor H domain. Thus the final
cover has \(14+2\cdot8=30\) rectangles, with no deeper refinement.

A pair in the table denotes I quarter indices; four indices add H half
and quarter indices. A reserve floor is a positive rational lower bound
on the exact stored reserve, independently checked by the complete runner.

| I indices; optional H indices | Contradiction | Used terminal rows | Exact reserve floor |
|:---:|---|---:|---:|
| (0,0) | All four F–I inset alternatives impossible | 0 | — |
| (0,1) | Affine rational sum | 3 | 1/16 |
| (0,2) | Affine rational sum | 3 | 1 |
| (0,3) | Affine rational sum | 3 | 1 |
| (1,0) | Affine rational sum | 3 | 1 |
| (1,1,0,0) | Affine rational sum | 3 | 1 |
| (1,1,0,1) | Quadratic rational sum | 1494 | 1/256 |
| (1,1,0,2) | Quadratic rational sum | 1534 | 1/2048 |
| (1,1,0,3) | Affine sum after proved bound induction | 44 | 1/512 |
| (1,1,1,0) | All four H–I inset alternatives impossible | 0 | — |
| (1,1,1,1) | Affine rational sum | 29 | 1/64 |
| (1,1,1,2) | Quadratic rational sum | 1502 | 1/512 |
| (1,1,1,3) | Affine sum after proved bound induction | 41 | 1/1024 |
| (1,2) | Quadratic rational sum | 1525 | 1/1024 |
| (1,3) | Quadratic rational sum | 1508 | 1/512 |
| (2,0) | Quadratic rational sum | 1534 | 1/2048 |
| (2,1) | Quadratic rational sum | 14 | 1/64 |
| (2,2) | Quadratic rational sum | 26 | 1/512 |
| (2,3,0,0) | Affine sum after proved bound induction | 43 | 1/1024 |
| (2,3,0,1) | Affine sum after proved bound induction | 9 | 1/32 |
| (2,3,0,2) | Quadratic rational sum | 1538 | 1/8192 |
| (2,3,0,3) | Quadratic rational sum | 1537 | 1/32768 |
| (2,3,1,0) | Affine sum after proved bound induction | 39 | 1/1024 |
| (2,3,1,1) | Quadratic rational sum | 1535 | 1/4096 |
| (2,3,1,2) | Quadratic rational sum | 17 | 1/256 |
| (2,3,1,3) | Quadratic rational sum | 1521 | 1/512 |
| (3,0) | Affine rational sum | 3 | 1/64 |
| (3,1) | Affine rational sum | 3 | 1 |
| (3,2) | All four G–I inset alternatives impossible | 0 | — |
| (3,3) | Affine rational sum | 3 | 1 |

The complete cover has 9 direct affine terminals,
3 exact interval terminals, 13 quadratic terminals,
and five affine terminals following proved bound induction. Their final
contradictions use 15,514 printed rows. The five local inductions
add 3,014 distinct-per-round printed premise rows and prove
2,297 bounds in 12 rounds in total. Ancestor rows
are recorded and checked separately.

## 3. Finite bound induction inside an unchanged rectangle

Each of the five induction certificates starts with exactly the original
ancestor plus the table's explicit I and H coordinate guards. At a round,
all used physical affine rows \(a_r\cdot x\le b_r\) are independently
reconstructed in the preceding state. Each target is either one signed
original scalar coordinate, or one signed coordinate difference between
two original centers.

Let \(v\cdot x\) be the target. For positive rational row weights
\(\lambda_r\), put
\[
w=\sum_r\lambda_r a_r,\qquad b=\sum_r\lambda_r b_r,\qquad e=w-v.
\]
If the current proved box gives \(|x_k|\le B_k\), then every physical
configuration in this rectangle satisfies
\[
v\cdot x=w\cdot x-e\cdot x
\le b+\sum_k B_k|e_k|.
\]
The proposed upper bound is the rational right-hand side rounded upward
to the printed dyadic grid. The checker verifies the exact weighted sum,
all positive multipliers, the residual correction, and the direction of
rounding. It installs only the intersection with that proved bound.

All proposals within one round use the same preceding state. The exact
physical frame equations justify any subsequent angle inference, and
analytic scalar bounds are intersected only after that inference passes.
The checker then reconstructs the next round's rows in the new proved
state. Thus no installed bound is an unproved extra assumption and none
creates a smaller uncovered branch.

Each of these five runs ends with an ordinary positive rational affine
contradiction. There is no numerical or semidefinite premise in these
five terminals.

## 4. Thirteen quadratic rational certificates

The quadratic representation contains the same 54 physical variables
and the products \(x_i x_j\), \(i\le j\), for a total of 1,539 entries.
A physical configuration defines all these products simultaneously.

The thirteen certificates use 15,285 final weighted rows, including
424 independently rebuilt affine premises for interval-factor products
and 189 explicit negative rational squares, counted per certificate.
Every original corner, frame, product and separation row used in the
weighted sum is reconstructed independently.

For a proved affine row \(a\cdot x\le b\) and proved interval
\(l\le x_k\le u\), the relevant product inequalities are
\[
(x_k-l)(a\cdot x-b)\le0,\qquad
(u-x_k)(a\cdot x-b)\le0.
\]
The affine premise and both interval bounds are checked in the same
physical rectangle before the product coefficients are expanded.

A rational square row is the universal inequality
\[
-\left(q_0+\sum_{k=0}^{53}q_{k+1}x_k\right)^2\le0.
\]
Its explicit rational vector is expanded exactly. Numerical eigenvalues,
solver residuals and solver statuses are not proof premises.

The used owner-axis union concerns the original A–B pair. The checker
starts with all eight actual separating-axis alternatives: either original
owner, either axis and either sign. It discards an alternative only through
an exact interval contradiction. For the surviving projections \(p_a\)
with proved lower bounds \(l_a<1\), at least one satisfies \(p_a\ge1\),
and all displayed summands are nonnegative. Therefore
\[
\sum_a\frac{p_a-l_a}{1-l_a}\ge1.
\]
This is valid on the complete surviving union. No unproved separating-axis
choice is promoted to a premise.

## 5. The all-nine radial premise

The radial upper bound follows directly from original corner containment.
For \(r=\|c_i\|\), one corner has squared radius at least \(r^2+r+1/2\).
Since
\[
(91/60)^2+91/60+1/2-1105/256=31/57600>0,
\]
one has \(r<91/60\). The replay uses its weaker non-strict squared form,
intersected with the exact coordinate-box maximum.

Four quadratic terminals also use the all-nine lower bound
\(\|c_F\|>27/100\), weakened to its non-strict squared form. The included
central-arc theorem says that any unit square in the closed Q disk whose
clearance from the origin is at least \(23/100\) occupies more than
\(\pi/4\) angular measure of the radius-\(123/100\) circle through its
open interior. If an original center had norm at most \(27/100\),
that square would contain the closed radius-\(23/100\) central disk:
each own-frame coordinate of its center has absolute value at most
\(27/100\). The other eight original squares would have clearance at
least \(23/100\). Their disjoint open-interior circle subsets would then
have total measure greater than \(8\pi/4=2\pi\), a contradiction.

The full central-arc argument, endpoint treatment, radial corollary and
accepted independent review are frozen under ancestry/proofs. This
premise uses all nine original labels. The checker reconstructs the
actual lower row and exact guard; it does not infer the premise from a
numerical sample.

## 6. Rational contradiction and complete-cell conclusion

For any final terminal, write its independently reconstructed inequalities
as \(a_r\cdot m\le b_r\). Here \(m=x\) in an affine terminal, and \(m\)
also includes the exact original-variable products in a quadratic terminal.
The positive stored multipliers have denominator \(2^{40}\). Set
\[
c=\sum_r\lambda_r a_r,\qquad b=\sum_r\lambda_r b_r,\qquad
R=-b-\sum_k B_k|c_k|.
\]
The bound \(|m_k|\le B_k\) is proved from the checked state; a product
uses the product of its factor absolute bounds. The exact replay checks
every coefficient and verifies \(R>0\) and the table's reserve floor.

A physical configuration would imply both
\(c\cdot m\le b\) and \(c\cdot m\ge-\sum_kB_k|c_k|\).
The positive reserve makes these incompatible. The interval terminals
instead have independently reconstructed empty intervals or an empty
complete inset-alternative union. Every one of the thirty closed
rectangles is therefore impossible. Their exhaustive coverage proves
the complete original cell impossible.

## 7. Preserved numerical provenance and replay boundary

The numerical run for HI(2,3,0,3) exhausted its declared iteration budget
without a positive paid numerical dual. Its completed-budget diagnostic
and saved numerical arrays are retained unchanged. A separate continuation
proposed rational square vectors from those arrays; any rational vector
defines the universal negative-square inequality regardless of its origin.
The continuation has explicit source and raw-data hashes and does not
claim numerical infeasibility. A subsequent exact weighted certificate,
independently expanded and checked, supplies the contradiction.

Run python -B -S verify_all.py from this packet. The standard-library
runner checks the complete frozen byte manifest, the original ancestor,
all thirty coordinate rectangles, every used row and bound proof, and
every table entry. It verifies the preserved continuation bindings.
The audit hook disallows external workspace reads; historical source
paths resolve only to explicit frozen copies. No numerical producer or
optimizer is imported.

The generated COMPLETE_REPLAY.json grants exactly one original-cell
closure and zero mask closures. This is an independently replayed exact
computer-assisted proof, without a Lean kernel claim. No Lean, Lake or
CI was run.

## 8. Delivered archive

The [ordered part inventory](computer_assisted/a2_00100_b_265_psd_archive_parts.json)
records each part and the full archive hash. From the directory containing
the two parts, reconstruct and run the complete proof with:

```sh
cat a2_00100_b_265_psd_checkpoint.tar.xz.part01 a2_00100_b_265_psd_checkpoint.tar.xz.part02 > a2_00100_b_265_psd_checkpoint.tar.xz
tar -xJf a2_00100_b_265_psd_checkpoint.tar.xz
cd b_265_psd_package
python -B -S verify_all.py
```

The complete compressed archive is 10,433,852 bytes, with SHA-256
`21124d68cc25fe4b126ae8c647ca3d2b7e0560680abec9cef0091a621110219b`.
