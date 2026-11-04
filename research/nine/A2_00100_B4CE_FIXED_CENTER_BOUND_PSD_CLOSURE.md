# Complete B4ce original-cell proof

November 4, 2026. This complete original-cell proof advances the same
231-cell register from **209 CLOSED / 22 OPEN to 210 CLOSED / 21 OPEN**.
The remaining original families are **A4, B8, C6, D3**. The full-mask
ledger remains **8 CLOSED / 24 OPEN**. Mask `001/00`, its reversal
`100/00`, A.2, the unrestricted bound and global equality remain OPEN.

[Source-bound packet and root fresh replay](computer_assisted/a2_00100_b_4ce_bound_psd_manifest.json) ·
[Current fixed register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Physical caller and coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md)

The separate independent checks and the complete original-cell assembly
passed. The root then repeated the whole proof from a relocated frozen
packet. All source hashes remained unchanged. This is independent exact
rational arithmetic and a complete written physical argument; no human
or proof-kernel verification is claimed. No Lean, Lake or CI was run.

The complete original cell negative-4ce055f43b28d796 in mask 001/00 is
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
Their necessary circle inequalities use the closed squared-radius bound
\(Q=1105/256\).
The quantities \(z_i=|\beta_i|\) and
\(g_i=1/[2(\alpha_i+z_i)]\) use that same frame. The eighteen center
coordinates and these thirty-six scalar quantities give 54 original variables.
All induced bounds concern these same original quantities and center differences.
The certified canonical frame intervals have \(\alpha_i>0\), so the actual
frame slope is \(t_i=\beta_i/\alpha_i\).

The source-bound original path has compact JSON hash prefix 4ce055f43b28d796.
The independent ancestor replay checks 30 coordinate
deductions and 5 exact rounds containing 191
further deductions and 531 printed rows. Its original frames, pair
predicates, coordinate and frame bounds, and physical rows are reconstructed
before any cover rectangle is attached.

## 2. Complete fixed cover

The certified original centers H and I both lie in
\[
[-245887/1048576,\;5/4]\times[-91/60,\;91/60].
\]
For each coordinate interval \([L,U]\), retain all four closed quarters
\([L+j(U-L)/4,L+(j+1)(U-L)/4]\), \(j=0,1,2,3\).
Their sixteen products cover the entire I domain, including shared faces.
Inside each of I(1,3) and I(2,3), divide the entire original-parent H rectangle
into two closed x halves and four closed y quarters. Each replacement retains
all eight products, giving exactly \(14+8+8=30\) final rectangles.
Every other coordinate retains its full certified domain until a proved
bound deduction strengthens it throughout that whole rectangle.

Two indices below specify I; four indices also specify H. Each positive
reserve floor is checked against the independently replayed exact reserve.

| I indices; optional H indices | Contradiction | Used terminal rows | Exact reserve floor |
|:---:|---|---:|---:|
| (0,0) | Affine rational sum after proved bounds | 28 | 1/2048 |
| (0,1) | Direct affine rational sum | 19 | 1/128 |
| (0,2) | Direct affine rational sum | 5 | 1 |
| (0,3) | Quadratic rational sum after proved bounds | 1537 | 1/8192 |
| (1,0) | Direct affine rational sum | 3 | 1 |
| (1,1) | Affine rational sum after proved bounds | 30 | 1/512 |
| (1,2) | All four F–I inset alternatives impossible | 0 | — |
| (1,3,0,0) | Affine rational sum after proved bounds | 30 | 1/512 |
| (1,3,0,1) | Affine rational sum after proved bounds | 23 | 1/512 |
| (1,3,0,2) | Direct affine rational sum | 26 | 1/1024 |
| (1,3,0,3) | Affine rational sum after proved bounds | 3 | 1/2 |
| (1,3,1,0) | Empty propagated original center interval | 0 | — |
| (1,3,1,1) | Affine rational sum after proved bounds | 26 | 1/1024 |
| (1,3,1,2) | Direct affine rational sum | 3 | 1/32 |
| (1,3,1,3) | All four H–I inset alternatives impossible | 0 | — |
| (2,0) | Empty propagated original center interval | 0 | — |
| (2,1) | All four F–I inset alternatives impossible | 0 | — |
| (2,2) | Contradictory original E alpha bounds | 0 | — |
| (2,3,0,0) | Affine rational sum after proved bounds | 30 | 1/512 |
| (2,3,0,1) | Affine rational sum after proved bounds | 23 | 1/512 |
| (2,3,0,2) | All four F–H inset alternatives impossible | 0 | — |
| (2,3,0,3) | Quadratic rational sum after proved bounds | 1532 | 1/16384 |
| (2,3,1,0) | Empty propagated original center interval | 0 | — |
| (2,3,1,1) | All four F–H inset alternatives impossible | 0 | — |
| (2,3,1,2) | Empty propagated original center interval | 0 | — |
| (2,3,1,3) | All four H–I inset alternatives impossible | 0 | — |
| (3,0) | Direct affine rational sum | 5 | 1 |
| (3,1) | All four D–I inset alternatives impossible | 0 | — |
| (3,2) | Direct affine rational sum | 3 | 1/1024 |
| (3,3) | Direct affine rational sum | 3 | 1 |

The final contradictions use 3329 printed terminal rows. The sixteen
local affine records prove 5647 bounds in 39 rounds using
9576 printed induction rows. 14 records end in exact affine or interval contradictions.
The 2 records for I(0,3), HI(2,3,0,3) are certified OPEN and supply the
proved states for their separate quadratic contradictions.

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

For HI(1,3,0,1), HI(2,3,0,1), a separate source-bound continuation appends
at most three rounds to a frozen completed three-round OPEN record. The
checker verifies the old file hash, exact equality of its first three rounds,
all original source bindings, and the old final state against the first
appended round's preceding state. It then replays every round from the
original ancestor. These continuations retain the same whole rectangle;
they introduce no branch or additional geometric assumption.

In I(2,2), the exact weighted deductions and same-frame analytic bounds give
\[
\alpha_E\ge \frac{276243972583697}{281474976710656},\qquad
\alpha_E\le \frac{513763}{524288}.
\]
Their exact positive gap is \(\frac{419562221841}{281474976710656}\).

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

## 4. Four-center and physical-square energy rows

The local bound proofs use 3 printed four-center rows. For any four
selected original centers, all six pair distances are at least one because
the original squares contain disjoint open disks of radius one half. Their
six squared distances have sum at least eight, as follows.

For a strictly convex quadrilateral, label the vertices A,B,C,D in cyclic
order. From the diagonal intersection write
\(A=xe,C=-ye,B=zf,D=-wf\), where
\(x,y,z,w>0\) and \(e,f\) are unit vectors. Give the four cyclic
squared edge lengths AB,BC,CD,DA the respective weights
\[
\frac{yw}{(x+y)(z+w)},\quad\frac{xw}{(x+y)(z+w)},\quad
\frac{xz}{(x+y)(z+w)},\quad\frac{yz}{(x+y)(z+w)}.
\]
These weights sum to one; expansion cancels the cross terms and gives
their weighted average \(xy+zw\). Since each edge has squared length
at least one, \(xy+zw\ge1\). The diagonal squared lengths therefore sum to
\((x+y)^2+(z+w)^2\ge4xy+4zw\ge4\). The four edges contribute at least
four more, proving the bound eight.

Otherwise one point \(P\) belongs to the closed convex hull of the other
three. If it lies on a segment between two of them, their separation is at
least two, and their squared distance plus the other five is at least nine.
If \(P\) lies strictly inside their triangle, the three consecutive angles
about it sum to \(2\pi\), so one is at least \(2\pi/3\). Its two radial
lengths \(a,b\) are at least one; the cosine rule gives the corresponding
outer squared edge at least \(a^2+b^2+ab\ge3\). The remaining five
squared distances are each at least one, again giving eight. This includes
all hull, boundary and collinear cases.

For every proved difference interval \(l\le d\le u\),
\(d^2\le(l+u)d-lu\). Replacing each squared coordinate difference in
the six-pair energy by this affine upper bound yields a necessary affine
row with threshold eight. The identity
\(d_x^2+d_y^2=((d_x+d_y)^2+(d_x-d_y)^2)/2\) also permits proved
diagonal intervals. Each used row is the unconditional total-energy bound
for its same four original centers. The checker rebuilds all labels,
intervals and coefficients; the full theorem and independent review are
frozen as FOUR_ORIGINAL_PLANAR_MATCHING_AND_ENERGY_HAND_PROOF.md and
FOUR_ORIGINAL_PLANAR_ENERGY_INDEPENDENT_REVIEW.md under ancestry/proofs.

The local bound proofs use 3 printed physical-square area rows.
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
The full area proof is frozen as PHYSICAL_SQUARE_AREA_MOMENT_HAND_PROOF.md
under ancestry/proofs. The exact secant
\(t^2\le(a+b)t-ab\) for \(a\le t\le b\) converts this necessary energy
bound into affine rows using the same round's proved projected-difference
intervals. Every subset, matrix, interval and coefficient is reconstructed.

## 5. Quadratic certificates on independently proved states

Each selected OPEN affine record (I(0,3), HI(2,3,0,3)) is independently replayed first. With the
same original 54 coordinates \(x\), introduce all simultaneous products
\(x_i x_j\), \(i\le j\), giving 1,539 entries. Every physical configuration
assigns them their actual values. No original corner or pair acquires another
frame. The quadratic certificates together use 3069 terminal rows, 92 rebuilt
affine antecedents, and 45 explicit rational negative squares.

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

The I(0,3) numerical run stopped at its declared iteration budget with
no positive paid numerical reserve. The original diagnostic and full saved
numerical state remain byte-for-byte intact. A separate source-bound
continuation suggested rational negative squares; every such square is
universally valid regardless of the numerical dual or eigenvalue.
The active-row rational sum was then reconstructed and accepted independently.

The provenance preflight checks the raw diagnostic and saved-state hashes,
the frozen square-export source, and exact equality of every diagnostic field
except the explicitly added square list, stop reason and continuation record.
It also checks that the active candidate binds this continued diagnostic and
its square list. The independently reviewed complete-cover logic is retained
byte-for-byte except for the import of the extended affine-bound checker.
The assembly preflight verifies that this is the only source change, then
performs every mathematical replay. The numerical status receives no proof
credit.

Each used radial upper bound follows from the same original corners: for \(r=\|c_i\|\), a corner has squared radius at least \(r^2+r+1/2\). Since \((91/60)^2+91/60+1/2-1105/256=31/57600>0\), one has \(r<91/60\). The checker intersects the weak squared upper bound with the exact coordinate-box bound.

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
All thirty closed rectangles are therefore impossible, and their
complete coverage excludes the immutable original cell.

## 7. Portable complete replay

Run python -B -S verify_all.py from this packet. The standard-library master
checks the frozen byte inventory, original ancestor, complete I cover,
both complete conditional H covers, every bound proof and quadratic expansion,
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
cat a2_00100_b_4ce_bound_psd_checkpoint.tar.gz.part01 a2_00100_b_4ce_bound_psd_checkpoint.tar.gz.part02 a2_00100_b_4ce_bound_psd_checkpoint.tar.gz.part03 a2_00100_b_4ce_bound_psd_checkpoint.tar.gz.part04 > a2_00100_b_4ce_bound_psd_checkpoint.tar.gz
printf '%s  %s\n' e27189ede76b941ba27ff92369cc784ef428c2bfccc4f75f4738bd078fabe38d a2_00100_b_4ce_bound_psd_checkpoint.tar.gz | sha256sum -c -
tar -xzf a2_00100_b_4ce_bound_psd_checkpoint.tar.gz
cd b_4ce_bound_package
python -B -S verify_all.py
```
