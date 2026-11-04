# Complete B79 original-cell proof

November 4, 2026. This is one of the two complete original-cell proofs in the
[204 CLOSED / 27 OPEN assembly](A2_00100_A2D5_B79_FIXED_CENTER_CLOSURES.md). The original mask remains OPEN.

This packet excludes the complete original cell negative-79cdbfcbed2f1fac
in mask 001/00. The proof retains all nine original physical unit squares,
their 36 original corners and all 36 original pairs, the immutable
original path, and its strict CD predicate. It earns one original-cell
closure and zero mask closures.

## 1. Same original geometry and exact ancestor

Each original center \(c_i\), \(i\in\{A,\ldots,I\}\), has one actual
orthonormal frame
\[
u_i=(\alpha_i,\beta_i),\quad v_i=(-\beta_i,\alpha_i),\quad
\alpha_i^2+\beta_i^2=1.
\]
Its four original corners are \(c_i+(s u_i+t v_i)/2\),
\(s,t\in\{-1,1\}\). The variables \(z_i=|\beta_i|\) and
\(g_i=1/[2(\alpha_i+z_i)]\) are functions of that same frame.
No corner or pair receives a separate frame.

The original path has compact JSON hash prefix 79cdbfcbed2f1fac.
The independent ancestor replay reconstructs that path and checks 34
coordinate deductions, followed by 11 exact bound rounds containing
606 further deductions and 2,040 printed rows.

Two separating-axis choices are already part of the immutable original
path: C–D and D–G, both using the positive second axis of original D.
The affine representation therefore also contains six derived product
coordinates per such pair. They are the two products of the signed normal
components with the corresponding original center differences, and the
four products \(\alpha_i\alpha_j,\beta_i\beta_j,
\alpha_i\beta_j,\beta_i\alpha_j\).
Every physical configuration gives these twelve quantities their actual
values. Their product bounds and separation inequalities are independently
reconstructed. The affine proof thus uses 66 physical and derived
coordinates; only original coordinates and original center differences
are targets of bound induction.

## 2. Exhaustive I-center cover

The certified ancestor gives
\[
c_I\in[-1/1048576,\;5/4]\times[-10403/131072,\;91/60].
\]
For each coordinate interval \([L,U]\), define the four closed intervals
\[
[L+j(U-L)/4,\;L+(j+1)(U-L)/4],\qquad j=0,1,2,3.
\]
All sixteen products are retained. Shared faces remain in the cover,
and the other eight original centers retain their entire certified
ancestor domains. There are no additional center subdivisions.

The table lists an exact contradiction for every rectangle. Positive
reserve floors are rational lower bounds on the exact stored reserves,
and the complete runner checks them against the replay results.

| I quarter indices | Contradiction | Used terminal rows | Exact reserve floor |
|:---:|---|---:|---:|
| (0,0) | All four F–I inset alternatives impossible | 0 | — |
| (0,1) | Direct affine rational sum | 26 | 1/1024 |
| (0,2) | Direct affine rational sum | 2 | 1/2 |
| (0,3) | Direct affine rational sum | 17 | 1/64 |
| (1,0) | Direct affine rational sum | 30 | 1/128 |
| (1,1) | Affine rational sum after proved bounds | 44 | 1/128 |
| (1,2) | Affine rational sum after proved bounds | 22 | 1/32 |
| (1,3) | Affine rational sum after proved bounds | 3 | 1 |
| (2,0) | Affine rational sum after proved bounds | 31 | 1/64 |
| (2,1) | Empty G–I inset union after proved bounds | 0 | — |
| (2,2) | Contradictory G frame bounds | 0 | — |
| (2,3) | Quadratic rational sum after proved bounds | 1539 | 1/2048 |
| (3,0) | Direct affine rational sum | 3 | 1 |
| (3,1) | Direct affine rational sum | 3 | 1 |
| (3,2) | All four G–I inset alternatives impossible | 0 | — |
| (3,3) | Direct affine rational sum | 3 | 1 |

The final weighted contradictions use 1,723 printed rows.
The seven local bound inductions use another 3,173 printed
premise rows, counted once within each round, and prove 1,776
bounds in 12 rounds. The ancestor proof is checked separately.
Six induced states end in affine or interval contradictions; the seventh
is certified OPEN and is the premise of the last quadratic certificate.

## 3. Exact finite bound induction

Inside each listed rectangle, the preceding proved state supplies
physical affine rows \(a_r\cdot m\le b_r\) and absolute bounds
\(|m_k|\le B_k\), including the twelve derived product coordinates when
present. For a target \(v\cdot m\), positive rational row multipliers give
\[
w=\sum_r\lambda_r a_r,\qquad b=\sum_r\lambda_r b_r.
\]
Every physical configuration in the same rectangle then satisfies
\[
v\cdot m\le b+\sum_k B_k|w_k-v_k|.
\]
The checker reconstructs each used physical row and verifies the exact
weighted sum and residual correction. The proposed dyadic upper bound
must be at least this rational value.

All proposals in one round use the same preceding state. Only after they
pass does the checker intersect the coordinate and center-difference
intervals. Any angle inference is checked against the same original unit
frame, and analytic frame bounds are intersected exactly. Each subsequent
round rebuilds its rows from this proved state. Consequently the tighter
intervals are conclusions about the whole listed rectangle, not extra
uncovered assumptions.

In I(2,1), the resulting exact state makes all four original G–I inset
separation alternatives impossible. The independent checker recomputes
this complete union from the derived physical angle and center intervals.

In I(2,2), the final bound round proves an empty physical frame interval
for original G. The independently checked slope bound implies
\[
\alpha_G\ge\frac{277664635599709}{281474976710656},
\qquad
\alpha_G\le\frac{59491}{65536},
\]
whose gap is
\[
\frac{22152736193373}{281474976710656}>0.
\]
The same exact deductions also give
\(\beta_G\in[-28237/524288,\;85975/524288]\) and
\(z_G\ge387475/1048576\), which contradict
\(z_G=|\beta_G|\). All 189 bound proofs and the physical frame inferences
in that round are checked before accepting this terminal.

The producer stopped immediately when that intersection became empty.
Its saved final-state fields consequently describe the preceding state.
The independent checker explicitly checks the final round's deductions
and the actual empty interval; those saved fields are never treated as a
new derived state.

## 4. The final quadratic certificate in I(2,3)

The three-round affine record for I(2,3) is OPEN. It is independently
replayed to obtain a certified state for the same complete original
rectangle. Its status is not itself a contradiction.

Using the same 54 original coordinates \(x\), introduce their simultaneous
products \(x_i x_j\), \(i\le j\), giving 1,539 entries. Every physical
configuration defines all these values. The quadratic checker first
reconstructs the original cell and exact I rectangle, then replays the
source-bound OPEN affine record, and finally reconstructs the quadratic
rows on the resulting certified state.

For a checked affine premise \(a\cdot x\le b\) and interval
\(l\le x_k\le u\), the valid product inequalities are
\[
(x_k-l)(a\cdot x-b)\le0,\qquad
(u-x_k)(a\cdot x-b)\le0.
\]
The checker rebuilds the actual affine premise before expanding these
products. Each explicit rational vector \(q\) also supplies the universal
inequality
\[
-\left(q_0+\sum_{k=0}^{53}q_{k+1}x_k\right)^2\le0.
\]
The exact rational coefficients are expanded independently. Numerical
eigenvalues and solver statuses are not proof premises.

Both original separating-axis choices are checked against their actual
path entries. For their signed unit normal \(n\), original separation gives
\[
2(c_j-c_i)\cdot n
\ge1+|u_i\cdot u_j|+|\det(u_i,u_j)|.
\]
It therefore implies each used signed quadratic row
\[
2(c_j-c_i)\cdot n
\ge1+u_i\cdot u_j+\varepsilon\det(u_i,u_j),
\qquad \varepsilon\in\{-1,1\}.
\]
All products use the same original frames.

The A–B owner-axis union is treated exhaustively. All eight alternatives
are considered, and an alternative is removed only after exact interval
exclusion. If its retained projections have proved lower bounds \(l_a<1\),
then at least one \(p_a\ge1\), while all \((p_a-l_a)/(1-l_a)\ge0\).
Hence their sum is at least one, a valid inequality for the whole union.

The used radial upper bounds follow directly from original corner
containment. A center of norm \(r\) has a corner of squared radius at least
\(r^2+r+1/2\). Since
\((91/60)^2+91/60+1/2-1105/256=31/57600>0\), one has \(r<91/60\).
The checker uses the weaker non-strict squared bound, intersected with
the exact coordinate-box bound.

## 5. Rational contradiction and complete original-cell conclusion

For each weighted terminal, let \(a_r\cdot m\le b_r\) be its independently
reconstructed physical rows. The positive multipliers have denominator
\(2^{40}\). Put
\[
c=\sum_r\lambda_r a_r,\qquad b=\sum_r\lambda_r b_r,\qquad
R=-b-\sum_k B_k|c_k|.
\]
The checker verifies all coefficients, bounds, multipliers and the exact
positive rational reserve \(R\), including the table's stated floor.
For a quadratic product, its absolute bound is the product of its
factors' proved absolute bounds.

A physical configuration would satisfy both \(c\cdot m\le b\) and
\(c\cdot m\ge-\sum_kB_k|c_k|\), which is impossible when \(R>0\).
The remaining terminals are the independently recomputed exact inset or
frame contradictions described above. All sixteen closed rectangles
are therefore impossible, and their full coverage excludes the entire
immutable original cell.

## 6. Portable independent replay

Run python -B -S verify_all.py from this packet. The standard-library
runner checks the complete byte manifest, replays the original ancestor,
reconstructs every I rectangle, checks all bound inductions and terminal
rows, and compares every table entry with the exact result.
An audit hook rejects external workspace reads. Historical source paths
resolve only to explicit frozen bytes inside the packet.

The independent checkers import no numerical producer or optimizer.
The full result is written to COMPLETE_REPLAY.json and grants exactly
one original-cell closure and zero mask closures. No Lean, Lake or CI
was run; the packet makes no Lean kernel claim.
