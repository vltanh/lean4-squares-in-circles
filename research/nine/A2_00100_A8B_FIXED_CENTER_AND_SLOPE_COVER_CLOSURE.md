# Original A8b: complete fixed-center and inherited-slope contradiction

November 4, 2026. This complete original-cell proof advances the same
231-cell register from **214 CLOSED / 17 OPEN to 215 CLOSED / 16 OPEN**.
The remaining original families are **A3, B6, C4, D3**. The full-mask
ledger remains **8 CLOSED / 24 OPEN**. Mask `001/00`, its reversal
`100/00`, A.2, the unrestricted bound and global equality remain OPEN.

[Source-bound packet and root fresh replay](computer_assisted/a2_00100_a_8b_fixed_center_slope_manifest.json) ·
[Current fixed register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Physical caller and coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md)

The separate independent checks and the complete original-cell assembly
passed. The complete proof was repeated from a relocated frozen packet.
The root independently checked all 219 input hashes, the two replay
summaries, exact accounting and attachment to the original register.
All source hashes remained unchanged. This is independent exact
rational arithmetic and a complete written physical argument; no human
or proof-kernel verification is claimed. No Lean, Lake or CI was run.

This is the complete hand/table argument for the source-bound finite cover.
The executable replay supplies its exact arithmetic and accepts this one
unchanged original cell only after every member and every cover gate pass.
An internal tile is never counted as an original cell or an entire mask.

## Scope and unchanged original caller

The original is `positive-8b53ccaa15bad220` in the `001/00` frontier. Its
complete canonical path is

```json
[["angle",3,1],["angle_cut",[0,"0"],0],["inward_row_escape",[7,8],[3]]]
```

All nine original physical unit squares A through I remain present, with
their independent frames, all 36 original corners, all 36 pairwise physical
nonoverlap conditions, the original marked actual links, and the strict
weak-link bit. In particular, the inward-row child retains the complements
of every earlier escape row, as prescribed by the canonical caller.
No closed sibling's complement is inferred without those predecessor
guards. The order of H and I is retained; no exchange of their labels or
reflection of the caller is used.

The exact inherited state is
`central_cover_bounds/positive-8b53ccaa15bad220.json`, with SHA-256
`47cb5e43f50445bd174248cb2566adb8db9b628ece3609bf82ada6a88f48098b`.
Its full source-bound ancestry is replayed from the original caller. Every
subsequent deduction is an exact physical consequence of that same state
and the declared closed interval restrictions.

The complete packet's entry point is `verify_a_fixed_cover.py`. Numerical
search discovers weights and useful restrictions; all proof acceptance is
by the separate standard-library rational replay. No Lean, Lake, or CI is
part of this argument.

## 1. Complete fixed-center cover

The inherited original centers satisfy the two exact rectangles

\[
\begin{aligned}
H&\in\left[-\frac{1472789}{1048576},\frac54\right]
       \times\left[-\frac{91}{60},\frac{91}{60}\right],\\
I&\in\left[-\frac{361205}{262144},\frac54\right]
       \times\left[-\frac{91}{60},-\frac{5135}{65536}\right].
\end{aligned}
\]

For any certified interval \([l,u]\), its \(m\) equal closed pieces are

\[
J_{m,k}(l,u)=
\left[l+\frac{k}{m}(u-l),\;l+\frac{k+1}{m}(u-l)\right],
\qquad 0\leq k<m.
\]

Their union is the entire interval. First use every product of the four
I x-pieces and four I y-pieces. Fourteen have direct physical contradictions.
For each of I(1,0) and I(1,1), use every product of the two H x-pieces and
four H y-pieces. The resulting outer cover has
\(14+2\cdot8=30\) fixed-center members. Every shared face and endpoint is
retained; repeated boundary points are harmless in an exclusion proof.

| I indices | Fixed-center proof | Additional fixed-center bound rounds |
|---|---|---:|
| (0,0) | Direct physical interval terminal | 1 |
| (0,1) | Direct physical interval terminal | 0 |
| (0,2) | Direct positive affine reserve | 0 |
| (0,3) | Direct physical interval terminal | 0 |
| (1,0) | All eight H members, with three complete slope subcovers | See next table |
| (1,1) | All eight H members | See next table |
| (1,2) | Direct positive affine reserve | 3 |
| (1,3) | Direct physical interval terminal | 7 |
| (2,0) | Direct positive affine reserve | 1 |
| (2,1) | Direct positive affine reserve | 0 |
| (2,2) | Direct physical interval terminal | 1 |
| (2,3) | Direct positive affine reserve | 1 |
| (3,0) | Direct positive affine reserve | 0 |
| (3,1) | Direct positive affine reserve | 0 |
| (3,2) | Direct positive affine reserve | 0 |
| (3,3) | Direct positive affine reserve | 0 |

Here a bound round is an exact induction step on the same fixed rectangle.
It does not create another geometric member. The two H covers have all
eight index pairs in each column:

| H indices | I(1,0) proof | I(1,1) proof |
|---|---|---|
| (0,0) | Complete H-slope cover after 12 fixed rounds | Positive affine reserve after 2 rounds |
| (0,1) | Empty original D-angle interval after 4 rounds | Positive affine reserve after 1 round |
| (0,2) | Complete H-slope cover after 6 fixed rounds | Positive affine reserve after 2 rounds |
| (0,3) | Complete inherited-slope cover after 6 fixed rounds | Positive affine reserve after 2 rounds |
| (1,0) | Positive affine reserve, 0 rounds | Positive affine reserve, 0 rounds |
| (1,1) | Positive affine reserve, 0 rounds | Physical interval terminal, 0 rounds |
| (1,2) | Positive affine reserve after 1 round | Positive affine reserve, 0 rounds |
| (1,3) | Positive affine reserve after 1 round | Positive affine reserve, 0 rounds |

## 2. Exact physical bound induction

The affine state uses the original 54 variables: the 18 center coordinates
and, for each square, its alpha component, signed beta component, absolute
beta component, and physical inset halfwidth. All original geometry and
frame identities are retained. Every printed affine row is rebuilt from
its literal physical rule and the current certified intervals.

Accepted rules include the original corner and inset conditions, owned-axis
and relative-support consequences, unit-frame bounds, strip and altitude
capacities, incircle and point-disk inequalities, and the unconditional
original-nine central-capacity consequences. The universal four-center
energy and physical square-area moment secants have separate independent
rational reconstructions. Conditional central-cover rows retain their
declared original callers; none becomes unconditional merely through a
numerical result.

The final inherited I-frame covers also admit the independently proved
three-square energy inequality. For any three retained original physical
squares with centers \(c_i,c_j,c_k\), it states

\[
E=|c_i-c_j|^2+|c_i-c_k|^2+|c_j-c_k|^2\geq\frac72.
\]

The accompanying hand proof exhausts pair-separator ownership by a star
case and a directed-cycle case. The cycle uses a complete 128-triangle
angular cover and 384 exact vertex inequalities in \(\mathbb Q(\sqrt2)\).
The portable entry point freshly replays that finite arithmetic and pins
the reviewed hand reduction, independent review, table, and checker bytes.

For a certified difference component \(l\leq d\leq u\),
\(d^2\leq(l+u)d-lu\). Summing its two Cartesian components over the
three unordered pairs therefore gives the necessary affine row

\[
-\sum_{\{p,q\},a}(l_{pqa}+u_{pqa})(c_{q,a}-c_{p,a})
\leq-\frac72-\sum_{\{p,q\},a}l_{pqa}u_{pqa}.
\]

The independent row helper reconstructs that expression from the actual
certified intervals and original indices. Its separately checked exact
identity is the geometric inequality plus the nonpositive products
\((d-l)(d-u)\). The new checker changes only the named-row dispatch and
accounting for this universal family; the original caller, restrictions,
bound induction, and terminal checks are unchanged.

Suppose the current physical state implies \(a_r\cdot z\leq b_r\) and
\(|z_k|\leq M_k\). For nonnegative rational weights \(w_r\), define

\[
a=\sum_r w_ra_r,\qquad b=\sum_r w_rb_r.
\]

For every requested linear objective \(c\cdot z\), these same physical
conditions imply

\[
c\cdot z\leq b+\sum_k M_k|a_k-c_k|.
\]

The checker evaluates the right side exactly. Rounding a new upper bound
upward to its declared rational grid preserves it, so it may be intersected
with the old bound. Coordinate, Cartesian difference, scalar, and frame
inferences are all checked in their declared order. Induction consequently
proves the entire state used by the next round and any later restriction.

## 3. Inherited closed slope covers

The canonical frame representative has positive alpha. Write its signed
slope as \(t_i=\beta_i/\alpha_i\), in the certified interval contained
in \([-1,1]\). A slope restriction changes only that original's slope
interval to one of its exact equal closed pieces. It preserves every other
current scalar bound, center bound, difference interval, fixed H/I
rectangle, and original caller predicate.

Each of the three hard fixed members begins with the four closed H-slope
quarters \([-1,-1/2]\), \([-1/2,0]\), \([0,1/2]\), and \([1/2,1]\).
The outer quarters have direct exact terminals. Each unresolved central
quarter first undergoes six local bound rounds, and then its **proved final
slope interval** is covered by two closed equal halves. These final
intervals can be smaller than the original quarter. The discarded portion
is excluded by the checked parent bound induction; it is not an uncovered
branch.

For HI(1,0,0,0), the two negative halves are \([-1/2,-1/4]\) and
\([-1/4,0]\). The positive parent has narrowed to \([0,u_0]\), where

\[
u_0=\frac{69389109155731}{140737488355328}.
\]

It is covered by \([0,u_0/2]\) and \([u_0/2,u_0]\). Its six terminal
leaves are:

| H interval | Local rounds | Exact terminal |
|---|---:|---|
| [-1,-1/2] | 3 | Positive affine reserve |
| [-1/2,-1/4] | 2 | Positive affine reserve |
| [-1/4,0] | 2 | Positive affine reserve |
| [0,u0/2] | 1 | Positive affine reserve |
| [u0/2,u0] | 1 | Empty analytic original frame |
| [1/2,1] | 3 | Positive affine reserve |

For HI(1,0,0,2), the negative halves are the same, while the positive parent
has narrowed to \([0,u_2]\), where

\[
u_2=\frac{15525784264067}{35184372088832}.
\]

Its six terminal leaves are:

| H interval | Local rounds | Exact terminal |
|---|---:|---|
| [-1,-1/2] | 3 | Empty original angle interval |
| [-1/2,-1/4] | 2 | Positive affine reserve |
| [-1/4,0] | 5 | Positive affine reserve |
| [0,u2/2] | 4 | Positive affine reserve |
| [u2/2,u2] | 2 | Empty original angle interval |
| [1/2,1] | 2 | Positive affine reserve |

For HI(1,0,0,3), the negative middle H quarter has its two usual halves.
The positive quarter has the two halves [0,1/4] and [1/4,1/2]. Each positive
half undergoes six local bound rounds before its final I-slope interval is
partitioned into four exact closed quarters. Those two I intervals are

\[
\begin{aligned}
[a_0,b_0]&=\left[-\frac{85649956090393}{140737488355328},
                  \frac{159758148637381}{281474976710656}\right],\\
[a_1,b_1]&=\left[-\frac{37379214425641}{70368744177664},
                  \frac{4015879687435}{8796093022208}\right].
\end{aligned}
\]

Here $J_{4,k}$ is the exact interval formula from Section 1. All twelve
leaves in the following complete table have a positive affine reserve.
A dash means there is no additional I restriction beyond the inherited
parent state; it does not remove any inherited I bound.

| H interval | Additional I interval | Local leaf rounds |
|---|---|---:|
| [-1,-1/2] | — | 3 |
| [-1/2,-1/4] | — | 2 |
| [-1/4,0] | — | 4 |
| [0,1/4] | $J_{4,0}(a_0,b_0)$ | 2 |
| [0,1/4] | $J_{4,1}(a_0,b_0)$ | 9 |
| [0,1/4] | $J_{4,2}(a_0,b_0)$ | 4 |
| [0,1/4] | $J_{4,3}(a_0,b_0)$ | 1 |
| [1/4,1/2] | $J_{4,0}(a_1,b_1)$ | 1 |
| [1/4,1/2] | $J_{4,1}(a_1,b_1)$ | 4 |
| [1/4,1/2] | $J_{4,2}(a_1,b_1)$ | 3 |
| [1/4,1/2] | $J_{4,3}(a_1,b_1)$ | 1 |
| [1/2,1] | — | 4 |

The nine-round leaf is a continued exact induction on its original I
quarter. Its earlier rounds are retained unchanged; no endpoint is moved
and no extra geometric cut is introduced by continuing that proof.

Every nested cover is attached to the exact source-bound OPEN parent from
which its interval was inherited. The independent gate requires all sibling
indices, their common parent hash, exact adjacency and endpoints, and the
complete recursive cover of any still-open child. It rejects cycles and
never promotes an isolated restricted leaf to its parent. Changing the
selected original at a deeper level is allowed only by the same complete
closed cover rule.

## 4. Exact terminal implications

For a final nonnegative weighted sum \(a\cdot z\leq b\), the checker
computes the reserve

\[
\eta=-b-\sum_k M_k|a_k|.
\]

If \(\eta>0\), the absolute bounds also give
\(a\cdot z\geq-\sum_k M_k|a_k|=b+\eta\), a contradiction. Every
accepted affine terminal checks its exact weights, independently rebuilt
physical rows, residual coefficients, and strictly positive reserve.

An interval terminal is accepted only when the independent physical
reconstruction yields its contradiction: an empty center interval, the
failure of every required inset-separation alternative, an empty original
slope interval, or an empty original unit-frame region after the preceding
exact bound deductions. A text label or numerical infeasibility result is
insufficient. Early empty-frame and empty-angle exits still check every
preceding induction identity and reject stale final-state fields.

## 5. Whole-original assembly and frozen replay

The outer verifier requires all 16 I quarter products. Each is either a
single complete direct member or all eight H half-by-quarter members.
Every attached slope cover must begin at the exact unrestricted fixed
member, retain its original path and original prefix, and prove that whole
member by its complete recursively checked sibling cover. It deduplicates
shared bound records by certificate SHA when reporting the amount of
checked arithmetic; shared antecedents are not counted as new terminals.

The packet binds historical provenance paths to local immutable bytes.
The final replay checks the complete original ancestry, every new bound
induction, every terminal, and all levels of closed coverage. It snapshots
the cover index and inventory, rehashes every frozen input at return, and
rejects workspace imports or reads outside the packet. The numerical
producers and optimizers are not imported.

The 27 outer members without a slope subcover contribute one physical
terminal each. The three complete slope subcovers contribute 6, 6, and 12
terminals, giving 51 physical leaves in total. Their terminal types are
41 positive affine reserves, six independently reconstructed physical
interval terminals, three empty original angle intervals, and one empty
analytic original frame. Every one of the 41 exact affine reserves exceeds
$1/4096$; the full rational reserves are retained in the certificates and
recomputed during replay.

The entry point also reruns the finite three-square theorem check before
the unchanged complete-original cover gate. It requires the reviewed
geometric hand proof and independent review, the exact table/checker,
independent row helper, restricted bound checker, slope gate, and outer
gate to have their pinned reviewed hashes. The theorem and outer modules
must resolve to their local frozen packet paths.

The successful machine report is written to
`new_reviews/COMPLETE_ORIGINAL_REPLAY.json`; its required status is
`PASS_COMPLETE_ORIGINAL_PARENT`. It records every fixed member, every
recursive subcover, the SHA-deduplicated bound deductions and printed rows,
all exact terminal reserves, the freshly checked three-square theorem,
and the unchanged frozen inventory. A second run after relocation uses
the same source bytes and verifies that historical workspace paths serve
only as provenance keys. These complete replay gates establish the
contradiction for this one original cell. They give no whole-mask closure.


## Reconstruct the committed packet

From `research/nine/computer_assisted`, run:

```sh
cat a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part01 a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part02 a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part03 a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part04 a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part05 a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part06 a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part07 a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part08 a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part09 a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part10 a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz.part11 > a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz
printf '%s  %s\n' 1345da2280fdb42ade1e11a593a9b888afeaab0d1227439a24c76f87aafef14c a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz | sha256sum -c -
tar -xzf a2_00100_a_8b_fixed_center_slope_checkpoint.tar.gz
cd a_8b_extended_cover_package
python -B -S verify_a_fixed_cover.py
```
