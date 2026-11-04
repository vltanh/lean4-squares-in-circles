# Independent physical and hand/table review of B340

## Decision and scope

**PASS for the physical row rules and the complete delivered hand/table content of the frozen B340 candidate. No mathematical or packaging defect was found in this review.**

The reviewed original is `negative-34029ea8b047982f`, with unchanged path

```json
[["angle",3,0],["angle_cut",[0,"0"],0],["position_cut",[11,"1/2"],1],["f_side_escape",[5,7],[2]]]
```

The frozen complete-tree manifest has SHA256
`97ff1c6d4af4f92a7de377a3e3d4487f701706f3889bd29db7bda3c7652c2805`.
The original initial-state record has SHA256
`d7663ff3b35a6a08062695af46494ad85e1632d94d1cc1bb25d59198c89c1019`.

This review concerns the continuous physical validity of the four-product original-corner rows, both Gram-square families, the exact residual rule, the accepted geometric premises, and the delivered human-readable hand/table argument. The separate parent reviewer owns the original-domain attachment and complete-cover review. The root's fresh exact replay supplies the arithmetic ancestry of every bound. This review does not promote a numerical candidate or a saved PASS field to a whole-original proof on its own.

I read the frozen source and hand documents. I also wrote `review_physical_rows.py`, which imports no producer, checker, optimizer, or numerical package. Its independent exact audit is `PHYSICAL_LITERAL_AUDIT.json`. It reads the unchanged packet and writes only to the review directory. No historical source, certificate, ledger, or active search was modified.

## 1. The same physical original variables

For original square `i`, the variables used here are its actual center `(x_i,y_i)` and actual orthonormal side vectors

\[
u_i=(\alpha_i,\beta_i),\qquad v_i=(-\beta_i,\alpha_i),
\qquad \alpha_i^2+\beta_i^2=1.
\]

The four corners are the original points

\[
\left(x_i+\frac{\epsilon\alpha_i-\tau\beta_i}{2},
y_i+\frac{\epsilon\beta_i+\tau\alpha_i}{2}\right),
\qquad \epsilon,\tau\in\{-1,1\}.
\]

The closed-disk row relaxation uses `Q=1105/256`. The original caller continues to retain all nine physical squares, all 36 corners and all 36 physical pair predicates, the five marked center cones, actual AB/BC/EF/FG and strictly weak CD. A necessary-row relaxation need not encode every physical condition as an equality in the LP; every actual original witness must admit the indicated values of all the retained variables. This is the direction used by the proof. No relaxed auxiliary point is asserted to be a physical packing.

The canonical slope intervals and all later cuts remain restrictions of the same original frames. Nothing in the reviewed corner or Gram rules requires nonzero tilt, positive pair clearance, a strict internal interval endpoint, or a common square orientation.

## 2. Four independent product planes for an original corner

Expanding the corner norm and using the original unit-frame equation gives exactly

\[
\|\text{corner}\|^2=x^2+y^2+\frac12
 +\epsilon\alpha x+\tau\alpha y
 +\epsilon\beta y-\tau\beta x.
\]

Consequently the sum of the two center squares and the four signed products is at most `Q-1/2=977/256`. The signs, the constant, and the original variable indices in the delivered converter agree with this identity.

For one of the four products `fg`, choose either both lower endpoints `(a,b)` of its independently proved factor intervals or both upper endpoints. In either case `(f-a)(g-b)>=0`, so

\[
fg\ge ag+bf-ab.
\]

For arbitrary rational `p_x,p_y`, the two center-square tangents give

\[
x^2+y^2\ge2p_xx+2p_yy-p_x^2-p_y^2.
\]

Adding these inequalities yields the printed affine row. Its slack is exactly the original corner-disk slack plus

\[
(x-p_x)^2+(y-p_y)^2+\sum_{j=0}^{3}(f_j-a_j)(g_j-b_j).
\]

Every term is nonnegative on the entire certified rectangle. The four choices may be made independently even when two products contain the same original scalar: all four inequalities hold for that same value, and adding them is valid. The 16 endpoint patterns are simultaneously valid inequalities, not 16 cases whose alternatives need to be covered. Signed coordinates and negative beta are handled by reversing the signed interval endpoints before choosing a plane. Degenerate intervals and every closed face satisfy the same argument.

The live converter and independent converter are byte-identical to their accepted four-product copies in `code/accepted_unit_four_corner`. In particular the independent converter's SHA256 is `bfb6dc614269eaaa2c9f087cc7295c2598648d9349d76006b1e4aa08e66380a6`.

My independently written audit reconstructed all **14,386 bound-round four-product occurrences** directly from the displayed corner expansion and the saved propagated original intervals. It also reconstructed all **7,458 bound-round grouped-corner occurrences** as the corresponding common endpoint choices. The full packet contains 14,476 four-product and 7,523 grouped-corner occurrences; the additional 90 and 65 occurrences lie in affine terminals. Their current geometric propagation and literal validity are checked by the complete exact replay. The universal continuous proof above applies to those occurrences without a new premise.

The adapter correctly uses the freshly propagated positions and scalar bounds when rebuilding these rows. It does not reuse the producer's floating frame or a cached endpoint from a different caller.

## 3. Frame Gram-square rows

For the selected original pair `i<j`, the existing last four SAT auxiliary variables have the physical meanings

\[
z_2=\alpha_i\alpha_j,\quad z_3=\beta_i\beta_j,
\quad z_4=\alpha_i\beta_j,\quad z_5=\beta_i\alpha_j.
\]

Put `C=z_2+z_3` and `S=z_4-z_5`. Direct dot products give
`u_i·u_j=v_i·v_j=C`, `u_i·v_j=-S` and `v_i·u_j=S`.

For arbitrary rational `x,y,a,b,c,d`, expanding

\[
\|(x,y)+a u_i+b v_i+c u_j+d v_j\|^2\ge0
\]

gives constant `x^2+y^2+a^2+b^2+c^2+d^2`, original-frame coefficients
`2(xa+yb)`, `2(ya-xb)`, `2(xc+yd)`, `2(yc-xd)`, and cross terms
`2(ac+bd)C+2(bc-ad)S`. Moving the variable terms to the other side is exactly the printed necessary inequality. I checked the two sine signs in particular.

The decoder identifies the auxiliary block by the ordered SAT choices retained in the same original path. It checks the pair and its two original indices. Choosing another owned normal for the same pair does not alter the meanings of these four cross-frame products.

My separate audit reconstructed **all 4,482 frame-square occurrences**, including affine-terminal occurrences, from the six-vector expansion. Its formula was written without importing the delivered checker or producer. Both delivered Gram modules match their accepted copies byte for byte.

These rows introduce no additional variable or domain restriction. Numerical eigenvectors may suggest useful rational coefficients, but every rational vector gives a valid squared-norm inequality. No numerical eigenvalue is an acceptance premise.

## 4. Shared projection Gram-square rows

Let `d=c_j-c_i` and let `n` be the signed unit normal owned by the retained physical SAT alternative. Its first two existing auxiliary variables are `z_0=n_x d_x` and `z_1=n_y d_y`. I checked that the owner/axis/sign decoder agrees with the physical SAT product definitions: axis 0 uses the signed original `u`, and axis 1 the signed original `v`.

For a proved interval `lo_k<=d_k<=hi_k`,

\[
d_k^2\le(lo_k+hi_k)d_k-lo_k hi_k
\]

follows from `(d_k-lo_k)(hi_k-d_k)>=0`. Let `D` be the sum of the two secants. For arbitrary rational `x,y,a,b`,

\[
0\le\|(x,y)+a n+b d\|^2
\le x^2+y^2+a^2+b^2D
 +2a(xn_x+yn_y)+2b(xd_x+yd_y)+2ab(z_0+z_1).
\]

The second inequality has the required direction because `b^2>=0`. The slack of the resulting affine row is the squared norm plus `b^2` times the two nonnegative rectangle products. This proves validity at all endpoints, including intervals of zero length.

I checked the constant `x^2+y^2+a^2-b^2(lo_x hi_x+lo_y hi_y)`, the two projection-product coefficients, and the signed owner substitutions. My independent audit reconstructed **2,905 bound-round projection-square occurrences**. The full packet has 2,923 such occurrences; the remaining 18 terminal occurrences are covered by the full exact replay using its independently propagated difference intervals.

## 5. Disk supports, accepted conditional rows, and their premises

For an arbitrary rational direction `(p,q)`, the corner-disk supporting row is valid when its claimed nonnegative support cap `U` satisfies

\[
256U^2\ge1105(p^2+q^2).
\]

My audit independently checked that squared inequality and expanded the same original corner in **all 77,352 adaptive corner-disk occurrences**, including terminals. It uses no square-root approximation.

The packet also contains the accepted guarded oriented-cap and coupled-three-energy hand proofs and exact premise bindings. There are **304 oriented-cap occurrences** and **679 coupled-three-energy occurrences** in the literal inventory. The oriented cap requires a strictly interior horizontal difference interval in `(-1,1)`, a proved vertical center sign and a proved main-frame sign. The converter tests these guards on the propagated original intervals. The accepted physical review supplies the separator-sign argument and the reflected affine formula. The cap's scalar cover and its accepted bindings are included; this review does not restart that already accepted scalar computation.

For coupled-three energy, the third projected pair difference is the same sum of the other two. The supplied physical derivation retains this identity, clips the closed two-dimensional difference polygon, and bounds its convex quadratic at all vertices. The underlying three-square center-energy theorem and its hand proof are present in the pinned 507-input prior packet. The proof packet does not use a foreign cell's height consequence as an original premise.

The exact terminal inventory has no sharp/full-angle row terminal: all leaves are affine or directly checked original interval/frame contradictions. The unused theorem guards and scalar tables preserved in the source inventory therefore supply no unreported terminal in this tree.

## 6. Exact affine induction and residual payment

For checked inequalities `c_k·z<=b_k` and nonnegative rational multipliers, put `C=sum w_k c_k` and `B=sum w_k b_k`. If `|z_j|<=M_j` for the same variables, then

\[
a\cdot z\le B+\sum_j M_j|C_j-a_j|.
\]

This follows by subtracting the objective from the weighted inequality and bounding every residual coordinate with its certified absolute bound. There is no cancellation tolerance. The implementation requires positive integer multipliers divided by `2^40`; zero-weight rows are simply absent. It verifies the complete row-index set and every used literal. A new grid upper bound is rounded upward to denominator `2^20` by exact integer arithmetic.

For a contradiction, the exact reserve is

\[
-B-\sum_j M_j|C_j|>0.
\]

I reviewed that rule in `independent_physical_sat_replay.py` and independently reconstructed **all 181 affine-terminal weighted sums and residual payments** from their literal fractions. Every reserve is strictly positive and equals its saved exact value. The smallest is at node 306:

\[
\frac{151733336600989615520443323263491089484860283}
     {10676154221601432410482833817168273548178505072640}>0.
\]

This displayed fraction is a ratio of the two stated positive integers. The JSON audit retains it as one exact rational string. It is not a numerical feasibility margin.

## 7. Complete delivered hand/table content

The packet delivers:

- `B340_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md`, identifying the exact original, its literal decoded inequalities, the original physical caller and its whole-domain attachment;
- `records/REGISTERED_B_COMPLETE_TREE_HAND_PROOF.md`, deriving the exact induction, all three complete cover rules and the whole-root conclusion;
- `COMPLETE_TERMINAL_TABLE.md`, with every terminal's node, parent, depth, last choice, local rounds, deductions and exact reserve floor or physical contradiction kind;
- all 403 unchanged node records with every printed coefficient, rational multiplier, intermediate interval and terminal witness;
- the accepted physical row derivations and the immutable prior packet used by the exact reconstruction.

I independently parsed all **279 hand-table rows**, matched them bijectively to the literal leaves, checked every table field and compared every displayed reserve floor with the independently recomputed exact reserve. There are no omitted leaves, duplicate terminal entries or invented reserves for analytic terminals.

| Terminal kind | Complete leaves |
| --- | ---: |
| Positive exact affine reserve | 181 |
| Original center-interval contradiction | 71 |
| Original effective-angle contradiction | 14 |
| Empty analytic frame interval | 10 |
| Unit-frame inference contradiction | 3 |
| **Total** | **279** |

The independent inventory agrees with the delivered report: **403 nodes, 400 local rounds, 67,336 exact deductions, 199,016 bound-round row occurrences and 4,173 terminal-row occurrences**, for **203,189 printed row occurrences**. Literal JSON records are part of the complete table evidence; the Markdown terminal table is its readable index. The displayed reserve floors do not replace the full exact fractions.

The source manifest retains the relevant hand derivations. The four-product and both Gram producers/checkers are identical to their accepted bound copies. The audit rehashes all 403 node records and its inspected mathematical sources at completion.

## Acceptance limit

The physical row identities, literal table, exact affine terminal arithmetic and document coverage pass this independent review. The root must still use its fresh exact replay and the independent full-parent/cover review to award the original closure. Those are complementary parts of the already required acceptance standard, not additional gates. This review grants no mask, positional-root or roadmap credit. No Lean, Lake or CI was run.
