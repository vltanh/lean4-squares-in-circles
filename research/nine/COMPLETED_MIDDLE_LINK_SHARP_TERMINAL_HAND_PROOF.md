# A weak middle link is already a sharp four-plus-three terminal

November 2, 2026 UTC (November 1 in America/Chicago). Complete hand
derivation. No mathematical script, numerical search, Lean, Lake, or CI.

This note closes the entire nonzero marked-chain pattern **(010,00)**:
the four-chain has actual outer links, its middle link is weak, and the
disjoint three-chain is actual. The physical poses, pair separators,
other two squares of a nine-square packing, and all other exceptional
pairs are unrestricted. This is one structural mask closure; it does
not count as a canonical positional-root exclusion or close A.2.

## 1. Physical pair span in a maximal-gap coordinate

For a unit square S in an orthonormal coordinate frame, put

\[
 h_S=\tfrac12(|u_S\cdot e_x|+|v_S\cdot e_x|),\qquad
 g_S=\frac1{4h_S},\qquad
 \eta_S=h_S+g_S-1=\frac{(2h_S-1)^2}{4h_S}\ge0.
\]

Both coordinate projection halfwidths are h_S, with
1/2<=h_S<=1/sqrt(2). The square contains the centered axis-aligned
square of halfwidth g_S: each of its physical side coordinates has
absolute value at most 2h_S g_S=1/2. Strict interior containment holds
for the open inset square.

Let B,C be physical squares with disjoint open interiors. If

\[
             d=x_C-x_B>0,\qquad |y_C-y_B|\le d,
\tag{1}
\]

then their inset squares force d>=g_B+g_C. Otherwise both coordinate
gaps would be strictly smaller than the sum of the inset halfwidths,
making the open insets overlap. Consequently

\[
              d+h_B+h_C\ge2+\eta_B+\eta_C\ge2.
\tag{2}
\]

Equality in the final inequality requires h_B=h_C=1/2 and d=1.
Thus equality makes B,C aligned and actually x-separated. In
particular, if d<h_B+h_C, then the last inequality in (2) is strict.
No vertical small-gap hypothesis is needed: (1) is sufficient.

## 2. Recovering the physical long span

Suppose four distinct physical squares A,B,C,D satisfy (1) for B,C and
the two actual outer projection comparisons

\[
       x_B-x_A\ge h_A+h_B,\qquad
       x_D-x_C\ge h_C+h_D.
\tag{3}
\]

Adding (2)--(3) gives the quantitative physical endpoint span

\[
       x_D-x_A-h_A-h_D\ge2+\eta_B+\eta_C.
\tag{4}
\]

Every completed middle comparison that is not actual has (1), by the
maximal-coordinate rule. If it is actual, its own gap gives the usual
long-span bound directly. Thus an arbitrary completed four-chain with
actual outer links has the required long span in either middle-link
case. A weak middle link gives strictness in (4).

## 3. The sharp terminal and the complete weak-mask exclusion

Put Q=1105/256. Let E,F be two further distinct physical squares,
different from A,D, whose endpoint span satisfies

\[
              x_F-x_E-h_E-h_F\ge1.
\tag{5}
\]

For example, a disjoint actual three-chain E<G<F gives (5), since
the intervening physical square has width 2h_G>=1. Suppose all the
physical squares lie in a disk centered at zero, of squared radius q.

The already proved physical two-square cap theorem in
`PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`
says that any disjoint physical pair M,N in the closed Q-disk obeys

\[
 46(-x_M-h_M)+\frac{27}{2}(-x_N-h_N)\le\frac{211}{4},
\tag{6}
\]

strictly if q<Q. It requires no coordinate separator for that pair.
Apply (6) to the actual pair A,E and its reflected version to D,F.
The sum is

\[
 46(x_D-x_A-h_A-h_D)
 +\frac{27}{2}(x_F-x_E-h_E-h_F)\le\frac{211}{2},
\tag{7}
\]

strictly below Q. Equations (4)--(5) bound its left side below by

\[
       46(2+\eta_B+\eta_C)+\frac{27}{2}
       =\frac{211}{2}+46(\eta_B+\eta_C).
\tag{8}
\]

Therefore q<Q is impossible. If the middle link is weak, at least one
of B,C is not aligned: two aligned squares would have g_B+g_C=
h_B+h_C=1 and no weak gap would exist. Hence eta_B+eta_C>0, and
(7)--(8) exclude even q=Q.

**Conclusion.** A completed four-chain with actual outer links and a
disjoint actual three-chain forces q>=Q. If the middle link is genuinely
weak, it forces q>Q. In the five-bit convention of
`UNRESTRICTED_MARKED_CHAIN_EDGE_LEDGER_HAND_PROOF.md`, the full mask
(010,00) is excluded throughout q<=Q. The all-actual mask (000,00)
was already the sharp physical terminal. No count of exceptional pairs
elsewhere in the packing is used.

At q=Q the middle pair must be aligned with center gap one, so all
five selected chain links are actual. The existing physical 4+3
equality theorem then applies to these seven squares. This implication
does not classify the two other squares or global nine-square equality.

## 4. A quantitative sufficient test for every other marked pattern

This exact formula can be useful without declaring an unsolved mask
closed. For every square set

\[
       b_i=h_i-\frac12,\qquad d_i=h_i-g_i\ge0.
\]

Label the completed four-chain 0,1,2,3 and the completed three-chain
4,5,6. Mark the consecutive links w_0,w_1,w_2 and z_0,z_1, with one
meaning weak and zero meaning actual. Each actual gap is at least
h_i+h_j; each weak gap is at least g_i+g_j. Summing gives

\[
 L:=x_3-x_0-h_0-h_3
 \ge2+2b_1+2b_2-\sum_{i=0}^2w_i(d_i+d_{i+1}),
\]
\[
 S:=x_6-x_4-h_4-h_6
 \ge1+2b_5-z_0(d_4+d_5)-z_1(d_5+d_6).
\tag{9}
\]

Thus every pose satisfying

\[
\begin{split}
 \mathcal R={}&46\left[2b_1+2b_2-
                  \sum_{i=0}^2w_i(d_i+d_{i+1})\right]\\
 &+\frac{27}{2}\left[2b_5-z_0(d_4+d_5)-z_1(d_5+d_6)\right]
 \ge0
\end{split}
\tag{10}
\]

is impossible below Q by the same two physical endpoint-cap
inequalities. A strict positive reserve excludes the closed Q-disk.
For (010,00), use 2b_i-d_i=h_i+g_i-1=eta_i to recover

\[
             \mathcal R=46(\eta_1+\eta_2)+27b_5>0.
\]

For a different mask, (10) is an additional explicit orientation
condition, not an unconditional proof of that mask. All physical
nonoverlap hypotheses remain required for (7). In particular this
criterion does not claim that endpoints with a weak external link can
be omitted or that the two unselected units may be dropped from the
remaining global problem.

## 5. Fixed accounting

The structural five-link universe has 32 masks. Two now have complete
unconditional terminal treatment: (000,00) and (010,00). Up to 30
other formal masks remain, before symmetry or geometric infeasibility.
This is structural indexing, not 30 certified continuous cells, and
provides no completion percentage. The published positional-root
ledger and all canonical gate IDs are unchanged. A.2 remains open.
