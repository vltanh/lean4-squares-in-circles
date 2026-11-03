# The actual short-chain middle original lies above C

November 3, 2026. A complete three-original physical reduction and finite
rational table, with full exact replay and a fresh independent replay.
Computer-assisted discovery preceded both exact replays. No Lean, Lake, or CI.

## 1. Original scope and the missing middle-square order

Keep all nine original physical unit squares in the fixed strict
`001/00` predicate. The main originals are A,B,C,D, with A/B and B/C
actual; the short originals are E,F,G, with both E/F and F/G actual.
All original cone comparisons, frames, and physical nonoverlap
conditions remain part of the caller. Put

\[
 Q=1105/256,\qquad a=46,\quad b=27/2,\quad
 T=211/4=a+b/2,\quad \kappa=a/b=92/27.
\]

Use the common vertical normalization

\[
 d=x_D-x_C\ge v=y_D-y_C\ge2/3,
 \qquad d<h_C+h_D.                                      \tag{1}
\]

The strict weak bit in (1) is retained as an original premise, including
in any use of a necessary closed relaxation. The theorem to be proved
is

\[
                         \boxed{y_F>y_C.}                \tag{2}
\]

The finite table proves the stronger necessary scalar statement

\[
 S=x_G-y_G+y_C+\kappa(x_C-h_C)<0.                         \tag{3}
\]

Only the unchanged C,D,G centers and original frames appear as table
variables. The derivation below retains the actual original F through
necessary original-chain and endpoint-cap inequalities. It neither
replaces F by a newly chosen square nor imposes a pose on F.

## 2. Physical derivation of the contrary half-plane

Let `u=x_C-h_C`. Adding the two original actual main links gives

\[
 x_C-x_A\ge h_A+2h_B+h_C\ge h_A+1+h_C,
 \qquad -x_A-h_A\ge1-u.                                \tag{4}
\]

The actual E/F comparison separately gives

\[
                         -x_E-h_E\ge h_F-x_F.           \tag{5}
\]

Apply the already accepted physical A/E endpoint cap in the leftward
direction to these same two originals. Substitution of (4)--(5) yields

\[
 a(1-u)+b(h_F-x_F)\le T=a+b/2,
 \qquad x_F\ge h_F-1/2-\kappa u\ge-\kappa u.           \tag{6}
\]

The completed endpoint-order theorem gives `y_G>y_D>y_C` under (1).
If `y_F<=y_C`, the original marked F/G cone therefore implies

\[
 x_G-x_F\ge|y_G-y_F|=y_G-y_F\ge y_G-y_C,
 \qquad x_F\le x_G-y_G+y_C.                            \tag{7}
\]

Combining (6) and (7) proves `S>=0`, contrary to (3). Thus it suffices
to exclude that single closed half-plane. Every equality face of this
contrary domain is retained by the finite table. More generally, the
original F/G cone always gives `y_G-y_F<=x_G-x_F`, so (6) implies
`y_F-y_C>=-S` without any preliminary F/G height-order assumption.

## 3. Inherited necessary physical domain

The complete physical kernel is the one proved in Sections 2--5 of
`WEAK_OUTER_LARGE_GAP_C_SLANT_HAND_TABLE.md`. Its source and certificate
are frozen and unchanged. The present proof uses the same three
original centers `(x_C,y_C,x_D,y_D,x_G,y_G)` and the same canonical
slopes `(t_C,t_D,t_G)` in `[-1,1]^3`.

All eight closed sign roots are retained, with each slope independently
in `[-1,0]` or `[0,1]`. The table uses the original center-radius bound
`rho=91/60`, the original inset halfwidths `g_i=1/(4h_i)`, the compressed
left cap, the right cap and its separately valid universal and signed
tolls, and every physically possible owned separator of C/D, D/G, C/G.

In particular the existing physical domain supplies

\[
\begin{gathered}
 x_C>h_C-1/60,\qquad x_C-h_C<5/64,\qquad x_D>4/3,\\
 x_G-h_G>101/432,\qquad
 x_D-x_G<1459/1728,\qquad x_G-x_D<11/60,\\
 a(x_C-h_C)+b(x_G-h_G)\ge27/4,\qquad y_G>y_D,\\
 y_G-y_D\ge g_D+g_G,\qquad
 y_G-y_D>\frac78(h_D+h_G)-\frac{41}{120}.              \tag{8}
\end{gathered}
\]

The separately completed C-slant theorem now also gives

\[
                    y_C+\frac78x_C< -\frac7{32}.       \tag{9}
\]

There is no circular dependency: that theorem used none of (2), (3),
or a contrary F-height assumption. It is a previously completed
three-original theorem on precisely the same original caller.

We additionally retain the actual original C/G vertical separation

\[
                  y_G-y_C>h_C+h_G+\frac{97}{4480}.     \tag{10}
\]

Its full hand proof is Section 4 of
`GLOBAL_OUTER_LINK_EXTRACTION_DG_INSET_AND_SLANT_HAND_REDUCTION.md`.
For clarity, it follows independently of C-slant by splitting at
`h_D=9/16`. If `h_D<=9/16`, the inset clearance gives excess at least
`10/9-3sqrt(2)/4>127/2520>97/4480`. If `h_D>=9/16`, the affine
clearance gives excess strictly greater than
`523/640-9sqrt(2)/16>97/4480`. Both rational comparisons use
`sqrt(2)<99/70`. These are comparisons of the full original vertical
projections, not only their insets.

## 4. Exact changes to the inherited rational table

The discovery and independent exact replayer are separate new files,
`weak_outer_hand_F_order_search.py` and
`weak_outer_hand_F_order_verify.py`. Their complete table is obtained
from the frozen C-slant table by the following explicit changes.

For an original orientation box let `[h_i^-,h_i^+]` be the same exact
outward halfwidth enclosure. The old contrary slant row is replaced by

\[
 -\kappa x_C-y_C-x_G+y_G\le-\kappa h_C^-.             \tag{11}
\]

Indeed `S>=0` implies the same left side is at most `-kappa*h_C`,
which is no larger than the right side of (11). Thus the use of the
lower support endpoint weakens the necessary condition in the safe
direction.

The old zero dummy row is replaced by the closed necessary version
of the accepted theorem (9):

\[
                    \frac78x_C+y_C\le-\frac7{32}.      \tag{12}
\]

Correspondingly, the previous *contrary* slant lower bound on `y_C`
is removed. The new accepted upper bound is

\[
                      y_C\le-7/32-(7/8)x_C^-.          \tag{13}
\]

All other original coordinate intervals and their sequential
propagation are retained. In particular both D/G lower clearances
remain in the same maximum. The C/G difference interval additionally
uses the lower bound `h_C^-+h_G^-+97/4480` from (10).

Finally a new explicit row is appended after the entire inherited
circle-support block:

\[
                 y_C-y_G\le-h_C^- -h_G^- -97/4480.    \tag{14}
\]

The row index is `12+3*len(DIRS)+15+len(choice)+3*len(EXTRA_DIRS)`.
There are 96 integer directions and 128 rational unit directions per
original, exactly as in the inherited table. The append-only position
does not alter any earlier circle, owned-separator, or cap row index.

The exact radical and support formulas, signed-normal interval errors,
and residual Farkas rule are unchanged. Every terminal with weights
`lambda_j>=0` requires

\[
 -\sum_j\lambda_j b_j-
 \rho\sum_{k=1}^6\left|\sum_j\lambda_j(A_j)_k\right|>0,
 \qquad A_jX\le b_j.                                  \tag{15}
\]

Weights are integer multiples of `2^-40`; radicals use exact integer
square-root enclosures on the `2^-48` grid. Every residual coefficient
is explicitly paid by the original center-radius bound. Empty
necessary intervals have their own exact terminal rule.

Each angle split keeps both closed halves. Every signed owned separator
of the three physical pairs remains covered, except only the omissions
proved in the inherited original strict weak-cone and upward-D/G
lemmas. The closed weak row does not change the theorem's strict
original caller. The exact replayer imports only Fraction/radical
helpers from the frozen `weak_outer_hand_right_lower_verify.py`; its
unrelated four-original verifier and all floating discovery code are
outside the exact replay path.

## 5. Finite coverage and acceptance

The full exact forest has eight orientation roots, 10,397 nodes,
3,743 closed angle splits, 457 owned-separator splits, and 6,197
terminal rational combinations. It uses no empty-interval terminal.
The maximum depth is 12 and the unresolved frontier is empty.

Write `-` for `[-1,0]` and `+` for `[0,1]`. The complete root counts are:

| Root | C,D,G intervals | Nodes | Terminals |
|---|---|---:|---:|
| 0 | `---` | 1,855 | 1,121 |
| 1 | `--+` | 1,771 | 1,038 |
| 2 | `-+-` | 603 | 386 |
| 3 | `-++` | 946 | 569 |
| 4 | `+--` | 1,568 | 945 |
| 5 | `+-+` | 1,536 | 896 |
| 6 | `++-` | 729 | 455 |
| 7 | `+++` | 1,389 | 787 |
| **Total** | **All eight closed roots** | **10,397** | **6,197** |

Every exact terminal reserve is greater than

\[
                         \frac{43298503}{10^{12}}>0.
\]

The complete rational minimum and all coverage counts are in
`computer_assisted/weak_outer_hand_F_order_exact_replay.json`.
The complete exact source, original physical implication, and changes
in Section 4 were independently reviewed and accepted. A separate
fresh exact replay checked every root and terminal with identical
counts and exact minimum. The certificate, verifier, and exact helper
hashes matched before that run and were unchanged afterward. Its
report is `computer_assisted/weak_outer_F_order_global_independent_replay.json`,
and its complete review is
`GLOBAL_OUTER_LINK_EXTRACTION_F_ORDER_INDEPENDENT_REVIEW.md`.

The 125,529-byte packed certificate is
`computer_assisted/weak_outer_hand_F_order_certificate.json.gz`, with
SHA-256

`3dcc723d03f388a05f086e01b8877328aa8d694a2b42a2c3048f7e58c5e1bdd1`.

The frozen exact replayer SHA-256 is
`f6ddccb3037e50826af9a10f92dccd1fca332640bcc5eee4b783db061113b953`.
The exact helper SHA-256 is
`c3c66a1fcfca7d2e0acd8d9b5a32340f8e8d2253e5e802ff1be34f5cbd0e109f`.
Both sources are separately bound in the replay report. No inherited
C-slant source or certificate was edited for this theorem.

All six damaged-certificate controls were rejected: a missing
orientation root, a missing closed angle child, a missing owned
separator child, a false whole-root combination, a negative multiplier,
and a false empty-interval terminal. Their complete records are
`computer_assisted/weak_outer_hand_F_order_controls.py` and
`computer_assisted/weak_outer_hand_F_order_rejection_controls.json`.
The manifest binds the paper, finite certificate, exact source and
helper, complete replay reports, and damaged controls.


## 6. Scope of the conclusion

The accepted finite inequality (3), together with the original
derivation (4)--(7), proves (2) on the caller (1). It establishes an
order between the actual short middle original and C. It does not
assert an unproved placement for either of the two unselected
originals, or exclude all remaining nine-square configurations. This
local result does not itself change the fixed-mask coverage ledger.
