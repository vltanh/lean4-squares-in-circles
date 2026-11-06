# Cd402 leaf 480: complete exact four-original exclusion

**The saved internal leaf 480 is excluded. The whole Cd402 original is
not proved empty by this packet.** The unchanged original register remains
224/231 closed, seven open. Relative to the accepted 507-node continuation,
twelve other saved leaves still require proofs. This is a replacement for
the previously incomplete two-part certificate publication, not a second
closure credit for leaf 480.

## Reproduce the complete arithmetic and coverage check

Keep `four_exact.py`, `basis_integer.py`, `check_leaf480.py` and all six
`leaf480_basis.b64.partNN` files in the same directory, then run:

```sh
python -B -S check_leaf480.py
```

Only the Python standard library is used. The default always checks the
entire table afresh; it reads no saved PASS report. The expected final
status is `PASS_COMPLETE_LEAF480`. Optional `--start` and `--count`
arguments check an explicitly stated arithmetic slice while checking the
whole tree structure; such a run reports only `PASS_EXPLICIT_PARTIAL_REPLAY`.
A partial run must not be called a complete proof replay.

The six parts are one replacement revision. Do not mix them with the old
8,193-byte partial files. Their concatenated base64 decodes to a 38,312-byte
xz payload, SHA-256:

`1d5bb687607de8ccdb56d425a6015632963666a204a61a30155347ff2d36e742`.

## Exact theorem and original attachment

Retain the original physical unit squares E,F,H,I, with their independent
frames, all four original corners in the closed Q-disk, Q=1105/256, and
all six original physical pair conditions. Write h for coordinate
halfwidth and g=1/(4h) for the halfwidth of the same square's contained
aligned inset. The additional hypotheses are:

- EF has actual horizontal projection separation and its original
  positive-horizontal center-cone comparison;
- y_H-y_F >= g_F+g_H and y_I-y_H >= g_H+g_I;
- x_H-x_E >= g_E+g_H and x_H <= x_I;
- H has a canonical side tangent in [-1,0];
- the four centers lie in the following closed rational boxes.

| Original | Horizontal interval | Vertical interval |
|---|---|---|
| E | [-161/125,-47/64] | [641/1000,567/500] |
| F | [-103/500,17/64] | [-71/200,11/1000] |
| H | [-41/100,507/1000] | [203/500,359/500] |
| I | [-201/500,103/100] | [1113/1000,91/60] |

**These simultaneous hypotheses are impossible.** No other original's
orientation is fixed, no physical pair is discarded, and no new square
replaces an original. This four-square theorem contradicts the full
nine-original leaf because that caller implies all these hypotheses.

The attachment is to the accepted `cd402_opposite_507` state at archive
commit `6a9a45e0ad997c8e143b0f22a0de88370d9d7adb`, file
`research/nine/computer_assisted/a2_00100_c_finite_frontiers_v2/covers/cd402_opposite_507/MANIFEST.json`,
Git blob `12b58e41d467daeac461e246055ce7aca7aec421`.
The node-480 path retains the F/H and H/I upward inset choices, H's
nonpositive tangent, and E/H rightward inset choice; EF is actual in the
original mask. The last selected D/G owned axis is unnecessary for this
four-original contradiction. All nine originals remain in the caller.

`attachment()` prints the exact sixteen coordinate-endpoint containments
from that saved state into the larger boxes above. It also checks the
small-F radius bound used below. **The prior proof of the incoming bounds
and the rest of the legacy 507-node ancestry are reused, not freshly
replayed here.** A source hash is not being represented as a new proof of
those inherited bounds.

## Elementary physical rows

Every original frame is written u=(alpha,beta), v=(-beta,alpha), with
alpha>0, |beta|<=alpha, alpha^2+beta^2=1 and t=beta/alpha in [-1,1].
The model uses these same frame variables in every pair and every corner.
All auxiliary variables can be assigned their actual simultaneous products.

The necessary affine rows in `four_exact.py` have the following proofs:

1. Frame sine/cosine bounds use monotonicity and exact outward radical
   bounds. The cosine lower chord and upper supporting tangents follow
   from circle concavity. Absolute values use the exact sign or their
   convex upper secant. The inset function 1/(4h) uses its convex lower
   tangents and upper secant; h+g>=1 follows from (2h-1)^2>=0.
2. Each original corner obeys every retained rational projection bound
   w.c+H(w)<=sqrt(Q)|w|. The literal direction's exact norm is used;
   none of the binary rational trigonometric suggestions is assumed to
   have norm one. The squared-corner identity is
   |c|^2+1/2+s(alpha*x+beta*y)+t(-beta*x+alpha*y)<=Q
   for each independent sign s,t. Square tangents/secants and the four
   McCormick inequalities enclose the actual original products.
3. Original incircles imply center distance at least one. Every original
   center has norm strictly below rho=91/60 because its farthest corner
   has squared norm at least |c|^2+|c|+1/2 and
   rho^2+rho+1/2-Q=31/57600>0. Square secants turn those necessary
   distance comparisons into affine rows on the current center box.
4. For an actual separating axis owned by either square, the required
   support is R=(1+cos(delta)+|sin(delta)|)/2. Both determinant signs
   and the same original frame products are retained. The eight choices
   of owner, local axis and sign form a complete physical alternative
   set. A vertical or horizontal sign is forced only when the opposite
   coordinate gap has magnitude below one, while R>=1.
5. The halfwidth function f(theta)=(|cos(theta)|+|sin(theta)|)/2 is
   quarter-turn periodic and concave between its corners. For relative
   angle delta, |h_i-h_j|<=f(delta)-1/2=R-1: on each smooth interval
   the phase difference is monotone, so its maximum is at a projection
   corner. Thus the physical center distance squared is at least
   1+2*a_min*|h_i-h_j| for any proved 0<a_min<=1. This justifies the
   two signed owner-free width rows used in the table.
6. Each canonical square contains the coordinate diamond of L1 radius
   1/(2*alpha). Disjointness of these actual contained diamonds requires
   |dx|+|dy| at least the sum of their radii. Convex absolute-value
   secants give the stated all-sign diamond rows.
7. For an owned tangent t and the other original tangent u, the support
   multiplied by sqrt(1+t^2) is
   sqrt(1+t^2)/2+(1+t*u+|u-t|)/(2*sqrt(1+u^2)).
   In the coupled separator bound, replacing t by the interval midpoint
   pays (t-t_mid) times the *same* transverse center gap, using its
   appropriate endpoint on each half. In u the minimum is at an
   interval endpoint or u=t, by support concavity in the other frame
   angle. Each remaining t-piece is A*sqrt(1+t^2)+B*t+C with A>0.
   Its convex minimum is at an endpoint or the explicitly enclosed
   critical point. `coupled_lower` prints this finite endpoint/kink
   reduction; `cvx_lower` encloses every radical downward.

Imported pair-cap, beta-toll, sharp-toll and three-square-energy slots are
replaced by the true row 0<=0, preserving indices only. The checker rejects
any arithmetic terminal that selects one of those unused slots. None of
those imported theorems is a proof premise for this table.

## Exact arithmetic rule

Radicals use integer-square-root enclosures at precision 2^-54. Each row
is rounded outward onto the 2^-44 grid. A coefficient change is paid on
the right by four times its absolute value. Every original and auxiliary
variable is explicitly checked to have absolute value at most four.

For integer row coefficients A_j and right sides B_j, nonnegative
integer multipliers w_j give a contradiction whenever

    reserve = -sum_j w_j*B_j - 4*sum_k |sum_j w_j*A_jk| > 0.

No approximate coefficient cancellation is accepted. The compact table
records selected row indices and, when necessary, selected kernel-equation
indices. `basis_integer.py` reconstructs integer multipliers by exact
fraction-free elimination. Omitting a kernel equation is safe only because
the checker pays the entire residual across *all* actual variables. Three
terminals retain explicit integer weights instead. A reconstructed vector
is merely a candidate until its nonnegativity and full reserve pass.
The delivered table therefore needs no numerical solver to verify.

The 47 remaining terminals use the printed common-axis theorem in
`EFHI_COMMON_AXIS_PRUNING.md`: the F box gives |c_F|<29/60, so its distance
to any other original center is <2. Two successive genuine separations
along the identical owned axis, with F at one end, require projected
span at least two. The checker requires literal owner-and-axis identity;
nearby axes or unrelated original frames cannot be joined.

## Complete cover and fresh validation

The eight closed roots independently choose signs for E,F,I, with H's
complete permitted interval [-1,0]. Every angle split retains both closed
midpoint halves. Every physical split retains all eight owned-axis/sign
children. Finite induction therefore covers every original caller,
including contacts and all shared faces.

| Item | Count |
|---|---:|
| Signed roots | 8 |
| Total nodes | 6,462 |
| Complete angle splits | 2,759 |
| Complete eight-way physical splits | 117 |
| Exact weighted contradiction leaves | 3,539 |
| Common-axis geometric leaves | 47 |
| Weighted row occurrences checked | 137,731 |
| Unresolved leaves | 0 |

This continuation freshly regenerated and checked every weighted leaf in
eight explicit disjoint batches covering arithmetic indices 0 through
3538. Each batch also checked the entire cover. The minimum exact reserve,
normalized by 2^44 times the sum of the integer weights, is strictly greater
than 1/1,000,000. `LEAF480_REPLAY.json` binds the exact sources and ranges.
Twelve damaged structure/arithmetic controls were rejected while bypassing
the packet hash, so rejection was not merely a checksum test.

The source-level mathematical derivations are author-checked. No separate
human review, proof-kernel verification, Lean, Lake or CI is claimed.
No complete Cd402 or C887 original is credited. The remaining saved Cd402
leaves are 42,44,45,47,48,51,468,495,498,499,502,506.
