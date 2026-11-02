# Independent hand review of the unrestricted structural continuation

November 2, 2026. This review records mathematical reconstruction by the
integrating agent and separate agents. It is not a claim of independent
human review or kernel verification. No mathematical script was used to
derive or verify any accepted identity below.

## 1. Selective coordinate orders: PASS

Source: `UNRESTRICTED_FIVE_PROXY_CHAIN_HAND_PROOF.md`.

The constrained unary maximum is correct in both branches: in own square
coordinates the containing condition is
`(|U|+1/2)^2+(|V|+1/2)^2<=Q`. Maximizing the requested coordinate is either
the circle support value `r-h` or the constrained endpoint value
`(h+k)(sqrt(Q-1/4)-1/2)`. The strong-concavity estimate for F has the correct
second derivative and all its signs. The rational anchor and derivative
were independently reconstructed:

    F(119/202)=255347/240380,
    F'(119/202)=-159665/3356157,
    17/16-F(119/202)=227/961520>1/5600.

The five-chain internal halfwidth, narrow center bands, and both outer
orientation branches are correct. In particular the last endpoint exclusion
uses the two distinct constrained unary cases and does not extend either
case beyond its premise.

The full g-orders and the selective completed orders are distinguished.
A full g-chain may have a consecutive pair actually separated in the other
coordinate. Only a nonactual consecutive edge in the selective construction
is guaranteed to be genuinely uncovered and to satisfy the selected-gap
dominance. This distinction is retained in the manuscript.

The orientation-dependent center-distance bound follows from an actual
owned separating normal. Both chirality formulas were reconstructed:
`cos(Delta)+sin(Delta)=2h_B a_A ± 2k_B b_A`. The resulting lower bound
`144/125` contradicts the selected-coordinate upper bound
`13sqrt(2)/16<23/20`. All new comparisons are already transitive because a
two-step path implies actual separation of its extremes.

The final nine-element Greene argument uses the cited theorem only for
maximal unions of two chains or antichains. At height four, the sole
partition when the largest two-chain union has size at most six is
`(4,2,2,1)`, with conjugate `(4,3,1,1)`. It does not assert simultaneous
partitions with every listed size. The completed-grid and completed-chain
alternatives retain their nonphysical edges.

The root agent and a second agent independently checked the mathematical
argument. The global lower-bound caller remains open.

## 2. Unrestricted actual-four-chain outsider strip: PASS

Source: `UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md`.

The endpoint-vector estimate uses the smaller of the two outward-quadrant
corner expressions when X>Y; it does not assume a particular corner offset
is physically present. The affine support estimate and expansion give

    S+(37/50)U<=1/8,
    g_E-|y_E|>=4421/12000>221/600.

The separating-axis argument keeps the outsider's full physical square.
Only the main endpoint is replaced by a contained g-square. Horizontal,
vertical and both outsider-owned side axes are all covered, including a
zero component. The minimum over the two component ratios has the correct
direction.

The two scalar branches are exhaustive because the comparison defining m
changes sign exactly with `b(k-17/480)`. The corner substitution is valid
before taking the smaller expression; its substituted X exceeds Y.
The polynomial coefficients in F, P1 and P2 were re-expanded by hand.
The rational values and derivative bounds at t=1/2 were also checked,
including the reserve `829849/3709440000`. The strict convexity estimate
proves the advertised lower bound `F>Q+3/2000` on the whole interval.

Thus the new conclusion `|x_F|<13/12` has no coordinate-cover assumption.
No side-column capacity or complete five-outsider exclusion is inferred
from it.

## 3. Unrestricted center cap at 21/20: PASS

Source: `THREE_SQUARE_DIRECTIONAL_CAP_21_OVER_20_HAND_PROOF.md`.

The horizontal-section formula and strict offset bounds ensure length at
least one. The marker separation is smaller than one, so the final capture
is interior. A section lying beyond a marker has an actual inward owned
normal with positive horizontal component; both signs are treated.

The upward-normal center contradiction and two short corner bounds are
correct. For downward normals the large-component center exclusion and
the half-angle substitution leave the complete interval `[0,3/7]`.
All nine coefficients of P were independently reconstructed from

    P=4(A^2+B^2)-155390625(1-t^4)^2.

Both rational anchors were checked by hand, including an independent
Horner reconstruction of their numerators:

    P(2/5)=130272735091/390625,
    P'(2/5)=475586408864/78125.

The monotonic first interval and the lower bound `P''>180000000` on the
second interval are valid. The completed-square reserve
`P>1475000/9` is positive and uses no sampled values. A single actual corner
suffices in the downward case; its being the farthest corner is not assumed.

The normalized boundary square contains the positive marker strictly.
Every other qualifying unit must therefore use the negative marker.
The bound of at most one other center with x>=21/20 and the center-triangle
corollary have the stated unrestricted scopes. The rational cap is not
claimed optimal.

The root agent and a second agent independently checked the full proof.

## 4. Sharp three-square half-plane cap: PASS

Source: `THREE_SQUARE_SHARP_HALFPLANE_CAP_HAND_PROOF.md`.

The larger-halfwidth threshold is exact:
`49/80+7/16=21/20`. The center-cap theorem therefore handles that full
range. In the remaining range, the own-axis components satisfy
`b<13/50`, `a>24/25`. Both steep normal signs are excluded by the printed
center comparisons, including the exact upper bound `987/2000<1/2`.

For the shallow upward normal, decreasing the center variables to the
stated boundary decreases the exact farthest-corner norm. The linear
increment from `(3/2,23/16)` is nonnegative by the displayed factorization;
the squared increments are retained. For the shallow downward normal,
the formula

    Delta x=(1-p+u(p-35/48))/p,  Delta y=p-1

and its linear contribution were independently derived. All four owned-side
possibilities are exhaustive, and the strict missing-marker inequality
handles the aligned endpoints too.

The markers at horizontal positions ±1/2 are **closed** captures. The
strict-counterexample argument first expands all three centers slightly,
preserving the positive half-plane guard and every square frame, to make
the closed squares pairwise disjoint. Pigeonhole is then legitimate.
Equality may share markers on boundaries. This is not replaced by an
unsupported interior-capture claim or an equality classification.

The aligned three-square attainer checks exactly. The root agent and a
second agent independently reviewed the entire derivation.

## 5. Publication boundary

All four proofs are accepted as hand theorems in their printed scopes.
They add no whole canonical-root transfer. The original 15 gates, 7,915
root IDs, and published 5,838 excluded / 2,077 open tally remain unchanged.
Unrestricted A.2 and global equality remain open.

Two allowed 48-start numerical experiments tested potential directions
across the continuation. Neither supplies proof evidence, a table entry,
or a case exclusion. No mathematical proof scripts, Lean, Lake, or CI ran.
