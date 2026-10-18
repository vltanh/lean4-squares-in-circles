# Independent audit: symmetric outer edge 4, aligned and whole angle

**Result: PASS. No mathematical or source correction is needed.**

This audit independently rereads and binds the two restored sources

- `proof_integration/WRONG_0011011_SYMMETRIC_ALIGNED_OUTER_HAND_PROOF.md`;
- `proof_integration/WRONG_0011011_SYMMETRIC_OUTER_WHOLE_ANGLE_HAND_PROOF.md`.

The first is the strict aligned contact inequality. The second proves the
entire edge-4 `OO(+,-)` row for `-.7<=phi<=.7`, including all four retained
axes, by reduction to the first. Both use `Q=9789/2500` and the exact
role label with coefficient vector
`[3965,0,385510,-149748,-189442]/100000` in the feature order
`[1,a,b,b^2,ab]`. I checked this vector directly against the role JSON.

The independent companion
`audit_wrong_0011011_symmetric_outer_hand.py` makes **45 strict rational
comparisons**, reconstructs the **five quartic coefficients** from the
radical elimination, and replays both author checkers in a fresh temporary
directory. The two author replays pass all **16 and 71 comparisons**.
The aligned output is byte-identical. The restored whole-angle JSON has
one additional final newline; after removing only final newline bytes it
is identical, and every parsed JSON value is exactly equal. The original
files remain unchanged. The audit JSON records this distinction and binds
both manuscripts, both checkers, both original arithmetic files, and the
role coefficient file by SHA-256.

## 1. The aligned quartic

I expanded both labels before eliminating their radicals. With
`b=1/2+x`, `B=1/2-x`, `z=x^2`, and
`U=sqrt(Q-(1+x)^2)+sqrt(Q-(1-x)^2)`, their sum minus gamma is

\[
 C-\frac g2U-2pz+\frac{4gz}{U},
 \qquad C=3.23522,
\]

where `p=1.49748`, `g=1.89442`. The genuine-radical identity

\[
 z=\frac{U^2(4(Q-1)-U^2)}{4(U^2+4)}
\]

gives precisely the printed quartic divided by `U^2+4`. In particular its
coefficients are `4C`, `g(4(Q-1)-2)`, `C-2p(Q-1)`, `-3g/2`, and `p/2`.
No converse implication after squaring is used.

The actual contact domain has `|x|<.4`. The radical sum is even and
strictly concave on the larger closed interval `[-.4,.4]`; its second
derivatives are negative and the radicals remain positive. The three
displayed square comparisons therefore prove `3.28<U<3.42` with the
correct endpoint directions. The quartic has increasing second derivative
and `P''>29` on that interval. Its value and derivative at the rational
point `3.3974` give `P>.0019` by the stated completed square. Consequently
the aligned sum exceeds gamma by more than `19/156964>.00012`.

All quartic coefficient identities, interval endpoint comparisons,
reference value/derivative bounds and the completed-square reserve were
reconstructed separately from the author's program.

## 2. The full-angle contact reduction

I rederived the two source projections from the own-frame centers
`(a,-b)` and `(A,B)`. Reflection followed by reversal preserves their
cost and takes axes `1,2,3,4` to `3,4,1,2`; hence both target-owned
separators are included by the source-axis proof.

The primary-axis exclusions have the correct signs for negative phi and
for the two positive intervals. In the last positive interval the forced
target coordinate `B>.6` and the global lower derivative bound on the
label supply the displayed direct cost reserve.

For the secondary separator its projection and both labels strictly
increase with either coordinate. Decreasing coordinates to contact is
valid, and the two-zero state cannot still separate. This reduction is
made in an explicitly larger pair domain, so it does not silently require
preservation of any center-angle constraint.

For positive phi I checked both contact derivatives, the speed identity,
and all three coordinate strips. In the two strips flowing to alignment,
the resulting aligned coordinate stays inside the outer arc. The small
target strip with an unavailable aligned endpoint is handled separately
by the scalar lower bound; it is not incorrectly continued past the arc.
The concavity of the label on `[0,.15]` gives a **lower** chord, and the
convexity of its derivative with a negative right endpoint rules out an
interior minimum on `[0,.6]`. The remaining strongly convex scalar bound
has the correct coefficient `(.005)^2`.

## 3. The negative-angle minimum cannot occur off alignment

I independently obtained `v^2=Q-2B-(b-.5)^2`, the two derivatives
`H_x=-1+D(b)v`, `H_B=D(B)-D(b)K`, and the exact formula for `K/v`.
Differentiating this ratio gives exactly the two derivatives printed in
the note. The apparent sign qualification `z>=0` for its `B` derivative
causes no gap: first increase `z` to the positive endpoint `.06` or `.16`
using the globally positive `z` derivative, then use monotonicity in B.

The three stationary exclusions use lower bounds for `D`, `D'` and the
squared speed with the correct directions. They imply `B>.67` and the
stated upper bounds on b. On those remaining intervals the ratio bounds
give `H_B>0` whenever `H_x<=0`. I independently evaluated both ratio
endpoints and the global four-term upper bound for its B derivative.

Finally, I checked every boundary of the compact contact domain. The
upper angle `.7` is infeasible; the lower B boundary meets alignment;
at the source diagonal decreasing x is a feasible improving direction;
at the target diagonal a minimum away from the other boundaries would
have `H_x=0` and `H_B<=0`, contradicting the proved implication.
An interior minimum is likewise impossible. Thus every minimum occurs
at alignment, where the independent quartic theorem applies.

This is a complete continuous proof of the one stated pair row. Its only
geometric scope premises are the previously proved outer boundary and
four-axis reduction for the physical seven-ring. Its use in the full
`0011011` cyclic cover is recorded separately in the finite coverage audit.
