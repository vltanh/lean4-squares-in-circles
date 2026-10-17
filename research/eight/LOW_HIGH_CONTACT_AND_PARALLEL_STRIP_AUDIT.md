# Independent audit of the low/high contact and parallel-strip proofs

Reviewed:

- `LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md`;
- `LOW_HIGH_PARALLEL_STRIP_HAND_PROOF.md`.

**Result: both hand lemmas pass.** Their scope is the specified low/high
outer-state contacts and the opposite-sign parallel strip with the
source positive secondary separator. They do not by themselves establish
the whole pair theorem or a global capture result.

## Aligned contacts

The outer arc is parametrized monotonically by its transverse coordinate.
The derivative identities `a'=-r`, `r'=Q/(a+1/2)^3`, and the two label
derivatives have the correct signs on both type arcs.

For the parallel contact, a feasible pair can lower its target transverse
coordinate to `B=1-b`: this value is above the high arc's lower endpoint
and no greater than the original feasible value. At contact, feasibility
with `B<=c` gives `b>=1-c`, and the entire contact interval is the one
printed in the note. Both terms of the displayed second derivative have
the correct signs. Its negative term uses the lower bound on the source
radical, and its positive term uses the upper bound on the target radical.
The endpoint derivative is strictly positive, so the lower endpoint is
the minimum throughout the contact interval.

For the positive-sign quarter contact, minimizing over the high state
at fixed low coordinate gives `A=max(c,1-b)`, because `-ell_H` increases
with A. If `b>=1-c`, the diagonal high endpoint is the minimizer and
monotonicity of the low label applies. If `b<=1-c`, the contact
`A=1-b` stays on the high arc: `c<=A<=1`, and its transverse coordinate
is greater than 1/2, so `B/A>1/2>3/7`. The two derivative identities at
the common endpoint, and the positive lower curvature, give exactly the
quadratic loss `2 d_0^2`. This is below the stated `1/50000000`.

The four radical comparisons, the endpoint ratio comparisons, both
curvature reserves, and the final rational costs were independently
recomputed with exact fractions. Their printed rational values agree.

## Parallel strip contact reduction

For the target transverse coordinate, the derivative of the signed
projection is

\[
D=\cos\phi-r\sin\phi>0.
\]

The target's minimum transverse endpoint is strictly infeasible in both
type orders, while every given feasible pair has a nonnegative margin.
Thus decreasing the target coordinate reaches a unique contact inside
the same type arc and cannot increase the cost.

At contact the derivatives

\[
B'=-P/D,\qquad
C'=1-\beta h'-\ell_t'P/D
\]

follow with the stated sign of `P`. The four derivative bounds have
the correct directions:

- For a high target and negative angle, contact implies
  `B>=1-b>=27/40`. This is the essential strengthened lower bound on
  its ratio r. The rational lower product exceeds 1.17 and hence
  exceeds the largest possible `1-beta h'`, which is 1.09.
- For a high target and positive angle, contact gives `B>=.651`.
  The outer circle then gives `A<9/8`, providing the necessary upper
  bound on P. The displayed lower bound for `C'` is positive.
- For a low target and negative angle, the uniform primary-coordinate
  lower bound makes the product exceed 3/2.
- For a low target and positive angle, contact supplies the lower
  transverse bound `.0717` and hence the sharpened ratio lower bound.
  Its product upper bound is below `.909`, strictly below `.91`.

The exact fractional identities in the two narrow product estimates,
and the inequalities in the other two cases, were independently
recomputed. In total, 23 displayed identities and scalar inequalities
were checked independently; all pass.

## Type boundaries and reversal

For negative angle, increasing the angle toward zero decreases the target
coordinate. Its endpoint `1-b` is above the target type's minimum in
both orders, and it is no greater than the original negative-angle
contact coordinate. The path therefore remains inside the type arc.

For positive angle, decreasing the angle increases the target coordinate.
If its upper type endpoint is reached, holding that endpoint fixed and
continuing the source by the displayed contact equation is valid. The
source then increases only up to `1-c` in the low-source case or
`1-b_L` in the high-source case. Both final coordinates lie strictly
within the source type arc. The two boundary cost derivatives remain
strictly positive, so this continuation lowers the cost as the angle
decreases. There is no unproved appeal to continuity of the aligned
inequality across a type boundary.

Reversing the pair and reflecting the plane preserves the relative frame
angle phi, the positive center-angle gap, and the displayed corrected
cost. It interchanges the relevant source and target ownership. Thus the
stated reversed target-axis regimes follow from the same proof.
