# High GA with both A-primary alternatives: complete assembly

## 1. Precise owner scope

Work on the fixed-original-witness G0--G2 boundary at

\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10}.
\tag{1}
\]

The original sorted outer states H, G, B and D have signed tangents
respectively positive, negative, negative and negative. The states
A, T and E may initially have either sign and either radial kind.
Retain the original owners

\[
\begin{gathered}
 HG\in\{0,2\},\qquad GA\in\{2,3\},\qquad AB\in\{0,2\},\\
 BT=2,\qquad TD\in\{0,2\},\qquad DE=2,\qquad EH=0.
\end{gathered}
\tag{2}
\]

There is no such cycle, for any signs of the seven original errors
and without a frame-order hypothesis.

The conclusion covers every combination of the GA3, AB2 and TD2
alternatives in (2). It retains the BT2, DE2 and EH0 hypotheses;
it does not identify them with their other original-owner alternatives.

The original variation theorem gives

\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{3}
\]

The proof below joins the pointwise stress theorems and the actual
flat-core transport. When the transport changes A, only its proved
neighboring inequalities, circle conditions and variation bounds
are used afterward.

## 2. The secondary A pair

First suppose \(GA=2\), \(AB=0\). If \(TD=0\), apply the
[secondary-owner four-circle exclusion](HAND_G3_HIGH_GA_LOW_EH_SECONDARY_OWNER_FOUR_CIRCLE_EXCLUSION.md).
If \(TD=2\), apply the
[TD2 angle reduction](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md)
and its
[complete scalar theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_COMPLETE_SCALAR_EXCLUSION.md).
Their nonpositive and positive TD branches exhaust all errors.

These proofs use the four retained sorted outer circles, the
circle/core inequalities for the intermediate states, the original
separating projections, and (3). Consequently they also exclude
a necessary comparison system with these same inputs after a local
transport; they do not require a marker value to be recomputed.

At an aligned edge the two relevant owner projections coincide:

\[
 P_{GA3}=P_{GA2}=a_G-y_A\quad(d_{GA}=0),\qquad
 P_{AB2}=P_{AB0}=y_A+b_B\quad(d_{AB}=0).
\tag{4}
\]

Thus a primary alternative with zero error may immediately be
replaced by its actual secondary witness.

## 3. A single positive primary error

Suppose exactly one of GA3 or AB2 is selected, and its error is
strictly positive. Let \(a>0\) denote that error; the other A edge
has its secondary owner and arbitrary error.

For \(TD=0\), the
[positive-intermediate TD0 theorem](HAND_G3_POSITIVE_INTERMEDIATE_TD0_FOUR_CIRCLE_EXCLUSION.md)
excludes the pattern for every original TD error.
For \(TD=2\) with \(d_{TD}\ge0\), use the
[two-positive split theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md)
and its
[complete endpoint theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_COMPLETE_SCALAR_EXCLUSION.md).
For \(TD=2\) with \(d_{TD}\le0\), use the
[positive-intermediate / nonpositive-TD2 theorem](HAND_G3_POSITIVE_INTERMEDIATE_NEGATIVE_TD2_EXCLUSION.md).

All three results allow either sign and either radial kind at A,
T and E, and arbitrary signed errors on every retained secondary
edge. They therefore exhaust the single-positive-primary case.

## 4. A single negative primary error

Suppose exactly one of GA3 or AB2 is selected, and its error is
strictly negative. If \(TD=0\), or if \(TD=2\) has nonpositive
error, the
[negative-intermediate fixed-stress theorem](HAND_G3_NEGATIVE_INTERMEDIATE_ERRORS_FIXED_STRESS_EXCLUSION.md)
already excludes the system. It has no additional sign or radial
hypothesis on A.

It remains to consider \(TD=2\) with \(z=d_{TD}>0\).
Apply the
[negative-primary entry theorem](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md)
to the negative A edge.

If the actual secondary projection is feasible at the same states
and frames, select it. This gives the secondary A pair treated
in Section 2. Otherwise the original A state is positive flat core,
and the genuine primary alternative satisfies

\[
\begin{array}{ll}
 GA3:\;&a_A=7/12,\quad 0<y_A<39/250,\quad -1/4<d_{GA}<0;\\
 AB2:\;&a_A=7/12,\quad 0<y_A<1/2,\quad -19/50<d_{AB}<0.
\end{array}
\tag{5}
\]

The
[negative-flat-core / positive-TD2 concentration theorem](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_ANGLE_CONCENTRATION.md)
and its
[complete scalar exclusion](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md)
exclude exactly these two necessary systems. Their proof retains
all original circles, permits either sign and radial kind at T and E,
and covers the closed versions of the two angle intervals in (5).

This finishes every single-negative-primary case.

## 5. Two primary errors with nonnegative signed sum

Now suppose \(GA=3\), \(AB=2\), and write

\[
 u=d_{GA},\qquad v=d_{AB},\qquad a=u+v.
\tag{6}
\]

If \(a\ge0\), apply
[the signed combination theorem](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md).
Its local charge inequality is valid for both same-sign and
opposite-sign allocations, including \(a=0\). With equal multipliers
on GA3 and AB2 it bounds their combined A contribution by the same
support charge as a single positive primary error of size \(a\).

That theorem explicitly joins all three downstream alternatives:
arbitrary TD0, nonnegative TD2, and nonpositive TD2. In each case
the two removed angular arguments may be set to zero in the
algebraic circle expression. The remaining variation domain only
enlarges, by (3). No new original owner or frame is inferred.
Thus every allocation with \(a\ge0\) is excluded.

## 6. Two primary errors with negative signed sum

It remains that \(u+v<0\). If either error is zero, (4) reduces
to the single-primary cases. Otherwise use
[the negative-sum flat-core transport](HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md).
That theorem covers both opposite signs and two negative errors.

Its first alternative selects an already feasible actual secondary
owner at a negative primary edge, leaving a single-primary pattern.
The preceding sections exclude that pattern, whatever the sign of
its remaining primary error.

In its other alternative, only A changes. The output has either

\[
 GA3\text{ with error }u+v<0,\quad AB0\text{ aligned},
\tag{7}
\]

or

\[
 GA2\text{ aligned},\quad AB2\text{ with error }u+v<0.
\tag{8}
\]

The aligned secondary witness is an actual feasible projection at
the constructed state. The four sorted outer states H, G, B, D
and their frames stay fixed; T and E also stay fixed. A remains
positive, sorted and on its true flat core, with strict shifted-circle
slack below \(Q\). Its tangent stays below \(1/2\).

Both changed errors retain their sum. Their positive and negative
variation decreases by the same amount in the opposite-sign case,
and is unchanged in the two-negative case. Thus the full transformed
necessary system still satisfies (3). Every unchanged neighboring
projection is identical, and both changed projections remain feasible
by the transport theorem.

If the terminal negative primary already has its secondary projection
feasible, Section 2 applies. Otherwise the same-state local inequalities
from the entry theorem recover the corresponding genuine-primary
angle cut in (5). This step only uses the retained outer neighboring
circle, the positive flat-core A state with \(y_A<1/2\), the actual
two projections, and the shifted-circle inequality. It does not
invoke the global marker theorem on the moved state.

For arbitrary TD0 or nonpositive TD2, the fixed-stress proof of
Section 4 applies directly to the transformed necessary system.
For positive TD2, the negative-flat-core scalar proof applies with
the recovered cut. Every input of those stress proofs has just been
retained explicitly, so no preservation of nonneighbor packing
constraints is required.

Hence (7) and (8) are both impossible. This excludes all allocations
with \(u+v<0\), and completes every original-owner alternative in (2).
