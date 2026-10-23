# Every tangent cut follows from S <= 3/200 alone

## 1. Complete conditional capture theorem

Assume the G0--G2 candidate geometry with cyclic roles
`(H,G,A,B,T,D,E)`, quarter word `0101011`, and the G2 reflection
normalization `y_E<=0`. Retain the original sorted own-frame centers,
the original signed separating-axis disjunction on every edge, core
avoidance, and corner containment at

\[
 q\le Q_0=9789/2500.
\]

Let the mismatch of this normalized candidate be

\[
 S=|d_H|+|d_A|+|d_B|+|d_T|+|d_D|\le3/200.
\]

For a center written `(a_i,-y_i)`, put `u_i=y_i/a_i`.
Then every such candidate satisfies all six strict tangent cuts:

\[
 \boxed{
 -4/5<u_G<-1/20,\qquad
 1/20<u_T<4/5,\qquad
 u_H>1/2,\qquad u_D<-1/2.}
\tag{1}
\]

In addition, all six zero-edge signs are the intended signs and
every original feasible BT and DE witness belongs to `{2,3}`.
No tangent cut, mixed owner, tilt window, or earlier mismatch
contraction is a hypothesis of this theorem.

The condition on S is essential to the present proof. This note
does not claim that every unrestricted packing satisfies it.

## 2. Forward dependency order

First apply
`HAND_G3_D_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md`
and then
`HAND_G3_B_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md`.
Their larger threshold `S<=1/32` applies here. They prove both
quarter-owner restrictions and the strict signs

\[
 (y_H,y_G,y_A,y_B,y_T,y_D)
       =(b_H,-b_G,b_A,-b_B,b_T,-b_D),\qquad b_i>0,
 \qquad b_E=-y_E\ge0.
\]

Those proofs use only G0--G2, the E normalization, and the stated
mismatch bound. In particular, they do not borrow an H or G cut
from the conclusions below.

Next apply `HAND_G3_FOUR_CUTS_AT_ONE_THIRTY_SECOND.md`. From
the same original zero edges and the now proved quarter owners,
it gives

\[
 u_G<-1/20,\qquad 1/20<u_T<4/5,\qquad u_D<-1/2.
\tag{2}
\]

To prove the H cut, suppose `b_H<=a_H/2`. The complete
whole-arc reductions and stresses in
`HAND_G3_H_LOW_HIGH_INDEX_STRESSES_AT_THREE_TWO_HUNDREDTHS.md`
exclude GA0 and GA2 on the full frame interval, and exclude
every nonnegative GA tilt. The only possible GA witnesses would
therefore be G1 or G3 at negative tilt. That same note excludes
their five pairs

\[
 (G1,E2),\ (G1,E3),\ (G3,E1),\ (G3,E2),\ (G3,E3).
\]

The other three pairs

\[
                    (G1,E0),\ (G1,E1),\ (G3,E0)
\]

are excluded in
`HAND_G3_H_LOW_PRIMARY_BRANCHES_AT_THREE_TWO_HUNDREDTHS.md`.
Every actual EH edge has an original feasible witness. Hence no
original GA witness can coexist with it under the H-low assumption.
This contradicts the original separating-axis disjunction and proves

\[
                              u_H>1/2.                       \tag{3}
\]

Finally apply
`HAND_G3_HIGH_G_CUT_FROM_H_CONE_AT_THREE_TWO_HUNDREDTHS.md`.
Its only extra tangent input is the weak H cone, which (3) has
now supplied in forward order. It proves `u_G>-4/5` without any
prior G, T, or D tangent cut. Together with (2)--(3), this is (1).

Every exclusion is strict for each retained original witness.
Thus an inadmissible axis tied with an admissible one is excluded
as well. No existential witness has silently been replaced by a
preferred owner.

## 3. Consequence for the remaining global proof

The complete later owner-frame chain at `S<=3/200` can now take
G0--G2 and the mismatch bound as its inputs, rather than separately
assuming the six tangent cuts. In forward order:

1. This note supplies all tangent cuts, all zero-edge signs, and
   both intended short-quarter owner restrictions.
2. `HAND_MIXED_OWNER_CLOSURE_AT_THREE_TWO_HUNDREDTHS.md` supplies
   every original mixed owner G0/E1.
3. The negative-tilt and owner-frame positive-tilt theorems give
   `t>S` and `1/10<tau<4/25`, using the actual retained ED-owner
   frame to define tau.
4. `HAND_OWNER_GAUGE_SHARP_TERMINAL_AT_THREE_TWO_HUNDREDTHS.md`
   gives the sharp lower bound and forces `S=0` at equality.
5. The fixed-ceiling transfer and original-center equality argument
   in `HAND_FIXED_CEILING_TRANSFER_AT_THREE_TWO_HUNDREDTHS.md`
   supply the documented boundary/radius implication and complete
   five-parameter equality family.

For the last stages it suffices to consider
`q<=Q1=1957767069/500000000<Q0`, because the stationary construction
already proves `q_*<Q1`.

The unresolved unrestricted capture implication can therefore be
stated particularly simply:

\[
 \boxed{\text{every G0--G2 candidate at }q\le Q1,
       \text{ normalized by }y_E\le0,\text{ has }S\le3/200.}
\]

A proof may reach that bound by the historical coarse and middle
contractions or by a new coupled argument. Those contractions
remain open. The present theorem removes the tangent cuts as
independent missing premises after small mismatch; it does not
prove the small-mismatch premise itself.
