# Both original outer zero owners are sharp on the nonnegative-error ordered class

## 1. Original-candidate statement

Put `Q=9789/2500`. Retain original sorted own-frame coordinates,
corner containment at squared radius q<=Q, and the signs

\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
       =(b_H,-b_G,b_A,-b_B,b_T,-b_D,-b_E),\qquad b_i\ge0.
\tag{1}
\]

Let the original real frames have spread less than 7/10 and order

\[
 \theta_D\le\theta_A,\theta_B\le\theta_H,
 \qquad\theta_D\le\theta_E\le\theta_H.
\tag{2}
\]

Assume the actual outer zero differences have the nonnegative signs

\[
                 \theta_G-\theta_H\ge0,
                 \qquad\theta_D-\theta_T\ge0.
\tag{3}
\]

Retain any original witnesses in the following stated sets:

\[
\begin{array}{c|rrrrrrr}
\text{edge}&HG&GA&AB&BT&TD&DE&EH\\ \hline
\text{axis}&0\text{ or }2&0&0\text{ or }2&2&0\text{ or }2&3&1.
\end{array}
\tag{4}
\]

**Sharp original-class theorem.** Every such candidate has `q>=q_*`.
At equality its three original zero differences vanish, its original
five anchors are the unique stationary anchors at tilt t_*, and the
full weak five-parameter equality classification applies to the
original packing.

For an original G0--G2 candidate, the signs of H, A, B and D in
(1) already follow from its four quarter owners, by Section 11 of
`HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md`. G negative and T
positive are still hypotheses for the noncanceling HG0/TD2 choices;
they are automatic from the global zero-owner theorem for HG2/TD0.
The frame order and the original-owner assumptions remain explicit.
This theorem does not assert unrestricted capture into (1)--(4).

## 2. Reduce all three zero differences at the actual radius

If q is smaller than `q_L=19577/5000`, first enlarge its containing
ceiling to q_L, without moving the original centers. Since
`q_L<q_*`, proving the result there also excludes the smaller q.
At q>=q_L use the actual q throughout the following constructions.

Section 7 of
`HAND_G5_POSITIVE_HG_ZERO_OWNER_BOUNDARY_REDUCTION.md`
applies to (1)--(4). It uses the unchanged intermediate circle for
every HG0/TD2 side and the canceling composite for every HG2/TD0
side. Its constant-cap comparison covers both original AB owners
and both signs of the AB error, and supplies a common A/B frame
with `b_A+b_B>=1`.

At least one middle tangent is at least 1/2. That outer side can
be aligned, by the canceling transport or the noncanceling theorem
as appropriate. Its middle primary then exceeds 1.1, and its
middle tangent is less than .665. The other middle tangent is
therefore greater than .335.

The remaining side also aligns unless it produces the explicit
G- or T-zero endpoint of that same theorem. The complete
`HAND_G5_G_ZERO_ENDPOINT_EXCLUSION.md` excludes both endpoints
on their entire constructed domains at Q, including either E
sign after reflection. Hence all three zero edges reduce to
alignment in the necessary five-anchor system, still at the
same actual radius q.

H, D and E and their two original mixed constraints are unchanged.
The A/B frame remains between H and D. Thus the result is exactly
the five-anchor system (1)--(3) of
`HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md`, with
nonnegative splits `t+u=delta+epsilon=alpha<=7/10`.
No original small-mismatch condition is used or claimed to survive.
No replacement G/T or omitted packing constraints are needed by
that five-anchor theorem.

Its sharp inequality immediately gives `q>=q_*`.

## 3. Preserve the strict anchor loss needed for original equality

We record why this is also an equality theorem for the original
centers. Every nonzero original AB difference yields strict AB
room in the common-frame comparison. Its constructed A/B circle
ceilings can therefore be decreased a little, retaining a strict
loss in at least one anchor.

For a nonzero canceling outer difference, its positive transport
has strict pair slack. For a nonzero noncanceling difference with
middle tangent at least 1/2, the direct transport has slack greater
than the difference divided by 25. These strict inequalities allow
a small primary decrease at the constructed middle anchor, and
therefore a corner value strictly less than q.

On the other noncanceling side, the whole-interval function F(h)
of the positive-owner theorem is strictly convex. Its two possible
endpoints are alignment and the now-excluded zero-transverse
endpoint. If the original h is positive, feasibility and the
strict endpoint comparison force strict room at the aligned
endpoint. Again a small primary decrease gives strict corner loss.

An inherited strict A or B loss is preserved when its side already
has h=0 by retaining that anchor. If the side has h>0, lifting it
to the common q-circle cannot erase the needed conclusion: the
strict direct comparison or strict convexity just described
recreates a strict circle loss after alignment. More explicitly,
a strict primary lift makes the quarter cap strictly feasible;
in the convex comparison it lies strictly before the zero-
transverse cap endpoint. This is the strictness argument recorded
in Section 4 of the positive-owner theorem. The argument also
applies after the AB cap comparison.

Thus every nonzero original zero difference leaves strict slack
in at least one of the final A/B circles. H, D and E have stayed
fixed. All further reductions in the aligned hard-class theorem
retain this slack through separate A/B ceilings; its five positive
circle masses make such slack impossible at q=q_*.

Consequently, at q=q_* all three original zero differences were
zero. The original five anchors now themselves satisfy the aligned
hard-class theorem. Reapplying its sharp identity to those
original anchors forces `u=delta=0`, `t=epsilon=t_*`, and the
five stationary corner vectors. No original center is identified
with a moved descendant merely because their radii agree.

For an original packing, its actual remaining G/T and central-
square constraints give precisely the full weak five-parameter
equality family and its converse, as in
`HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md`. The construction therefore closes the lower bound
and original-center equality on the entire class (1)--(4).

Negative noncanceling outer errors, other frame orders, the
remaining G/T sign alternatives and other original quarter/mixed
owners remain separate global-entry questions. No state table,
angle mesh, sampled minimum, external acceptance result, Lean
compilation or CI is used here.
