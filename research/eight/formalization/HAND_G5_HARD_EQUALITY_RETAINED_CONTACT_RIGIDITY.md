# Retained contact rigidity at sharp hard-owner equality

## 1. A strict neighboring gap also obstructs sharp equality

Use exactly the necessary-system hypotheses of
[the arbitrary-sign, arbitrary-frame hard-owner theorem](HAND_G5_ARBITRARY_SIGNS_AND_FRAMES_HARD_OWNERS_SHARP_REDUCTION.md).
In particular GA0 and BT2 are actual retained witnesses; HG,
AB and TD have their original transverse owner sets; the original
zero-owner sign implications and the E radial alternative are
retained. The common actual ceiling is the sharp value q_*.
Write the slack of an actual witness as its projection minus
its required width
\[
                 W(d)=(1+\cos d+|\sin d|)/2.
\tag{1}
\]

**Contact-rigidity lemma.** At this ceiling every retained HG
and TD witness has zero slack. The retained GA0 and BT2 witnesses
also have zero slack. Thus a necessary hard-owner input with a
strictly positive HG or TD slack cannot have ceiling q_*.
This conclusion concerns an actual separating inequality; it
does not require a circle loss at G or T.

The hard-owner equality theorem applies directly to this input.
It gives normal original G/T signs and the original frame identities
\[
 \theta_G=\theta_H,\qquad
 \theta_A=\theta_B=\theta_T=\theta_D=\theta_E,
 \qquad \theta_H-\theta_A=t_*>0.
\tag{2}
\]
It also identifies the input's own five anchors H,A,B,D,E with
the stationary five anchors. Their two composite contacts are
\[
 b_H+a_A\cos t_*-b_A\sin t_*=1+W(t_*),
 \qquad a_B+b_D=2.
\tag{3}
\]
These are the first and third equalities of (15) in
[the aligned five-anchor sharp theorem](HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md).
They follow there from the actual stationary contact equations;
equivalently the positive equilibrium weights in its (21)--(24)
force every composite contact to be tight.

Put g=-y_G and z=y_T. At the original alignments (2), either
surviving HG owner has projection b_H+g, and either TD owner
has projection z+b_D. The other two actual projections are
\[
                 P_{GA0}=-g+a_A\cos t_*-b_A\sin t_*,
                 \qquad P_{BT2}=a_B-z.
\tag{4}
\]
The HG and GA0 slacks are each nonnegative and, by (3)--(4),
their sum is zero. Hence each is zero. The BT2 and TD slacks
are likewise nonnegative and sum to a_B+b_D-2=0. This proves
the lemma, including every weak owner tie and without fixing
either intermediate's free primary coordinate.

## 2. What a pair-only descendant can prove about its source

Suppose a sequence of G-only and T-only pair constructions keeps
the original five anchors H,A,B,D,E, including their frames,
unchanged and ends in the hard-owner class of Section 1 at q_*.
Only the final input to that sharp theorem is used in the following
conclusions.

First, the original unchanged anchor frames obey
\[
          \theta_A-\theta_H=-t_*<0,
          \qquad \theta_D-\theta_B=0.
\tag{5}
\]
Consequently an original positive HG/GA signed total, or an
original positive BT/TD signed total, is impossible. This includes
both individual-sign possibilities in
[the uniform-radius primary-pair theorem](HAND_G5_UNIFORM_RADIUS_PRIMARY_PAIR_TRANSPORT.md).
The conclusion uses invariant anchor-frame differences, not the
new intermediate's frame or circle.

Second, a G-only construction that ends with G aligned to A
cannot itself be part of such a sharp hard-owner input. Equation
(2) would then give H=G=A, contradicting t_*>0. This excludes
that endpoint even without a strict local contact estimate.

Third, if the final input retains a strict HG or TD slack from
one of its pair constructions, the contact-rigidity lemma gives
a contradiction. The word “retains” is essential: a later change
to an incident anchor or intermediate must be checked to preserve
that same slack before this argument is used. An independent
operation on the other intermediate preserves it automatically.

These statements are also valid when a source was already a
necessary boundary-neighbor comparison system rather than a full
packing. The final hard-owner theorem is itself a necessary-system
theorem, so no omitted nonneighbor inequality is imported.

## 3. Strict information supplied by the established local pair proofs

The following consequences use the actual strictness statements
of the cited local proofs.

* The nonpositive-total
  [wrong-sign primary-pair construction](HAND_G5_GLOBAL_PRIMARY_ENTRY_WRONG_SIGN_PAIR_REDUCTION.md)
  ends at G=A with actual GA0 and HG0 slack greater than 1/25.
  Its reflected T construction ends at T=B with actual BT2 and
  TD2 slack greater than 1/25.
* A normal positive GA1 with nonpositive HG0/GA1 total has the
  [same-radius G=A construction](HAND_G5_GLOBAL_PRIMARY_ENTRY_POSITIVE_GA_NONPOSITIVE_TOTAL.md)
  with strict HG0 slack. Its local reflected construction has
  T=B and strict TD2 slack. This reflection involves only the
  three local states and does not assert any reflected E theorem.
* A genuine negative GA1 with nonaligned HG has either G=A or
  G=H as an endpoint, with a strict surviving transverse HG
  slack, by the
  [noncanceling](HAND_G5_CORE_NEGATIVE_GA1_WITH_NONCANCELING_HG.md)
  and [canceling](HAND_G5_CORE_NEGATIVE_GA1_WITH_CANCELING_HG.md)
  local companions. Their local reflected statements give the
  corresponding strict TD slack for a genuine negative BT3
  with nonaligned TD.

If one of these endpoints already supplies the missing hard
owner, and subsequent independent pair operations retain the
strict transverse slack, Section 1 excludes sharp equality.
If it supplies only alignment while the primary remains genuine,
an additional actual primary-entry theorem is still required.
For example the complete aligned negative-GA entry with BT2
records a strict H-anchor loss, and
[the two-negative direct second transport](HAND_G5_GLOBAL_PRIMARY_ENTRY_BOTH_NEGATIVE_DIRECT_SECOND_TRANSPORT.md)
records a strict D-anchor loss while preserving the earlier H loss.
Those losses give their own sharp-equality obstructions.

This note does not infer a missing entry theorem from a local
alignment. It supplies precise equality tests for a completed
finite join. A strict comparison-intermediate circle loss by
itself remains insufficient; a retained strict contact, an
invariant incompatible anchor frame, or a retained strict anchor
circle loss is sufficient for the respective argument above.

## 4. Returning to the original equality family

Once a finite primary-owner join has ruled out every branch in
which either original hard owner is unavailable at q_*, the
hard-owner sharp theorem must be reapplied to the original input.
Its original-center equality statement then gives the stationary
anchors and the full original G/T frame identities, without
identifying transported intermediates with their ancestors.

For an original packing, the fixed-witness boundary pullback and
the unchanged remaining separation constraints are exactly those
used by
[the complete five-parameter equality-family proof](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md).
That proof supplies the complete weak parameter domain, its
converse, and a five-dimensional family of pairwise noncongruent
configurations. No new stationary-coordinate enclosure or
numerical equality test is needed here.

The finite primary-owner join remains an explicit prerequisite
to this last application. The contact-rigidity lemma itself is
unconditional within the already completed hard-owner class.
