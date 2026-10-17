# Gate 3B.2 / M5: two exhaustive folded orientation types

2026-10-13. Continuation from `GATE3B_FOUR_FRAME_MAJORITY_BRANCHES.md`.
This closes the angular-order component of the M5 child, not its actual
packing/owner classification and not the unrestricted radius theorem.

## 1. Use actual maximality, not just the relaxed 5/3 chamber

Write T=pi/2 for the square-orientation circle and h=T/2=pi/4.
M5 here means that the MAXIMUM number of frames in a closed clockwise
h-window is exactly five. Multiplicities count. This is stronger than
merely labeling five frames L and three H in a closed chamber.

If theta_0<=...<=theta_7<theta_0+T are circularly ordered lifted frames,
extend theta_{i+8}=theta_i+T. The following exact condition is equivalent
to maximum closed-window count at most five:

    theta_{i+5}-theta_i > h     for all i=0,...,7.          (M)

Indeed, a violation places six consecutive labels in one closed window.
Conversely, any six labels in a closed window include six consecutive
labels whose span is at most h. The majority theorem supplies maximum
at least five, so (M) characterizes M5 itself.

All eight inequalities in (M) are strict. They may not be weakened when
using the maximum-five hypothesis. The folded-type closures below are
covering sets, not a replacement for (M).

## 2. Generic frames give only eight words

First suppose all frames are distinct and no two differ by h modulo T.
Choose a maximizing anchor at zero. Its window contains five L frames
in [0,h), including zero, and there are three H frames in (h,T).
Fold H back by h and sort all eight folded locations in [0,h).
Mark each location with its original group L or H.

As the h-window's starting point moves from 0-minus to h-minus, an L event
removes a frame and an H event adds one. At non-event points the window
and its complementary window partition the eight labels. Thus maximality
five forces occupancy between three and five. It starts at five and ends
at three, giving a length-eight walk with five downsteps L, three upsteps H,
and all heights in {3,4,5}.

There are exactly the following eight words:

| Word | Anchor event for the representative below (1-based) | Representative |
|---|---:|---|
| LHLHLHLL | 1 | I |
| LHLHLLHL | 7 | I |
| LHLLHHLL | 1 | II |
| LHLLHLHL | 5 | I |
| LLHHLHLL | 5 | II |
| LLHHLLHL | 7 | II |
| LLHLHHLL | 3 | II |
| LLHLHLHL | 3 | I |

This enumeration has a short complete proof: after every odd step the
height is necessarily four; after steps 2,4,6 it may independently be
three or five; after step 8 it must be three. These three binary choices
give exactly the eight displayed walks. It is not a sampled classification.

## 3. Legitimate re-anchoring leaves two types

Let C exchange L and H. Re-anchor at folded event k. The new folded word
before accounting for the anchor's group is

    w[k:] + C(w[:k]).

If the old event k was H, complement this entire word as well. This rule
follows directly from subtracting its folded position: events crossing
zero wrap by h, which switches their orientation half; an H anchor also
subtracts an extra h. It is a common rotation and relabeling of the actual
packing, not an independent change of frames.

The table gives an explicit re-anchoring for every word. Each selected
anchor has five L labels afterward, so is still maximizing. The two
representatives are

    M5-I:  L H L H L H L L,
    M5-II: L H L L H H L L.                              (F)

No reflection is needed for this reduction.

If x_0<...<x_7<h are folded positions and the initial anchor is x_0=0,
the original frames of an L event and an H event are respectively

    theta=x_r,       theta=h+x_r.

Thus (F) specifies relative order between EVERY L angle and EVERY folded
H angle. In particular it fixes on which side of h each of the fifteen
mixed relative frame differences lies. It retains considerably more
information than an arbitrary 5/3 grouping.

## 4. Closed, boundary-safe cover for all M5 frames

Every genuine M5 frame multiset, including coincident and antipodal frames,
has a representative in one of the two closed folded-type regions
obtained by replacing x_0<...<x_7<h with

    0=x_0<=...<=x_7<=h.                                  (CF)

Proof: (M) gives a strictly positive reserve for every six-frame cyclic
span. Therefore a sufficiently small perturbation of the ORIENTATIONS
alone preserves maximum at most five. Avoiding the finitely many
coincidence and antipodality conditions makes the perturbed frames generic;
the majority theorem keeps their maximum exactly five.

Apply the generic reduction to a sequence of these perturbations. There
are finitely many possible anchor labels, relabelings, and two types.
Pass to a subsequence on which those discrete choices are constant.
Their normalized frames converge, and their folded inequalities give (CF).
The chosen anchor has maximum five in the limit: it still has at least
five in its closed window, while the original configuration satisfies (M).

This argument does NOT claim that perturbing frames preserves a packing.
The perturbations are used only to prove a closed statement about frame
orders. The final common rotation and relabeling apply to the ORIGINAL
centers and original squares. Consequently no overlap-free deformation
or radius slack is being assumed.

The closures can contain non-M5 frames. Keep (M) wherever maximality is
used; any exclusion proved on an entire closure is stronger and is safe.

## 5. Polynomial tests in the Gate 1 chart

For ordered original half-tangents a<=b define

    A=1+ab, B=b-a,
    K(a,b)=A^2-B^2-2AB.

The exact Gate 1 formulas give

    sign K(a,b)=sign(cos(theta_b-theta_a)-sin(theta_b-theta_a)).

For an L frame alpha and an H frame beta, their folded comparison is

    alpha <= beta-h   iff   K(z_alpha,z_beta)<=0,
    beta-h <= alpha   iff   K(z_alpha,z_beta)>=0.

Thus the mixed folded-order conditions are polynomial weak inequalities
with integer coefficients, including exact h-ties. Within-group orders
are the ordinary z orders. No decimal approximation to pi/4 is required.
For (M), use the same sign test on a nonwrapping span; for a wrapping
span T-delta, the cosine-minus-sine sign is the negative of that for delta.
The corresponding sign remains STRICT for (M).

## 6. The M5 joint geometry remains attached

For each of M5-I and M5-II retain all of the following:

* the original eight squares and all 32 actual vertex constraints;
* all 28 actual pairwise SAT disjunctions and canonical-owner conditions;
* the ten L-L, three H-H, and fifteen mixed pairs, with their coherent
  Gate 3A projection-order classes;
* the common two-dimensional center realization, not four independent
  order assignments;
* (M) when an argument uses maximum five rather than its closed cover.

This gives a proved parent-to-two-children covering implication for the
ENTIRE M5 branch. Neither child has been excluded. Their actual joint
center/owner geometry is the next unresolved obligation in Gate 3B.2.
Do not advance to M6 or call the whole gate passed on the basis of (F).

## 7. Executed arithmetic regression

`verify_m5_folded_order_cover.py` checks all eight bounded walks and every
re-anchoring in the table. It was executed on 1,616 exact generic
maximizing-anchor instances obtained from rational direction vectors;
all eight words occurred. A separate configuration with four exact
antipodal orientation pairs has maximum five and is retained.
These are implementation regressions. The continuous covering theorem,
including ties, is proved in Sections 1--4.
