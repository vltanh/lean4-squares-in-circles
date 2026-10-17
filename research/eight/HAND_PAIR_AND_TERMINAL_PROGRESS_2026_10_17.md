# Hand-proof progress: global pair lemmas and the larger terminal

This checkpoint records completed analytic lemmas. It does **not** close
the unrestricted hand proof: complete frame concentration, the remaining
wrong-word exclusions, and candidate-word capture are still required.
The completed unrestricted computer-assisted proof remains valid and
separate.

## 1. The final sharp inequality now permits S ≤ 1/500

HAND_EXACT_CENTER_SQUARE_COMPLETION.md proves, for every allowed one of
the 32 separator-owner choices and the full projected-slider rectangle,

\[
 r\ge q_*+\frac{3\mu_H}{8}(t-t_*)^2+
 \sum_{i=A,B,D,E,H}\mu_i
 \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +\frac9{100000}S,\qquad S\le\frac1{500}.
\]

The actual anchored centers are unrestricted. The comparison sliders
are selected from the actual transverse projections, as in the earlier
broad terminal theorem. The completed squares are exact.

Completing these five squares before estimating angle errors reduces
the former nonlinear loss from \(130S^2\) to
\[
 C_2S^2+C_3S^3,\qquad C_2<9.28,\quad C_3<1.5.
\]
The already displayed owner reserve is \(1869/100000\). For
\(S\le1/500\), the total loss is below \(9.3S^2\), leaving the
strict linear term in the theorem.

Two independent geometric reviews rederived every force coefficient,
all eight owner-dependent support/offset rows, the mixed-edge cosine
cancellation, and both projected-slider remainder bounds. The exact
rational coefficient replay passes. This is a twenty-fold enlargement
of the earlier sufficient range \(S\le1/10000\).

The existing unrestricted computer-assisted assembly can still use its
earlier stronger capture and earlier terminal theorem. This enlargement
provides an easier target for hand global capture.

## 2. Two difficult frame-pair strips now have hand bounds

| Completed lemma | Entire proved domain | Method and strict bound |
|---|---|---|
| HIGH_LOW_NONALIGNED_SHORT_HAND_PROOF.md, with HIGH_LOW_NONALIGNED_SUPPORT_FORMULA.md | High-positive to low-positive, source secondary axis, \(2/25\le\phi\le3/10\) | Two explicit quartic radical upper bounds and one degree-ten polynomial. Three positive Bernstein rows, 31 coefficients, prove cost \(>.8833\). |
| CORE_MID_NONALIGNED_HAND_PROOF.md | Negative mid source to negative core target, source negative primary axis, \(1\le\phi\le29/25\), core slope \(p_C\le-2\) | A multiplier cancels the core tangent coordinate. Four fixed curvature intervals and one rational point give cost \(>.9005\). |

The high/low proof was independently checked algebraically and
arithmetically; its three displayed rows were reproduced exactly.
The mid/core separator signs, support reduction, derivative identities,
monotonic bounds and convexity conclusion were independently reviewed.
Its explicit core-slope hypothesis must be respected if labels change.

SAT_PROJECTION_CLIPPING_HAND_LEMMA.md proves exact necessary projection
cuts and the finite candidate formulas for clipped circle supports.
It is a reduction lemma, not a universal bound for a fitted table.
LIFTED_STATE_POTENTIAL_TELESCOPING.md explains why consistent vertex
lifts suffice for cyclic cancellation, without identifying the potential
values at different diagonal representations.

## 3. Four whole regimes of a simpler quarter-increment table

Conditional on frame concentration, the seven-quarter-word theorem
leaves seven cyclic words. Four of the six wrong words have one
increment equal to two. A proposed common marker table aims to exclude
all four using

\[
 \gamma_0=391/400,\qquad \gamma_1=157/200,\qquad
 \gamma_2=163/200.
\]

Each such word has four zero increments, two unit increments, and one
double increment. If **all** branches of the table are proved,
telescoping would give the contradiction
\[
 2\pi\ge4\gamma_0+2\gamma_1+\gamma_2=6.295>2\pi.
\]
This implication is conditional: the universal table is not yet
asserted in this checkpoint.

The following entire named regimes are now proved:

| Hand note | Outer-state signs and source axis | Frame domain | Proved lower cost |
|---|---|---|---:|
| QUARTER_ZERO_OUTER_POSITIVE_HAND_PROOF.md | Positive/positive, secondary | \([-.7,.7]\) | \(>.9783839>.9775\) |
| QUARTER_ONE_OUTER_OPPOSITE_HAND_PROOF.md | Negative/positive, negative primary | \([\pi/2-.7,\pi/2+.7]\) | \(>.7863>.785\) |
| QUARTER_ONE_OUTER_SAME_HAND_PROOF.md | Positive/positive, secondary | \([\pi/2-.7,\pi/2+.7]\) | \(>.787729>.785\) |
| JUMP_TWO_OUTER_OPPOSITE_HAND_PROOF.md | Negative/positive, negative primary | \([\pi-.7,\pi+.7]\) | \(>.815887>.815\) |

Every theorem treats all states on its two full outer arcs, without
assuming a support minimizer's location. Correct physical reflections
and reversals give the corresponding image-axis regimes.

The recurring circle-norm identity is
\[
 N''+\frac N4=\frac{(p^2+q^2-\lambda^2)^2}{4N^3}\ge0.
\]
Elementary norm bounds then prove concavity, leaving two or three
rational endpoint comparisons. The opposite-sign unit-increment case
also uses a uniform quarter-turn estimate in its small-angle region.
Every displayed endpoint comparison has an exact rational replay.

## 4. Remaining gates

1. **Complete frame concentration by hand.** Existing strip lemmas
   cover only named parts of the full four-type pair theorem.
2. **Complete the wrong-word exclusions.** The three-row table still
   needs its other state-kind, sign and axis regimes. Two wrong words
   without a double increment need separate arguments.
3. **Capture or directly prove the candidate word.** Derive all
   separator-owner, tilt, slider and mismatch hypotheses of the sharp
   terminal, or replace them by a larger-domain sharp inequality.
4. **Audit the unrestricted hand assembly.** Check all boundaries,
   ties, lifts and radius transfers after the hand replacements.

Numerical fits and failed solver attempts remain discovery work.
They are not counted as hand lemmas or used as premises.
