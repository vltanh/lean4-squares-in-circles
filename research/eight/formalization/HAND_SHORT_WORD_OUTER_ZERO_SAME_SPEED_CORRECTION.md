# Correction to the favorable same-sign outer zero hand proof

Date: 21 October 2026. Applies to Section 3 of
[HAND_SHORT_WORD_OUTER_ZERO_SAME_WITHOUT_TABLES.md](HAND_SHORT_WORD_OUTER_ZERO_SAME_WITHOUT_TABLES.md).

The sentence asserting that the target-zero contact speed exceeds `.963`
at both endpoints is incorrect at the initial endpoint. With the notation
of that proof, the initial event satisfies

\[
.1072632<\phi_a<.1072633,
\qquad
v_0(\phi_a)=(a_0-1/2)\cos\phi_a+\tfrac12\sin\phi_a.
\]

The corrected bound is

\[
\boxed{\quad .9628<v_0(\phi_a)<.963.\quad}
\]

The value is approximately `.96284827`; this approximation is explanatory,
not a proof premise. The rational event bracket, positive radical brackets,
and alternating sine/cosine bounds give the two strict inequalities.
`ShortOuterZeroSameEvent.speed_corrected` contains their uncompiled Lean
proof, with the actual event speed retained in the expression enclosure.

Replace `.963` by `.9628` in that sentence. Concavity of the same speed
function and its final endpoint value then give `v_0 > .9628` on the whole
physical interval. The next step of the hand proof is unchanged because

\[
.557\cdot .9628=.5362796>.536.
\]

Consequently the bound

\[
r(b_x)<1-.536(\phi-.1073)
\]

and the definitions `D=.536h`, `M=q+h+.1073D`, as well as equation (7)
and all subsequent quadratic comparisons, are retained verbatim. No new
case subdivision, optimization, or change of the proof argument is needed.

This is a mathematical correction encountered during direct transcription,
not a completed audit or a kernel-verification report. The corresponding
Lean source remains uncompiled.
