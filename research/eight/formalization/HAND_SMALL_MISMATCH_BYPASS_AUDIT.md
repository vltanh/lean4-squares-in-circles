# Small-mismatch mixed-owner audit (19 October 2026)

This note records a new exact arithmetic check, not closure of the unrestricted theorem.

At the surviving word 0101011, let (S=\sum_{i\in\{H,A,B,T,D\}}|d_i|).
The existing paper proof HAND_MIXED_PRIMARY_AT_THREE_TWO_HUNDREDTHS.md
excludes positive G1/E1 at (S\le3/200), assuming the signed role
pattern, G/T cuts, zero-owner restrictions and intended BT/DE owners.

The direct-E terminal HAND_DIRECT_E_SUPPORT_TERMINAL.md proves sharpness
under the intended seven owner sets and (S\le3/200). Thus it is logically
possible to bypass the old (3/200\to1/1000) contraction, but only after
all mixed-owner alternatives and the tilt window are proved at the larger
threshold. Neither implication follows from the existing small-mismatch
mixed-owner or positive-tilt notes.

A useful exact reserve for assessing proposed new stress arguments is
[
\frac{3027}{794375}
-\frac{97}{775}\frac3{200}
-8\left(\frac3{200}\right)^2
-\left(\frac3{200}\right)^3
=\frac{1319283}{10168000000}>0.
]
This is an arithmetic identity only. It is NOT an established universal
geometric inequality: one must still derive its stress, cusp, and
Hessian hypotheses uniformly for every original feasible owner, both
tilt signs, and shared vertex/frame coordinates.

Status: G3, G4, G5 contractions remain open. G7 last contraction may
be bypassable, but the replacement mixed-owner and tilt lemmas remain
open. No Lean compilation or CI was run.