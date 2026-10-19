# Independent review of the lower H tangent exclusion

**PASS.** I independently reviewed the complete theorem scope, state and
angle unions, analytic support reduction, frozen arithmetic binding, and
cyclic contradiction. No discovery optimizer is a premise of this review.

The exact squared radius is `3.915534138`; the quarter word is
`0101011` in the cyclic roles `(H,G,A,B,T,D,E)`. The excluded domain is

\[
u_H\in[-1,1/2],\qquad u_G\in[-4/5,-1/20],\qquad
u_T\in[1/20,4/5],\qquad u_E\in[-1,0].
\]

There is no D cut, additional mismatch range, width charge, or contact-owner
restriction. The proof covers both radial boundary kinds and every retained
original SAT axis. The author manuscript states the physical center-gap and
frame-span hypotheses explicitly; its later boundary-representative use
retains the existing deformation and radius interfaces.

## Independent domain reconstruction

`audit_H_lower_hand_assembly_independently.py` imports neither the proof
kernel nor a discovery routine. It uses Python fractions, its own rational
square-root mesh, alternating arctangent sums and Machin's identity to
reconstruct the state and angle unions. It verifies all 279 closed state
arcs and all 22 nonempty role/kind/sign domains. In particular, core-side
arcs end at the exact `6/7` junction and core-corner arcs begin there.

For each ordered pair of arcs, both half-angle branches and all four
original axes are enumerated before any normalization. Every one of the
45,560 required closed angle chains is covered, including shared arc and
angle endpoints. At a zero tangent or overlapping marker endpoint one
containing representation is chosen once for the vertex and retained on
both incident edges. The complete pair cover therefore permits ordinary
telescoping even when the labels on two touching arcs differ.

## Continuous inequalities and arithmetic

I checked the four displayed SAT margins against the own-frame centers
`(a,-sigma*b)` and `R_phi(A,-tau*B)`. Subtracting a nonnegative multiplier
times an actually nonnegative margin gives the stated lower bound. Axes
2 and 3 are correctly reduced by reflection and reversal, with the two
labels negated and exchanged. The source coefficients are then constant
in the angle. Endpoint minima, derivative-sign support rules and the
whole-circle lower support have the correct inequality directions on
both boundary curves. The exact radical-majorant identity and
Taylor-to-Bernstein argument are those of the previously independently
reviewed affine-arc kernel.

The frozen verifier has the approved SHA-256

```
1bd04b7b8890f7008108489da6fdf24b947e472eb4873f7523994ce4b81b85ee
```

All 48,050 fixed rows pass. The compact records contain 126,530
polynomials and 860,259 coefficient lower bounds. I independently
recounted them and checked that every premise lower bound is nonnegative
and every cost lower bound is strictly positive. The least strict cost
coefficient is `1122836547/100000000000000`. The complete arithmetic
replay is bound by SHA-256

```
de4a7e204de32faba3420dd85c57c90af1e847a36348cbd40a9c3bc9d83a4847
```

The independent script also checks the rational input, frozen source and
full-output hashes. The full coefficient report is an optional deterministic
replay artifact; the compact records and fixed input suffice to repeat this
assembly review. There is no adaptive subdivision in the accepted kernel.

## The contradiction

Every chosen feasible edge has corrected cost greater than
`8977/10000`. Both the labels and the actual frame differences telescope,
so a hypothetical cycle would give

\[
2\pi>\frac{62839}{10000}
=\frac{710}{113}+\frac{807}{1130000}>2\pi.
\]

Thus the entire closed bad domain is impossible. Under the established
G/T tangent bounds and the E reflection normalization, the conclusion is
the strict inequality `u_H>1/2`. Candidate D capture, mismatch, owners and
tilt remain separate gates. The machine-readable independent record is
`H_LOWER_AFFINE_HAND_INDEPENDENT_ASSEMBLY.json`.
