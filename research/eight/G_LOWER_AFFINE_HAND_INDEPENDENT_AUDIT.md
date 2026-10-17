# Independent assembly audit of the lower G exclusion

**PASS.** The fixed rational input excludes the bad domain
\(u_G\in[-1,-4/5]\), with \(u_E\in[-1,0]\), at
\(Q=3.915534138\) for the physical candidate word
\((0,1,0,1,0,1,1)\). The previously established center-order,
\(7/10\) frame-spread, and four-axis scope hypotheses are retained.

The kernel source has SHA-256
`1bd04b7b8890f7008108489da6fdf24b947e472eb4873f7523994ce4b81b85ee`.
It is exactly the source independently reviewed in
`AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md`; its geometry, support directions,
radical majorant, pointwise polynomial argument and integer arithmetic
require no new proof for this different rational table.

I checked the table's complete scope independently in
`audit_G_lower_hand_assembly_independently.py`. This script does not import
the JavaScript verifier or a discovery program. It recomputes endpoint
arctangents from exact rational half-angle and alternating-series bounds
with its own square-root mesh, and checks all interval unions.

The audit establishes:

* The exact input cuts are `G[-1,-4/5]` and `E[-1,0]`; the other five
  role tangents range over `[-1,1]`.
* All 114 arcs have rational endpoints and affine coefficients. Every
  core arc is split at the exact side/corner junction \(6/7\).
* All 24 nonempty role/kind/sign domains are covered by closed arcs.
  Both possible radial kinds are included independently at every role.
* Every one of the 8,240 nonempty original ordered-arc/axis/angle-half
  domains is covered by the fixed row intervals. All four retained SAT
  axes are checked, before any reflection/reversal normalization.
* Every multiplier is nonnegative, every angle range lies in \([0,.7]\),
  every quarter equals the corresponding declared word entry, and no
  circle support is used on a straight core side. No row weakens its
  declared edge bound.
* The compact report records 9,087 successful rows, 25,221 polynomials,
  and 184,288 nonnegative coefficient lower bounds. Every cost bound is
  strict; the least printed one is
  \(309500239/10^{14}>0\). The report's rational-input and source hashes
  match the actual frozen files. The full arithmetic output, when present,
  also matches its recorded SHA-256.

Choose one containing closed arc at each state once, and use its label on
both incident edges. The table covers every adjacent pair of such choices,
so possible discontinuities at shared arc endpoints do not affect the
telescoping sum. Its seven edge bounds give

\[
 \sum_i(\phi_i+L_i-L_{i+1})>
 7\frac{8977}{10000}=\frac{62839}{10000}
 =\frac{710}{113}+\frac{807}{1130000}>2\pi.
\]

For a physical boundary cycle the left side equals \(2\pi\), a
contradiction. Hence the full lower G bad domain is excluded. The input
hash is

```
619cf1f7f11aa9f82dd3a355df9a8d042f1d69403f25c53aaf1ac2bbe1dbf776
```

The independent exact output is
`G_LOWER_AFFINE_HAND_INDEPENDENT_ASSEMBLY.json`. No claim about the
remaining candidate mismatch, owner or tilt capture follows merely from
this G-domain exclusion.
