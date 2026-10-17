# Independent audit: edge 2 negative core to negative outer

**Result: PASS.** The stated whole-angle theorem is valid on both core
boundary pieces, for all four retained axes, at \(Q=9789/2500\).
Reflected reversal supplies its edge-6 partner.

I independently rederived the signed cost and all four SAT projections from
the own-frame centre convention \((a,+b),(A,+B)\). The source label agrees
with role 2 negative (the reflection of role 0 positive), and the target
polynomial agrees with role 3 negative in the exact 0011011 role JSON.

The derivative formula for \(T\), the lower bound on \(T'''\), and the
global bound \(.609<T'<1.069\) follow from the displayed strong-convexity
argument. The direct late-angle inequality applies to all axes. Below that
cutoff, I checked each of the following continuous reductions:

- Axis 1: substitution of the core-coordinate upper bound has the correct
  sign, and the resulting function increases in the outer coordinate on
  its complete arc. The one-variable curvature bound and square completion
  are valid.
- Axis 2: the use of \(a\ge d_c\) has the correct direction. The formula
  for \(F_2-F_1\) is exact, and its brace is positive by the stated
  two-dimensional Cauchy bound.
- Axis 3: both the small-angle bound on \(b\) and the later increasing
  scalar follow from the same necessary inequality
  \(B\ge B_0+b\cos\phi\). Both intervals include their common endpoint.
- Axis 4: replacing \(A\) by \(B\) uses \(\cos\phi>0\), replacing \(B\) by
  \(d\) uses \(\sin\phi>\cos\phi\), and the later lower bound \(B\ge5/12\)
  follows directly from the original separator. No side-only core premise
  is introduced.

I read the exact-arithmetic implementation, including the rational interval
operations, square-root bounds, alternating Taylor sums, and Machin enclosure.
A fresh execution passes all 38 fixed strict comparisons and is byte-identical
to the saved arithmetic JSON. No optimization, domain search, or unstated
contact-selection premise enters the proof.

## Bound artifacts

| Artifact | SHA-256 |
|---|---|
| WRONG_0011011_EDGE2_NEGATIVE_CORE_TO_OUTER_HAND_PROOF.md | 036854ca26f62693803c2f8abb5dec55b39a06c7ed45719ff30ee30a128c697c |
| verify_wrong_0011011_edge2_negative_core_to_outer.js | 09a8fbc2842a7203de0ec2f391bd0851cdfa82abb464b4f725e9127ab5430b7c |
| wrong_0011011_edge2_negative_core_to_outer_arithmetic.json | 8ae3d6a36fcd4e58d96705d5bf8b2136feec6654d1165250a1fd2d4d980ae2b7 |

This audit certifies only the whole family named above; it makes no inference
about the other quarter-one role/sign combinations.

