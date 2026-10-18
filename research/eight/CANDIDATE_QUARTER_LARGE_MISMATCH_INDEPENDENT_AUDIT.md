# Independent review: quarter owners at total mismatch at most 3/200

**PASS.** This review covers the first conclusion of
`HAND_CANDIDATE_MIXED_OWNERS_AND_TILT.md`: under its stated tangent cones,
circle ceiling 9789/2500, and total aligned mismatch at most 3/200, every
retained separator on B→T and D→E has original axis 3 or 4. It does not
claim a new global mismatch bound or review the later mixed-owner and
tilt conclusions.

## Continuous argument

I independently checked the coordinate convention, the four original SAT
projections, the five aligned nominal rows, the exact G→A angle, and the
E→H angle error. Each rotating center has norm less than 3/2. Therefore
the aligned projection loss is at most 3S/2; the E→H projection and width
loss together are at most 2S. These are necessary inequalities for every
configuration in the stated domain. They require neither radial-boundary
membership nor contact equality.

The additional primary-coordinate bounds for G and T are valid for all
centers satisfying their tangent cones. If a<7/12 and b≤4a/5, then
b<7/15<1/2, and avoidance of the open radius-1/12 central disk is
impossible. Conversely, b≥a/20 and containment exclude a≥349/250 by
the single strict comparison

\[
(349/250+1/2)^2+(349/5000+1/2)^2>9789/2500.
\]

Thus replacing the two G/T primary bounds in the 35 cone inequalities
is legitimate. All other cone rows agree with the previously audited
quarter-owner argument.

For each choice of feasible original separators, their nominal classes
give one of the displayed owner patterns. A forbidden B→T or D→E
separator produces one of exactly 48 bad patterns. The real-angle
normalization and sign conventions match the manuscript's mixed-row
table. Every possible mixed owner remains in the enumeration; desired
mixed owners are not assumed.

I rederived the positive circle dual directly. Adding nonnegative
separating and cone inequalities gives C·x≥B. With
y_i=(a_i+1/2,b_i+1/2), completing a square gives

\[
B+\tfrac12\sum C_j
\le \sum_i C_i\cdot y_i
\le Q\sum_i\mu_i+\sum_i\frac{|C_i|^2}{4\mu_i},
\qquad \mu_i>0.
\]

No sign restriction on C or optimality of the chosen weights is needed.
The strict reverse excludes the whole center domain. Substitution
z=tan(t/2) and multiplication by (1+z²)² yields the claimed quartic on
each fixed-sign interval. The enclosing range [-3/8,3/8] follows from
atan(3/8)>3/8−(3/8)³/3>7/20.

## Independent exact reconstruction

`audit_candidate_quarter_large_mismatch_independently.py` reconstructs
the nominal matrices and strengthened cone rows without importing any
author function. It evaluates each rational circle-dual polynomial at
five rational points and inverts the fixed Bernstein evaluation matrix.
This differs from the author's power expansion and direct conversion.
A sixth rational point checks every reconstructed quartic identity.

The independent replay verifies:

- exactly 48 bad owner patterns;
- a complete, gap-free closed interval union [-3/8,3/8] for every pattern;
- all 1,545 fixed quartics and all 7,725 printed positive coefficient bounds;
- all 1,545 additional identity points;
- positive circle weights and nonnegative SAT/cone weights;
- the exact minimum printed bound 2539981/10^12;
- a byte-identical isolated replay of the author's quarter-only checker.

The earlier 45-pattern intermediate was not accepted. This review binds
the complete 48-pattern data file with SHA-256
`a4a86562adf04d833a48eafcfd6a2b98fb344d7b32926d1ce5b0926afd70e1ee`.
All four author-file hashes and the independent arithmetic results are
recorded in
`candidate_quarter_owner_large_mismatch_independent_audit.json`.

Reproduce the review with:

```text
python audit_candidate_quarter_large_mismatch_independently.py
```

The script supports both its working layout and the flattened
`research/eight` repository layout. The proof excludes forbidden feasible
axes themselves, so it remains valid at separator ties and can be used
with the established selected-separator pullback.
