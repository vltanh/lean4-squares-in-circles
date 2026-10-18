# Independent review of conditional candidate quarter-owner capture

**PASS.** I independently reviewed the complete continuous reduction and
reconstructed every fixed quartic by a different rational method. The
conclusion is that B→T and D→E cannot use canonical axes 1 or 2 under the
explicit hypotheses of `HAND_CANDIDATE_QUARTER_OWNER_CAPTURE.md`.

The scope is the full seven-square adjacent-pair configuration at
`q≤9789/2500`, with the displayed closed tangent cones and `S≤1/500`.
It does not assume radial-boundary membership, a preselected mixed owner,
or contact equality. The H and D tangent bounds and the bound on S are
explicit prerequisites, not consequences of the quartic table.

## 1. Actual inequalities and their nominal limits

I rederived the canonical signs `(+,-,+,-,+,-,-)` and all four SAT
projections from the own-frame centers `(a,-sigma*b)`. The three
zero-quarter edges reduce nominally to sums of the two unsigned transverse
coordinates. Their only allowed actual axes are 1 and 3 by the earlier
mismatch theorem. The two aligned-quarter edges reduce as follows:

| Edge | Axes 1 and 2 | Axes 3 and 4 |
|---|---|---|
| B→T | `a_T-b_B` | `a_B-b_T` |
| D→E | `a_E-b_D` | `a_D+b_E` |

The two mixed-edge projection tables in the manuscript also have the
correct signs. G→A has exact relative angle `pi/2-t`. The telescoping
identity gives E→H the relative angle
`pi/2+t-(d_0+d_2+d_3+d_4+d_5)`, so its perturbation has magnitude at most S.

Every center has norm less than `3/2`: the square's radius-`1/2` incircle
lies inside its containing disk of radius less than 2. Changing one
relative angle in a SAT projection rotates only one center, so the
projection error is at most `3|d|/2`. The width function is globally
`1/2`-Lipschitz, including its quadrant junctions. Thus each aligned
nominal inequality has right side at least `997/1000`, G→A retains its
exact width, and E→H has width reduced by at most `1/250`. These are
necessary inequalities, so relaxing the shared total error into the five
individual estimates is valid.

If either aligned-quarter edge has a forbidden feasible actual axis,
choose it on that edge and any feasible axis on each other edge. The
nominal equivalences reduce this choice to exactly 48 patterns:
four G→A choices, four E→H choices, and the three quarter-owner pairs
`(1,1)`, `(1,3)`, `(3,1)`. This includes simultaneous feasible axes and
every owner tie; no mixed owner has been silently fixed.

## 2. The circle dual and quartic representation

I checked all 35 cone inequalities against the stated tangent bounds and
the weak consequences `447/800≤a≤283/200`, `b≤9/10` of core avoidance and
containment. With nonnegative multipliers, their sum with the seven
nominal SAT inequalities gives `C·x≥B`. Translation by `(1/2,1/2)` in
each coordinate pair therefore gives the lower bound
`B+(1/2)sum(C_j)` for the sum of seven scalar products.

For every positive rational mu, completing the exact square gives

\[
C_i\cdot v_i\le\mu_i|v_i|^2+\frac{|C_i|^2}{4\mu_i}.
\]

Using `|v_i|²≤Q` proves the manuscript's upper bound. All inequality
directions are correct; no dual optimality, numerical stationarity, or
equality condition is needed. This argument applies to arbitrary centers
and every independent core/outer boundary assignment.

The half-angle substitution makes every component of `(1+z²)C` and
`(1+z²)L` quadratic. Multiplication by the positive `(1+z²)²` consequently
gives an exact quartic. The range `|t|<.7` is covered by `|z|≤3/8`, using
the displayed strict rational arctangent bound. All 30 closed cells are
within `|z|<1`, so cos(t) is positive and the manuscript's width formula
is valid throughout. Zero is a shared cell endpoint, where both sign
formulas agree.

## 3. Independent arithmetic and complete coverage

`audit_candidate_quarter_owners_independently.py` does not import the
author's polynomial or SAT routines. It independently constructs the
explicit nominal projection vectors above and the eight mixed-edge
vectors. It evaluates the exact circle-dual difference at five rational
half-angle points in each cell, then inverts a fixed rational Bernstein
evaluation matrix. This differs from the author's power-basis expansion
and direct coefficient conversion. A sixth rational point checks the
quartic identity separately for every row.

All 1,440 quartics and all 7,200 displayed coefficient bounds pass.
The smallest printed positive coefficient is
`1970267266/1000000000000`. The complete Cartesian product of 48 patterns
and 30 closed cells is present exactly once, without omitted endpoints.
The author checker also replays byte-identically in an isolated directory.

The hash-bound results are in
`candidate_quarter_owner_capture_independent_audit.json`. The accepted
input has SHA-256

```
bcafd38fc19e78e0352d436b1f0c11d931a4a7436d2b9d320a2c3eae2edb52d2
```

Every excluded pattern has strict reserve. Thus the theorem creates no
additional equality case and fully closes its two claimed owner sets.
The two mixed owners, the common tilt and the prerequisite bound on S
remain separate candidate gates.
