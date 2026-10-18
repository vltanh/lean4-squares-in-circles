# Independent review: candidate tilt at mismatch at most 1/1000

**Result: PASS.** This review covers the continuous necessary inequalities,
the common-weight 21-alternative disjunction, its complete domain cover,
and an independent reconstruction of all 1,239 rational quartics in
`HAND_CANDIDATE_TILT_FROM_SIGNED_ERROR_VERTICES.md`.

## Continuous geometry and the disjunction

I differentiated the four actual SAT projections independently. The
aligned derivative coordinates are, respectively,

| Edge | Owners | Derivative coordinates |
|---|---|---|
| H→G | 1, 3 | \(a_G,a_H\) |
| A→B | 1, 3 | \(a_B,a_A\) |
| B→T | 3, 4 | \(b_B,a_T\) |
| T→D | 1, 3 | \(a_D,a_T\) |
| D→E | 3, 4 | \(b_D,a_E\) |

Their nominal projections agree within each pair of owners. For E→H,
whose owner is 2, the nominal projection and derivative are
\(a_H+a_E\sin t-b_E\cos t\) and
\(a_E\cos t+b_E\sin t\). G→A has its exact angle \(\pi/2-t\);
E→H has angle \(\pi/2+t-\Delta\), where
\(\Delta=\sum_{i\in I}d_i\).

The center norm bound gives \(|F''|<3/2\). Combining its upper Taylor
bound with the lower sine/cosine width bound gives the aligned loss
\((1+\varepsilon/12)d_i^2\), safely below
\((1001/1000)d_i^2\). The second-order constant is valid on the stated
closed mismatch ball.

The width function has smooth second derivative at least
\(-\sqrt2/2>-3/4\), and its derivative jumps upward at every quarter
cusp. Therefore \(W(\phi)+3\phi^2/8\) is globally convex.
Both one-sided cusp slopes are valid subgradients. Its supporting-line
bound, together with the projection Taylor bound, gives the claimed
E→H loss \(9\Delta^2/8\), including an error crossing zero tilt.
The signs in the linear \(\Delta\) term check directly.

For one fixed nonnegative vector \(\lambda\), summing the actual
inequalities yields the author's equation (15), with
\(c_j=\lambda_j f'_j-\lambda_6f'_6+\lambda_6w'_6\).
The exact maximum over \(\sum|d_j|\le\varepsilon\) is
\(\varepsilon\max(0,\max_j(|c_j|-\lambda_j/2))\).
Thus zero, or one signed extreme coordinate, gives a necessary
alternative. Only that coordinate's aligned owner affects its linear
term. This proves the exact count \(1+5\cdot2\cdot2=21\), covering
all 32 aligned-owner assignments. No separate weight vector is selected
after deciding which error alternative applies.

I rederived both the force and right side of equation (19). Adding
nonnegative valid cone rows then completing the seven translated circle
squares gives equation (21) with the displayed signs. Allowing separate
cone and positive circle weights for each alternative is valid after
the common-weight disjunction. Multiplication by \((1+z^2)^2\),
\(z=\tan(t/2)\), produces a quartic. These steps use arbitrary centers
under the stated inequalities, without a radial-boundary equality or
contact equality.

## Independent arithmetic and complete coverage

`audit_candidate_signed_error_tilt_independently.py` does not import an
author function. It directly assembles the seven explicit nominal
forces, each signed-error alternative, all selected cone rows and the
circle completion at five rational half-angle points. It then inverts
a fixed Bernstein evaluation matrix. This is different from the author's
power-coefficient expansion and conversion. An additional sixth point
checks each independently assembled quartic identity.

All of the following checks pass:

- 59 closed cells, with exactly one shared seven-entry nonnegative
  \(\lambda\) vector in each cell;
- all 21 required alternatives once per cell, with no vertex-specific
  edge-weight vector;
- 1,239 independently reconstructed quartics and 6,195 strictly positive
  displayed coefficient bounds;
- 1,239 additional rational identity points;
- the exact complete union
  \([-3/8,1001/20000]\cup[2/25,3/8]\), including every endpoint;
- all rational Taylor constants, primary-cone implications and final
  arctangent comparisons;
- an isolated replay of the author checker, byte-identical to its
  recorded arithmetic report.

The smallest displayed coefficient lower bound is
\(40703/500000000000>0\). Consequently the two tilt tails are impossible,
and \(1/10<t<4/25\) follows on the stated scope.

## Bound sources and reproducibility

The independently reconstructed results and complete SHA bindings are in
`candidate_signed_error_tilt_independent_audit.json`. The reviewed inputs
are:

| Input | SHA-256 |
|---|---|
| Manuscript | `2eed8e78c79cb07d3533f50bcc308b6701faf06504c89a7dea240a25358fb491` |
| Author checker | `05c4ed1b89ccaa16d2f44f4b0ad26408376fb921a5399fc647a1b1f245403d2f` |
| Rational table | `bc5305ef2b0b00e62b89259da64d8eedadfa93c71fcf1269110b29aeaae28bc1` |
| Author arithmetic | `0a48e82cdb52296c2b44f45bad883800f6cdf6b3249111e2b79cf52d734c8c6d` |

The independent script supports both the scratch layout and flattened
`research/eight` layout. Run it directly with Python to reproduce the
independent result. This review proves the conditional tilt gate; the
preceding owner theorem and mismatch bound remain its explicit premises.
