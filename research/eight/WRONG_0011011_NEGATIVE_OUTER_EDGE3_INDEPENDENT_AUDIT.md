# Independent review of the repaired whole negative outer quarter row

**PASS for the repaired 134-comparison version.** The theorem covers edge3
outer/outer signs \((-,-)\), hence reflected edge5 signs \((+,+)\), on
both complete quarter-angle halves and all four retained SAT axes.

The initial review identified an actual sign interchange between the
lower and upper halves of axis1 in Sections 3.1–3.2. The author repaired
those sections before this approval. The correct lower contact is

\[
 b=(A-.5)\cos x+(B-.5)\sin x-.5,
\]

and the correct upper contact has \(-(B+.5)\sin x\). The revised proof
does not retain the earlier incorrect angle cutoff for the whole lower
half. Its new positive target derivative and zero-source endpoint
argument cover that missing domain explicitly.

## Continuous review

I independently checked the following points against the corrected
manuscript and actual label table.

* The general derivative formulas, increasing \(T'''\), decreasing
  \(K''\) and \(K'''\), and the strong-convexity lower bounds for
  \(T'\) and \(T'-.76r\) have the correct signs. The primary-coordinate
  label \(M=-T\circ b(a)\) has derivative \(T'/r\), and its three
  lower-slope ranges and aligned upper-slope range are valid.
* The repaired lower axis1 contact cost increases in the target
  coordinate. When \(r\cos x-\sin x<0\), its lower derivative envelope
  is a concave function with positive endpoint values; the complementary
  sign is immediate. The feasible contact interval is a superlevel set
  of a concave coordinate function, and its possible first endpoints
  are exactly \(B=0\) or \(b=0\). The new split at \(x=.626\) covers
  every zero-source endpoint. The true upper-half projection gives its
  simpler direct source-coordinate cap. The other axis1/axis2 bounds
  and their alignment cases are complete.
* Both upper halves of axes3/4 have positive angular cost derivative on
  their active and clamped pieces. Their threshold domains permit
  continuation to alignment. For lower axis4, the positive threshold
  derivative, the three squared product comparisons, and the
  source-diagonal transition reduce every active case to the stated
  endpoints. I rederived the transition's \(B'=Uf\) and \(B''<0\)
  identities; composition with the increasing concave target label
  gives the required concavity.
* The active lower axis3 domain is a compact intersection of the six
  declared inequalities. Its inactive region decreases to the zero
  target boundary. In the interior, stationarity in the angle gives
  \(v=1/K'\). For \(B\ge.1\), the explicit angular second derivative
  is negative. For \(B\le.1\), the stated strongly concave function
  \(u(B)\) gives the correct bounds \(1.752<u<1.765\).
  I independently derived the decisive identity
  \[
    \frac{k}{v}=\frac{Q-u}{uq}+\frac{rz}{qv},
    \qquad q=Q+1-2u,
  \]
  by solving the two rotated projection equations. Every endpoint in
  its lower rational bound has the correct direction, including the
  negative term. This forces the transverse derivative to be positive
  and excludes all remaining interior minima.
* The six resulting boundary curves are exhaustive. The two diagonal
  transitions share the stated double-diagonal contact. The zero-target
  curve has increasing \(U\), decreasing \(V\) and decreasing positive
  \(f\) on its harmless extension. The six fixed derivative rows
  correctly clip the last physical coordinate interval at zero; their
  midpoint and mean-value bounds apply throughout the physical curve.
* On the fixed final-angle boundary, the positive last term in \(J'''\)
  is bounded with its largest numerator and smallest denominator.
  Thus \(J'''<-.36\) on the whole interval. Strong convexity on the
  first part and concavity of \(J'\) on the second part give the two
  complete endpoint/reference reductions. Their least final bound
  is strictly above \(.89777\).

No additional correction was found in the other three axes or in the
interior and boundary arguments.

## Exact arithmetic and reproducibility

`audit_wrong_0011011_negative_outer_edge3.py` runs an isolated copy of the
author's checker. All 134 strict comparisons pass, and its output is
byte-identical to the frozen arithmetic report. The script also binds
both labels directly to the shared rational table and makes twelve
independent Fraction comparisons. These include fresh radical bounds
for the two stationary-point tests, all three primary product bounds,
the repaired derivative curvature, and the final strong-convexity and
mean-value reserves.

The independent script supports both the flattened repository layout
and the local research layout. The exact source and report hashes are
recorded in `wrong_0011011_negative_outer_edge3_independent_audit.json`.
Only this corrected version is approved by this review.
