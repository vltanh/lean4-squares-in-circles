# Independent review: whole edge3 C+ to O+ quarter family

**PASS.** I independently reviewed
`WRONG_0011011_EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md`,
its complete four-axis/core-piece coverage, and all continuous reductions.
The source and target labels agree exactly with role3 C+ and role4 O+ in
the shared rational table. A fresh 166-comparison arithmetic replay is
byte-identical to the frozen report. No correction is needed.

The following are the substantive independent checks.

1. The derivatives of the outer label \(J\) have the stated signs.
   Increasing \(J''\), the two nearby derivative comparisons, and convexity
   of \(J'\) justify its positive lower bound and endpoint upper bound.
   The late-angle estimate covers every axis. On the remaining interval,
   the core norm excludes axis3, and the signed projection bound excludes
   axis4 on both angle halves.
2. On the lower axis1 and lower side-axis2 contacts, the source coordinate
   increases with target coordinate. The third derivative inequalities
   make the derivative of each contact cost concave. Once its left
   derivative is positive, no interior minimum can occur. The separate
   zero-coordinate cases correctly handle the clamp at source coordinate
   zero; discarding an upper source-coordinate limit is a relaxation.
3. I rederived the axis1 zero-contact formulas, including
   \(B_z'=Uf\), \(U'=-Vf\), and the numerator of \(f'\). All quantities
   used to choose interval endpoints have the required monotonicity.
   In particular, the numerator of \(f'\) increases and its positive
   denominator decreases on the stated range. The small-angle derivative
   comparison and the later negative second derivative prove the claimed
   endpoint reductions. The diagonal scalar's increasing second
   derivative and negative final first derivative give the correct
   decreasing direction.
4. Above the quarter turn, both least feasible source coordinates are
   side or zero states. Their target zero endpoints lie between \(B_1\)
   and the outer diagonal, and both contact costs are concave beyond that
   zero. The derivative bounds for the zero and diagonal endpoints are
   positive. The primary zero's upper-domain assertion follows, for
   example, from
   \(.5+.5(.99)-.11/12>.9>d\); thus it has no hidden out-of-arc case.
5. For lower side-axis2, the upper tangent to \(J\) is valid on the full
   target interval: the first part is concave, and after \(.5\) the convex
   derivative starts below the tangent slope, preventing an interior
   maximum above the two endpoint values. I rederived the circular
   support formula and the direction of both squaring substitutions.
   The negative tail allowance yields an actual lower polynomial.
   The accompanying independent Fraction script reconstructs every one
   of its nine power and nine Bernstein coefficients using triangular
   basis solving; all printed lower bounds pass.
6. The lower primary zero-contact curvature identity is
   \[
   \frac{B_z''}{(B_z')^2}=
       \frac{mV}{Uv^2}-\frac{Q}{U^2V}.
   \]
   Its lower bound and the increasing \(J''/J'\) bound have the correct
   directions and imply strict concavity of the zero-source cost.
7. On the remaining core-corner rectangle, decreasing-cost movements
   reach an actual primary contact before the core side endpoint. The
   extension of the target circle past its diagonal is an explicit
   enlargement containing all actual contacts. Both \(J'\) and \(J''\)
   remain positive there. Differentiation gives
   \[
   B''=\frac{|a''|\cos\phi}{r}
       -\frac{r'(\sin\phi+t\cos\phi)^2}{r^3}>0.
   \]
   The positive coefficient is justified by the displayed bounds:
   \((B+.5)^2(A+.5)>1.016^2(1.34)>1.3\). Cauchy's inequality then gives
   the strict sign. Thus the cost is concave on the entire enlarged
   source-corner interval, and its two endpoints suffice. Monotonicity of
   the target coordinate proves the thirty fixed angle-endpoint bounds.

The coverage ledger is complete. Late angles are universal; axes3 and4
are absent earlier; the lower axis1 proof includes every core source;
the upper proof includes both retained axes and both core pieces; and
the lower axis2 proof treats side and corner separately. Every shared
angle or coordinate endpoint is retained.

The resulting whole pair inequality is strict with target
\(\gamma=.89765\). This component is ready for the whole0011011
assembly; it makes no claim about the other still open pair components.

The hash-bound arithmetic audit is
`wrong_0011011_positive_core_outer_edge3_independent_audit.json`, produced
by `audit_wrong_0011011_positive_core_outer_edge3.py`.
