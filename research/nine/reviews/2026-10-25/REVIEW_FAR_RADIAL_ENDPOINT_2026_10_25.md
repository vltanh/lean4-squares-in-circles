# Independent saved-source review: far-radial endpoint bound

Reviewed source:
`ABC_UPPER_LEFT_FAR_RADIAL_ENDPOINT_BOUND.md`

SHA256 of the reviewed complete text:
`76456f210cb3e05c7f77c3d0df9c539beb4af84b3954f64df3590982343ff99f`

Reviewer: abc_remaining, independently of the endpoint source's author.

**Verdict: PASS.** The complete scalar endpoint theorem is valid on its
stated enlarged interval, and its conditional transfer to the original
far-radial prefix has exactly the stated scope.

The full source was read. I independently rederived the rational endpoint
formula for L, the identity a_end=d+1-A, and the circle identity for
b_end squared. I then differentiated A directly, obtaining exactly the
source's logarithmic derivative (3). All factors cleared in that formula
are positive on [9/10,11/10]. The negative coefficient in the global
comparison (6) is handled in the correct direction, and the three uniform
bounds used in (7) hold on the entire enlarged interval.

The monotonic decrease of A and A(9/10)<1/3 give a_end>3/2 without an
endpoint assumption about any physical square. The subsequent derivative
of b_end squared is exactly 2A[1+a_end A'/A], hence is strictly negative
by the established -A'/A>2/3. The rational endpoint at d=11/10 has the
strict stated reserve above 81/64.

As a separate exact arithmetic check, I built univariate polynomial
operations with standard Fraction arithmetic and verified:

- The cleared polynomial identity for L.
- The cleared polynomial identity for a_end.
- The full logarithmic derivative identity (3), including its denominator.
- The expansion from the derivative comparison to polynomial (6).
- A(9/10)=178605/573049 and its positive reserve below 1/3.
- Rpoly(11/10)=1408/125, T(11/10)=1283/125.
- The exact uniform reserve 7162/3125 in (7).
- A(11/10)=425920/1646089.
- The full positive endpoint reserve
  721591680879/173414975738944 above 81/64.

Every check passed. No numerical sample, angle mesh, Lean compilation or
CI was used.

The original endpoint beta=K is used only for scalar comparison. No
physical B corner tie is assigned to the actual unique B, and no actual
C mean, circle weight or side offset is changed. The source correctly
requires a separate whole-interval monotonicity result before transferring
the endpoint bound to the original beta interval. It correctly leaves
the root projection, normal-ratio and block-pressure obligations open.

The separate monotonicity source is
`ABC_FAR_RADIAL_A_MONOTONICITY_WORKING_2026_10_25.md`.
Its complete proof and all 52 rational coefficients were independently
reviewed by high_radius_review, who reported a full pass to root. That is
not an independent review by this endpoint reviewer of his own
monotonicity manuscript. Combining that independently audited monotonicity
with this independently audited endpoint lemma gives b>9/8 throughout
the original epsilon_B=1 far-radial prefix. It gives no full UUS exit.
