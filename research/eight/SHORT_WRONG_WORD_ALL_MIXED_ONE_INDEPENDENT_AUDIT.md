# Independent audit: 0010111 mixed quarter-one transitions

**Result: PASS.** This audit covers the complete continuous proof in
\`global_attack/hand_conversion/SHORT_WRONG_WORD_ALL_MIXED_ONE_HAND_PROOF.md\`,
including every permitted sign/kind/owner case. It is conditional on the
stated exterior axis reduction, common frame interval, and role signs.
It does not assert the outer/outer or core/core entries of the wrong word.

Audited manuscript SHA-256:
\`c1c85364c569266f4d793f8557cce7903ccb0bfacfae6850a4dcdf9fc5a3bba1\`.

Audited checker SHA-256:
\`22d650d8dcef5adb324d9dbe2cc390285f97f5ab27d756f65bc5f9830f68aad3\`.

## Continuous coverage and geometry

I independently rederived the four true separating projections in the
signed own-frame coordinates. Reflection followed by reversal has the
stated effect on the role labels, signs, and axes and preserves the
corrected cost. The 24 normalized rows in each radial order cover the
12 permitted edge/sign combinations and both direct/reflected orders.
Both source axes for those 48 rows recover all 96 original branches.
The source-primary sign dominance is valid at fixed coordinates and
survives reflection; the retained fourteen primary rows in each order
cover every removed positive-source row.

The full-circle and endpoint support formulas have the correct signs.
The core-side/corner distinctions are preserved. The norm identity
\(N''+N/4=(p^2+q^2-\lambda^2)^2/(4N^3)\) and the strictly positive
norm derivative justify the four concavity intervals in section 3.
I checked the source/target cap exclusions, all constant-multiplier
supports, and the monotonic or concave endpoint reductions in
sections 3--6. The multiplier signs and the nonnegative discarded
core terms agree with the normalized row table.

## The nontrivial negative-core primary class

For section 7 I independently expanded the multiplier
\(\lambda=g/\sin\phi\). Its side envelope is exactly formula (23).
Multiplication by positive \(\sin\phi\) yields the stated nonradical
term and squared radical. The chosen sine truncation in the signed
term \(-2gp\sin\phi\) gives an upper bound in both signs of \(p\).
The positive coefficient \(x+A\), the positive \(T\) polynomial, and
\(T^2-QV>0\) therefore imply the desired strict cost bound.

For section 8.2, the continued outer label is increasing from every
possible contact height through the actual outer axial endpoint.
Consequently extending the outer circle below its physical diagonal
gives a valid lower bound. The contact height decreases in both
core coordinate and angle. I checked the formula
\[
 D''=-6u+.789(Q-2u^2)/\sqrt{Q-u^2},
\]
its sign, the two endpoint range bounds, and both resulting bounds on
\(L''/L'\). The negative core-curvature contribution is
\(L'\cos\phi\,A''\), with \(A''\le-12\); the positive contribution is
at most \(2L''\). The two displayed comparisons make the full contact
cost concave in the core coordinate. Thus its endpoint reduction is
valid on the entire early corner.

For section 8.3, direct differentiation gives exactly (34).
Since \(u>1\), \(p/q<.253\), and \(q>.767\), the three positive
polynomials in (35) imply the common strict bound \(H''>.65\).
Every reference point lies in its proved interval. The completed-square
bound with denominator 1.3 and the left-endpoint increasing cases
therefore prove the twelve endpoint curves. The late corner and full
upper-half arguments in sections 8.1 and 9 have the stated derivative
and concavity signs.

## Independent exact arithmetic

A fresh Node replay of the complete author checker passed all
390 fixed comparisons. Its embedded original labels match
\`short_hand_labels.json\`.

The separate Python checker
\`audit_short_all_mixed_one_polynomials.py\` rebuilds all four side
inequalities and the common curvature polynomials using
\`fractions.Fraction\`. It converts to the Bernstein basis by
triangular elimination of the defining basis identity, independently
of the author's binomial conversion implementation.

All **11 polynomial rows and 144 individual printed coefficient
bounds** passed this independent reconstruction. The bound
\(C>.898>.89765\) is therefore supported for the complete stated
mixed quarter-one table, with no remaining mathematical issue found
in this review.

Machine-readable reconstruction record:
\`short_all_mixed_one_independent_polynomial_audit.json\`.
