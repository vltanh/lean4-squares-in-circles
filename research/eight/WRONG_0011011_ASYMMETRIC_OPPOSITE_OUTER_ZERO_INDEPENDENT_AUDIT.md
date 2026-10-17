# Independent audit: asymmetric opposite-sign outer zero-quarter pair

**Result: PASS.** The complete continuous proof and its 66 fixed arithmetic
comparisons were independently reviewed. The proof covers edge 0, outer/outer,
signs (+,−), every retained axis, and the entire angle interval [−.7,.7].
Reflected reversal supplies edge 1. Its strict conclusion is cost > .89778.

## Continuous derivation checked

The source secondary/primary formulas and the interchange of label orders
under reflected reversal are correct. The derivative formulas for the two
labels imply the stated global monotonicity and curvature directions.
In the aligned argument it is the derivative of the contact cost that is
convex; its nonpositive sublevel interval containing the right endpoint
indeed excludes any interior minimum below both endpoints.

Both primary orders are excluded by the displayed angle/coordinate barriers
and monotone label bounds. Secondary projections increase in both coordinates,
so the contact reduction is complete, including zero coordinates.

For positive angles I independently differentiated the contact coordinate and
the speed product J′(b)K. The signs in both partial derivatives in Section 6
are correct. Moving the target toward zero preserves the required source
coordinate range. The final one-variable speed product increases with angle
and remains below one. Both source labels therefore give the claimed cost
monotonicity until alignment or the source-diagonal boundary.

On that positive boundary the circle-coordinate formulas, f′ numerator,
and B″ = −Vf²−Uf′ are correct. The target-J curvature is immediate; the
target-P positive second-derivative term is dominated by the stated negative
term. The boundary endpoints are exhaustively covered.

For negative angles I independently recovered the cancellation
v² = Q−2B−(b−1/2)². The source-P monotonicity and source-J concavity follow
with their displayed strict rational reserves. Every feasible negative
contact reaches alignment or the source diagonal before angle .56.
On that diagonal, the formulas U′=−Vf, V′=Uf and the strictly negative
f′ numerator imply B′>0, B″<0. Its inverse angle function is convex,
so its endpoint chord is a valid upper bound. The derivative of the target
P label exceeds the chord slope, proving the whole boundary cost bound.

The only manuscript edit was an endpoint notation correction in (27): the
last strict chord-slope inequality became non-strict, since both sides
are zero at B=1−d. This does not weaken the strict final cost conclusion
or alter any arithmetic assertion.

## Arithmetic and binding

The checker contains no optimization, adaptive cover, or sampled acceptance.
Its integer square-root brackets, alternating trigonometric series, exact
rational comparisons, and all scalar substitutions were reviewed. A fresh
copy was executed in a unique temporary directory. All 66 comparisons passed,
and the regenerated JSON was byte-identical to the author's frozen JSON.

The source, checker, output hashes and replay directory are recorded in
`wrong_0011011_asymmetric_opposite_outer_zero_independent_audit.json`.
The audited manuscript SHA-256 is
`fbbd2da52f34c98507c2ea9a6c1756c2e14f73f588a1da75fd5a939223a5451a`.
