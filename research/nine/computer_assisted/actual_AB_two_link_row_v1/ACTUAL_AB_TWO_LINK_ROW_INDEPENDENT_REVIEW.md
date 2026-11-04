# Independent physical review of the actual-AB two-link theorem

**Accepted as a conditional physical theorem, with the hypotheses stated in
the source.** I found no gap in the physical separator reduction, scalar
target, closed finite cover, or strict-CD equality blocker. I freshly ran
the separate rational scalar checker: all 28 domains, 103 leaves, and
12,875 Bernstein coefficients passed, with no frontier. The reviewed
sources and this replay are bound in the accompanying JSON.

## Physical premises and endpoint signs

The theorem retains the original squares A,B,I,D,E,F,G and their independent
frames, original disk containment, and original pair separations. Its
projection hypotheses are actual AB, EF, and FG. Its sign and coordinate
guards are D nonnegative, G weakly above D, strict `|x_G-x_D|<1`,
`x_B<=x_I<=x_D`, and two-link vertical variation at most `3/5`.

For every genuine owned D/G separator, a nonpositive vertical component
would give projection at most `|x_G-x_D|<1`, while its support sum is at
least one. Thus the vertical component is strictly positive. This also
rules out a zero D/G vertical center gap. Rotation by pi reverses this
separator and both center coordinates, while preserving the canonical
orientation of the physical square modulo pi/2. The accepted oriented
cap therefore applies to original D with its original nonnegative signed
angle. No reflection that silently changes D's canonical sign is used.

The universal A/E cap is unrestricted in the other pair's owner, angle,
or height. Its normalized toll is at least `2|beta_A|/23`. Adding these
two original-pair caps is legitimate because their tolls belong to
different pairs. The actual EF and FG projections imply
`x_G-x_E-h_E-h_G>=2h_F>=1`. The resulting endpoint inequality is exactly

`span-h_A-h_D+T_good(D)+T_universal(A)<=2`,

and is strict below Q. Neither a common-side assertion for E,F,G nor a
new A/E shoulder premise is inserted.

## Both physical owner axes are covered

After reversing the row, each non-actual pair D/I or I/B has nonnegative
horizontal gap d and vertical gap v with `|v|<=3/5`. Disjoint half-unit
incircles give `d^2+v^2>=1`, hence `d>=4/5>|v|`. This justifies strict
horizontal order even though the supplied order guard is weak.

A separator with nonpositive horizontal component has projection at most
`|v|<1`, so it cannot separate these originals. For the forward shallow
axis of either owner, the projection is at most
`alpha_owner*d+|beta_owner|*|v|`. The forward steep axis has projection
at most `|beta_owner|*d+alpha_owner*|v|`, and this is bounded by the same
expression because

`(alpha_owner-|beta_owner|)*(d-|v|)>=0`.

The support sum is the same relative-frame expression for all four owned
axis choices. Thus each link obeys the displayed physical lower bound in
the source. All four choices of the two owners are retained. The actual
AB edge contributes its exact halfwidth sum without a vertical error.

## Scalar reconstruction and strictness

Writing `x=tan(|theta|/2)`, the independent checker reconstructs the cosine
terms from original frame dot products and the sine terms from
determinants. I checked the common denominator and the coefficients of
the good endpoint, actual-link halfwidth, and selected-owner penalty.
In particular,

`T_good(D)-h_D=(-368+529*x_D-1536*x_D^2)/(736*(1+x_D^2))`,

and the selected-slope term is exactly `(601/1000)*2*x_k/(1-x_k^2)`.
Multiplication by `736000*product(1-x_i^4)` is strictly positive throughout
the enlarged rational box `[0,5/12]^3`. The signed polynomial weights in
`[-8,8]` minorize the two absolute sine terms, so their use has the correct
inequality direction.

There are four internal sign choices and, over the four owner patterns,
seven distinct selected-owner cases: 28 domains in total. The independent
trie check requires both closed children at every split and forbids
duplicate or ancestor leaves. On an origin leaf only the origin Bernstein
coefficient is zero; all other 124 coefficients are positive. At every
nonzero point of that closed box some non-origin basis term is positive,
including every boundary face. Hence scalar strictness holds unless all
three D/I/B angles vanish, including when a nonselected frame is tilted.

## Equality and use in the original-nine mask

Let M be the maximum absolute slope of the selected owners. The physical
row lower bound differs from two by at least
`(601/1000-3/5)*M+T_universal(A)`, and additionally has the scalar table's
strict surplus whenever any D/I/B angle is nonzero. Equality at Q thus
aligns D,I,B, and then the nonnegative universal toll aligns A.

Each remaining non-actual aligned pair must separate horizontally because
its vertical gap is below one. Together with actual AB, this forces span
at least three; the cap inequality forces span at most three. In the
unchanged `001/00` caller, actual AB and BC, the original CD center cone,
and original inset separation then imply

`3>=h_A+2h_B+h_C+g_C+g_D=1+2h_B+h_C+g_C>=3`.

Equality aligns C and makes the original CD projection exactly one,
contradicting its retained strictly weak bit. All nine originals, all
corners, all physical pairs, and the closed-Q face remain in this argument.

The five-member complement is valid only after its additional parent
guards, including I strictly left of D, have been proved from the original
ancestor. The theorem and this review do not themselves close such a
parent: every remaining complementary domain still needs a complete
proof. No Lean, Lake, CI, or numerical optimizer was used in this review.
