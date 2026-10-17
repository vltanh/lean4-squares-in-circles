# Independent audit of the whole low/high frame-pair proof

**Result: PASS for the stated strict L/H pair inequality.** This is an
independent review of the continuous argument and its printed arithmetic,
not an inference from a successful numerical minimization or interval
cover. The conclusion is conditional only on the prior center-gap and
axis-retention lemmas and the four explicitly cited earlier hand lemmas.
It does not assert closure of the remaining global orientation words.

## Reviewed versions

The following SHA-256 values identify the files reviewed after correction
of the negative-angle explanation in Section 2:

| File | SHA-256 |
|---|---|
| `LOW_HIGH_WHOLE_PAIR_HAND_PROOF.md` | `3903a894e7e90bdcdba6423f3a628cd790e99047aeddbc92de881673910209b6` |
| `verify_low_high_whole_pair_hand.mjs` | `fed96599db643163ac2e0d58a4b1cf0fe94bf20200ab45f2d87af6766bdef449` |
| `audit_low_high_polynomial_rows.py` | `cfb3fc5e2bfb7b2f45b88ef058b5223226df9c75a43fcb68ccfd672a81bc6783` |

## Geometry, signs, and completeness

I rederived the two retained source projections from the own-frame center
convention `(a,-sigma*b)`. The corrected cost, both rows of the multiplier
table (11), and the reflected-reversal map all have the stated signs.
For a primary source axis the separating hypothesis is independent of the
source sign. Replacing its cost by the smaller negative-source cost is
therefore legitimate; it is not necessary that the artificial sign change
preserve the center-gap relation.

The first version's claim that a nonpositive frame increment itself forced
opposite signs was false. The reviewed version instead uses SAT directly.
For a nonpositive increment, the `(+,+)` secondary projection is at most
the source transverse coordinate, the `(-,-)` projection is at most the
target transverse coordinate, and the `(-,+)` projection is nonpositive.
All transverse coordinates are at most `c<1`. The stronger negative-H
source cap bound also holds at every angle. The two primary bounds (8)
use the absolute sine, so apply to either target sign. These arguments
repair the issue without changing any subsequent scalar or polynomial.

The lower bound `phi>-.272` uses only the proved center gap and the two
type-angle ranges. The angle tails use the uniform nonnegative width
excess and the correct label extrema. Every endpoint join is covered:
the four earlier hand inputs are the aligned, parallel-strip,
quarter-strip, and short H-positive/L-positive support lemmas identified
at the beginning of the manuscript.

## Contact arguments

For the ordinary H-positive/L-negative contact surface, both relevant
projections and both labels increase with the chosen transverse
coordinates. The lower corner remains infeasible through `.46`.
The derivative with respect to the low coordinate is strictly increasing
for `x<=.2`, with the asserted lower curvature, and is positive by the
separate direct estimate for `.2<=x<=.46`. Thus the minimum moves to the
diagonal-contact or axial-contact curve with the directions claimed.

The slightly extended diagonal curve is a legitimate analytic comparison:
its low coordinate stays in `[-.003,.101]`, the implicit denominator is
positive, and its physical subcurve is included in the comparison domain.
I independently differentiated its equation. The displayed formula for
the second derivative, its negative bound, and the resulting concavity
of the scalar cost are correct. The axial scalar has the stated positive
curvature, so its single-point completed-square estimate is valid.

For a negative H primary source, rotation of its frame through a quarter
turn changes the transverse coordinate to the old primary coordinate
`z`. The new label is exactly

`G(z)=pi/2-H = pi/4-(k-v)c-v*a(z)+k*z`.

The new separating inequality and the new corrected cost (25) therefore
agree exactly with the old primary problem. This rotation is not a
relaxation of the orientation penalty.

For the negative target and negative rotated increment, the contact path
decreases cost until it reaches either alignment or the high diagonal.
On the latter boundary the continuation decreasing the low coordinate
also decreases cost and stays in its allowed interval. Its aligned
endpoint can additionally be checked directly: writing `b0=1-c`, the
scalar `G(z)+L(1-z)` on `c<=z<=1` has derivative `-d0` at `z=c` and
second derivative greater than `1/4`. Indeed
`G''> .390886*Q/(c+.5)^3 > .55` and the low contribution has magnitude
less than `.403875*.59 < .239`. Hence its cost is at least
`F0-2*d0^2`, precisely the quarter-contact bound used in (9).

On the remaining upper-H/negative-L contact surface, I rederived all
three Hessian entries. The bounds `z<=1` and `B<=1-c` remove the upper
type boundaries; the only remaining boundary pieces are the four listed
in Section 5.3. Since `F_BB>0`, `F_xx<.4`, `F_BB<.6`, and
`F_xB>.7`, its Hessian determinant is negative everywhere in the
interior. It therefore has no interior local minimum. All four boundary
costs are covered by independently justified scalar bounds. The use of
compactness here is legitimate and does not assume any unproved
monotonicity of a numerical first-gap function.

For the positive target, the negative-increment deformation stays above
the high diagonal. At nonnegative increments through `.08`, the contact
cost is strictly increasing in the low coordinate, as follows from the
positive second derivative and the decreasing but still positive value
of the first derivative at the axial endpoint. The two subsequent
support polynomials use `0<lambda<=G'(c)`, so their claimed diagonal
source support is valid on the entire physical upper arc.

## Remaining support cases and calculus

I independently checked each source and target support selection in
Sections 6 and 7 from its derivative `-U*r+V`. In particular, the
negative-low source is correctly minimized at its axial endpoint on the
secondary axis and at its cut endpoint on the primary axis. The claimed
target endpoints and full-circle enlargements cover the respective full
arcs, including the one-sided cut boundaries.

The barrier maxima in Section 7 use monotonicity along the target arc;
they do not bound the target's primary coordinate by its diagonal value
without justification. The positive-positive first-endpoint scalar has
a convex first derivative that is negative at its right endpoint; this
excludes an interior minimum. The rotating-norm identity (37) is exact
and gives the required concavity with the correct sign in both
quadrants. All norm upper bounds are used on intervals where the norm
is increasing and nonzero.

The final table accounts for both type orders, four sign choices, and
the two retained source axes. Primary source signs are merged only by
the valid cost domination described above. Reflection and reversal give
the target axes. No additional restriction on the frame concentration
or on a radial C/O word is used.

## Independent arithmetic and transcription checks

The JavaScript replay completed with **232 strict comparisons**, including
all **80 displayed Bernstein coefficient bounds**. I reviewed the exact
fraction and directed-interval operations, the sine/cosine remainder
directions, positive square-root brackets, and the positivity conditions
before squaring support inequalities.

The separate Python checker rebuilds all six polynomials directly from
the manuscript formulas using `Fraction`, reads the displayed coefficient
lists from the manuscript, and performs a direct affine-substitution and
Bernstein conversion. It confirms every printed strict positive bound,
with degrees `16,16,14,8,10,10`. It also reruns the JavaScript replay and
checks that all **16 displayed scalar endpoint lower bounds** agree with
the replay's exact outward bounds. This independent check passed.

For the three extension polynomials, the two quartic norm envelopes are
positive, the norm-square error is bounded before taking square roots,
and the final lower scalar uses the correct directions for all rounded
constants. For the other three rows, the lower expression being squared
is positive before its square is compared with the norm square.

## Equality scope

Every retained branch gives a strict corrected-cost lower bound
`C>.8833`. There is consequently no equality case in this entry of the
rounded frame table. This strictness is useful for later exclusion
arguments; it is not an equality classification for the optimal
eight-square packing itself. That classification remains a separate
assembly theorem.
