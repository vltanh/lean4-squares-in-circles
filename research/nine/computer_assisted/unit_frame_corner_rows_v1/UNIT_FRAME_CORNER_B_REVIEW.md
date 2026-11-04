# Independent review of the unit-frame corner consequence

The original physical corner is `c+(εu+τJu)/2`, where `u=(α,β)` is a unit
vector and `Ju=(-β,α)`. Direct expansion gives
`||c||²+1/2+α(εx+τy)+β(εy−τx)` for its squared distance from the disk center.
Thus the original corner condition implies the producer's exact quadratic
upper bound with right side `1105/256−1/2=977/256`.

For a product of two quantities in proved closed intervals, either matching
lower endpoints or matching upper endpoints yields a nonnegative residual.
Consequently the choices `(a0,r0)` and `(b0,s0)` in the producer are valid
McCormick lower planes. This argument does not require the quantities to be
independent. Negative β, negative projections and point intervals all obey the
same sign-product reasoning. Adding the exact center squared-distance tangent
gives precisely the displayed four-variable row.

I checked every coefficient sign against the physical corner expansion and
the residual identity. The independent checker recomputes both projection
intervals by enumerating Cartesian endpoints, while the producer computes
signed extrema term by term. It independently adds the tangent and product
coefficients and checks the exact rational constant. No producer is imported
by that checker. No mathematical or code defect was found.

The essential caller obligation is to use independently certified current
positions and frame intervals. Rational direction and plane-choice parameters
can be cached across descendants, but their coefficients and right sides must
be rebuilt from each current propagated state. A row derived on a child box
cannot be moved unchanged to a wider parent. In-place numerical objective
separation must keep the same fixed propagated intervals throughout a bound
round; the exact replay reconstructs each weighted row from those intervals.

The accompanying independent review program checks every original and signed
corner, both choices for both rectangle planes, and five rational unit frames.
It verifies the complete exact residual identity, the physical unit-corner
identity, independent literal reconstruction, and the inequality whenever the
physical corner is contained. Its report contains exact source hashes. These
controls support the implementation; the preceding continuous implication is
the mathematical justification. No original-cell or mask credit is claimed.
