# Independent audit of the weak-middle upper-central whole-floor reduction

The geometric reduction in
`WEAK_MIDDLE_UPPER_CENTRAL_WHOLE_FLOOR.md` and the independent
Fraction formulas in `computer_assisted/verify_upper_central_floor.py` were
reviewed by the low-floor audit agent. No gap was found. This audit is
separate from, and does not replace, the complete arithmetic replay.

For either sign of x_P, choosing the original main on that half-plane
puts its reflected center in `[g-1/60,61/60-h]`. The displayed maximum
therefore bounds the actual horizontal gap; its universal cap31/60 is
valid. Its first term gives `g-d>=2g-|x|-1/60>=10/13-2/5`, and its second
gives `g-d>=eta+|x|-1/60>=-1/60`. Thus every physical and inset numerator
used in the vertical clearance is positive. The exact verifier's wider
interval lower bounds do not require the sharp pointwise numerator
constant; they remain outward bounds.

The main's original outer-cone/endpoint lower height is valid on both
sides. Its derivative changes sign at `h^2=41/128`; the endpoint or
AMGM value used in the exact checker is the correct interval minimum.
The two collected/direct support formulas agree at every point, and
taking their interval maximum together with the halfwidth-difference
bound is safe. All four physical owner axes and both independent
chiralities are retained.

For v<=-1/10, the left shoulder is horizontally left of U. If U were at
or above it, the horizontal and vertical gaps would be at most59/60
and13/480. Their squared-distance reserve is exactly7447/230400>0, so
the shoulder must be above U. Actual L/P separation gives the stated
lower endpoint A0; no cone comparison for L/U is assumed.

For fixed v in that branch, the function

    F_v(A)=sqrt(rho^2-A^2)-sqrt(1-(A+v)^2)

has real radicals and positive comparison terms on the full rectangle.
The sign of its A-derivative is the sign of
`rho*(A+v)-A=(rho-1)A+rho*v`, so any stationary point is a minimum.
Hence its maximum is at an interval endpoint. Its v-derivative is
positive. Replacing A0 by an interval lower endpoint enlarges the whole
allowed A interval; the two endpoint maximum remains an upper bound
without assuming F_v is monotone in A. Replacing v by its interval upper
endpoint also enlarges the cap. The checker correctly skips this extra
cap on boxes straddling v=-1/10 and leaves impossible A0>A1 boxes to the
separate necessary-condition row.

Finally y_U>=y_P and the two floor assumptions give precisely the
nonnegative vertical-gap upper bound used for the P/U disk and all-four-
owner projections. The maximum with zero only enlarges expressions
outside the already necessary ordered region. The exact root contains
every original sign, orientation, and boundary case. Completion and
acceptance still require the separately reported full tree replay.

## Subsequent acceptance record

The root agent subsequently reported a complete independent Fraction
replay of all 142,251 nodes / 71,126 leaves, maximum depth 38, with least
reserve greater than 1/10000000. Its certificate SHA-256 is

    942bb4be822f244eb2e7a1df96865997ac32eb1bcbddcde8c369f464fea4d619

Four deliberate corruptions were rejected. This completes the arithmetic
acceptance separately from the geometric audit above.
