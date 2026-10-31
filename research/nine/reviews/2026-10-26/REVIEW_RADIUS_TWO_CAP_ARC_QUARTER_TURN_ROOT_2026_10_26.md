# Root review: every radius-two unit in a cap above one quarter has a long inner arc

Date: October 26, 2026.

**Result: PASS for the strengthened H>1/4 theorem and its conditional
capacity consequence.** The earlier root-authored version assumed
H>1/(2sqrt(2)); the new outer-face proof was supplied separately by
certificate_reduction. This review checks the complete strengthened
source. A reviewer who authored neither portion has also independently
checked the whole proof in
REVIEW_RADIUS_TWO_CAP_ARC_QUARTER_TURN_C6_2026_10_26.md.

The own-frame split a>5/4 versus a<=5/4 is exhaustive. In the first
case the fixed-q interval may legitimately be enlarged to its b=1/2
and a=b endpoints; both endpoint bounds are strict throughout their
full ranges. The convex expression E is less than 3/5, which directly
implies (sqrt(2)A+B)^2<r^2-B^2. No sign assumption on the expression
being squared is needed to obtain its upper bound by the positive
square root. The exact closed arc interval, its open interior, both
possible upper endpoints and b=r are all treated correctly.

In the outer-face case the actual cap premise forces 0<B<=A<=1/4
and A^2+B^2>1/16. The exact intersection is the stated maximum-lower,
minimum-upper interval. I independently differentiated the outer-outer
gap at fixed k^2 and reconstructed its factorization:

    (A-B)[(A+B-1/4)^2+(k^2-1/16)(A+B+1)].

Both quantities compared by squaring the derivative have positive
denominators on the open interval. The interval from the diagonal
to the actual point is connected and stays in the original domain;
continuity includes the outer-face endpoint a=5/4. Its diagonal lower
bound has the exact positive radical reserve (16-9sqrt(2))/100.
The other three face-gap comparisons are valid on their whole domains.
All four differences exceed pi/4, proving one connected open arc
with that strict length.

The support half-width and farthest-corner inequalities place the
actual center norm strictly between 3/4 and 3/2. Hence its radial
point on the radius-5/4 circle is strictly within the actual inscribed
disk. This proves the point lies in the unique arc, without a chosen
orientation or any circle-contact premise.

The theorem supplies only arc length and connectedness. The implication
for two units still requires an actual routing theorem placing both
arcs in one interval of length at most pi/2; it neither proves that
interval nor assigns H>1/4 to an unproved C6 pocket. Every physical
unit and all original zero-weight, mean and slider cases are retained.
No parameter sampling, coefficient packet, Lean compilation or CI is
used in this proof.
