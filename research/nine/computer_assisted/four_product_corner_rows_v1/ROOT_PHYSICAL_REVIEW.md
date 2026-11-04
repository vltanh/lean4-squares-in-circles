# Root physical and code review of four-product corner rows

The continuous implication and both exact implementations are accepted,
subject to independently certified current original center/frame intervals.
This review grants no original-cell or mask credit by itself.

For the same physical original, the signed corner norm expands to
`x²+y²+1/2+epsilon*alpha*x+tau*alpha*y+epsilon*beta*y-tau*beta*x`.
The unit and quarter-turn identities therefore leave the exact upper bound
977/256 after subtracting1/2. Every frame coefficient in the producer uses
signed beta in column27+i, rather than the separate absolute-beta variable.

Each of the four signed products can independently take either matching
lower interval endpoints or matching upper endpoints. Its difference
from the corresponding affine lower plane is a nonnegative product of
two same-sign endpoint differences. Reusing alpha, beta, x or y in more
than one term does not affect this implication: each inequality holds
at the same actual values, so their sum holds. Negative coordinate signs
are incorporated by reversing the signed interval endpoints correctly.

Adding the squared-center tangent gives the producer's four-variable
row. The complete residual consists of two squares and four nonnegative
rectangle products. All16 plane choices are valid inequalities on the
same domain; they are not16 subdomains requiring an extra case cover.
Closed endpoints and zero-width intervals are included. No auxiliary,
selected normal or separator predicate is introduced.

The independent checker expands its own signed coordinate boxes, frame
columns and coordinate columns. It reconstructs every coefficient and
the rational977/256 constant without importing the producer. The row-name
prefix is distinct from the earlier grouped family, and its nine fields
bind the original corner, rational tangent and all four binary choices.

Taking equal choices on both alpha products and equal choices on both beta
products reproduces each accepted grouped row, because Cartesian signed
projection extrema are sums of the corresponding coordinate extrema.
Thus the new family contains the older four planes and can select a
stronger affine lower bound. It does not assume independent physical
coordinates or frames.

Fresh relocated standard-library controls pass3,456 exact literal and
physical residual checks,864 exact reproductions of the grouped family,
all36 signed original corners and all16 patterns. They reject five
damaged literals or substitutions of wider caller intervals. The
continuous proof establishes validity beyond these finite fixtures.

Applications may cache parameter tuples only. Each row must be rebuilt
from its own independently propagated current positions and signed-frame
intervals, and the ordinary exact multiplier/residual replay must check
every used literal. A child row may not be copied unchanged to a wider
parent. Numerical directions and plane selection provide no proof premise.
