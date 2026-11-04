# Exact supporting halfplanes for the original 36 corners

For each unchanged physical original i, let its center be (x_i,y_i),
its first unit side vector be (alpha_i,beta_i), and its positive quarter
turn be (-beta_i,alpha_i). For epsilon,tau in {-1,1}, its actual corner is

```
z = (x_i + (epsilon alpha_i-tau beta_i)/2,
     y_i + (epsilon beta_i+tau alpha_i)/2).
```

The original corner predicate gives `||z||²<=Q=1105/256`. For arbitrary
rational a,b, not both zero, choose any nonnegative rational U satisfying
`256 U² >= 1105(a²+b²)`. Cauchy-Schwarz then gives
`a z_x+b z_y <= sqrt((a²+b²)Q) <= U`. Expanding the left side yields

```
a x_i+b y_i
+ (epsilon a+tau b) alpha_i/2
+ (epsilon b-tau a) beta_i/2 <= U.
```

This is a necessary row in four of the existing 54 original variables.
It introduces no auxiliary, selected separator, interval premise, or
identification of different originals. Each of the four signed corners
is treated explicitly; all nine independent frames and original pairs,
cones and marked predicates remain in the enclosing caller.

## Integer-directed support bound

The producer computes the smallest multiple of2^-40 at least
`sqrt(Q(a²+b²))`: take the integer square root of the floor of
`2^80 Q(a²+b²)`, then add one if its exact square is too small.
All operations are integer or rational operations. The independent
checker does not reproduce this algorithm. It directly proves the
displayed squared comparison for the printed U, checks U>=0, and
independently expands the two corner coordinates. Thus even an arbitrary
alternative rational U is accepted only when it is a valid support bound.

Numerical points may suggest a,b and decide which rows are useful. Their
feasibility, tolerance and floating-point direction play no role in row
validity. Every literal row used by a proof is independently rebuilt,
and its enclosing nonnegative-multiplier certificate is checked exactly.
The rows are valid on the full closed disk, including its boundary.

The exact control suite checks the corner expansion, the independent
literal reconstruction, the squared support bound, and the identity
`(a²+b²)(z_x²+z_y²)-(a z_x+b z_y)²=(a z_y-b z_x)²`.
It includes exact rational boundary points obtained from
`(33/16)²+(1/4)²=1105/256`, zero coordinate directions, all36 signed
original corners, rational physical unit frames, and damaged literals.
These fixtures verify implementation; the displayed inequalities prove
the continuous implication. No original-cell or mask credit is earned
without the caller's independently replayed complete closed cover.
