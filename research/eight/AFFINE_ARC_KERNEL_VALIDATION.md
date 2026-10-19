# Validation status of the generalized one-angle hand kernel

The mathematical derivation is in `AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md`.
The verifier is `verify_affine_arc_hand.js`. Its candidate tables are
still being constructed and independently reviewed; this validation
note does not claim a candidate exclusion from a numerical screen.

As a regression on an already independently reviewed theorem, the entire
140-row scalar table for the wrong word 0010111 was translated into the
new unsigned-b affine schema. The seven original role labels and the
two edge targets were preserved exactly. All 140 rows and all 310
premise/cost polynomials pass the generalized checker.

The translated input is `legacy_140_kernel_replay_input.json`; its exact
output is `legacy_140_kernel_replay_fast_arithmetic.json`. After removing
trailing zero powers, the same proof uses 4,035 Bernstein coefficients.
The original untrimmed independent proof has 4,475 coefficients.

The faster Bernstein implementation clears denominators in the same
binomial formula: if coefficients have common denominator C and
u=(L+Wx)/D, multiply transformed power coefficients by C D^n.
Then clear the binomial denominators by their positive least common
multiple. All inner sums and products are integers; only the final
coefficients are converted back to rational numbers. This changes no
polynomial or mathematical estimate.

For full candidate tables the checker additionally checks every declared
state subarc union and every necessary angle chain using fixed exact
arctangent and Machin bounds. Duplicate state IDs are rejected; every
row must use the declared quarter word and an edge target at least as
strong as its declared baseline. The translated legacy input has no
candidate-domain declaration, because it deliberately covers only the
previous theorem's scalar component, whose complementary contact strips
are provided by its separate independently reviewed hand proof.
