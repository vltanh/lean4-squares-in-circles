module
public import SquaresInCircles.Six.Analytic.CompleteReduction

@[expose] public section

/-!
# Complete analytical six-square reduction

This entry point now exports an unconditional complete_reduction for every
NormalizedPacking, using the original normalization record without new fields.

The missing-south cases are closed by the cardinal-W argument and the two
OWN-W/S-bit arguments. ReflectedOwnWings closes the final missing-west case
by reflecting scalar inequalities while proving the enlarged reflected domain.
Together these give candidate_diagonal_separators. The candidate west-tail
bound and SouthOuterTail then give both bit-dependent pair domains.

The final OWN-S tail uses two distinct arguments. Cardinal W uses the original
whole-rectangle polynomial-root profile. OWN W retains the actual diagonal
coordinates until the wing angles have been reduced to endpoints; one corner
then uses a proved narrow radial-support cone. No endpoint of the earlier
invalid OWN-W scalar rectangle is asserted positive.

CompleteReduction feeds the analytic fixed-pair/diagonal radius closure and
the retained-source eight-contact equality reconstruction. The public
LowerBound and Uniqueness modules now use it directly; no finite
Classification module supplies an input to those endpoint declarations.

These are written analytical arguments and Lean source proof bodies. The
compiler, elaborated dependency/axiom audit and independent kernel replay have
not been run. The final tail derivation and full proof map are documented in
research/six/lean/ANALYTIC_SOUTH_TAIL_PROOF.md and docs/proof/six.md.
-/
