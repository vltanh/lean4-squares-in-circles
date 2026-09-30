module
public import SquaresInCircles.Six.Stress.DiagonalRemainder

@[expose] public section

/-!
# Compatibility import for the former diagonal vertex certificate

The old expression, root, weights, and finite-cover check have been removed.
The actual proof is now the human-analytic DiagonalRemainder development.
New analytic code should import that module directly. The historical namespace
below is retained only to avoid breaking existing callers.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress.DiagonalCertificate

/-- Historical name for the analytic vertex theorem; no computation is used. -/
theorem vertex_remainder_positive {w s d : ℝ} (hd : DiagonalDomain w s d)
    (hv : 1 ≤ 2 * Six.radius * |Real.sin (diagonalDelta w s d)|) :
    0 < pairLine w + pairLine (-s) + diagonalVertex w s d + 2 * pairBase :=
  diagonal_vertex_remainder_positive hd hv

end SquaresInCircles.Six.Stress.DiagonalCertificate
