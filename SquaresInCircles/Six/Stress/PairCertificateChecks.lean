import SquaresInCircles.Six.Stress.PairCertificateModel
import SquaresInCircles.Six.Analytic.CandidateBounds

/-!
# Remaining computational checks for the common pair envelope

The outer and local-derivative checks below have NOT yet been converted to
human analytic proofs. They remain a blocker under HUMAN_ANALYTIC_STANDARD.md.

The former diagonalConstantClaim and its checker have been removed. The
compatibility lemma at the end now follows from explicit candidate algebra in
Analytic.CandidateBounds, whose imports do not include normalization or
certificate modules.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SquaresInCircles.Six.Stress.PairCertificate
open ProofTools

def candidateSource : Fin 2 → Fin 4 := ![0,3]

theorem outer_checked (no wo : Bool) (u : Fin 4) :
    certify (outerClaim no wo u) (fun _ => 1) 0 96 root=true := by
  cases no <;> cases wo <;> fin_cases u <;> decide

theorem local_derivative_checked (no wo : Bool) (u : Fin 2) (sector : Fin 6) (axis : Fin 2) :
    certify (Smooth.derivativeClaim axis (localGap no wo (candidateSource u) sector) (1/100))
      (fun _ => 1) 0 24 localRoot=true := by
  cases no <;> cases wo <;> fin_cases u <;> fin_cases sector <;> fin_cases axis <;> decide

noncomputable section

/-- Compatibility name only: this bound is proved by rational algebra, not
by either checker above. New analytic code should use the Analytic name. -/
lemma diagonal_constant_bounds : (139:ℝ)/100<2*Six.hStar*mStar*rhoStar ∧
    2*Six.hStar*mStar*rhoStar<(141:ℝ)/100 :=
  Analytic.diagonal_constant_bounds

end
end SquaresInCircles.Six.Stress.PairCertificate
