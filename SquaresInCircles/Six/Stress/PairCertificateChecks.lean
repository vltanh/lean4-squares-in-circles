import SquaresInCircles.Six.Stress.PairCertificateModel

/-!
# Concrete checks for the common pair envelope

Ordinary `decide` reduces the proved exact-rational checker. The independent
fixed-dyadic replay is development evidence, not an assumption of these
statements. Compilation remains deferred; no kernel execution is claimed here.
The local checks include regularity as well as the derivative lower bound.
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

/-- The only coefficient bounds needed in the analytic diagonal cap argument. -/
def diagonalConstantClaim : Formula 1 :=
  let T := (2*(hE : Smooth 1)*mE*rhoE).expr
  .conj (.lt (er (139/100)) T) (.lt T (er (141/100)))

theorem diagonal_constants_checked :
    certify diagonalConstantClaim (fun _ => 1) 0 0 (fun _ => ⟨0,0⟩)=true := by
  decide

noncomputable section

lemma diagonal_constant_bounds : (139:ℝ)/100<2*Six.hStar*mStar*rhoStar ∧
    2*Six.hStar*mStar*rhoStar<(141:ℝ)/100 := by
  have hx : (fun _ : Fin 1 => (⟨0,0⟩:RInterval)).Mem (fun _ => 0) :=
    fun _ => ⟨le_rfl,le_rfl⟩
  have h := certify_sound diagonalConstantClaim (fun _ => 1) 0 0 diagonal_constants_checked hx
  simpa [diagonalConstantClaim,Formula.Holds,Expr.denote] using h

end
end SquaresInCircles.Six.Stress.PairCertificate
