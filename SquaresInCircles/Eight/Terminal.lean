module

public import SquaresInCircles.Eight.TerminalEstimates
public import SquaresInCircles.Eight.Arithmetic.PositiveEnergy

/-!
# The sharp bound and its equality mechanism

Once candidate capture is established, the argument has three steps.
First, the adaptive dual bounds the containing squared radius by the sharp
value plus nonnegative errors. Second, positivity forces those errors to
vanish at equality. Third, apply the stationary dual afresh to the untouched
original centers; moving centers never justifies equality of their originals.

The coordinate and projection estimates are in `TerminalEstimates`. Their
precision-dependent witnesses do not enter the positive-energy reasoning.
This source has not been compiled.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open ExactFamily Coordinates
namespace Terminal
open Candidate Perturbation

theorem boundary_quantitative {q z : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q≤Q0) (hz : z ∈ tiltBox) (ht : tilt F.theta=2*Real.arctan z)
    (htw : 1/10≤tilt F.theta ∧ tilt F.theta≤4/25)
    (hS : mismatch F.theta≤1/1000) (ho : OwnerRestriction C terminalOwners) :
    ∃ o : Owners,
      qStar+((adaptiveData z hz).mu 4/8)*(z-sharpData.z)^2+
        completed (adaptiveData z hz) (tilt F.theta) (errors F) o (positions C)+
        terminalReserve*mismatch F.theta≤q := by
  obtain ⟨o,hg⟩ := owners_and_gaps F ho
  obtain ⟨hX,hZabs,hU,hV,hZ,hη⟩ := automatic_projections F hq hz ht hS
  refine ⟨o,?_⟩
  simpa [error_sum F] using quantitative hz ht htw (errors F) o (positions C)
    (by simpa [error_sum F] using hS) (vertex_containment F) hg hX hZabs hU hV hZ hη

/-- Equality is a positivity argument, not a decimal comparison. -/
theorem boundary_rigid {q z : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q≤qStar) (hz : z ∈ tiltBox) (ht : tilt F.theta=2*Real.arctan z)
    (htw : 1/10≤tilt F.theta ∧ tilt F.theta≤4/25)
    (hS : mismatch F.theta≤1/1000) (ho : OwnerRestriction C terminalOwners) :
    q=qStar ∧ z=sharpData.z ∧ mismatch F.theta=0 := by
  obtain ⟨o,hbound⟩ := boundary_quantitative F
    (hq.trans qStar_limits.2.2.le) hz ht htw hS ho
  have hμ := (adaptive_weightDomain hz).mu_pos 4
  have henergy := completed_nonneg (adaptive_weightDomain hz)
    (tilt F.theta) (errors F) o (positions C)
  have hρ : 0<terminalReserve := terminal_constants.2.2.2.2.1
  have hrigid := Arithmetic.positive_energy_rigid
    (show 0 < (adaptiveData z hz).mu 4/8 by positivity)
    hρ henergy (mismatch_nonneg F.theta) hq hbound
  exact ⟨hrigid.1,sub_eq_zero.mp hrigid.2.1,hrigid.2.2⟩

/-- Apply the dual on the original centers. This has no displacement or
projected-slider hypothesis; only original vertices and separating gaps. -/
theorem original_pullback {p : Positions}
    (hv : ∀ i : Fin 5, normSq (add (p i.castSucc.castSucc) (sharpData.anchorOffsets i))≤qStar)
    (hg : ∀ e : Fin 7, 0≤OriginalDual.gap sharpData p e) :
    (∀ i : Fin 5, p i.castSucc.castSucc=sharpData.anchorCenters i) ∧
    (∀ e : Fin 7, OriginalDual.gap sharpData p e=0) ∧
      ∃ Z η : ℝ, p 5=sharpData.pT Z ∧ p 6=sharpData.pG η := by
  have h := OriginalDual.original_centers_rigid sharpData_stationary.toIsChain
    sharpData_stationary.weightDomain sharpData_stationary.zero_defect
    sharpData_stationary.position_stationary hv hg
  exact ⟨h.1,h.2,OriginalDual.slider_coordinates (h.1 1) (h.1 4) (h.2 1) (h.2 5)⟩

end Terminal
end SquaresInCircles.Eight
