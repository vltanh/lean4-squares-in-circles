module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTStress

/-!
# The actual aligned-T exclusion above the small primary-total range

Uncompiled source closure of Sections 6--10. The short T magnitude is
derived from the current two projections. Every concentration inequality
and every scalar endpoint is then supplied to the original weighted
separation inequality, with arbitrary signs in both selected A/E pairs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Source
open Candidate Secondary PositiveAngularEnvelope
open NonnegativeTotals.Source (aTotal eTotal)

theorem high_actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hδ : delta C.theta B≤0) (htd : delta C.theta T=0)
    (hlarge : L≤total C ga ab de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  let s : ℝ := -delta C.theta B
  let ε : ℝ := eTotal C de eh
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall := original_error_bound hvar hn B
  have hs : s∈Icc 0 frameCap := ⟨neg_nonneg.mpr hδ,(neg_le_abs _).trans hsmall⟩
  have hbt : delta C.theta B=-s := by dsimp [s]; ring
  have hM := aligned_short hsort hcoreT hc hQ hDy hs hBT hTD hbt htd
  have hb := budgets hg ga ab de eh ε hvar ha he hs hbt htd
  have hε : ε∈Icc 0 frameCap := hb.2.2.1
  have hp := Concentration.sum_scalar_positive
    (fun i => (blocks C hg ga ab de eh ε i).P)
    (fun i => (blocks C hg ga ab de eh ε i).N)
    (show total C ga ab de eh∈Icc L frameCap from ⟨hlarge,hb.1.2⟩)
    (show ε∈Icc 0 (total C ga ab de eh) from ⟨he,by dsimp [ε,total]; linarith⟩)
    (show s∈Icc 0 M from ⟨hs.1,hM.le⟩)
    (fun i => (blocks C hg ga ab de eh ε i).P_nonneg)
    (fun i => (blocks C hg ga ab de eh ε i).N_nonneg)
    hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  have hcost : primaryCost (total C ga ab de eh) ε=
      l ε*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh) := by
    simp [primaryCost,NonnegativeTotals.NegativeTD.primaryCost,total,ε]
  rw [hcost] at hp
  have hlow := stress_lower ga ab de eh hε hsort hc hcoreT hQ hHy hGy hBy hDy
    hvar ha he hs hbt htd hhg
  have hu := stress_nonpositive ga ab de eh hε hHG hGA hAB hBT hTD hDE hEH
  linarith [hp,hlow,hu]

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Source
