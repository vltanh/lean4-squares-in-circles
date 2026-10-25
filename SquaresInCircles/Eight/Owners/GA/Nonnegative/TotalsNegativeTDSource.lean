module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDConcentration
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDStress
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsSource
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsTD0Source

/-!
# Eight squares: the complete original nonnegative A/E, nonpositive-TD2 exclusion

The fixed low-total case and the E-dependent large-total case cover
both closed intervals. Every scalar certificate and sign-concentration
endpoint is supplied internally. The original weak owners are unchanged.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NonnegativeTotals.Source (aTotal eTotal)

theorem high_actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hδ : delta C.theta T≤0) (hlarge : L≤total C ga ab de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  let s : ℝ := -delta C.theta T
  let ε : ℝ := eTotal C de eh
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall := original_error_bound hvar hn T
  have hs : s∈Icc 0 frameCap := ⟨neg_nonneg.mpr hδ,(neg_le_abs _).trans hsmall⟩
  have htd : delta C.theta T=-s := by dsimp [s]; ring
  have hb := budgets hg ga ab de eh ε hvar ha he hs htd
  have hε : ε∈Icc 0 frameCap := hb.2.2.1
  have hd : Domain (total C ga ab de eh) ε :=
    ⟨⟨hlarge,hb.1.2⟩,⟨he,by dsimp [ε,total]; linarith⟩⟩
  have hp := Concentration.sum_scalar_positive
    (fun i => (blocks C hg ga ab de eh ε i).P)
    (fun i => (blocks C hg ga ab de eh ε i).N) hd hs
    (fun i => (blocks C hg ga ab de eh ε i).P_nonneg)
    (fun i => (blocks C hg ga ab de eh ε i).N_nonneg)
    hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  have hcost : primaryCost (total C ga ab de eh) ε=
      l ε*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh) := by
    simp [primaryCost,total,ε]
  rw [hcost] at hp
  have hlow := stress_lower ga ab de eh hε hsort hc hcoreT hQ hHy hGy hBy hDy
    hvar ha he hs htd hhg
  have hu := stress_nonpositive ga ab de eh hε hsmall hHG hGA hAB hBT hTD hDE hEH
  linarith [hp,hlow,hu]

theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh) (hδ : delta C.theta T≤0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  by_cases hlow : total C ga ab de eh≤L
  · have haLow : aTotal C ga ab∈Icc 0 (1/6:ℝ) :=
      ⟨ha,by dsimp [total,L] at hlow; linarith⟩
    exact PairedE.LowA.actual_false ga ab true de eh hsort hc hcoreT hQ
      hHy hGy hBy hDy hvar hHG hGA hAB hBT hTD hDE hEH haLow
      (fun _ => hδ) he
  · exact high_actual_false ga ab de eh hsort hc hcoreT hQ hHy hGy hBy hDy
      hvar ha he hδ (lt_of_not_ge hlow).le hHG hGA hAB hBT hTD hDE hEH

end Source
end NegativeTD

open Candidate Secondary

/-- Every original TD0/TD2 alternative with nonnegative selected A and
E totals is excluded. No sign assumption is made on the TD0 angle or
on either individual error inside a primary pair. -/
theorem all_TD_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤Source.aTotal C ga ab) (he : 0≤Source.eTotal C de eh)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 0∨C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2)) (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  rcases hTD with htd|htd
  · exact TD0.actual_false ga ab de eh hsort hc hcoreT hQ hHy hGy hBy hDy
      hvar ha he hHG hGA hAB hBT htd hDE hEH
  · rcases le_total 0 (delta C.theta T) with hz|hz
    · exact Source.actual_false ga ab de eh hsort hc hQ hHy hGy hBy hDy
        hvar ha hz he hHG hGA hAB hBT htd hDE hEH
    · exact NegativeTD.Source.actual_false ga ab de eh hsort hc hcoreT hQ hHy hGy hBy hDy
        hvar ha he hz hHG hGA hAB hBT htd hDE hEH

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals
