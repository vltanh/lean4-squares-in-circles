module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDStress

/-!
# The complete original nonnegative A/E, nonpositive-TD2 exclusion

Uncompiled source closure of
`HAND_G3_NONNEGATIVE_A_E_TOTALS_NEGATIVE_TD2_EXCLUSION.md`.
The fixed low-total case and the E-dependent large-total case cover
both closed intervals. Every scalar certificate and sign-concentration
endpoint is supplied internally. The original weak owners are unchanged.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Source
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

/-- The complete original-radius adapter, retaining every supplied
weak axis and deriving all physical anchor and variation premises. -/
theorem frame_all_TD_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (ga ab de eh : Bool)
    (hGA : (forwardAxis (if ga then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if ab then 2 else 0)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square D) ∨
      (forwardAxis 2).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis (if de then 3 else 2)).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis (if eh then 1 else 0)).Feasible (C.square E) (C.square H))
    (ha : 0≤Source.aTotal (SignedCycle.atFrame F) ga ab)
    (he : 0≤Source.eTotal (SignedCycle.atFrame F) de eh) : False := by
  have hn := SignedCycle.atFrame_necessary F
  obtain ⟨hH,hHy,hB,hBy,hD,hDy⟩ := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hhigh : (if ga then (3:Fin 4) else 2)=2∨(if ga then (3:Fin 4) else 2)=3 := by
    cases ga <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    (if ga then 3 else 2) hhigh (by simpa [G,A,next] using hGA)
  let j := SignedCycle.retainedOwner F H
  have hj := (SignedCycle.atFrame_feasible F H j).1 (SignedCycle.retainedOwner_feasible F H)
  have hHG : (SignedCycle.atFrame F).Feasible H 0∨(SignedCycle.atFrame F).Feasible H 2 := by
    rcases GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) j hj with hh|hh
    · have h0 : SignedCycle.retainedOwner F H=0 := hh.1
      exact Or.inl (h0 ▸ SignedCycle.retainedOwner_feasible F H)
    · have h2 : SignedCycle.retainedOwner F H=2 := hh.1
      exact Or.inr (h2 ▸ SignedCycle.retainedOwner_feasible F H)
  have hTD' : (SignedCycle.atFrame F).Feasible T 0∨(SignedCycle.atFrame F).Feasible T 2 := by
    rcases hTD with ht|ht
    · exact Or.inl ((SignedCycle.atFrame_feasible F T 0).2 (by simpa [T,D,next] using ht))
    · exact Or.inr ((SignedCycle.atFrame_feasible F T 2).2 (by simpa [T,D,next] using ht))
  apply all_TD_false ga ab de eh hn.sorted hn.contained (hn.core T) hq.2
    hHy.le ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le hBy.le hDy.le
    (FramePhysicalTransport.candidate_variations F hq).1.le ha he hHG
  · exact (SignedCycle.atFrame_feasible F G _).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A _).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact hTD'
  · exact (SignedCycle.atFrame_feasible F D _).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E _).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals
