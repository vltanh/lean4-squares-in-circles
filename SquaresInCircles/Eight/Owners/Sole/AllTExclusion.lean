module

public import SquaresInCircles.Eight.Owners.Sole.NegativeTExclusion
public import SquaresInCircles.Eight.Owners.Positive.GAOuterSoleReduction

/-!
# Eight squares: the complete T-owner join for sole EH and nonpositive sole DE

This finite dispatch consumes the actual preprocessed
T rows, including the negative-BT alignment produced by preprocessing.
It permits all original ordinary signs and both weak AB owners. Its
sole-DE sign is explicit; the positive-E contact successor is separate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleAllTExclusion
open Candidate SignedCycle PositiveGAOuterSoleReduction

theorem original {q : ℝ} (I : BoundaryInput q) (de : Bool)
    (hQL : qLow≤q) (hQU : q≤qTrial)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G) (hT : TRegime I)
    (hE : 0≤ if de then delta I.cycle.theta D else delta I.cycle.theta E)
    (hsign : de=true → (I.cycle.point E).y≤0)
    (hDE : I.cycle.Feasible D (if de then 3 else 2))
    (hEH : I.cycle.Feasible E (if de then 0 else 1)) : False := by
  have hab : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hf := reselect_E (CoreESignedExclusion.original_owners I hHG hGA) hDE hEH
  rcases hT with ⟨hBT,hTD⟩ | ⟨hBT,hTD⟩ | ⟨hBT,hTD,halign⟩
  · rw [hBT,hTD] at hf
    exact SolePositiveExclusion.original_false de hQL hQU I.necessary I.anchors_normal
      I.positive_variation.le hab hG hE hsign hf
  · rw [hBT,hTD] at hf
    exact SoleNegativeTExclusion.all_TD_false de hQL hQU I.necessary I.anchors_normal
      I.positive_variation.le hab hG hE (I.radial T) hsign hf
  · rw [hBT,hTD] at hf
    exact SoleNegativeTExclusion.all_BT_false de hQL hQU I.necessary I.anchors_normal
      I.positive_variation.le hab hG hE (I.radial T) halign hsign hf

theorem sole_EH_false {q : ℝ} (I : BoundaryInput q)
    (hQL : qLow≤q) (hQU : q≤qTrial)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G) (hT : TRegime I)
    (hDE : I.cycle.Feasible D 2) (hEH : I.cycle.Feasible E 1)
    (hE : 0≤delta I.cycle.theta E) : False :=
  original I false hQL hQU hHG hGA hG hT hE (by intro h; cases h) hDE hEH

theorem sole_DE_nonpos_false {q : ℝ} (I : BoundaryInput q)
    (hQL : qLow≤q) (hQU : q≤qTrial)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G) (hT : TRegime I)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 0)
    (hD : 0≤delta I.cycle.theta D) (hEy : (I.cycle.point E).y≤0) : False :=
  original I true hQL hQU hHG hGA hG hT hD (fun _ => hEy) hDE hEH

end SquaresInCircles.Eight.SoleAllTExclusion
