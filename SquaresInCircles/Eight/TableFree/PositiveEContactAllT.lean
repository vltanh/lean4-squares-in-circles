module

public import SquaresInCircles.Eight.TableFree.CriticalPositiveTExclusion
public import SquaresInCircles.Eight.TableFree.ExceptionalNegativeTExclusion
public import SquaresInCircles.Eight.TableFree.PositiveEContactExclusion
public import SquaresInCircles.Eight.TableFree.SoleAllTExclusion

/-!
# Actual positive-E contact normalization for every preprocessed T row

Uncompiled source. The replacement changes only the outer E point at
the original circle and frame. Every T witness and its actual primary
error survive. The zero-tangent endpoint uses the signed sole stress;
the contact endpoint uses the complete positive, negative, or hard T
contact theorem, according to the original error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveEContactAllT
open Candidate SignedCycle PositiveGAOuterSoleReduction PositiveEContact
open ExceptionalContactStress

theorem contact_G_zero {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {q : ℝ} (I : BoundaryInput q)
    (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G) (hD : 0≤delta I.cycle.theta D)
    (hT : TRegime I) (hEy : 0≤(I.cycle.point E).y) (hcontact : Contact I.cycle)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 0) : delta I.cycle.theta G=0 := by
  have hab : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hf := reselect_E (CoreESignedExclusion.original_owners I hHG hGA) hDE hEH
  rcases hT with ⟨hBT,hTD⟩ | ⟨hBT,hTD⟩ | ⟨hBT,hTD,halign⟩
  · rw [hBT,hTD] at hf
    exact ExceptionalEComplete.original_G_zero hd hsharp hQL hq I.necessary I.anchors_normal
      I.positive_variation.le hab hG hD hEy hcontact hf
  · rw [hBT,hTD] at hf
    by_cases ht : delta I.cycle.theta T<0
    · exact ExceptionalNegativeTExclusion.negative_TD_G_zero hd hsharp hQL hq I.necessary
        I.anchors_normal I.positive_variation.le hab hG hD (I.radial T) ht hEy hcontact hf
    · exact (ExceptionalPositiveTComplete.original_G_T_zero hd hsharp true hQL hq
        I.necessary I.anchors_normal I.positive_variation.le hab hG hD
        (by simpa [ExceptionalPositiveTStress.primary] using le_of_not_gt ht) hEy hcontact hf).1
  · rw [hBT,hTD] at hf
    by_cases ht : delta I.cycle.theta B<0
    · exact ExceptionalNegativeTExclusion.negative_BT_G_zero hd hsharp hQL hq I.necessary
        I.anchors_normal I.positive_variation.le hab hG hD (I.radial T) ht (halign ht) hEy hcontact hf
    · exact (ExceptionalPositiveTComplete.original_G_T_zero hd hsharp false hQL hq
        I.necessary I.anchors_normal I.positive_variation.le hab hG hD
        (by simpa [ExceptionalPositiveTStress.primary] using le_of_not_gt ht) hEy hcontact hf).1

theorem replacement_TRegime {q : ℝ} {I : BoundaryInput q} (hcap : q≤qCap)
    (O : Replacement q I.cycle) (hT : TRegime I) : TRegime (O.boundaryInput I hcap) := by
  change ((O.witnesses I.witnesses).owner B=2 ∧ (O.witnesses I.witnesses).owner T=0) ∨
    ((O.witnesses I.witnesses).owner B=2 ∧ (O.witnesses I.witnesses).owner T=2) ∨
    ((O.witnesses I.witnesses).owner B=3 ∧ (O.witnesses I.witnesses).owner T=0 ∧
      (delta O.cycle.theta B<0 → delta O.cycle.theta T=0))
  simpa [Replacement.witnesses,B,T,D,E,O.theta_eq,TRegime] using hT

/-- The full sole-DE branch, including either original E sign. -/
theorem sole_DE_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {q : ℝ} (I : BoundaryInput q)
    (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0<delta I.cycle.theta G) (hD : 0≤delta I.cycle.theta D)
    (hT : TRegime I) (hE : (I.cycle.point E).Outer q)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 0) : False := by
  by_cases hy : (I.cycle.point E).y≤0
  · exact SoleAllTExclusion.sole_DE_nonpos_false I hQL (hq.trans hsharp.2)
      hHG hGA hG.le hT hDE hEH hD hy
  · obtain ⟨O⟩ := PositiveEContact.replace hQL I.necessary hE (lt_of_not_ge hy).le hD hDE hEH
    have hcap := (hq.trans hsharp.2).trans uniform_radius_order.2.2.1.le
    let J := O.boundaryInput I hcap
    have hHG' : J.witnesses.owner H=2 := by
      change (O.witnesses I.witnesses).owner H=2
      simpa [Replacement.witnesses,H,D,E] using hHG
    have hGA' : J.witnesses.owner G=1 := by
      change (O.witnesses I.witnesses).owner G=1
      simpa [Replacement.witnesses,G,D,E] using hGA
    have hG' : 0<delta J.cycle.theta G := by
      change 0<delta O.cycle.theta G
      simpa only [O.theta_eq] using hG
    have hD' : 0≤delta J.cycle.theta D := by
      change 0≤delta O.cycle.theta D
      simpa only [O.theta_eq] using hD
    have hT' : TRegime J := replacement_TRegime hcap O hT
    have hDE' : J.cycle.Feasible D 3 := O.DE_actual
    have hEH' : J.cycle.Feasible E 0 := O.EH_actual
    have hEpoint : J.cycle.point E=O.point := by simp [J,Replacement.boundaryInput,Replacement.cycle,replacePoint]
    rcases O.terminal with hz | he
    · have hy' : (J.cycle.point E).y≤0 := by rw [hEpoint,hz]
      exact SoleAllTExclusion.sole_DE_nonpos_false J hQL (hq.trans hsharp.2)
        hHG' hGA' hG'.le hT' hDE' hEH' hD' hy'
    · have hy' : 0≤(J.cycle.point E).y := by rw [hEpoint]; exact O.nonnegative
      have hc : Contact J.cycle := PositiveEContactExclusion.terminal_contact O he
      have hzero := contact_G_zero hd hsharp J hQL hq hHG' hGA' hG'.le hD' hT' hy' hc hDE' hEH'
      linarith

end SquaresInCircles.Eight.TableFree.PositiveEContactAllT
