module

public import SquaresInCircles.Eight.Owners.Critical.PositiveTExclusion
public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTExclusion
public import SquaresInCircles.Eight.Owners.Positive.NoncancelingCycle
public import SquaresInCircles.Eight.Owners.Sole.AllTExclusion
public import SquaresInCircles.Eight.Owners.Stationary.SourceOwners

/-!
# Eight squares: no positive GA terminal, for every preprocessed T row

The reduction of E gives a sole primary at the same radius, keeping the positive G error and the
selected row of T (`PositiveGAOuterSoleReduction.original`). Both sole directions are excluded,
the sole-DE one through the positive-E contact, for every signed error of T
(`original_boundary_false`, `original_false`).
-/

section
/-!
## The positive-E contact for every preprocessed T row

The replacement changes only the outer point E, on its circle and at its frame; every T witness and
its primary error stay (`replacement_TRegime`). The endpoint at zero tangent uses the signed sole
stress, and the contact endpoint uses the positive, negative or hard contact theorem of T,
according to the error (`contact_G_zero`). So the sole-DE branch is excluded for either sign of E
(`sole_DE_false`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveEContactAllT
open Candidate SignedCycle PositiveGAOuterSoleReduction PositiveEContact
open ExceptionalContactStress

theorem contact_G_zero {d : Stationary.Coordinates} (hd : d.IsStationary)
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

/-- The sole-DE branch of a positive GA terminal is impossible, for either sign of E. -/
theorem sole_DE_false {d : Stationary.Coordinates} (hd : d.IsStationary)
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

end SquaresInCircles.Eight.PositiveEContactAllT
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveGAAllTExclusion
open Candidate SignedCycle PositiveGAOuterSoleReduction

theorem original_boundary_false {d : Stationary.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : BoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0<delta I.cycle.theta G) (hT : TRegime I) : False := by
  have hsharp := StationaryOriginalReductions.sharp_interval hd
  have hcap := (hq.trans hsharp.2).trans uniform_radius_order.2.2.1.le
  obtain ⟨O⟩ := PositiveGAOuterSoleReduction.original I hQL hcap hHG hGA hG hT
  rcases O.sole with ⟨hDE,hEH,he⟩ | ⟨hDE,hEH,he⟩
  · exact SoleAllTExclusion.sole_EH_false O.boundary hQL (hq.trans hsharp.2)
      O.HG O.GA O.G_positive.le O.T_regime hDE hEH he.le
  · exact PositiveEContactAllT.sole_DE_false hd hsharp O.boundary hQL hq
      O.HG O.GA O.G_positive he.le O.T_regime O.E_outer hDE hEH

theorem original_false {d : Stationary.Coordinates} (hd : d.IsStationary)
    {q : ℝ} (I : NormalizedBoundaryInput q) (hQL : qLow≤q) (hq : q≤d.q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0<delta I.cycle.theta G) (hT : TRegime I.toBoundaryInput) : False :=
  original_boundary_false hd I.toBoundaryInput hQL hq hHG hGA hG hT

end SquaresInCircles.Eight.PositiveGAAllTExclusion
end
end
end
