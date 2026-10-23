module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3ANormalSource

/-!
# Complete high-GA source exclusion at sole nonnegative BT3 / TD0

Uncompiled final all-A/E source dispatch. Outer E is reselected on the
same actual state. Core E is normalized while the boundary-neighbor
source record is still available. Its nonnegative-total escape and both
single-negative terminals are dispatched before the A-only necessary
transport is used. The original TD0 error remains arbitrary throughout.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Complete
open Candidate Secondary SignedCycle PairedE

theorem reduced_core_false {Q : ℝ} {C : SignedCycle} (I : SourceDomain Q C)
    (hQL : qLow≤Q) (hQU : Q≤qCap) (hEc : (C.point E).Core)
    (hr : CoreENormalForm.Reduced C (I.owner D) (I.owner E))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0) (hz : 0≤delta C.theta B) : False := by
  rcases hr with he|⟨hflat,hnegative⟩
  · obtain ⟨de,hde⟩ : ∃de : Bool,I.owner D=(if de then 3 else 2) := by
      have ho : I.owner D=2∨I.owner D=3 := by simpa [highGAOwners,D] using I.allowed D
      rcases ho with ho|ho
      · exact ⟨false,ho⟩
      · exact ⟨true,ho⟩
    obtain ⟨eh,heh⟩ : ∃eh : Bool,I.owner E=(if eh then 1 else 0) := by
      have ho : I.owner E=0∨I.owner E=1 := by simpa [highGAOwners,E] using I.allowed E
      rcases ho with ho|ho
      · exact ⟨false,ho⟩
      · exact ⟨true,ho⟩
    have hDE : C.Feasible D (if de then 3 else 2) := by simpa [hde] using I.feasible D
    have hEH : C.Feasible E (if eh then 1 else 0) := by simpa [heh] using I.feasible E
    have he' : 0≤cycleTotal C de eh := by
      rw [hde,heh,CoreENegativeTotal.selected_total] at he
      exact he
    exact prepared_false I hQL hQU de eh hDE hEH (Or.inl he') hBT hTD hz
  · rcases hnegative with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · have hDE : C.Feasible D 3 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 0 := by simpa [heh] using I.feasible E
      exact prepared_false I hQL hQU true false hDE hEH
        (Or.inr ⟨hflat,Or.inl ⟨rfl,rfl,hd⟩⟩) hBT hTD hz
    · have hDE : C.Feasible D 2 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 1 := by simpa [heh] using I.feasible E
      by_cases hEH0 : C.Feasible E 0
      · exact prepared_false I hQL hQU false false hDE hEH0
          (Or.inl (by simp [cycleTotal,total,selected])) hBT hTD hz
      · obtain ⟨_,hb,hcap⟩ := NegativeEHPositiveTD.Source.genuine_domain
          I.necessary.sorted I.necessary.contained hQU I.H_positive.le I.E_nonpos hEc
          I.positive_variation.le he hEH hEH0
        exact prepared_false I hQL hQU false true hDE hEH
          (Or.inr ⟨hflat,Or.inr ⟨rfl,rfl,he,hcap,hb⟩⟩) hBT hTD hz

/-- Every source A total, every E radial kind and every E owner/sign are
included. This theorem needs no designated A/E normal form as input. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (I : SourceDomain Q C)
    (hQL : qLow≤Q) (hQU : Q≤qCap)
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0) (hz : 0≤delta C.theta B) : False := by
  rcases I.radial E with houter|hcore
  · let S := OuterE.select I hQU houter
    exact prepared_false I hQL hQU S.de S.eh S.DE S.EH
      (Or.inl S.total_nonneg) hBT hTD hz
  · obtain ⟨O⟩ := CoreENormalForm.reduce I hQL hQU hcore
    have hBT' := (O.other_feasible B (by norm_num [B,D]) (by norm_num [B,E]) 3).2 hBT
    have hTD' := (O.other_feasible T (by norm_num [T,D]) (by norm_num [T,E]) 0).2 hTD
    have hz' : 0≤delta O.cycle.theta B := by
      rw [O.other_delta B (by norm_num [B,D]) (by norm_num [B,E])]
      exact hz
    exact reduced_core_false O.source hQL hQU O.E_core O.reduced hBT' hTD' hz'

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Complete
