module

public import SquaresInCircles.Eight.TableFree.CriticalEExclusion
public import SquaresInCircles.Eight.TableFree.SolePositiveExclusion

/-!
# The sole positive DE primary, with either original E sign

Uncompiled source. A nonpositive E uses the signed sole-DE stress.
A positive outer E is moved only on its original q circle, with every
frame unchanged. Its actual endpoint is either zero tangent or exact
EH0 contact. The complete sharp contact theorem handles the latter.
No E-sign preservation is assumed for the preceding paired transport.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveEContactExclusion
open Candidate PositiveEContact ExceptionalContactStress

theorem moved_owners {q : ℝ} {C : SignedCycle} (O : Replacement q C) {ab : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) :
    ∀ i,O.cycle.Feasible i (CoreEStress.owners ab 2 0 3 0 i) := by
  intro i
  by_cases hiD : i=D
  · subst i; simpa [CoreEStress.owners,D] using O.DE_actual
  · by_cases hiE : i=E
    · subst i; simpa [CoreEStress.owners,E] using O.EH_actual
    · exact (O.other_feasible i hiD hiE _).2 (hf i)

theorem terminal_contact {q : ℝ} {C : SignedCycle} (O : Replacement q C)
    (he : O.point.y=demand (C.point H) (delta C.theta E)) : Contact O.cycle := by
  dsimp [Contact]
  rw [O.theta_eq,O.unchanged H (by decide)]
  have hE : O.cycle.point E=O.point := by simp [Replacement.cycle,replacePoint]
  rw [hE,he]
  dsimp [demand]
  ring

/-- All signs of an actual outer E are covered at the sharp radius.
The strictly positive original G error is the only strict angle input. -/
theorem sole_DE_false {d : ExactFamily.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0<delta C.theta G) (hD : 0≤delta C.theta D)
    (hE : (C.point E).Outer q)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : False := by
  by_cases hy : (C.point E).y≤0
  · exact SolePositiveExclusion.sole_DE_false hQL (hq.trans hsharp.2) hC hn hvar hab hG.le hD hy hf
  · have hDE : C.Feasible D 3 := by simpa [CoreEStress.owners,D] using hf D
    have hEH : C.Feasible E 0 := by simpa [CoreEStress.owners,E] using hf E
    obtain ⟨O⟩ := PositiveEContact.replace hQL hC hE (lt_of_not_ge hy).le hD hDE hEH
    have hnec := O.necessary hC
    have hnormal := O.normal hn
    have hvar' : positiveVariation O.cycle.theta≤frameCap := by simpa only [O.theta_eq] using hvar
    have hG' : 0<delta O.cycle.theta G := by simpa only [O.theta_eq] using hG
    have hD' : 0≤delta O.cycle.theta D := by simpa only [O.theta_eq] using hD
    have hf' := moved_owners O hf
    have hEpoint : O.cycle.point E=O.point := by simp [Replacement.cycle,replacePoint]
    rcases O.terminal with hz | hcontact
    · have hy' : (O.cycle.point E).y≤0 := by rw [hEpoint,hz]
      exact SolePositiveExclusion.sole_DE_false hQL (hq.trans hsharp.2) hnec hnormal hvar'
        hab hG'.le hD' hy' hf'
    · have hy' : 0≤(O.cycle.point E).y := by rw [hEpoint]; exact O.nonnegative
      have hzero := ExceptionalEComplete.original_G_zero hd hsharp hQL hq hnec hnormal hvar'
        hab hG'.le hD' hy' (terminal_contact O hcontact) hf'
      linarith

end SquaresInCircles.Eight.TableFree.PositiveEContactExclusion
