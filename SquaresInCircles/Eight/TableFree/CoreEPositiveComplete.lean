module

public import SquaresInCircles.Eight.TableFree.FlatEPreprocess
public import SquaresInCircles.Eight.TableFree.NegativeCoreEReduction

/-!
# Positive GA with core E, without any E-primary sign restriction

Uncompiled source. A negative total is reduced by the actual geometric
E construction at the original q. Its endpoint either enters the proved
nonnegative-total stress or the proved flat-negative stress. All six
other points and the four nonincident T/G/A/B errors are retained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CoreEPositiveComplete
open Candidate ActualCoreEBlocks NegativeCoreE

theorem original_owners {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1) :
    ∀ i,I.cycle.Feasible i (CoreEStress.owners (I.witnesses.owner A) (I.witnesses.owner B)
      (I.witnesses.owner T) (I.witnesses.owner D) (I.witnesses.owner E) i) := by
  intro i
  fin_cases i
  · have h := I.witnesses.feasible H
    rw [hHG] at h
    exact h
  · have h := I.witnesses.feasible G
    rw [hGA] at h
    exact h
  · exact I.witnesses.feasible A
  · exact I.witnesses.feasible B
  · exact I.witnesses.feasible T
  · exact I.witnesses.feasible D
  · exact I.witnesses.feasible E

theorem moved_owners {q : ℝ} {C : SignedCycle} (O : CycleMove q C)
    {ab bt td de eh : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i)) :
    ∀ i,O.cycle.Feasible i (CoreEStress.owners ab bt td O.de O.eh i) := by
  intro i
  by_cases hiD : i=D
  · subst i
    exact O.DE_actual
  · by_cases hiE : i=E
    · subst i
      exact O.EH_actual
    · apply (O.other_feasible i hiD hiE _).2
      fin_cases i
      · have h := hf H
        change C.Feasible H 2 at h
        exact h
      · have h := hf G
        change C.Feasible G 1 at h
        exact h
      · have h := hf A
        change C.Feasible A ab at h
        exact h
      · have h := hf B
        change C.Feasible B bt at h
        exact h
      · have h := hf T
        change C.Feasible T td at h
        exact h
      · exact absurd rfl hiD
      · exact absurd rfl hiE

theorem normalized_core_E_false {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) (hcore : (I.cycle.point E).Core)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G)
    (hT : (I.witnesses.owner B=2 ∧ I.witnesses.owner T=0) ∨
      (I.witnesses.owner B=2 ∧ I.witnesses.owner T=2) ∨
      (I.witnesses.owner B=3 ∧ I.witnesses.owner T=0 ∧
        (delta I.cycle.theta B<0 → delta I.cycle.theta T=0))) : False := by
  have hab : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [SignedCycle.normalOwners,A] using I.witnesses.allowed A
  have hde : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
    simpa [SignedCycle.normalOwners,D] using I.witnesses.allowed D
  have heh : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
    simpa [SignedCycle.normalOwners,E] using I.witnesses.allowed E
  have hf := original_owners I hHG hGA
  by_cases he : 0≤eTotal I.cycle (I.witnesses.owner D) (I.witnesses.owner E)
  · exact CoreENegativeExclusion.preprocessed_core_E_false hqU I.necessary I.anchors_normal
      hcore I.positive_variation.le hab hde heh hG he (I.radial T) hT hf
  · obtain ⟨R⟩ := reduce_negative_total I hqL hqU hcore (lt_of_not_ge he)
    let O := R.move
    have hnec := O.necessary I.necessary
    have hnormal := O.normal I.anchors_normal
    have hcore' : (O.cycle.point E).Core := by
      simpa [CycleMove.cycle,replacePoint] using O.core
    have hy' : (O.cycle.point E).y≤0 := by
      simpa [CycleMove.cycle,replacePoint] using O.nonpos
    have hvar : positiveVariation O.cycle.theta≤frameCap :=
      O.positive_nonincrease.trans I.positive_variation.le
    have hG' : 0≤delta O.cycle.theta G := by
      rw [O.other_delta G (by decide) (by decide)]
      exact hG
    have hTb : (O.cycle.point T).Boundary q := by
      rw [(O.unchanged T (by decide)).1]
      exact I.radial T
    have hT' : (I.witnesses.owner B=2 ∧ I.witnesses.owner T=0) ∨
        (I.witnesses.owner B=2 ∧ I.witnesses.owner T=2) ∨
        (I.witnesses.owner B=3 ∧ I.witnesses.owner T=0 ∧
          (delta O.cycle.theta B<0 → delta O.cycle.theta T=0)) := by
      simpa only [O.other_delta B (by decide) (by decide),
        O.other_delta T (by decide) (by decide)] using hT
    have hf' := moved_owners O hf
    rcases R.normal_form with hnonnegative | ⟨hflat,hDE,hEH⟩
    · exact CoreENegativeExclusion.preprocessed_core_E_false hqU hnec hnormal hcore'
        hvar hab O.de_allowed O.eh_allowed hG' hnonnegative hTb hT' hf'
    · have hflat' : (O.cycle.point E).a=7/12 := by
        simpa [O,CycleMove.cycle,replacePoint] using hflat
      exact FlatEPreprocess.preprocessed_flat_E_false hqU hnec hnormal hflat' hDE hEH
        hvar hab O.de_allowed O.eh_allowed hG' hTb hT' hf'

end SquaresInCircles.Eight.TableFree.CoreEPositiveComplete
