module

public import SquaresInCircles.Eight.Owners.Flat.EPreprocess
public import SquaresInCircles.Eight.Frames.Signed.CoreEReduction

/-!
# Eight squares: core-E positive-primary exclusion before E-sign normalization

The charge and the flat secant stress use the original signed E coordinate. With positive GA
(`positive_GA_false`), a nonnegative E-primary total is excluded directly and a negative total
through a constructed same-radius endpoint, for either sign. Physical reflection then gives the
positive-BT case (`positive_BT_false`), including a negative GA primary with aligned HG.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CoreESignedExclusion
open Candidate ActualCoreEBlocks SignedCycle

theorem original_owners {q : ℝ} (I : BoundaryInput q)
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

/-- The T regimes BT2/TD0, BT2/TD2 and BT3/TD0 are impossible for either sign of the original E
tangent and every selected E-primary total. -/
theorem positive_GA_false {q : ℝ} (I : BoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) (hcore : (I.cycle.point E).Core)
    (hHG : I.witnesses.owner H=2) (hGA : I.witnesses.owner G=1)
    (hG : 0≤delta I.cycle.theta G)
    (hT : (I.witnesses.owner B=2 ∧ I.witnesses.owner T=0) ∨
      (I.witnesses.owner B=2 ∧ I.witnesses.owner T=2) ∨
      (I.witnesses.owner B=3 ∧ I.witnesses.owner T=0 ∧
        (delta I.cycle.theta B<0 → delta I.cycle.theta T=0))) : False := by
  have hab : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hde : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
    simpa [normalOwners,D] using I.witnesses.allowed D
  have heh : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
    simpa [normalOwners,E] using I.witnesses.allowed E
  have hf := original_owners I hHG hGA
  by_cases he : 0≤eTotal I.cycle (I.witnesses.owner D) (I.witnesses.owner E)
  · exact CoreENegativeExclusion.preprocessed_core_E_false hqU I.necessary I.anchors_normal
      hcore I.positive_variation.le hab hde heh hG he (I.radial T) hT hf
  · obtain ⟨R⟩ := SignedCoreEReduction.reduce_negative_total I hqL hqU hcore (lt_of_not_ge he)
    let J := R.boundary
    have hHG' : J.witnesses.owner H=2 := by
      rw [R.unchanged_owners H (by decide) (by decide)]
      exact hHG
    have hGA' : J.witnesses.owner G=1 := by
      rw [R.unchanged_owners G (by decide) (by decide)]
      exact hGA
    have hab' : J.witnesses.owner A=0 ∨ J.witnesses.owner A=2 := by
      simpa [normalOwners,A] using J.witnesses.allowed A
    have hde' : J.witnesses.owner D=2 ∨ J.witnesses.owner D=3 := by
      simpa [normalOwners,D] using J.witnesses.allowed D
    have heh' : J.witnesses.owner E=0 ∨ J.witnesses.owner E=1 := by
      simpa [normalOwners,E] using J.witnesses.allowed E
    have hG' : 0≤delta J.cycle.theta G := by
      rw [R.unchanged_errors G (by decide) (by decide)]
      exact hG
    have hT' : (J.witnesses.owner B=2 ∧ J.witnesses.owner T=0) ∨
        (J.witnesses.owner B=2 ∧ J.witnesses.owner T=2) ∨
        (J.witnesses.owner B=3 ∧ J.witnesses.owner T=0 ∧
          (delta J.cycle.theta B<0 → delta J.cycle.theta T=0)) := by
      simpa only [J,R.unchanged_owners B (by decide) (by decide),
        R.unchanged_owners T (by decide) (by decide),
        R.unchanged_errors B (by decide) (by decide),
        R.unchanged_errors T (by decide) (by decide)] using hT
    have hf' := original_owners J hHG' hGA'
    rcases R.normal_form with hnonnegative | ⟨hflat,hDE,hEH⟩
    · exact CoreENegativeExclusion.preprocessed_core_E_false hqU J.necessary J.anchors_normal
        R.core J.positive_variation.le hab' hde' heh' hG' hnonnegative (J.radial T) hT' hf'
    · exact FlatEPreprocess.preprocessed_flat_E_false hqU J.necessary J.anchors_normal
        hflat hDE hEH J.positive_variation.le hab' hde' heh' hG' (J.radial T) hT' hf'

/-- Reflection sends BT3/TD0 to GA1/HG2. The reflected E keeps the sign it gets, with no new
sign normalization. -/
theorem positive_BT_false {q : ℝ} (I : BoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) (hcore : (I.cycle.point E).Core)
    (hBT : I.witnesses.owner B=3) (hTD : I.witnesses.owner T=0)
    (hB : 0≤delta I.cycle.theta B)
    (hG : (I.witnesses.owner G=0 ∧ I.witnesses.owner H=2) ∨
      (I.witnesses.owner G=0 ∧ I.witnesses.owner H=0) ∨
      (I.witnesses.owner G=1 ∧ I.witnesses.owner H=2 ∧
        (delta I.cycle.theta G<0 → delta I.cycle.theta H=0))) : False := by
  simp only [B,T,G,H] at hBT hTD hG
  let J := I.reflected
  have hc : (J.cycle.point E).Core := by
    simpa [J,BoundaryInput.reflected,SignedCycle.reflected,reflectedIndex,E] using hcore
  have hHG : J.witnesses.owner H=2 := by
    simp [J,BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,H,reflectedOwner,hTD]
  have hGA : J.witnesses.owner G=1 := by
    simp [J,BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,G,reflectedOwner,hBT]
  have hd : 0≤delta J.cycle.theta G := by
    simpa [J,BoundaryInput.reflected,reflected_delta,reflectedIndex,next,G,B] using hB
  have hT : (J.witnesses.owner B=2 ∧ J.witnesses.owner T=0) ∨
      (J.witnesses.owner B=2 ∧ J.witnesses.owner T=2) ∨
      (J.witnesses.owner B=3 ∧ J.witnesses.owner T=0 ∧
        (delta J.cycle.theta B<0 → delta J.cycle.theta T=0)) := by
    rcases hG with ⟨hga,hhg⟩ | ⟨hga,hhg⟩ | ⟨hga,hhg,halign⟩
    · left
      simp [J,BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,
        B,T,reflectedOwner,hga,hhg]
    · right; left
      simp [J,BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,
        B,T,reflectedOwner,hga,hhg]
    · right; right
      refine ⟨?_,?_,?_⟩
      · simp [J,BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,
          B,reflectedOwner,hga]
      · simp [J,BoundaryInput.reflected,Witnesses.reflected,reflectedIndex,next,
          T,reflectedOwner,hhg]
      · intro hneg
        have hneg' : delta I.cycle.theta G<0 := by
          simpa [J,BoundaryInput.reflected,reflected_delta,reflectedIndex,next,G,B] using hneg
        simpa [J,BoundaryInput.reflected,reflected_delta,reflectedIndex,next,H,T]
          using halign hneg'
  exact positive_GA_false J hqL hqU hc hHG hGA hd hT


end SquaresInCircles.Eight.CoreESignedExclusion
