module

public import SquaresInCircles.Eight.Owners.Negative.CoreEReduction

/-!
# Eight squares: actual core-E reduction with either original tangent sign

Reflection is used to invoke the local E construction,
then undone. The returned boundary cycle has the original common radius,
all six original non-E points, all five nonincident owners and errors,
and no larger positive or negative variation. The harmless common frame
offset from two reflections is not mistaken for a changed edge error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCoreEReduction
open Candidate ActualCoreEBlocks NegativeCoreE SignedCycle

theorem reflected_primary_DE (C : SignedCycle) {eh : Fin 4}
    (heh : eh=0 ∨ eh=1) :
    primaryDE C.reflected (reflectedOwner eh)=primaryEH C eh := by
  rcases heh with rfl | rfl <;>
    simp [primaryDE,primaryEH,reflectedOwner,reflected_delta,reflectedIndex,next,D,E]

theorem reflected_primary_EH (C : SignedCycle) {de : Fin 4}
    (hde : de=2 ∨ de=3) :
    primaryEH C.reflected (reflectedOwner de)=primaryDE C de := by
  rcases hde with rfl | rfl <;>
    simp [primaryDE,primaryEH,reflectedOwner,reflected_delta,reflectedIndex,next,D,E]

theorem boundary_primary_DE {q : ℝ} (I : BoundaryInput q) :
    primaryDE I.reflected.cycle (I.reflected.witnesses.owner D)=
      primaryEH I.cycle (I.witnesses.owner E) := by
  change primaryDE I.cycle.reflected (reflectedOwner (I.witnesses.owner E))=_
  apply reflected_primary_DE
  simpa [normalOwners,E] using I.witnesses.allowed E

theorem boundary_primary_EH {q : ℝ} (I : BoundaryInput q) :
    primaryEH I.reflected.cycle (I.reflected.witnesses.owner E)=
      primaryDE I.cycle (I.witnesses.owner D) := by
  change primaryEH I.cycle.reflected (reflectedOwner (I.witnesses.owner D))=_
  apply reflected_primary_EH
  simpa [normalOwners,D] using I.witnesses.allowed D

theorem boundary_total {q : ℝ} (I : BoundaryInput q) :
    eTotal I.reflected.cycle (I.reflected.witnesses.owner D) (I.reflected.witnesses.owner E)=
      eTotal I.cycle (I.witnesses.owner D) (I.witnesses.owner E) := by
  rw [eTotal,boundary_primary_DE,boundary_primary_EH,eTotal,add_comm]

structure Endpoint (q : ℝ) (I : BoundaryInput q) where
  boundary : BoundaryInput q
  core : (boundary.cycle.point E).Core
  unchanged_points : ∀ i,i≠E → boundary.cycle.point i=I.cycle.point i
  unchanged_errors : ∀ i,i≠D → i≠E → delta boundary.cycle.theta i=delta I.cycle.theta i
  unchanged_owners : ∀ i,i≠D → i≠E → boundary.witnesses.owner i=I.witnesses.owner i
  positive_nonincrease : positiveVariation boundary.cycle.theta≤positiveVariation I.cycle.theta
  negative_nonincrease : negativeVariation boundary.cycle.theta≤negativeVariation I.cycle.theta
  normal_form :
    0≤eTotal boundary.cycle (boundary.witnesses.owner D) (boundary.witnesses.owner E) ∨
    ((boundary.cycle.point E).a=7/12 ∧
      primaryDE boundary.cycle (boundary.witnesses.owner D)≤0 ∧
      primaryEH boundary.cycle (boundary.witnesses.owner E)≤0)

def Endpoint.ofNormalized {q : ℝ} {I : NormalizedBoundaryInput q}
    (hq : q≤qCap) (R : Reduction q I) : Endpoint q I.toBoundaryInput where
  boundary := (R.move.boundaryInput I hq).toBoundaryInput
  core := by
    simpa [CycleMove.boundaryInput,CycleMove.cycle,replacePoint] using R.move.core
  unchanged_points i hi := (R.move.unchanged i hi).1
  unchanged_errors := R.move.other_delta
  unchanged_owners := R.move.other_owner I.witnesses
  positive_nonincrease := R.move.positive_nonincrease
  negative_nonincrease := R.move.negative_nonincrease
  normal_form := by
    simpa [CycleMove.boundaryInput,CycleMove.witnesses,CycleMove.cycle,replacePoint,D,E]
      using R.normal_form

/-- Return from a reduction on the reflected triple. All nonincident
original data are recovered, even though absolute frames acquire an offset. -/
def Endpoint.returnFromReflection {q : ℝ} {I : BoundaryInput q}
    (R : Endpoint q I.reflected) : Endpoint q I where
  boundary := R.boundary.reflected
  core := by
    simpa [BoundaryInput.reflected,SignedCycle.reflected,reflectedIndex,E] using R.core
  unchanged_points i hi := by
    have hj : reflectedIndex i≠E := by
      revert hi; fin_cases i <;> decide
    change (R.boundary.cycle.point (reflectedIndex i)).reflect=I.cycle.point i
    rw [R.unchanged_points _ hj]
    change (I.cycle.point (reflectedIndex (reflectedIndex i))).reflect.reflect=I.cycle.point i
    simp
  unchanged_errors i hiD hiE := by
    have hjD : reflectedIndex (next i)≠D := by
      revert hiD hiE; fin_cases i <;> decide
    have hjE : reflectedIndex (next i)≠E := by
      revert hiD hiE; fin_cases i <;> decide
    change delta R.boundary.cycle.reflected.theta i=delta I.cycle.theta i
    rw [reflected_delta,R.unchanged_errors _ hjD hjE]
    change delta I.cycle.reflected.theta (reflectedIndex (next i))=delta I.cycle.theta i
    rw [reflected_delta,reflectedIndex_next,reflectedIndex_involutive]
  unchanged_owners i hiD hiE := by
    have hjD : reflectedIndex (next i)≠D := by
      revert hiD hiE; fin_cases i <;> decide
    have hjE : reflectedIndex (next i)≠E := by
      revert hiD hiE; fin_cases i <;> decide
    change reflectedOwner (R.boundary.witnesses.owner (reflectedIndex (next i)))=
      I.witnesses.owner i
    rw [R.unchanged_owners _ hjD hjE]
    change reflectedOwner (reflectedOwner
      (I.witnesses.owner (reflectedIndex (next (reflectedIndex (next i))))))=I.witnesses.owner i
    simp only [reflectedOwner_involutive,reflectedIndex_next,reflectedIndex_involutive]
  positive_nonincrease := by
    change positiveVariation R.boundary.cycle.reflected.theta≤positiveVariation I.cycle.theta
    rw [reflected_positiveVariation]
    simpa [BoundaryInput.reflected,reflected_positiveVariation] using R.positive_nonincrease
  negative_nonincrease := by
    change negativeVariation R.boundary.cycle.reflected.theta≤negativeVariation I.cycle.theta
    rw [reflected_negativeVariation]
    simpa [BoundaryInput.reflected,reflected_negativeVariation] using R.negative_nonincrease
  normal_form := by
    rcases R.normal_form with h | ⟨hflat,hDE,hEH⟩
    · left
      rw [boundary_total]
      exact h
    · right
      refine ⟨?_,?_,?_⟩
      · simpa [BoundaryInput.reflected,SignedCycle.reflected,reflectedIndex,E,SignedPoint.reflect]
          using hflat
      · rw [boundary_primary_DE]
        exact hEH
      · rw [boundary_primary_EH]
        exact hDE

/-- The only source premises are the actual boundary data, the original
core label, and the sign of the selected primary total. -/
theorem reduce_negative_total {q : ℝ} (I : BoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) (hc : (I.cycle.point E).Core)
    (hneg : eTotal I.cycle (I.witnesses.owner D) (I.witnesses.owner E)<0) :
    Nonempty (Endpoint q I) := by
  by_cases hy : (I.cycle.point E).y≤0
  · let J : NormalizedBoundaryInput q := { toBoundaryInput := I, E_nonpos := hy }
    obtain ⟨R⟩ := NegativeCoreE.reduce_negative_total J hqL hqU hc hneg
    exact ⟨Endpoint.ofNormalized hqU R⟩
  · have hy' : (I.reflected.cycle.point E).y≤0 := by
      change -(I.cycle.point E).y≤0
      linarith
    let J : NormalizedBoundaryInput q := { toBoundaryInput := I.reflected, E_nonpos := hy' }
    have hc' : (J.cycle.point E).Core := by
      simpa [J,BoundaryInput.reflected,SignedCycle.reflected,reflectedIndex,E] using hc
    have hneg' : eTotal J.cycle (J.witnesses.owner D) (J.witnesses.owner E)<0 := by
      change eTotal I.reflected.cycle
        (I.reflected.witnesses.owner D) (I.reflected.witnesses.owner E)<0
      rw [boundary_total]
      exact hneg
    obtain ⟨R⟩ := NegativeCoreE.reduce_negative_total J hqL hqU hc' hneg'
    exact ⟨(Endpoint.ofNormalized hqU R).returnFromReflection⟩

end SquaresInCircles.Eight.SignedCoreEReduction
