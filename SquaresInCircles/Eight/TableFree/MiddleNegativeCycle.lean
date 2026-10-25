module

public import SquaresInCircles.Eight.TableFree.MiddleNegativeContraction
public import SquaresInCircles.Eight.TableFree.MiddlePositiveCycle

/-!
# A genuine negative-AB-error reduction of a hard necessary cycle

Uncompiled draft.  An original negative AB0 error contracts B to A's
frame when T is at or below B.  Only B changes, its actual original
circle strictly decreases, and every original nonincident owner witness
is retained.  Together with the positive-error reduction, this handles
both nonzero AB0 signs when T is below both middle frames.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate MiddlePositiveContraction
namespace SignedCycle

theorem HardInput.negative_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hT : I.cycle.theta T ≤ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 0) :
    Nonempty (BContraction (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta A-I.cycle.theta T)) := by
  have hγu : I.cycle.theta A-I.cycle.theta T ≤ 7/10 := by
    have hh := I.necessary.spread A T
    have ha := le_abs_self (I.cycle.theta A-I.cycle.theta T)
    dsimp [frameCap] at hh
    linarith
  have hAB' : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (-(I.cycle.theta A-I.cycle.theta B)) 0 := by
    rw [neg_sub]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-((I.cycle.theta A-I.cycle.theta T)-(I.cycle.theta A-I.cycle.theta B))) 2 := by
    rw [show -((I.cycle.theta A-I.cycle.theta T)-
      (I.cycle.theta A-I.cycle.theta B))=I.cycle.theta T-I.cycle.theta B by ring]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  exact MiddleNegativeContraction.actual_B_contraction
    (I.necessary.sorted A) (I.necessary.core A)
    ((I.necessary.contained A).trans hq) (I.necessary.sorted B)
    ((I.necessary.contained B).trans hq) I.anchors_normal.A_nonneg
    I.anchors_normal.B_nonpos hyT (sub_pos.mpr hd)
    (show I.cycle.theta A-I.cycle.theta B ≤ I.cycle.theta A-I.cycle.theta T by linarith)
    hγu hAB' hBT'

/-- The original negative AB0 error gives a full same-q hard descendant
with a strict loss on B's original circle.  The constructor used here
depends only on the proved concrete contact output, not its error sign. -/
theorem HardInput.align_negative_AB0 {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hT : I.cycle.theta T ≤ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 0) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta B=I.cycle.theta A ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.negative_middle_contraction hq hyT hd hT hAB
  refine ⟨I.fromPositiveMiddle O,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [HardInput.fromPositiveMiddle,replaceB,replacePoint,A,B]
  · simp [HardInput.fromPositiveMiddle,replaceB,replacePoint]
  · simpa [HardInput.fromPositiveMiddle,replaceB,replacePoint,A,B] using O.AB_exact
  · simpa [HardInput.fromPositiveMiddle,replaceB,replacePoint] using O.circle_lt
  · intro i hi
    by_cases hb : i=B
    · subst i
      simpa [HardInput.fromPositiveMiddle,replaceB,replacePoint] using O.circle_lt.le
    · exact (congrArg SignedPoint.circle (replaceB_unchanged I.cycle O.point i hb).1).le
  · refine ⟨B,by simp [anchorVertices],?_⟩
    simpa [HardInput.fromPositiveMiddle,replaceB,replacePoint] using O.circle_lt
  · exact replaceB_unchanged I.cycle O.point

/-- Both original AB0 signs are now covered when T is below the two
middle frames.  A nonzero error is charged to B, never to free T. -/
theorem HardInput.align_nonzero_AB0_above_T {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hT : I.cycle.theta T ≤ min (I.cycle.theta A) (I.cycle.theta B))
    (hne : I.cycle.theta A ≠ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 0) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta B=I.cycle.theta A ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  rcases lt_or_gt_of_ne hne with hpos | hneg
  · exact I.align_positive_AB0 hq hyT hpos (hT.trans (min_le_left _ _)) hAB
  · exact I.align_negative_AB0 hq hyT hneg (hT.trans (min_le_right _ _)) hAB

end SignedCycle
end SquaresInCircles.Eight.TableFree
