module

public import SquaresInCircles.Eight.Words.Middle.NegativeContraction
public import SquaresInCircles.Eight.Owners.NecessaryCycle

/-!
# Eight squares: a negative-AB-error reduction of a hard necessary cycle

An original negative AB0 error contracts B to A's frame when T is at or below B
(`HardInput.negative_middle_contraction`). Only B changes, its original circle strictly
decreases, and every original nonincident owner witness is kept. Together with the
positive-error reduction, this handles both nonzero AB0 signs when T is below both middle
frames.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
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

end SignedCycle
end SquaresInCircles.Eight
