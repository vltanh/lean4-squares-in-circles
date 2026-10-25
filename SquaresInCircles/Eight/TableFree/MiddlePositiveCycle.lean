module

public import SquaresInCircles.Eight.TableFree.MiddlePositiveContraction
public import SquaresInCircles.Eight.TableFree.NecessaryCycle

/-!
# A genuine positive-AB-error reduction of a hard necessary cycle

Uncompiled draft.  The original positive AB0 error is removed by the
explicit B contraction.  Only B's center and frame change.  Its new frame
is the original A frame, so the real frame interval cannot expand.  The
strict circle loss is at the anchor B and retains every earlier B loss.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate MiddlePositiveContraction
namespace SignedCycle

def replaceB (C : SignedCycle) (P : SignedPoint) : SignedCycle :=
  replacePoint C B P (C.theta A)

theorem replaceB_unchanged (C : SignedCycle) (P : SignedPoint)
    (i : Vertex) (hi : i ≠ B) :
    (replaceB C P).point i=C.point i ∧ (replaceB C P).theta i=C.theta i := by
  simp [replaceB,replacePoint,hi]

theorem replaceB_spread {C : SignedCycle} (h : C.Spread) (P : SignedPoint) :
    (replaceB C P).Spread := by
  intro i j
  by_cases hi : i=B <;> by_cases hj : j=B
  · subst i; subst j
    simpa [replaceB,replacePoint] using h A A
  · subst i
    simpa [replaceB,replacePoint,hj] using h A j
  · subst j
    simpa [replaceB,replacePoint,hi] using h i A
  · simpa [replaceB,replacePoint,hi,hj] using h i j

theorem replaceB_AB (C : SignedCycle) (P : SignedPoint) (j : Fin 4) :
    (replaceB C P).Feasible A j ↔ zeroFeasible (C.point A) P 0 j := by
  simp [replaceB,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,A,B,
    zeroFeasible,sub_nonneg]

theorem replaceB_BT (C : SignedCycle) (P : SignedPoint) (j : Fin 4) :
    (replaceB C P).Feasible B j ↔
      quarterFeasible P (C.point T) (C.theta T-C.theta A) j := by
  simp [replaceB,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,A,B,T,
    quarterFeasible,sub_nonneg]

theorem replaceB_slack_other (C : SignedCycle) (P : SignedPoint)
    (i : Vertex) (hi : i ≠ B) (hn : next i ≠ B) (j : Fin 4) :
    (replaceB C P).slack i j=C.slack i j := by
  simp [replaceB,replacePoint,slack,edge,delta,hi,hn]

def Witnesses.replaceB {C : SignedCycle} (w : C.Witnesses)
    (O : BContraction (C.point A) (C.point B) (C.point T) (C.theta A-C.theta T)) :
    (SignedCycle.replaceB C O.point).Witnesses where
  owner i := if i=B then 2 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · exact (replacePoint_other_feasible (v := B) (by decide : H ≠ B)
        (by decide : next H ≠ B)).2 (w.feasible H)
    · exact (replacePoint_other_feasible (v := B) (by decide : G ≠ B)
        (by decide : next G ≠ B)).2 (w.feasible G)
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      show (SignedCycle.replaceB C O.point).Feasible A (w.owner A)
      rcases hj with hj | hj
      · rw [hj]; exact (replaceB_AB C O.point _).2 O.AB_zero
      · rw [hj]; exact (replaceB_AB C O.point _).2 O.AB_two
    · apply (replaceB_BT C O.point 2).2
      unfold quarterFeasible
      have hh := O.BT_exact.symm.le
      simpa only [neg_sub] using hh
    · exact (replacePoint_other_feasible (v := B) (by decide : T ≠ B)
        (by decide : next T ≠ B)).2 (w.feasible T)
    · exact (replacePoint_other_feasible (v := B) (by decide : D ≠ B)
        (by decide : next D ≠ B)).2 (w.feasible D)
    · exact (replacePoint_other_feasible (v := B) (by decide : E ≠ B)
        (by decide : next E ≠ B)).2 (w.feasible E)
  allowed := by
    intro i
    by_cases hi : i=B
    · subst i; norm_num [normalOwners,B]
    · simpa [hi] using w.allowed i

def HardInput.fromPositiveMiddle {q : ℝ} (I : HardInput q)
    (O : BContraction (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta A-I.cycle.theta T)) : HardInput q where
  cycle := SignedCycle.replaceB I.cycle O.point
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=B
      · subst i; simpa [replaceB,replacePoint] using O.sorted
      · simpa [replaceB,replacePoint,hi] using I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=B
      · subst i
        have hh := O.circle_lt.le.trans (I.necessary.contained B)
        simpa [replaceB,replacePoint,SignedPoint.Contained] using hh
      · simpa [replaceB,replacePoint,hi] using I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=B
      · subst i; simpa [replaceB,replacePoint] using O.avoids
      · simpa [replaceB,replacePoint,hi] using I.necessary.core i
    spread := replaceB_spread I.necessary.spread O.point }
  anchors_normal := by
    constructor
    · simpa [replaceB,replacePoint,H,B] using I.anchors_normal.H_nonneg
    · simpa [replaceB,replacePoint,A,B] using I.anchors_normal.A_nonneg
    · simpa [replaceB,replacePoint] using O.normal.le
    · simpa [replaceB,replacePoint,D,B] using I.anchors_normal.D_nonpos
  E_nonpos := by simpa [replaceB,replacePoint,E,B] using I.E_nonpos
  witnesses := I.witnesses.replaceB O
  GA_hard := (replacePoint_other_feasible (v := B) (by decide : G ≠ B)
    (by decide : next G ≠ B)).2 I.GA_hard
  BT_hard := by
    apply (replaceB_BT I.cycle O.point 2).2
    unfold quarterFeasible
    simpa only [neg_sub] using O.BT_exact.symm.le
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.replaceB,H,B] using hh
      simpa [replaceB,replacePoint,G,B] using I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.replaceB,T,B] using hh
      simpa [replaceB,replacePoint,T,B] using I.zero_signs.TD_canceling hj }
  E_radial := by simpa [replaceB,replacePoint,H,D,E,B] using I.E_radial

theorem HardInput.positive_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta A < I.cycle.theta B)
    (hγ : I.cycle.theta T ≤ I.cycle.theta A)
    (hAB : I.cycle.Feasible A 0) :
    Nonempty (BContraction (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta A-I.cycle.theta T)) := by
  have hspan : (I.cycle.theta A-I.cycle.theta T)+
      (I.cycle.theta B-I.cycle.theta A) ≤ 7/10 := by
    have hh := I.necessary.spread B T
    have ha := le_abs_self (I.cycle.theta B-I.cycle.theta T)
    dsimp [frameCap] at hh
    linarith
  have hAB' : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-((I.cycle.theta A-I.cycle.theta T)+(I.cycle.theta B-I.cycle.theta A))) 2 := by
    rw [show -((I.cycle.theta A-I.cycle.theta T)+
      (I.cycle.theta B-I.cycle.theta A))=I.cycle.theta T-I.cycle.theta B by ring]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  exact actual_B_contraction (I.necessary.sorted A) (I.necessary.core A)
    ((I.necessary.contained A).trans hq) (I.necessary.sorted B)
    ((I.necessary.contained B).trans hq) I.anchors_normal.A_nonneg
    I.anchors_normal.B_nonpos hyT (sub_nonneg.mpr hγ) (sub_pos.mpr hd)
    hspan hAB' hBT'

/-- A nonzero original AB0 error in this frame sector has an actual hard
descendant with the original A frame and a strict B-anchor circle loss. -/
theorem HardInput.align_positive_AB0 {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta A < I.cycle.theta B)
    (hγ : I.cycle.theta T ≤ I.cycle.theta A)
    (hAB : I.cycle.Feasible A 0) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta B=I.cycle.theta A ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.positive_middle_contraction hq hyT hd hγ hAB
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

end SignedCycle
end SquaresInCircles.Eight.TableFree
