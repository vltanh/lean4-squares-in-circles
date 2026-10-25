module

public import SquaresInCircles.Eight.TableFree.MiddleBelowCycle
public import SquaresInCircles.Eight.TableFree.MiddleCrossingReflectedCycle

/-!
# Negative AB2 errors in every frame order

Uncompiled draft.  The last negative-AB2 sector is the exact local
reflection of the explicit below-T AB0 construction.  Its full hard
descendant changes A alone, including when the aligned frame is above G.
The final theorem covers either original AB owner for every negative
middle error and retains strict original anchor-circle loss.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate MiddleBelowContraction

namespace MiddleAboveContraction

structure AWeakContraction (G A B : SignedPoint) (δ : ℝ) where
  point : SignedPoint
  sorted : point.Sorted
  avoids : point.AvoidsCore
  normal : 0 < point.y
  circle_lt : point.circle < A.circle
  AB_gap : 1 ≤ point.y-B.y
  AB_zero : zeroFeasible point B 0 0
  AB_two : zeroFeasible point B 0 2
  GA : quarterFeasible G point δ 0

def reflectBWeak {G A B : SignedPoint} {δ : ℝ}
    (O : BWeakContraction B.reflect A.reflect G.reflect δ) : AWeakContraction G A B δ where
  point := O.point.reflect
  sorted := by simpa using O.sorted
  avoids := by simpa using O.avoids
  normal := by simpa [SignedPoint.reflect] using neg_pos.mpr O.normal
  circle_lt := by simpa using O.circle_lt
  AB_gap := by
    have hh := O.AB_gap
    dsimp [SignedPoint.reflect] at hh ⊢
    linarith
  AB_zero := (zeroFeasible_reflect O.point.reflect B 0 0).1
    (by simpa [reflectedOwner] using O.AB_two)
  AB_two := (zeroFeasible_reflect O.point.reflect B 0 2).1
    (by simpa [reflectedOwner] using O.AB_zero)
  GA := (quarterFeasible_reflect G O.point.reflect δ 0).1
    (by simpa [reflectedOwner] using O.BT)

end MiddleAboveContraction

open MiddleAboveContraction
namespace SignedCycle

def Witnesses.replaceAWeak {C : SignedCycle} (w : C.Witnesses)
    (O : AWeakContraction (C.point G) (C.point A) (C.point B) (C.theta B-C.theta G)) :
    (SignedCycle.replaceA C O.point).Witnesses where
  owner i := if i=G then 0 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · exact (replacePoint_other_feasible (v := A) (by decide : H ≠ A)
        (by decide : next H ≠ A)).2 (w.feasible H)
    · exact (replaceA_GA C O.point 0).2 O.GA
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      simp only [A] at hj
      rcases hj with hj | hj
      · exact (replaceA_AB C O.point _).2 (by simpa [hj,G] using O.AB_zero)
      · exact (replaceA_AB C O.point _).2 (by simpa [hj,G] using O.AB_two)
    · exact (replacePoint_other_feasible (v := A) (by decide : B ≠ A)
        (by decide : next B ≠ A)).2 (w.feasible B)
    · exact (replacePoint_other_feasible (v := A) (by decide : T ≠ A)
        (by decide : next T ≠ A)).2 (w.feasible T)
    · exact (replacePoint_other_feasible (v := A) (by decide : D ≠ A)
        (by decide : next D ≠ A)).2 (w.feasible D)
    · exact (replacePoint_other_feasible (v := A) (by decide : E ≠ A)
        (by decide : next E ≠ A)).2 (w.feasible E)
  allowed := by
    intro i
    by_cases hi : i=G
    · subst i; norm_num [normalOwners,G]
    · simpa [hi] using w.allowed i

def HardInput.fromAboveMiddle {q : ℝ} (I : HardInput q)
    (O : AWeakContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta G)) : HardInput q where
  cycle := SignedCycle.replaceA I.cycle O.point
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=A
      · subst i; simpa [replaceA,replacePoint] using O.sorted
      · simpa [replaceA,replacePoint,hi] using I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=A
      · subst i
        have hh := O.circle_lt.le.trans (I.necessary.contained A)
        simpa [replaceA,replacePoint,SignedPoint.Contained] using hh
      · simpa [replaceA,replacePoint,hi] using I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=A
      · subst i; simpa [replaceA,replacePoint] using O.avoids
      · simpa [replaceA,replacePoint,hi] using I.necessary.core i
    spread := replaceA_spread I.necessary.spread O.point }
  anchors_normal := by
    constructor
    · simpa [replaceA,replacePoint,H,A] using I.anchors_normal.H_nonneg
    · simpa [replaceA,replacePoint] using O.normal.le
    · simpa [replaceA,replacePoint,B,A] using I.anchors_normal.B_nonpos
    · simpa [replaceA,replacePoint,D,A] using I.anchors_normal.D_nonpos
  E_nonpos := by simpa [replaceA,replacePoint,E,A] using I.E_nonpos
  witnesses := I.witnesses.replaceAWeak O
  GA_hard := (replaceA_GA I.cycle O.point 0).2 O.GA
  BT_hard := (replacePoint_other_feasible (v := A) (by decide : B ≠ A)
    (by decide : next B ≠ A)).2 I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.replaceAWeak,H,G] using hh
      simpa [replaceA,replacePoint,G,A] using I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.replaceAWeak,T,G] using hh
      simpa [replaceA,replacePoint,T,A] using I.zero_signs.TD_canceling hj }
  E_radial := by simpa [replaceA,replacePoint,H,D,E,A] using I.E_radial

theorem HardInput.above_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hGB : I.cycle.theta G ≤ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 2) :
    Nonempty (AWeakContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta G)) := by
  have hGAsrc : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hABsrc : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) 2 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hABref : zeroFeasible (I.cycle.point B).reflect (I.cycle.point A).reflect
      (-(I.cycle.theta A-I.cycle.theta B)) 0 := by
    simpa [reflectedOwner,neg_sub] using (zeroFeasible_reflect _ _ _ 2).2 hABsrc
  have hBTref : quarterFeasible (I.cycle.point A).reflect (I.cycle.point G).reflect
      ((I.cycle.theta B-I.cycle.theta G)+(I.cycle.theta A-I.cycle.theta B)) 2 := by
    rw [show (I.cycle.theta B-I.cycle.theta G)+
      (I.cycle.theta A-I.cycle.theta B)=I.cycle.theta A-I.cycle.theta G by ring]
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ _ 0).2 hGAsrc
  have hspan : (I.cycle.theta B-I.cycle.theta G)+
      (I.cycle.theta A-I.cycle.theta B) ≤ 7/10 := by
    have hh := I.necessary.spread A G
    have ha := le_abs_self (I.cycle.theta A-I.cycle.theta G)
    dsimp [frameCap] at hh
    linarith
  obtain ⟨O⟩ := MiddleBelowContraction.actual_B_contraction
    (by simpa using I.necessary.sorted B)
    (by simpa using I.necessary.core B)
    (by simpa using (I.necessary.contained B).trans hq)
    (by simpa using I.necessary.sorted A)
    (by simpa [SignedPoint.reflect] using neg_nonpos.mpr I.anchors_normal.A_nonneg)
    (show -(1/10 : ℝ) ≤ (I.cycle.point G).reflect.y by
      dsimp [SignedPoint.reflect]; linarith)
    (sub_pos.mpr hd) (sub_nonneg.mpr hGB) hspan hABref hBTref
  exact ⟨reflectBWeak O⟩

theorem HardInput.align_negative_AB2_above_G {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hGB : I.cycle.theta G ≤ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 2) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta A=I.cycle.theta B ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.above_middle_contraction hq hyG hd hGB hAB
  refine ⟨I.fromAboveMiddle O,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [HardInput.fromAboveMiddle,replaceA,replacePoint,A,B]
  · simp [HardInput.fromAboveMiddle,replaceA,replacePoint]
  · simpa [HardInput.fromAboveMiddle,replaceA,replacePoint,A,B] using O.AB_gap
  · simpa [HardInput.fromAboveMiddle,replaceA,replacePoint] using O.circle_lt
  · intro i hi
    by_cases ha : i=A
    · subst i
      simpa [HardInput.fromAboveMiddle,replaceA,replacePoint] using O.circle_lt.le
    · exact (congrArg SignedPoint.circle (replaceA_unchanged I.cycle O.point i ha).1).le
  · refine ⟨A,by simp [anchorVertices],?_⟩
    simpa [HardInput.fromAboveMiddle,replaceA,replacePoint] using O.circle_lt
  · exact replaceA_unchanged I.cycle O.point

theorem HardInput.align_negative_AB2_all_orders {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hAB : I.cycle.Feasible A 2) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta A=I.cycle.theta B ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  rcases le_total (I.cycle.theta B) (I.cycle.theta G) with hBG | hGB
  · obtain ⟨J,halign,hframe,hgap,hloss,hnon,hstrict,hfixed⟩ :=
      I.align_nonzero_AB2_B_below_G hq hyG hBG (ne_of_gt hd) hAB
    exact ⟨J,halign,hframe,hgap.symm.le,hloss,hnon,hstrict,hfixed⟩
  · exact I.align_negative_AB2_above_G hq hyG hd hGB hAB

/-- The original physical owner, rather than a relabeling assumption,
chooses the A or B contraction for every negative middle error. -/
theorem HardInput.align_negative_AB_all_owners {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta B < I.cycle.theta A) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.theta A=I.cycle.theta A ∨ J.cycle.theta A=I.cycle.theta B) ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  rcases hj with hj | hj
  · have hAB : I.cycle.Feasible A 0 := by simpa [hj] using I.witnesses.feasible A
    obtain ⟨J,halign,hframe,hgap,hloss,hnon,hstrict,hfixed⟩ :=
      I.align_negative_AB0_all_orders hq hyT hd hAB
    refine ⟨J,halign,Or.inl (halign.trans hframe),hgap,hnon,hstrict,?_⟩
    intro i hiA hiB
    exact hfixed i hiB
  · have hAB : I.cycle.Feasible A 2 := by simpa [hj] using I.witnesses.feasible A
    obtain ⟨J,halign,hframe,hgap,hloss,hnon,hstrict,hfixed⟩ :=
      I.align_negative_AB2_all_orders hq hyG hd hAB
    refine ⟨J,halign,Or.inr hframe,hgap,hnon,hstrict,?_⟩
    intro i hiA hiB
    exact hfixed i hiA

end SignedCycle
end SquaresInCircles.Eight.TableFree
