module

public import SquaresInCircles.Eight.Words.Middle.CrossingCycle
public import SquaresInCircles.Eight.Words.Middle.ReflectedCycle

/-!
# Eight squares: the reflected crossing middle contraction

The AB2 owner is kept through local reflection of the crossing formula
(`HardInput.reflected_crossing_middle_contraction`). Thus B at or below G suffices for a direct
A contraction, also when A starts strictly above G (`HardInput.align_nonzero_AB2_B_below_G`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate MiddlePositiveContraction MiddleReflectedContraction
namespace SignedCycle

theorem HardInput.reflected_crossing_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hBG : I.cycle.theta B ≤ I.cycle.theta G)
    (hGA : I.cycle.theta G ≤ I.cycle.theta A)
    (hAB : I.cycle.Feasible A 2) :
    Nonempty (AContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta G-I.cycle.theta B)) := by
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
      ((I.cycle.theta A-I.cycle.theta B)-(I.cycle.theta G-I.cycle.theta B)) 2 := by
    rw [show (I.cycle.theta A-I.cycle.theta B)-
      (I.cycle.theta G-I.cycle.theta B)=I.cycle.theta A-I.cycle.theta G by ring]
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ _ 0).2 hGAsrc
  have hdu : I.cycle.theta A-I.cycle.theta B ≤ 7/10 := by
    have hh := I.necessary.spread A B
    have ha := le_abs_self (I.cycle.theta A-I.cycle.theta B)
    dsimp [frameCap] at hh
    linarith
  obtain ⟨O⟩ := MiddleCrossingContraction.actual_B_contraction
    (by simpa using I.necessary.sorted B)
    (by simpa using I.necessary.core B)
    (by simpa using (I.necessary.contained B).trans hq)
    (by simpa using I.necessary.sorted A)
    (by simpa using (I.necessary.contained A).trans hq)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos)
    (by simpa [SignedPoint.reflect] using neg_nonpos.mpr I.anchors_normal.A_nonneg)
    (show -(1/10 : ℝ) ≤ (I.cycle.point G).reflect.y by
      dsimp [SignedPoint.reflect]; linarith)
    (sub_pos.mpr hd) (sub_nonneg.mpr hBG)
    (show I.cycle.theta G-I.cycle.theta B ≤ I.cycle.theta A-I.cycle.theta B by linarith)
    hdu hABref hBTref
  exact ⟨reflectB O⟩

/-- A may lie on either side of G in this direct AB2 result. -/
theorem HardInput.middle_AB2_contraction_below_G {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hBG : I.cycle.theta B ≤ I.cycle.theta G)
    (hne : I.cycle.theta A ≠ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 2) :
    Nonempty (AContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta G-I.cycle.theta B)) := by
  rcases le_total (I.cycle.theta A) (I.cycle.theta G) with hAG | hGA
  · exact I.reflected_middle_contraction hq hyG (max_le hAG hBG) hne hAB
  · have hd : I.cycle.theta B < I.cycle.theta A := by
      rcases lt_or_gt_of_ne hne with hab | hba
      · linarith
      · exact hba
    exact I.reflected_crossing_middle_contraction hq hyG hd hBG hGA hAB

theorem HardInput.align_nonzero_AB2_B_below_G {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hBG : I.cycle.theta B ≤ I.cycle.theta G)
    (hne : I.cycle.theta A ≠ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 2) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta A=I.cycle.theta B ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.middle_AB2_contraction_below_G hq hyG hBG hne hAB
  refine ⟨I.fromReflectedMiddle O,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [HardInput.fromReflectedMiddle,replaceA,replacePoint,A,B]
  · simp [HardInput.fromReflectedMiddle,replaceA,replacePoint]
  · simpa [HardInput.fromReflectedMiddle,replaceA,replacePoint,A,B] using O.AB_exact
  · simpa [HardInput.fromReflectedMiddle,replaceA,replacePoint] using O.circle_lt
  · intro i hi
    by_cases ha : i=A
    · subst i
      simpa [HardInput.fromReflectedMiddle,replaceA,replacePoint] using O.circle_lt.le
    · exact (congrArg SignedPoint.circle (replaceA_unchanged I.cycle O.point i ha).1).le
  · refine ⟨A,by simp [anchorVertices],?_⟩
    simpa [HardInput.fromReflectedMiddle,replaceA,replacePoint] using O.circle_lt
  · exact replaceA_unchanged I.cycle O.point

end SignedCycle
end SquaresInCircles.Eight
