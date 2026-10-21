module

public import SquaresInCircles.Eight.TableFree.PositiveNoncancelingOuter
public import SquaresInCircles.Eight.TableFree.HardCancelingOuterCycle

/-!
# Positive HG0/TD2 alignment retains the original large-side circle

Uncompiled draft.  These actual hard-cycle constructors invoke the
unlifted same-circle reserve.  The source large middle primary decreases
by one sixtieth of the original outer error.  Every other anchor, every
original mixed E witness, and the opposite intermediate are unchanged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate HardCancelingOuter
namespace SignedCycle

theorem HardInput.positive_HG0_large_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H≤I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hlarge : 1/2≤(I.cycle.point A).y)
    (hHG : I.cycle.Feasible H 0) :
    Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A)
      ((I.cycle.theta H-I.cycle.theta A)-(2/9)*(I.cycle.theta G-I.cycle.theta H))) := by
  have hspan : (I.cycle.theta H-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta H)≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread G A)
    dsimp [frameCap] at hh
    linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      (I.cycle.theta G-I.cycle.theta H) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-((I.cycle.theta H-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta H))) 0 := by
    rw [show -((I.cycle.theta H-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta H))=
      I.cycle.theta A-I.cycle.theta G by ring]
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  exact PositiveNoncancelingOuter.actual_G_alignment hqL hq
    (I.necessary.sorted H) (I.necessary.sorted G) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core A)
    (I.necessary.contained H) (I.necessary.contained G) (I.necessary.contained A)
    I.anchors_normal.H_nonneg hGy hlarge (sub_nonneg.mpr hAH)
    (sub_nonneg.mpr hHGorder) hspan hHG' hGA'

theorem HardInput.align_nonnegative_HG0_large {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H≤I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hlarge : 1/2≤(I.cycle.point A).y)
    (hHG : I.cycle.Feasible H 0) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta H<I.cycle.theta G → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠G → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠G → i≠A → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨O⟩ := I.positive_HG0_large_output hqL hq hAH hHGorder hGy hlarge hHG
  refine ⟨I.fromCancelingHG hAB O,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · exact hAB
  · exact O.A_tangent
  · intro i hi
    by_cases hiA : i=A
    · subst i; exact O.A_circle
    by_cases hiG : i=G
    · subst i; simp [anchorVertices,H,G,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1).le
  · intro hstrict
    exact ⟨A,by simp [anchorVertices],O.A_strict (by linarith)⟩
  · intro i hi
    change (alignGACycle I.cycle O.pointG O.pointA).theta i=I.cycle.theta i
    simp [alignGACycle_theta,hi]
  · intro i hiG hiA
    exact (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1

theorem HardInput.positive_TD2_large_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T≤I.cycle.theta D)
    (hTy : 0≤(I.cycle.point T).y) (hlarge : 1/2≤ -(I.cycle.point B).y)
    (hTD : I.cycle.Feasible T 2) :
    Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D)
      ((I.cycle.theta B-I.cycle.theta D)-(2/9)*(I.cycle.theta D-I.cycle.theta T))) := by
  have hspan : (I.cycle.theta B-I.cycle.theta D)+(I.cycle.theta D-I.cycle.theta T)≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread B T)
    dsimp [frameCap] at hh
    linarith
  have hTD' : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta T) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using hTD
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-((I.cycle.theta B-I.cycle.theta D)+(I.cycle.theta D-I.cycle.theta T))) 2 := by
    rw [show -((I.cycle.theta B-I.cycle.theta D)+(I.cycle.theta D-I.cycle.theta T))=
      I.cycle.theta T-I.cycle.theta B by ring]
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  exact PositiveNoncancelingOuter.actual_T_alignment hqL hq
    (I.necessary.sorted B) (I.necessary.sorted T) (I.necessary.sorted D)
    (I.necessary.core B) (I.necessary.core D)
    (I.necessary.contained B) (I.necessary.contained T) (I.necessary.contained D)
    hlarge hTy I.anchors_normal.D_nonpos (sub_nonneg.mpr hDB)
    (sub_nonneg.mpr hTDorder) hspan hBT' hTD'

theorem HardInput.align_nonnegative_TD2_large {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T≤I.cycle.theta D)
    (hTy : 0≤(I.cycle.point T).y) (hlarge : 1/2≤ -(I.cycle.point B).y)
    (hTD : I.cycle.Feasible T 2) :
    ∃ J : HardInput q,
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point B).y=(I.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta T<I.cycle.theta D → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠T → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠T → i≠B → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨O⟩ := I.positive_TD2_large_output hqL hq hDB hTDorder hTy hlarge hTD
  refine ⟨I.fromCancelingTD hAB O,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · exact hAB
  · exact O.B_tangent
  · intro i hi
    by_cases hiB : i=B
    · subst i; exact O.B_circle
    by_cases hiT : i=T
    · subst i; simp [anchorVertices,H,T,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignBTCycle_unchanged I.cycle O.pointT O.pointB i hiT hiB).1).le
  · intro hstrict
    exact ⟨B,by simp [anchorVertices],O.B_strict (by linarith)⟩
  · intro i hi
    change (alignBTCycle I.cycle O.pointT O.pointB).theta i=I.cycle.theta i
    simp [alignBTCycle_theta,hi]
  · intro i hiT hiB
    exact (alignBTCycle_unchanged I.cycle O.pointT O.pointB i hiT hiB).1

end SignedCycle
end SquaresInCircles.Eight.TableFree
