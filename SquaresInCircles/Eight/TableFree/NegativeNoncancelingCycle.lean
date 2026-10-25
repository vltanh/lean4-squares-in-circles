module

public import SquaresInCircles.Eight.TableFree.NegativeNoncancelingOuter
public import SquaresInCircles.Eight.TableFree.HardCancelingOuterCycle

/-!
# Negative noncanceling outer alignment in the actual hard cycle

Uncompiled draft.  Both local transports retain the original outer
anchor, original E, the opposite path, and the aligned AB witness.  The
changed middle primary has a loss on its own source circle whenever the
original outer error is nonzero.  The free intermediate supplies only
the needed actual circle, core and neighboring axes.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate HardCancelingOuter
namespace SignedCycle

theorem HardInput.negative_HG0_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hsmall : (I.cycle.point A).y≤1/2)
    (hHG : I.cycle.Feasible H 0) :
    Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A)
      ((I.cycle.theta H-I.cycle.theta A)-(2/45)*(I.cycle.theta H-I.cycle.theta G))) := by
  have hΘ : I.cycle.theta H-I.cycle.theta A∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith,(le_abs_self _).trans (I.necessary.spread H A)⟩
  have ht : I.cycle.theta G-I.cycle.theta A∈
      Icc 0 (I.cycle.theta H-I.cycle.theta A) := by constructor <;> linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      ((I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)) 0 := by
    rw [show (I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)=
      I.cycle.theta G-I.cycle.theta H by ring]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta G-I.cycle.theta A)) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  have hh := NegativeNoncancelingOuter.actual_G_alignment hqL hq
    (I.necessary.sorted H) (I.necessary.sorted G) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core G) (I.necessary.core A)
    (I.necessary.contained H) (I.necessary.contained A)
    I.anchors_normal.H_nonneg ⟨I.anchors_normal.A_nonneg,hsmall⟩ hΘ ht hHG' hGA'
  simpa [show (I.cycle.theta H-I.cycle.theta A)-(I.cycle.theta G-I.cycle.theta A)=
    I.cycle.theta H-I.cycle.theta G by ring] using hh

theorem HardInput.align_nonpositive_HG0_small {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hsmall : (I.cycle.point A).y≤1/2)
    (hHG : I.cycle.Feasible H 0) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta G<I.cycle.theta H → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠G → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠G → i≠A → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨O⟩ := I.negative_HG0_output hqL hq hAG hGH hsmall hHG
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

theorem HardInput.negative_TD2_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hsmall : -(I.cycle.point B).y≤1/2)
    (hTD : I.cycle.Feasible T 2) :
    Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D)
      ((I.cycle.theta B-I.cycle.theta D)-(2/45)*(I.cycle.theta T-I.cycle.theta D))) := by
  have hΘ : I.cycle.theta B-I.cycle.theta D∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith,(le_abs_self _).trans (I.necessary.spread B D)⟩
  have ht : I.cycle.theta B-I.cycle.theta T∈
      Icc 0 (I.cycle.theta B-I.cycle.theta D) := by constructor <;> linarith
  have hTD' : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)) 2 := by
    rw [show (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)=
      I.cycle.theta D-I.cycle.theta T by ring]
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using hTD
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta B-I.cycle.theta T)) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,neg_sub]
      using I.BT_hard
  have hh := NegativeNoncancelingOuter.actual_T_alignment hqL hq
    (I.necessary.sorted B) (I.necessary.sorted T) (I.necessary.sorted D)
    (I.necessary.core B) (I.necessary.core T) (I.necessary.core D)
    (I.necessary.contained B) (I.necessary.contained D)
    ⟨neg_nonneg.mpr I.anchors_normal.B_nonpos,hsmall⟩ I.anchors_normal.D_nonpos
    hΘ ht hBT' hTD'
  simpa [show (I.cycle.theta B-I.cycle.theta D)-(I.cycle.theta B-I.cycle.theta T)=
    I.cycle.theta T-I.cycle.theta D by ring] using hh

theorem HardInput.align_nonpositive_TD2_small {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hsmall : -(I.cycle.point B).y≤1/2)
    (hTD : I.cycle.Feasible T 2) :
    ∃ J : HardInput q,
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point B).y=(I.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta D<I.cycle.theta T → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠T → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠T → i≠B → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨O⟩ := I.negative_TD2_output hqL hq hDT hTB hsmall hTD
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
