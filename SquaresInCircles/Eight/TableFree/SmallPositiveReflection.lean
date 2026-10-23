module

public import SquaresInCircles.Eight.TableFree.SmallPositiveCycle
public import SquaresInCircles.Eight.TableFree.NegativeNoncancelingOuter

/-!
# The small positive TD2 alignment at the unchanged original E

Uncompiled source draft.  Reflection is applied to local necessary
geometry and the already proved invariant endpoint budget.  The local
three-point alignment is then reflected back, producing a new original
hard cycle with only T and B changed.  No reflected E normalization and
no change of the source mixed-edge witnesses is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate HardCancelingOuter
namespace SignedCycle

theorem HardInput.positive_TD2_small_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : -(I.cycle.point B).y∈Icc (67/200 : ℝ) (1/2))
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T<I.cycle.theta D)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y)
    (hTD : I.cycle.Feasible T 2) :
    ∃ t, t<I.cycle.theta B-I.cycle.theta D ∧
      Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
        (I.cycle.theta B-I.cycle.theta D) t) := by
  let J := I.outerGeometry.reflected
  have hJAB : J.cycle.theta A=J.cycle.theta B := by
    change I.cycle.theta B-I.cycle.theta B=I.cycle.theta B-I.cycle.theta A
    linarith
  have hJnorm : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    change -(I.cycle.point B).y-(-(I.cycle.point A).y)=1
    linarith
  have hJsmall : (J.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) := hsmall
  have hJTA : J.cycle.theta T≤J.cycle.theta A := by
    change I.cycle.theta B-I.cycle.theta G≤I.cycle.theta B-I.cycle.theta B
    linarith
  have hJAH : J.cycle.theta A≤J.cycle.theta H := by
    change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta D
    linarith
  have hJHGorder : J.cycle.theta H<J.cycle.theta G := by
    change I.cycle.theta B-I.cycle.theta D<I.cycle.theta B-I.cycle.theta T
    linarith
  have hJGy : (J.cycle.point G).y≤0 := by
    change -(I.cycle.point T).y≤0
    linarith
  have hJTy : 0≤(J.cycle.point T).y := by
    change 0≤ -(I.cycle.point G).y
    linarith
  have hJHG : J.cycle.Feasible H 0 := by
    have hh := (reflected_feasible I.cycle H 2).2
      (by simpa [reflectedIndex,next,H,T] using hTD)
    simpa [J,HardOuterGeometry.reflected,HardInput.outerGeometry,reflectedOwner] using hh
  obtain ⟨t,ht,⟨O⟩⟩ := J.positive_HG0_small_output hqL hq hJAB hJnorm hJsmall
    hJTA hJAH hJHGorder hJGy hJTy hJHG
  change t<(I.cycle.theta B-I.cycle.theta D)-
    (I.cycle.theta B-I.cycle.theta B) at ht
  change GAlignment q (I.cycle.point D).reflect (I.cycle.point B).reflect
    ((I.cycle.theta B-I.cycle.theta D)-(I.cycle.theta B-I.cycle.theta B)) t at O
  have O' : GAlignment q (I.cycle.point D).reflect (I.cycle.point B).reflect
      (I.cycle.theta B-I.cycle.theta D) t := by
    simpa only [sub_self,sub_zero] using O
  exact ⟨t,by simpa only [sub_self,sub_zero] using ht,
    ⟨NegativeNoncancelingOuter.reflect_alignment O'⟩⟩

/-- The strict loss is recorded on the original B anchor, while the
actual original E point and all its incident witnesses are unchanged. -/
theorem HardInput.align_positive_TD2_small {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : -(I.cycle.point B).y∈Icc (67/200 : ℝ) (1/2))
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T<I.cycle.theta D)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y)
    (hTD : I.cycle.Feasible T 2) :
    ∃ J : HardInput q,
      J.cycle.theta T=J.cycle.theta D ∧ J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point B).y=(I.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i,i≠T → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠T → i≠B → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨t,ht,⟨O⟩⟩ := I.positive_TD2_small_output hqL hq hAB hnorm hsmall
    hAG hDB hTDorder hGy hTy hTD
  refine ⟨I.fromCancelingTD hAB O,rfl,hAB,O.B_tangent,?_,?_,?_,?_⟩
  · intro i hi
    by_cases hiB : i=B
    · subst i; exact O.B_circle
    by_cases hiT : i=T
    · subst i; simp [anchorVertices,H,T,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignBTCycle_unchanged I.cycle O.pointT O.pointB i hiT hiB).1).le
  · exact ⟨B,by simp [anchorVertices],O.B_strict ht⟩
  · intro i hi
    change (alignBTCycle I.cycle O.pointT O.pointB).theta i=I.cycle.theta i
    simp [alignBTCycle_theta,hi]
  · intro i hiT hiB
    exact (alignBTCycle_unchanged I.cycle O.pointT O.pointB i hiT hiB).1

end SignedCycle
end SquaresInCircles.Eight.TableFree
