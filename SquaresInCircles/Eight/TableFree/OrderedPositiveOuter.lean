module

public import SquaresInCircles.Eight.TableFree.OrderedNormalMiddle
public import SquaresInCircles.Eight.TableFree.SmallPositiveReflection

/-!
# Every positive outer error with ordered normal hard contacts aligns

Uncompiled source draft.  The retained weak owner chooses one of the
two actual local constructions.  The noncanceling owner uses the source
large-side circle or the complete small-side convexity argument.  The
canceling owner uses its same-circle support reserve.  Each construction
spends a strict loss on the original A or B anchor and fixes the
opposite side and all of H/D/E.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate HardCancelingOuter
namespace SignedCycle

theorem HardInput.positive_HG_normal_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hfloor : 67/200≤(I.cycle.point A).y)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H<I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ t, t<I.cycle.theta H-I.cycle.theta A ∧
      Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
        (I.cycle.theta H-I.cycle.theta A) t) := by
  have howners : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
    simpa [normalOwners,H] using I.witnesses.allowed H
  rcases howners with ho | ho
  · have hf : I.cycle.Feasible H 0 := by simpa [ho] using I.witnesses.feasible H
    by_cases hlarge : 1/2≤(I.cycle.point A).y
    · obtain ⟨O⟩ := I.positive_HG0_large_output hqL hq hAH hHGorder.le hGy hlarge hf
      exact ⟨_,by linarith,⟨O⟩⟩
    · exact I.outerGeometry.positive_HG0_small_output hqL hq hAB hnorm
        ⟨hfloor,(lt_of_not_ge hlarge).le⟩ hTA hAH hHGorder hGy hTy hf
  · have hf : I.cycle.Feasible H 2 := by simpa [ho] using I.witnesses.feasible H
    obtain ⟨O⟩ := I.ordered_canceling_HG_output hqL hq hAH
      (hAH.trans hHGorder.le) (by linarith) hf
    have hp : 0 < |I.cycle.theta G-I.cycle.theta H| :=
      abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hHGorder))
    exact ⟨_,by linarith,⟨O⟩⟩

theorem HardInput.positive_TD_normal_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hfloor : 67/200≤ -(I.cycle.point B).y)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T<I.cycle.theta D)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ t, t<I.cycle.theta B-I.cycle.theta D ∧
      Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
        (I.cycle.theta B-I.cycle.theta D) t) := by
  have howners : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  rcases howners with ho | ho
  · have hf : I.cycle.Feasible T 0 := by simpa [ho] using I.witnesses.feasible T
    obtain ⟨O⟩ := I.ordered_canceling_TD_output hqL hq hDB
      (hTDorder.le.trans hDB) (by linarith) hf
    have hp : 0< |I.cycle.theta T-I.cycle.theta D| :=
      abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hTDorder))
    exact ⟨_,by linarith,⟨O⟩⟩
  · have hf : I.cycle.Feasible T 2 := by simpa [ho] using I.witnesses.feasible T
    by_cases hlarge : 1/2≤ -(I.cycle.point B).y
    · obtain ⟨O⟩ := I.positive_TD2_large_output hqL hq hDB hTDorder.le hTy hlarge hf
      exact ⟨_,by linarith,⟨O⟩⟩
    · exact I.positive_TD2_small_output hqL hq hAB hnorm
        ⟨hfloor,by linarith⟩ hAG hDB hTDorder hGy hTy hf

theorem HardInput.align_positive_HG_normal {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hfloor : 67/200≤(I.cycle.point A).y)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H<I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧ J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧
      (J.cycle.point G).y< -(1/10 : ℝ) ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i,i≠G → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠G → i≠A → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨t,ht,⟨O⟩⟩ := I.positive_HG_normal_output hqL hq hAB hnorm hfloor
    hTA hAH hHGorder hGy hTy
  refine ⟨I.fromCancelingHG hAB O,rfl,hAB,O.A_tangent,O.G_normal,?_,?_,?_,?_⟩
  · intro i hi
    by_cases hiA : i=A
    · subst i; exact O.A_circle
    by_cases hiG : i=G
    · subst i; simp [anchorVertices,H,G,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1).le
  · exact ⟨A,by simp [anchorVertices],O.A_strict ht⟩
  · intro i hi
    change (alignGACycle I.cycle O.pointG O.pointA).theta i=I.cycle.theta i
    simp [alignGACycle_theta,hi]
  · intro i hiG hiA
    exact (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1

theorem HardInput.align_positive_TD_normal {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hfloor : 67/200≤ -(I.cycle.point B).y)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T<I.cycle.theta D)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ J : HardInput q,
      J.cycle.theta T=J.cycle.theta D ∧ J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point B).y=(I.cycle.point B).y ∧
      (1/10 : ℝ)<(J.cycle.point T).y ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i,i≠T → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠T → i≠B → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨t,ht,⟨O⟩⟩ := I.positive_TD_normal_output hqL hq hAB hnorm hfloor
    hAG hDB hTDorder hGy hTy
  refine ⟨I.fromCancelingTD hAB O,rfl,hAB,O.B_tangent,O.T_normal,?_,?_,?_,?_⟩
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
