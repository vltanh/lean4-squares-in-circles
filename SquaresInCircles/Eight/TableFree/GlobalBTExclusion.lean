module

public import SquaresInCircles.Eight.TableFree.GlobalBTSoftCapPath

/-!
# Complete original low-BT owner exclusion

Every signed AB/BT error, both original zero owners at AB and TD,
both high DE owners, and every E radial chart have been discharged.
The only chart condition is the original E tangent being nonpositive.
All weak original separating witnesses are retained, and fixed-ray
expansion transfers the obstruction to every admissible source radius.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open Candidate FramePair GlobalOuterAnchor

namespace SoftCap

theorem ceiling_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hAB : (forwardAxis 2).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hABpositive : 0≤delta F.theta A) (hBTnegative : delta F.theta B≤0) : False := by
  obtain ⟨L⟩ := lowSource F hE 1 (Or.inr rfl) hBT
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hv : delta F.theta A∈Icc 0 frameCap :=
    ⟨hABpositive,(le_abs_self (delta F.theta A)).trans (hdelta A)⟩
  have hz : -delta F.theta B∈Icc 0 frameCap :=
    ⟨by linarith,(neg_le_abs (delta F.theta B)).trans (hdelta B)⟩
  have hABp : GlobalOuterAnchor.width (delta F.theta A)≤
      projection false (stateOf C A) (stateOf C B) (delta F.theta A) 2 := by
    simpa [A,B,next] using frame_zero_projection F A (by norm_num [word,A]) 2
      (by simpa [A,B,next] using hAB)
  have hcap : max (-delta F.theta T) 0+max (-delta F.theta D) 0≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    have hb : 0≤ max (-delta F.theta B) 0 := le_max_right _ _
    linarith
  have hpath := path (stateOf C A) (stateOf C B) (stateOf C T) (stateOf C D)
    (stateOf C E) L.TD L.DE L.A_positive L.T_positive L.D_negative L.E_negative hv hz
    (hdelta T) (hdelta D) hcap L.DE_owner hABp
    (by simpa only [neg_neg] using L.BT_projection) L.TD_projection L.DE_projection
  simp only [sub_neg_eq_add] at hpath
  have hreturn := frame_tail_cap F hE L.A_tangent.le
  dsimp [tailCharge] at hreturn
  linarith

end SoftCap

theorem ceiling_BT1_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T)) : False := by
  by_cases hBTpositive : 0≤delta F.theta B
  · exact OnePositive.ceiling_false F hE hBT hBTpositive
  · have hBTnegative : delta F.theta B≤0 := le_of_not_ge hBTpositive
    by_cases hABnegative : delta F.theta A≤0
    · exact OneNegative.ceiling_nonpositive_AB_false F hE hBT hABnegative hBTnegative
    · have hABpositive : 0≤delta F.theta A := le_of_not_ge hABnegative
      have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
      obtain ⟨jA,hjA⟩ := F.forward_complete A (C.selected A) (C.feasible A)
      have hf : (forwardAxis jA).Feasible (C.square A) (C.square (next A)) :=
        hjA ▸ C.feasible A
      have hAB : (forwardAxis jA).Feasible (C.square A) (C.square B) := hf
      rcases GlobalZeroSign.of_frame F hq A (by norm_num [word,A]) jA hf with ho | ho
      · rw [ho.1] at hAB
        exact OneNegative.ceiling_AB0_false F hE hAB hBT
      · rw [ho.1] at hAB
        exact SoftCap.ceiling_false F hE hAB hBT hABpositive hBTnegative

theorem frame_BT1_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T)) : False := by
  let K := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C K := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame K := FramePhysicalTransport.candidatePushforward F hR le_rfl
  have hBT' : (forwardAxis 1).Feasible (K.square B) (K.square T) := by
    simpa [B,T,next] using hR.preserves_all_axes B (forwardAxis 1)
      (by simpa [B,T,next] using hBT)
  exact ceiling_BT1_false F' (by simpa only [hR.same_tangents] using hE) hBT'

/-- Every original weak BT witness belongs to the high owner pair. -/
theorem frame_BT_high {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square B) (C.square T)) : j=2 ∨ j=3 := by
  fin_cases j
  · exact False.elim (frame_BT0_false F hq hE hj)
  · exact False.elim (frame_BT1_false F hq hE hj)
  · exact Or.inl rfl
  · exact Or.inr rfl

end SquaresInCircles.Eight.TableFree.GlobalBT
