module

public import SquaresInCircles.Eight.TableFree.GlobalBTOneNegativeAB0Cap
public import SquaresInCircles.Eight.TableFree.GlobalBTOneNegativePrefixCycle
public import SquaresInCircles.Eight.TableFree.GlobalBTOneNegativeAlignedCycle

/-!
# Complete original BT1 exclusion with an actual AB0 witness

All signed AB and BT errors are dispatched.  The intermediate
positive AB range uses its exact effective cap; the dominating range
uses the aligned charge; nonpositive AB and nonnegative BT use their
complete original-cycle obstructions.  Weak ties are included.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative

open Candidate FramePair GlobalOuterAnchor

theorem ceiling_AB0_intermediate_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hAB : (forwardAxis 0).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hABpositive : 0≤delta F.theta A) (hBTnegative : delta F.theta B≤0)
    (horder : delta F.theta A≤ -delta F.theta B) : False := by
  obtain ⟨L⟩ := lowSource F hE 1 (Or.inr rfl) hBT
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hv : delta F.theta A∈Icc 0 frameCap :=
    ⟨hABpositive,(le_abs_self (delta F.theta A)).trans (hdelta A)⟩
  have hz : -delta F.theta B∈Icc 0 frameCap :=
    ⟨by linarith,(neg_le_abs (delta F.theta B)).trans (hdelta B)⟩
  have hABp : width (delta F.theta A)≤
      projection false (stateOf C A) (stateOf C B) (delta F.theta A) 0 := by
    simpa [A,B,next] using frame_zero_projection F A (by norm_num [word,A]) 0
      (by simpa [A,B,next] using hAB)
  have hp := AB0_effective_cap (stateOf C A) (stateOf C B) (stateOf C T)
    L.A_positive hv hz horder hABp (by simpa only [neg_neg] using L.BT_projection)
  have hr : -delta F.theta B-delta F.theta A∈Icc 0 frameCap :=
    ⟨by linarith,by linarith [hz.2]⟩
  have hcharge : -(-delta F.theta B-delta F.theta A)+
      kappa*(HighPrimary.prefix (-delta F.theta B-delta F.theta A)-
        (stateOf C T).a/Real.cos (-delta F.theta B-delta F.theta A))≤
        delta F.theta A+delta F.theta B+kappa*(stateOf C A).b := by
    simpa only [sub_neg_eq_add] using hp.2
  have hcap : max (-delta F.theta T) 0+max (-delta F.theta D) 0≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    have hb : 0≤max (-delta F.theta B) 0 := le_max_right _ _
    linarith
  have hpath := HighPrimary.path (stateOf C A) (stateOf C T) (stateOf C D)
    (stateOf C E) L.TD L.DE L.T_positive L.D_negative L.E_negative hr hp.1 hcharge
    (hdelta T) (hdelta D) hcap L.DE_owner L.TD_projection L.DE_projection
  have hreturn := frame_tail_cap F hE L.A_tangent.le
  dsimp [tailCharge] at hreturn
  linarith

theorem ceiling_AB0_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hAB : (forwardAxis 0).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T)) : False := by
  by_cases hBTpositive : 0≤delta F.theta B
  · exact OnePositive.ceiling_false F hE hBT hBTpositive
  · have hBTnegative : delta F.theta B≤0 := le_of_not_ge hBTpositive
    by_cases hABnegative : delta F.theta A≤0
    · exact ceiling_nonpositive_AB_false F hE hBT hABnegative hBTnegative
    · by_cases hdom : -delta F.theta B≤delta F.theta A
      · exact ceiling_AB0_dominating_false F hE hAB hBT hBTnegative hdom
      · exact ceiling_AB0_intermediate_false F hE hAB hBT
          (le_of_not_ge hABnegative) hBTnegative (le_of_not_ge hdom)

/-- A complete original-owner row at the unchanged source radius. -/
theorem frame_AB0_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hAB : (forwardAxis 0).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T)) : False := by
  let K := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C K := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame K := FramePhysicalTransport.candidatePushforward F hR le_rfl
  exact ceiling_AB0_false F' (by simpa only [hR.same_tangents] using hE)
    (by simpa [A,B,next] using hR.preserves_all_axes A (forwardAxis 0)
      (by simpa [A,B,next] using hAB))
    (by simpa [B,T,next] using hR.preserves_all_axes B (forwardAxis 1)
      (by simpa [B,T,next] using hBT))

end SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative
