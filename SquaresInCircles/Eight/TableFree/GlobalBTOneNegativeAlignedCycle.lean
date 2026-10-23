module

public import SquaresInCircles.Eight.TableFree.GlobalBTAlignedPrefixPath

/-!
# Original-cycle exclusion for the dominating AB0 error

The actual AB0 and BT1 witnesses give an aligned-prefix charge when
the nonnegative AB error dominates the magnitude of negative BT.
The complete unchanged TD--DE tail then contradicts the original
three-edge return.  Fixed-ray expansion preserves both witnesses
and the error order at every admissible source radius.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative

open Candidate FramePair GlobalOuterAnchor

theorem ceiling_AB0_dominating_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hAB : (forwardAxis 0).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hnegative : delta F.theta B≤0)
    (hdominates : -delta F.theta B≤delta F.theta A) : False := by
  obtain ⟨L⟩ := lowSource F hE 1 (Or.inr rfl) hBT
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hABp : width (delta F.theta A)≤
      projection false (stateOf C A) (stateOf C B) (delta F.theta A) 0 := by
    simpa [A,B,next] using frame_zero_projection F A (by norm_num [word,A]) 0
      (by simpa [A,B,next] using hAB)
  have hpref : kappa*(2-(stateOf C T).a)≤
      delta F.theta A+delta F.theta B+kappa*(stateOf C A).b := by
    have hh := AB0_dominating_charge (stateOf C A) (stateOf C B) (stateOf C T)
      L.A_positive (show 0≤-delta F.theta B by linarith) hdominates
      ((le_abs_self (delta F.theta A)).trans (hdelta A)) hABp
      (by simpa only [neg_neg] using L.BT_projection)
    simpa only [sub_neg_eq_add] using hh
  have hcap : max (-delta F.theta T) 0+max (-delta F.theta D) 0≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    have hb : 0≤max (-delta F.theta B) 0 := le_max_right _ _
    linarith
  have hpath := aligned_path (stateOf C B) (stateOf C T) (stateOf C D)
    (stateOf C E) L.TD L.DE L.T_positive L.D_negative L.E_negative hpref
    (hdelta T) (hdelta D) hcap L.DE_owner L.TD_projection L.DE_projection
  have hreturn := frame_tail_cap F hE L.A_tangent.le
  dsimp [tailCharge] at hreturn
  linarith

theorem frame_AB0_dominating_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hAB : (forwardAxis 0).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hnegative : delta F.theta B≤0)
    (hdominates : -delta F.theta B≤delta F.theta A) : False := by
  let K := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C K := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame K := FramePhysicalTransport.candidatePushforward F hR le_rfl
  apply ceiling_AB0_dominating_false F' (by simpa only [hR.same_tangents] using hE)
    (by simpa [A,B,next] using hR.preserves_all_axes A (forwardAxis 0)
      (by simpa [A,B,next] using hAB))
    (by simpa [B,T,next] using hR.preserves_all_axes B (forwardAxis 1)
      (by simpa [B,T,next] using hBT)) hnegative hdominates

end SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative
