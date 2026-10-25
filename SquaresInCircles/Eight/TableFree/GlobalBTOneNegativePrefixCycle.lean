module

public import SquaresInCircles.Eight.TableFree.GlobalBTOneNegativePrefix

/-!
# Original BT1 exclusion when AB has nonpositive error

Both actual AB owners, both TD owners and every DE family are covered.
The cap and charge are derived from the original two prefix contacts;
the complete transported tail contradicts the original return charge.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative

open Candidate FramePair GlobalOuterAnchor

theorem ceiling_nonpositive_AB_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hABnegative : delta F.theta A≤0) (hBTnegative : delta F.theta B≤0) : False := by
  obtain ⟨L⟩ := lowSource F hE 1 (Or.inr rfl) hBT
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hw : -delta F.theta A∈Icc 0 frameCap :=
    ⟨by linarith,(neg_le_abs (delta F.theta A)).trans (hdelta A)⟩
  have hz : -delta F.theta B∈Icc 0 frameCap :=
    ⟨by linarith,(neg_le_abs (delta F.theta B)).trans (hdelta B)⟩
  have hp := nonpositive_prefix (stateOf C A) (stateOf C B) (stateOf C T) L.AB
    L.A_positive hw hz
    (by simpa only [neg_neg] using L.AB_projection)
    (by simpa only [neg_neg] using L.BT_projection)
  have hcharge : -(-delta F.theta B)+
      kappa*(HighPrimary.«prefix» (-delta F.theta B)-(stateOf C T).a/Real.cos (-delta F.theta B))≤
        delta F.theta A+delta F.theta B+kappa*(stateOf C A).b := by
    have hh := hp.2
    nlinarith only [hh,hw.1]
  have hcap : max (-delta F.theta T) 0+max (-delta F.theta D) 0≤frameCap := by
    have hh := (frame_tail_negative_budget F hq).le
    have hb : 0≤ max (-delta F.theta B) 0 := le_max_right _ _
    linarith
  have hpath := HighPrimary.path (stateOf C A) (stateOf C T) (stateOf C D)
    (stateOf C E) L.TD L.DE L.T_positive L.D_negative L.E_negative hz hp.1 hcharge
    (hdelta T) (hdelta D) hcap L.DE_owner L.TD_projection L.DE_projection
  have hreturn := frame_tail_cap F hE L.A_tangent.le
  dsimp [tailCharge] at hreturn
  linarith

theorem frame_nonpositive_AB_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hBT : (forwardAxis 1).Feasible (C.square B) (C.square T))
    (hABnegative : delta F.theta A≤0) (hBTnegative : delta F.theta B≤0) : False := by
  let K := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C K := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame K := FramePhysicalTransport.candidatePushforward F hR le_rfl
  have hBT' : (forwardAxis 1).Feasible (K.square B) (K.square T) := by
    simpa [B,T,next] using hR.preserves_all_axes B (forwardAxis 1)
      (by simpa [B,T,next] using hBT)
  exact ceiling_nonpositive_AB_false F' (by simpa only [hR.same_tangents] using hE)
    hBT' hABnegative hBTnegative

end SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative
