module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Path

/-!
# Excluding every original BT0 owner

Every DE owner, radial kind and signed error is dispatched.  Both
zero-edge owners, both signs of B and all original weak axis ties
remain available.  Fixed-ray expansion preserves the supplied BT0
witness, so the contradiction belongs to the source radius.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open Candidate FramePair

theorem ceiling_BT0_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 0).Feasible (C.square B) (C.square T)) : False := by
  obtain ⟨j,hj⟩ := F.forward_complete D (C.selected D) (C.feasible D)
  have hDE : (forwardAxis j).Feasible (C.square D) (C.square E) := hj ▸ C.feasible D
  by_cases htwo : j=2
  · exact ceiling_BT0_ordinary_false F hE hBT j hDE (Or.inl htwo)
  by_cases hpositive : 0≤delta F.theta D
  · exact ceiling_BT0_ordinary_false F hE hBT j hDE (Or.inr (Or.inl hpositive))
  by_cases houter : C.kind E=.outer
  · exact ceiling_BT0_ordinary_false F hE hBT j hDE (Or.inr (Or.inr houter))
  have howner := (GlobalQuarterSign.frame_DE F (by norm_num [Q0]) hE).2 j hDE
  have hthree : j=3 := howner.resolve_left htwo
  have hDE3 : (forwardAxis 3).Feasible (C.square D) (C.square E) := by
    simpa only [hthree] using hDE
  exact CoreDE3.ceiling_false F hE hBT hDE3 houter (le_of_lt (lt_of_not_ge hpositive))

/-- This complete original-axis exclusion has only the intrinsic
nonpositive-E chart condition.  Every tail branch is proved above. -/
theorem frame_BT0_false {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hBT : (forwardAxis 0).Feasible (C.square B) (C.square T)) : False := by
  let K := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C K := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame K := FramePhysicalTransport.candidatePushforward F hR le_rfl
  apply ceiling_BT0_false F'
  · simpa only [hR.same_tangents] using hE
  · simpa [B,T,next] using hR.preserves_all_axes B (forwardAxis 0)
      (by simpa [B,T,next] using hBT)

theorem frame_BT_owner_ne_zero {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square B) (C.square T)) : j≠0 := by
  intro hzero
  subst j
  exact frame_BT0_false F hq hE hj

end SquaresInCircles.Eight.TableFree.GlobalBT
