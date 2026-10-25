module

public import SquaresInCircles.Eight.Candidate.Model

/-!
# Frame pullback along an actual radius expansion

The proof uses only equality of frames, rays and signed tangent ratios, plus
preservation of every originally feasible signed axis. It is independent of
candidate capture and its generated affine inputs. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate

def Frame.pullback {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : Frame D) (hR : RadiusExpansion C D) : Frame C where
  theta := F.theta
  theta_A := F.theta_A
  canonical_eq i := by
    have he : C.canonicalAngle i=D.canonicalAngle i := by
      simp [BoundaryCycle.canonicalAngle,BoundaryCycle.alpha,← hR.same_rays,← hR.same_tangents]
    rw [he]
    exact F.canonical_eq i
  spread := F.spread
  gap_lower i := by simpa only [hR.same_rays] using F.gap_lower i
  gap_upper i := by simpa only [hR.same_rays] using F.gap_upper i
  forward_complete i axis hi := F.forward_complete i axis (hR.preserves_all_axes i axis hi)

@[simp] theorem Frame.pullback_theta {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : Frame D) (hR : RadiusExpansion C D) : (F.pullback hR).theta=F.theta := rfl

end SquaresInCircles.Eight.Candidate
