module

public import SquaresInCircles.Eight.Boundary.Candidate.Model

/-!
# Eight squares: candidate frames along a radius expansion

If `D` is an expansion of the boundary cycle `C` to a larger level, a candidate frame of `D` is a
candidate frame of `C` with the same angles (`Frame.pullback`, `Frame.pullback_theta`): the two
cycles have the same frames, centre directions and tangents, and every signed axis that separates
two consecutive squares of `C` separates them in `D`, where it is a forward axis.
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
