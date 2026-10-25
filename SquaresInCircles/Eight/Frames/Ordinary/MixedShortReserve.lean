module

public import SquaresInCircles.Eight.Frames.Ordinary.NegativeShortSlope

/-!
# Eight squares: the positive-surplus companion of the short same-block reserve

The positive angle may range up to the original frame cap; only the
common negative mass is bounded by .6. Monotonicity moves the positive
angle to the true cap before its trigonometric coefficients are bounded.
In particular no false separate lower bound for phi(P) is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OrdinaryMixedShortReserve
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeShortSlope

lemma constant_add {f : ℝ→ℝ} {l u : ℝ}
    (hf : ConcaveOn ℝ (Icc l u) f) (C : ℝ) :
    ConcaveOn ℝ (Icc l u) (fun t => C+f t) := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy r v hr hv hrv
  have hh := hf.2 hx hy hr hv hrv
  have he := congrArg (fun w : ℝ => w*C) hrv
  simp only [smul_eq_mul] at hh ⊢
  nlinarith only [hh,he]

def phiD (t : ℝ) : ℝ := Real.cos t-Real.sin t

lemma phi_hasDerivAt (t : ℝ) : HasDerivAt PositiveAngularEnvelope.phi (phiD t) t := by
  have h := (Real.hasDerivAt_cos t).fun_add (Real.hasDerivAt_sin t)
  exact h.congr_deriv (by unfold phiD; ring)

end SquaresInCircles.Eight.OrdinaryMixedShortReserve
