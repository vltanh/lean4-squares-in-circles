module

public import SquaresInCircles.Eight.Owners.BT.TailTransfer

/-!
# Eight squares: complete positive-BT1 scalar gain

One strictly concave rational polynomial controls the full original
error interval.  Its two endpoint values are fixed positive rational
numbers.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.OnePositive

open Polynomial FramePair FrameCircleArc

def gain (x : ℝ) : ℝ :=
  x+kappa*((c0-1/2)*(1-Real.cos x)-(R-Real.cos x)*Real.sin x)

namespace Certificate

def P : ℚ[X] := C (1-(49/50)*(979/1000))+C ((49/50)*(399/2000))*X-
  C ((49/50)*(1/2-979/6000))*X^2-C ((49/50)*(399/24000))*X^3+
    C ((49/50)*(1/12-979/120000))*X^4-C ((49/50)/240)*X^6
def second : ℚ[X] :=
  C (-2*(49/50)*(1/2-979/6000))-C (6*(49/50)*(399/24000))*X+
    C (12*(49/50)*(1/12-979/120000))*X^2-C (30*(49/50)/240)*X^4

theorem second_identity : P.derivative.derivative=second := by
  ext n
  simp only [coeff_derivative]
  rcases n with _|_|_|_|_|n <;>
    simp only [P,second,coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C] <;>
    norm_num

theorem endpoints : 0<P.eval 0 ∧ 0<P.eval (7/10) := by
  constructor <;> norm_num [P]

theorem second_negative {x : ℝ} (hx : x∈Icc 0 frameCap) :
    aeval x P.derivative.derivative<0 := by
  rw [second_identity]
  have h2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h4 := pow_nonneg hx.1 4
  dsimp [frameCap] at hx h2
  norm_num [second]
  nlinarith only [hx.1,h2,h4]

theorem concave : ConcaveOn ℝ (Icc 0 frameCap) (fun x : ℝ => aeval x P) :=
  concave_of_deriv2 (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt P x)
    (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt P.derivative x)
    (fun x hx => (second_negative hx).le)

theorem positive {x : ℝ} (hx : x∈Icc 0 frameCap) : 0<aeval x P := by
  apply concave_gt_of_endpoints concave hx
  · norm_num [P]
  · have he : aeval (frameCap:ℝ) P=((P.eval (7/10):ℚ):ℝ) := by
      rw [show (frameCap:ℝ)=((7/10:ℚ):ℝ) by norm_num [frameCap]]
      exact TailPolynomial.rational_aeval _ _
    rw [he]
    exact_mod_cast endpoints.2

theorem identity_eval (x : ℝ) : x*aeval x P=
    x+kappa*((399/1000)*(x^2/2-x^4/24)-
      (979/1000+x^2/2)*(x-x^3/6+x^5/120)) := by
  simp [P,kappa] <;> ring

end Certificate

theorem gain_lower {x : ℝ} (hx : x∈Icc 0 frameCap) : x*aeval x Certificate.P≤gain x := by
  have hs := sin_upper_five hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hu := cos_upper_four hx.1
  have tr := transport_trig hx
  have hR : R-Real.cos x≤979/1000+x^2/2 := by linarith [radius_upper]
  have hnegative := mul_le_mul hR hs tr.2.2.1
    (show 0≤(979/1000:ℝ)+x^2/2 by positivity)
  have hdiag : (399/1000:ℝ)≤c0-1/2 := by linarith [FrameHighArc.diagonal_bounds.1]
  have hpositive := mul_le_mul_of_nonneg_right hdiag
    (sub_nonneg.mpr (Real.cos_le_one x))
  have hdrop : x^2/2-x^4/24≤1-Real.cos x := by linarith
  have hdrop' := mul_le_mul_of_nonneg_left hdrop (by norm_num : (0:ℝ)≤399/1000)
  rw [Certificate.identity_eval]
  dsimp [gain,kappa]
  nlinarith only [hnegative,hpositive,hdrop']

theorem gain_nonnegative {x : ℝ} (hx : x∈Icc 0 frameCap) : 0≤gain x :=
  (mul_nonneg hx.1 (Certificate.positive hx).le).trans (gain_lower hx)

end SquaresInCircles.Eight.GlobalBT.OnePositive
