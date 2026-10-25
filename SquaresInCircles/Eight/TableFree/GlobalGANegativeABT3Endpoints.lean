module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Norms

/-!
# The fourteen actual reference endpoint inequalities

Uncompiled Sections 6--8. Each endpoint follows from its exact rational
numerator, the separately positive cubic masses, the norm square bounds,
and the signed nonradical Taylor comparison. The cosine scale is removed
only after its positivity has been established.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

namespace Analytic
open Certificate (Curve)

theorem curve_positive (e : Curve) {z : ℝ} (hz : Domain e z) : 0<curve e z := by
  have hx := native_domain e hz
  have hr := fun j => Certificate.mass_positive e j hx
  have hn := scaledNorm_nonnegative e hz
  have hsq := norm_square_upper e hz
  have hA := nonradical_lower e hz
  have hnum := Certificate.numerator_positive e hx
  have hpos : 0<nonradical e z-R*normSum (Certificate.family e) (scaledNorm e z) := by
    by_cases hf : Certificate.family e=.low
    · have hh := PositiveTD.Certificate.num3_transfer (hr 0) (hr 1) (hr 2)
        (hn 0) (hn 1) (hn 2) (hsq 0) (hsq 1) (hsq 2) hA
        (by simpa only [Certificate.numerator,if_pos hf] using hnum)
      simpa only [normSum,NegativeAPositiveTD.normSum,hf,↓reduceIte] using hh
    · have hh := PositiveTD.Certificate.num4_transfer (hr 0) (hr 1) (hr 2) (hr 3)
        (hn 0) (hn 1) (hn 2) (hn 3) (hsq 0) (hsq 1) (hsq 2) (hsq 3) hA
        (by simpa only [Certificate.numerator,if_neg hf] using hnum)
      simpa only [normSum,NegativeAPositiveTD.normSum,if_neg hf] using hh
  rw [←curve_identity e hz] at hpos
  exact (mul_pos_iff_of_pos_left (scale_positive e hz)).mp hpos

theorem endpoint_positive (e : Curve) {z : ℝ} (hz : Domain e z) :
    0<baseline (Certificate.atG e) (Explicit.k (Certificate.family e) z)
      (Explicit.l (Certificate.family e) z) (Explicit.m (Certificate.family e) z)
      (angle e z) z+charge e z := by
  have hh := curve_positive e hz
  have hl := reduced_le_baseline (Certificate.family e) (Certificate.atG e) (angle e z) z
  dsimp [curve] at hh
  linarith
end Analytic

theorem low_endpoints {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      V R (Explicit.k .low z) 1 z ∧
    0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      mixedG (Explicit.k .low z) (Explicit.l .low z) z ∧
    0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z-
      (109/160)*(frameCap-z)+V R (Explicit.k .low z) 1 frameCap ∧
    0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z-
      (109/160)*(frameCap-z)+V R (Explicit.k .low z) (Explicit.l .low z) frameCap ∧
    0<baseline true (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z z := by
  have hD (e : Certificate.Curve) (hf : Certificate.family e=.low)
      (hs : Certificate.start e=0) : Analytic.Domain e z := by
    simp only [Analytic.Domain,hf,hs,Certificate.right,Certificate.split]
    push_cast
    exact hz
  have h₀ : 0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      V R (Explicit.k .low z) 1 z := Analytic.endpoint_positive .lowH (hD .lowH rfl rfl)
  have h₁ : 0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      mixedG (Explicit.k .low z) (Explicit.l .low z) z :=
    Analytic.endpoint_positive .lowM (hD .lowM rfl rfl)
  have h₂ : 0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      (-(109/160)*(frameCap-z)+V R (Explicit.k .low z) 1 frameCap) :=
    Analytic.endpoint_positive .lowSH (hD .lowSH rfl rfl)
  have h₃ : 0<baselineZero (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z+
      (-(109/160)*(frameCap-z)+V R (Explicit.k .low z) (Explicit.l .low z) frameCap) :=
    Analytic.endpoint_positive .lowSG (hD .lowSG rfl rfl)
  have h₄ : 0<baseline true (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z z+0 :=
    Analytic.endpoint_positive .lowGA (hD .lowGA rfl rfl)
  refine ⟨h₀,h₁,?_,?_,?_⟩
  · linarith
  · linarith
  · simpa using h₄

theorem high_endpoints {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.k .high z) 1 z ∧
    0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.k .high z) (Explicit.l .high z) z ∧
    0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.m .high z) (Explicit.l .high z) z ∧
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z z ∧
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z z := by
  have hD (e : Certificate.Curve) (hf : Certificate.family e=.high)
      (hs : Certificate.start e=1/4) : Analytic.Domain e z := by
    simp only [Analytic.Domain,hf,hs,Certificate.right]
    push_cast
    exact hz
  have h₀ : 0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.k .high z) 1 z := Analytic.endpoint_positive .highH (hD .highH rfl rfl)
  have h₁ : 0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.k .high z) (Explicit.l .high z) z :=
    Analytic.endpoint_positive .highG (hD .highG rfl rfl)
  have h₂ : 0<baselineZero (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) z+
      V R (Explicit.m .high z) (Explicit.l .high z) z :=
    Analytic.endpoint_positive .highB (hD .highB rfl rfl)
  have h₃ : 0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      z z+0 := Analytic.endpoint_positive .highGA (hD .highGA rfl rfl)
  have h₄ : 0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      z z+0 := Analytic.endpoint_positive .highAB (hD .highAB rfl rfl)
  rw [add_zero] at h₃ h₄
  exact ⟨h₀,h₁,h₂,h₃,h₄⟩

theorem GA_cut_endpoints {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) (1/4) z+
      V R (Explicit.k .high z) 1 (z-1/4) ∧
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) (1/4) z+
      V R (Explicit.m .high z) (Explicit.l .high z) (z-1/4) := by
  have hD (e : Certificate.Curve) (hf : Certificate.family e=.high)
      (hs : Certificate.start e=1/4) : Analytic.Domain e z := by
    simp only [Analytic.Domain,hf,hs,Certificate.right]
    push_cast
    exact hz
  have hH : 0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      (1/4) z+V R (Explicit.k .high z) 1 (z-1/4) :=
    Analytic.endpoint_positive .gaH (hD .gaH rfl rfl)
  have hB : 0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      (1/4) z+V R (Explicit.m .high z) (Explicit.l .high z) (z-1/4) :=
    Analytic.endpoint_positive .gaB (hD .gaB rfl rfl)
  exact ⟨hH,hB⟩

theorem AB_cut_endpoints {z : ℝ} (hz : z∈Icc (19/50:ℝ) (7/10:ℝ)) :
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) (19/50) z+
      V R (Explicit.k .high z) (Explicit.l .high z) (z-19/50) ∧
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) (19/50) z+
      V R (Explicit.k .high z) 1 (z-19/50) := by
  have hD (e : Certificate.Curve) (hf : Certificate.family e=.high)
      (hs : Certificate.start e=19/50) : Analytic.Domain e z := by
    simp only [Analytic.Domain,hf,hs,Certificate.right]
    push_cast
    exact hz
  have hG : 0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      (19/50) z+V R (Explicit.k .high z) (Explicit.l .high z) (z-19/50) :=
    Analytic.endpoint_positive .abG (hD .abG rfl rfl)
  have hH : 0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z)
      (19/50) z+V R (Explicit.k .high z) 1 (z-19/50) :=
    Analytic.endpoint_positive .abH (hD .abH rfl rfl)
  exact ⟨hG,hH⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
