module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveASupport
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositivePolynomialData

/-!
# The single polynomial A endpoint envelope

Uncompiled translation of Section 7 of the two-positive split proof.
The full-circle loss is bounded by its exact half-angle expression.
The ratio in that proof increases on the complete intrinsic interval
from one half to the frame cap; no angular subdivision is introduced.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.ASupport
open Secondary PositiveAngularEnvelope

def lossRatio (a : ℝ) : ℝ := a*(a-1/2)^2/(a-1/6)^4

theorem lossRatio_derivative {a : ℝ} (ha : (1/2:ℝ)≤a) :
    HasDerivAt lossRatio
      ((a-1/2)*(-a^2+a+1/12)/(a-1/6)^5) a := by
  have hne : a-1/6≠0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x-1/2) 1 a := (hasDerivAt_id' a).sub_const _
  have h2 : HasDerivAt (fun x : ℝ => x-1/6) 1 a := (hasDerivAt_id' a).sub_const _
  have hd := ((hasDerivAt_id' a).fun_mul (h1.fun_pow 2)).fun_div (h2.fun_pow 4) (pow_ne_zero 4 hne)
  unfold lossRatio
  refine hd.congr_deriv ?_
  rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 4 hne)) (pow_ne_zero 5 hne)]
  norm_num
  ring

theorem lossRatio_monotone : MonotoneOn lossRatio (Icc (1/2:ℝ) frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro a ha
    exact (lossRatio_derivative ha.1).continuousAt.continuousWithinAt
  · intro a ha
    exact lossRatio_derivative ha.1.le
  · intro a ha
    have hden : 0<a-1/6 := by linarith [ha.1]
    have hp := mul_nonneg (show 0≤a by linarith [ha.1])
      (show 0≤1-a by dsimp [frameCap] at ha; linarith [ha.2])
    have hnum : 0≤-a^2+a+1/12 := by nlinarith
    exact div_nonneg (mul_nonneg (by linarith [ha.1]) hnum) (pow_nonneg hden.le 5)

theorem loss_ratio_bound {a : ℝ} (ha : a∈Icc (1/2:ℝ) frameCap) :
    (R/8)*a*(a-1/2)^2≤(43/500)*(a-1/6)^4 := by
  have hpow : 0<(a-1/6)^4 := pow_pos (by linarith [ha.1]) 4
  have hm := lossRatio_monotone ha (by norm_num [frameCap]) ha.2
  have hvalue : lossRatio frameCap=2835/8192 := by norm_num [lossRatio,frameCap]
  rw [hvalue] at hm
  have hclear := (div_le_iff₀ hpow).mp hm
  have hp : 0≤a*(a-1/2)^2 := mul_nonneg (by linarith [ha.1]) (sq_nonneg _)
  have hR : R/8≤99/400 := by linarith [radius_bounds.2]
  have hfirst := mul_le_mul_of_nonneg_right hR hp
  have hsecond := mul_le_mul_of_nonneg_left hclear (show (0:ℝ)≤99/400 by norm_num)
  nlinarith only [hfirst,hsecond,hpow]

theorem circle_loss_bound {a : ℝ} (ha : a∈Icc alpha frameCap) :
    axialCharge a-circleCharge a≤(R/8)*a*(a-1/2)^2 := by
  have ha0 : a∈Icc 0 frameCap := ⟨by linarith [ha.1,alpha_bounds.1],ha.2⟩
  obtain ⟨d,hdd⟩ : ∃ d : ℝ,d=(a-alpha)/2 := ⟨_,rfl⟩
  have hd : 0≤d := by rw [hdd]; linarith [ha.1]
  have hdu : d≤(a-1/2)/2 := by rw [hdd]; linarith [alpha_bounds.1]
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=d)
  have hsin := Real.sin_le (show 0≤a/2 by linarith [ha0.1])
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hs := (half_trig ha0).1
  have hdsq : d^2≤((a-1/2)/2)^2 := pow_le_pow_left₀ hd hdu 2
  have h₁ := mul_le_mul_of_nonneg_left
    (show 1-Real.cos d≤d^2/2 by linarith)
    (show 0≤2*R*Real.sin (a/2) by have := mul_nonneg hR hs; linarith)
  have h₂ := mul_le_mul_of_nonneg_right hsin (show 0≤R*d^2 by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hdsq
    (show 0≤R*a/2 by have := mul_nonneg hR ha0.1; linarith)
  rw [charge_difference,← hdd]
  linarith only [h₁,h₂,h₃]

/-- The high endpoint uses this one quartic correction across the support join. -/
theorem high_charge_lower {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) :
    axialCharge a-(43/500)*(a-1/6)^4≤charge a := by
  by_cases hcut : a≤alpha
  · rw [charge,if_pos hcut]
    have hp : 0≤(43/500:ℝ)*(a-1/6)^4 := by positivity
    linarith
  · have hca := circle_loss_bound (show a∈Icc alpha frameCap from
      ⟨(lt_of_not_ge hcut).le,ha.2⟩)
    have hratio := loss_ratio_bound (show a∈Icc (1/2:ℝ) frameCap from
      ⟨by linarith [alpha_bounds.1,lt_of_not_ge hcut],ha.2⟩)
    rw [charge,if_neg hcut]
    linarith

theorem axial_le_abar : axial≤(Certificate.abar:ℝ) := by
  have hs := axial_circle
  have hp := axial_bounds.1
  norm_num [qCap,Certificate.abar] at hs ⊢
  nlinarith

theorem low_polynomial_charge {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    Polynomial.aeval a Certificate.lowJ≤charge a := by
  have ha' : a∈Icc 0 frameCap := ⟨ha.1,by norm_num [frameCap]; linarith [ha.2]⟩
  have ht := PositiveTD.Certificate.taylor_bounds ha'
  have hs : 0≤Real.sin a := (transport_trig ha').2.2.1
  have hcoef : (1/2:ℝ)-(Certificate.abar:ℝ)≤0 := by norm_num [Certificate.abar]
  have h₁ := mul_le_mul_of_nonpos_left ht.2.2.1 hcoef
  have h₂ := mul_le_mul_of_nonneg_right axial_le_abar hs
  have hab : (Certificate.abar:ℝ)=1414575672/1000000000 := by norm_num [Certificate.abar]
  rw [hab] at h₁ h₂
  rw [charge_low ha.2]
  simp only [Certificate.lowJ,map_add,map_sub,map_mul,map_one,Polynomial.aeval_C,eq_ratCast]
  push_cast
  dsimp only [axialCharge]
  linarith only [ht.2.2.2.2.1,h₁,h₂]

theorem high_polynomial_charge {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) :
    Polynomial.aeval a Certificate.highJ≤charge a := by
  have ha' : a∈Icc 0 frameCap := ⟨by linarith [ha.1],ha.2⟩
  have ht := PositiveTD.Certificate.taylor_bounds ha'
  have hs : 0≤Real.sin a := (transport_trig ha').2.2.1
  have hcoef : (1/2:ℝ)-(Certificate.abar:ℝ)≤0 := by norm_num [Certificate.abar]
  have h₁ := mul_le_mul_of_nonpos_left ht.2.2.1 hcoef
  have h₂ := mul_le_mul_of_nonneg_right axial_le_abar hs
  have hmain := high_charge_lower ha
  have hab : (Certificate.abar:ℝ)=1414575672/1000000000 := by norm_num [Certificate.abar]
  rw [hab] at h₁ h₂
  simp only [Certificate.highJ,Certificate.t,map_add,map_sub,map_mul,map_pow,map_one,
    Polynomial.aeval_C,Polynomial.aeval_X,eq_ratCast]
  push_cast
  dsimp only [axialCharge] at hmain
  linarith only [hmain,ht.2.2.2.2.1,h₁,h₂]

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.ASupport
