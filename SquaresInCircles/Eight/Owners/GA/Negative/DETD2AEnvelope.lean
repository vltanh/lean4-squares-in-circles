module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveAEnvelope

/-!
# Eight squares: the sixth-power A support allowance for negative DE

The exact sorted-support loss
is bounded on the complete intrinsic interval [1/2,7/10]; its ratio to
(a-1/6)^6 increases there.  There is no auxiliary angle subdivision.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.AEnvelope
open Candidate Secondary TwoPositive.ASupport

def ratio (a : ℝ) : ℝ := a*(a-1/2)^2/(a-1/6)^6

theorem ratio_derivative {a : ℝ} (ha : (1/2:ℝ)≤a) :
    HasDerivAt ratio ((a-1/2)*(-3*a^2+2*a+1/12)/(a-1/6)^7) a := by
  have hne : a-1/6≠0 := by linarith
  have hp2 : HasDerivAt (fun y : ℝ => (y-1/2)^2) (2*(a-1/2)) a :=
    (((hasDerivAt_id' a).sub_const (1/2:ℝ)).pow 2).congr_deriv (by norm_num)
  have hp6 : HasDerivAt (fun y : ℝ => (y-1/6)^6) (6*(a-1/6)^5) a :=
    (((hasDerivAt_id' a).sub_const (1/6:ℝ)).pow 6).congr_deriv (by norm_num)
  have hd := ((hasDerivAt_id' a).fun_mul hp2).fun_div hp6 (pow_ne_zero 6 hne)
  have hf : ratio=fun y : ℝ => y*(y-1/2)^2/(y-1/6)^6 := rfl
  rw [hf]
  refine hd.congr_deriv ?_
  field_simp
  ring

theorem ratio_monotone : MonotoneOn ratio (Icc (1/2:ℝ) frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro a ha
    exact (ratio_derivative ha.1).continuousAt.continuousWithinAt
  · intro a ha
    exact ratio_derivative ha.1.le
  · intro a ha
    have ha0 : 0≤a := by linarith [ha.1]
    have hcap : a≤7/10 := by simpa only [frameCap] using ha.2.le
    have hsq : a^2≤(7/10)*a := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hcap)]
    have hnum : 0≤-3*a^2+2*a+1/12 := by nlinarith
    exact div_nonneg (mul_nonneg (by linarith [ha.1]) hnum)
      (pow_nonneg (by linarith [ha.1]) 7)

theorem loss_bound {a : ℝ} (ha : a∈Icc (1/2:ℝ) frameCap) :
    (R/8)*a*(a-1/2)^2≤(151/500)*(a-1/6)^6 := by
  have hp : 0<(a-1/6)^6 := pow_pos (by linarith [ha.1]) 6
  have hm := ratio_monotone ha (by norm_num [frameCap]) ha.2
  have he : ratio frameCap=637875/524288 := by norm_num [ratio,frameCap]
  rw [he] at hm
  have hclear := (div_le_iff₀ hp).mp hm
  have hx : 0≤a*(a-1/2)^2 := mul_nonneg (by linarith [ha.1]) (sq_nonneg _)
  have hR : R≤(494696877/250000000:ℝ) := by
    have h := PositiveTD.Certificate.radius_le_Rbar
    rw [show ((PositiveTD.Certificate.Rbar:ℚ):ℝ)=494696877/250000000 by
      norm_num [PositiveTD.Certificate.Rbar]] at h
    exact h
  have hfirst := mul_le_mul_of_nonneg_right hR hx
  have hsecond := mul_le_mul_of_nonneg_left hclear
    (show (0:ℝ)≤494696877/250000000 by norm_num)
  linarith only [hfirst,hsecond,hp]

theorem charge_lower {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) :
    axialCharge a-(151/500)*(a-1/6)^6≤TwoPositive.ASupport.charge a := by
  by_cases hcut : a≤GlobalGA.TwoPositive.ASupport.alpha
  · rw [TwoPositive.ASupport.charge,ite_eq_left hcut]
    have hh : 0≤(151/500:ℝ)*(a-1/6)^6 := by positivity
    linarith
  · have hcircle := circle_loss_bound ⟨(lt_of_not_ge hcut).le,ha.2⟩
    have hr := loss_bound (a:=a) ⟨by linarith [alpha_bounds.1,lt_of_not_ge hcut],ha.2⟩
    rw [TwoPositive.ASupport.charge,ite_eq_right hcut]
    linarith

theorem low_polynomial_charge {a : ℝ} (ha : a∈Icc (0:ℝ) (1/6)) :
    Polynomial.aeval a Certificate.J0≤TwoPositive.ASupport.charge a := by
  simpa only [Certificate.J0,Certificate.abar,TwoPositive.Certificate.lowJ,
    TwoPositive.Certificate.abar] using TwoPositive.ASupport.low_polynomial_charge ha

theorem high_polynomial_charge {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) :
    Polynomial.aeval a Certificate.J1≤TwoPositive.ASupport.charge a := by
  have ha' : a∈Icc 0 frameCap := ⟨by linarith [ha.1],ha.2⟩
  have ht := PositiveTD.Certificate.taylor_bounds ha'
  have hs : 0≤Real.sin a := (transport_trig ha').2.2.1
  have hcoef : (1/2:ℝ)-(Certificate.abar:ℝ)≤0 := by norm_num [Certificate.abar]
  have h₁ := mul_le_mul_of_nonpos_left ht.2.2.1 hcoef
  have hax : axial≤(Certificate.abar:ℝ) := axial_le_abar
  have h₂ := mul_le_mul_of_nonneg_right hax hs
  have hmain := charge_lower ha
  have hJ : Polynomial.aeval a Certificate.J1=(1/2)*(Polynomial.aeval a PositiveTD.Certificate.C10-1)+
      ((1/2:ℝ)-(Certificate.abar:ℝ))*Polynomial.aeval a PositiveTD.Certificate.S9-
        (151/500)*(a-1/6)^6 := by
    simp only [Certificate.J1,Certificate.J0,map_add,map_sub,map_mul,map_pow,map_one,
      Polynomial.aeval_C,Polynomial.aeval_X,eq_ratCast]
    rw [show ((1/2:ℚ):ℝ)=1/2 by norm_num,show ((151/500:ℚ):ℝ)=151/500 by norm_num,
      show ((PositiveTD.Certificate.L:ℚ):ℝ)=1/6 by norm_num [PositiveTD.Certificate.L]]
  rw [hJ]
  dsimp [axialCharge] at hmain
  generalize ((Certificate.abar:ℚ):ℝ)=A at h₁ h₂ ⊢
  linarith only [hmain,ht.2.2.2.2.1,h₁,h₂]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.AEnvelope
