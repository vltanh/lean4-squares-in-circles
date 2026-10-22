module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2Ranges
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveAEnvelope

/-!
# The sixth-power A support allowance for negative DE

Uncompiled transcription of Section 5.  The exact sorted-support loss
is bounded on the complete intrinsic interval [1/2,7/10]; its ratio to
(a-1/6)^6 increases there.  There is no auxiliary angle subdivision.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.AEnvelope
open Candidate Secondary TwoPositive.ASupport

def ratio (a : ℝ) : ℝ := a*(a-1/2)^2/(a-1/6)^6

theorem ratio_derivative {a : ℝ} (ha : (1/2:ℝ)≤a) :
    HasDerivAt ratio ((a-1/2)*(-3*a^2+2*a+1/12)/(a-1/6)^7) a := by
  have hne : a-1/6≠0 := by linarith
  have hd := ((hasDerivAt_id a).mul (((hasDerivAt_id a).sub_const (1/2)).pow 2)).div
    (((hasDerivAt_id a).sub_const (1/6)).pow 6) (pow_ne_zero 6 hne)
  convert hd using 1
  · rfl
  · field_simp [hne]
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
  have hR := PositiveTD.Certificate.radius_le_Rbar
  have hfirst := mul_le_mul_of_nonneg_right hR hx
  have hsecond := mul_le_mul_of_nonneg_left hclear
    (show (0:ℝ)≤(PositiveTD.Certificate.Rbar:ℝ)/8 by norm_num [PositiveTD.Certificate.Rbar])
  norm_num [PositiveTD.Certificate.Rbar] at hfirst hsecond
  nlinarith only [hfirst,hsecond,hp]

theorem charge_lower {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) :
    axialCharge a-(151/500)*(a-1/6)^6≤charge a := by
  by_cases hcut : a≤alpha
  · rw [charge,if_pos hcut]
    have hh : 0≤(151/500:ℝ)*(a-1/6)^6 := by positivity
    linarith
  · have hcircle := circle_loss_bound ⟨(lt_of_not_ge hcut).le,ha.2⟩
    have hr := loss_bound (a:=a) ⟨by linarith [alpha_bounds.1,lt_of_not_ge hcut],ha.2⟩
    rw [charge,if_neg hcut]
    linarith

theorem low_polynomial_charge {a : ℝ} (ha : a∈Icc (0:ℝ) (1/6)) :
    Polynomial.aeval a Certificate.J0≤charge a := by
  simpa only [Certificate.J0,Certificate.abar,TwoPositive.Certificate.lowJ,
    TwoPositive.Certificate.abar] using TwoPositive.ASupport.low_polynomial_charge ha

theorem high_polynomial_charge {a : ℝ} (ha : a∈Icc (1/6:ℝ) frameCap) :
    Polynomial.aeval a Certificate.J1≤charge a := by
  have ha' : a∈Icc 0 frameCap := ⟨by linarith [ha.1],ha.2⟩
  have ht := PositiveTD.Certificate.taylor_bounds ha'
  have hs : 0≤Real.sin a := (transport_trig ha').2.2.1
  have hcoef : (1/2:ℝ)-(Certificate.abar:ℝ)≤0 := by norm_num [Certificate.abar]
  have h₁ := mul_le_mul_of_nonpos_left ht.2.2.1 hcoef
  have hax : axial≤(Certificate.abar:ℝ) := axial_le_abar
  have h₂ := mul_le_mul_of_nonneg_right hax hs
  have hmain := charge_lower ha
  norm_num only [Certificate.J1,Certificate.J0,map_add,map_sub,
    map_mul,map_pow,map_one,Polynomial.aeval_C,Polynomial.aeval_X,Rat.cast_sub,
    PositiveTD.Certificate.L]
  dsimp [axialCharge] at hmain
  nlinarith only [hmain,ht.2.2.2.2.1,h₁,h₂]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.AEnvelope
