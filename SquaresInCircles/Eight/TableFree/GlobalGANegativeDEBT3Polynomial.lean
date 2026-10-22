module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3PolynomialData

/-!
# Whole-interval DE3 / BT3 numerator, mass and coefficient bounds

Uncompiled Section 8 and the coefficient part of Section 7. Each
certificate is the displayed rational polynomial identity and one
coefficient aggregate on its entire native interval. The exceptional
H numerator retains its positive constant and its first quotient.
No sampled-angle premise or externally trusted computation is used.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Certificate
open WholeIntervalPolynomial

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_mass_certificate (i : Fin 3) :
    centered 0 L (lowMass i)=expansion 3 (centered 0 L (lowMass i)) ∧
      (23/20:ℚ)<lowerOn 3 0 L (lowMass i) := by fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_numerator_certificate (ep : Split) :
    centered 0 L (lowNumerator ep)=expansion 32 (centered 0 L (lowNumerator ep)) ∧
      (17/10000:ℚ)<lowerOn 32 0 L (lowNumerator ep) := by cases ep <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_base_certificate (ep : Split) :
    centered 0 L (lowBase ep)=expansion 12 (centered 0 L (lowBase ep)) ∧
      (37/5:ℚ)<lowerOn 12 0 L (lowBase ep) := by cases ep <;> decide

theorem low_mass_positive (i : Fin 3) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<aeval θ (lowMass i) := by
  have hh := positive_on_interval (by norm_num [L] : (0:ℚ)<L)
    (low_mass_certificate i).1 (low_mass_certificate i).2 hθ
  norm_num at hh
  linarith

theorem low_numerator_positive (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<aeval θ (lowNumerator ep) := by
  have hh := positive_on_interval (by norm_num [L] : (0:ℚ)<L)
    (low_numerator_certificate ep).1 (low_numerator_certificate ep).2 hθ
  norm_num at hh
  linarith

theorem low_base_positive (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<aeval θ (lowBase ep) := by
  have hh := positive_on_interval (by norm_num [L] : (0:ℚ)<L)
    (low_base_certificate ep).1 (low_base_certificate ep).2 hθ
  norm_num at hh
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_mass_certificate (r : HighCase) (i : Fin 4) :
    centered 0 span (highMass r i)=expansion 3 (centered 0 span (highMass r i)) ∧
      (69/100:ℚ)<lowerOn 3 0 span (highMass r i) := by cases r <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_direct_certificate (r : HighCase) (hr : r≠.H) :
    centered 0 span (highNumerator r)=
      expansion (highDegree r) (centered 0 span (highNumerator r)) ∧
    highReserve r<lowerOn (highDegree r) 0 span (highNumerator r) := by
  cases r <;> norm_num at hr <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_H_certificate :
    highNumerator .H=C ((highNumerator .H).eval 0)+X*highHQuotient ∧
    (79/100000:ℚ)<(highNumerator .H).eval 0 ∧
    centered 0 span highHQuotient=expansion 38 (centered 0 span highHQuotient) ∧
    (13/100:ℚ)<lowerOn 38 0 span highHQuotient := by decide

theorem high_mass_positive (r : HighCase) (i : Fin 4) {x : ℝ}
    (hx : x∈Icc (0:ℝ) (8/15)) : 0<aeval x (highMass r i) := by
  have hh := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span)
    (high_mass_certificate r i).1 (high_mass_certificate r i).2 hx
  norm_num at hh
  linarith

theorem high_numerator_positive (r : HighCase) {x : ℝ}
    (hx : x∈Icc (0:ℝ) (8/15)) : 0<aeval x (highNumerator r) := by
  by_cases hr : r=.H
  · subst r
    obtain ⟨hid,h0,hq,hres⟩ := high_H_certificate
    have hquot := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span) hq hres hx
    have h0' : (79/100000:ℝ)<((highNumerator .H).eval 0:ℝ) := by exact_mod_cast h0
    rw [hid]
    simp only [map_add,map_mul,aeval_C,aeval_X]
    have hp := mul_nonneg hx.1 (show 0≤aeval x highHQuotient by norm_num at hquot; linarith)
    linarith
  · have hc := high_direct_certificate r hr
    have hh := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span) hc.1 hc.2 hx
    have hres : (0:ℝ)<(highReserve r:ℝ) := by cases r <;> norm_num [highReserve]
    exact hres.trans hh

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem derivative_mass_certificate (atH : Bool) :
    (centered 0 span (derivativeMass atH)=expansion 3 (centered 0 span (derivativeMass atH)) ∧
      (23/20:ℚ)<lowerOn 3 0 span (derivativeMass atH)) ∧
    (centered 0 span derivativeDMass=expansion 3 (centered 0 span derivativeDMass) ∧
      (23/20:ℚ)<lowerOn 3 0 span derivativeDMass) := by cases atH <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem derivative_certificate (atH : Bool) :
    centered 0 span (derivativeNumerator atH)=
      expansion (derivativeDegree atH) (centered 0 span (derivativeNumerator atH)) ∧
    derivativeReserve atH<lowerOn (derivativeDegree atH) 0 span (derivativeNumerator atH) := by
  cases atH <;> decide

theorem derivative_masses_positive (atH : Bool) {x : ℝ} (hx : x∈Icc (0:ℝ) (8/15)) :
    0<aeval x (derivativeMass atH) ∧ 0<aeval x derivativeDMass := by
  have hc := derivative_mass_certificate atH
  have h0 := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span) hc.1.1 hc.1.2 hx
  have h1 := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span) hc.2.1 hc.2.2 hx
  norm_num at h0 h1
  exact ⟨by linarith,by linarith⟩

theorem derivative_numerator_positive (atH : Bool) {x : ℝ}
    (hx : x∈Icc (0:ℝ) (8/15)) : 0<aeval x (derivativeNumerator atH) := by
  have hc := derivative_certificate atH
  have hh := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span) hc.1 hc.2 hx
  have hr : (0:ℝ)<(derivativeReserve atH:ℝ) := by cases atH <;> norm_num [derivativeReserve]
  exact hr.trans hh

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_auxiliary_certificate :
    (centered 0 span (highBase-1)=expansion 20 (centered 0 span (highBase-1)) ∧
      (399/50:ℚ)<lowerOn 20 0 span (highBase-1)) ∧
    (centered 0 span (-highSineCoefficient)=expansion 6 (centered 0 span (-highSineCoefficient)) ∧
      0<lowerOn 6 0 span (-highSineCoefficient)) ∧
    (centered 0 span (-highC.derivative)=expansion 14 (centered 0 span (-highC.derivative)) ∧
      (22/125:ℚ)<lowerOn 14 0 span (-highC.derivative)) ∧
    highC.eval 0<(1057/1000:ℚ) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem late_coefficient_certificate :
    (centered lateLeft span (-lateDifference.derivative.derivative)=
      expansion 13 (centered lateLeft span (-lateDifference.derivative.derivative)) ∧
      (37/40:ℚ)<lowerOn 13 lateLeft span (-lateDifference.derivative.derivative)) ∧
    (9/50000:ℚ)<lateDifference.eval lateLeft ∧
    (3/62500:ℚ)<lateDifference.eval span := by decide

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Certificate
