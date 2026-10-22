module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2PolynomialData

/-!
# Whole-interval positivity for the genuine negative-EH / TD2 endpoints

Uncompiled transcription of the small-error and remaining-error
certificate sections. The two low T endpoints retain their centered
quadratic; all other numerators use the displayed coefficient aggregate.
Every mass is proved positive on its entire native interval. These are
exact finite polynomial identities, not a grid of angle evaluations.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Certificate
open WholeIntervalPolynomial ChebyshevLeadingBounds
open PositiveTD.Certificate (L h)

theorem small_interval (r : SmallCase) : smallLeft r<smallRight r := by
  cases r <;> norm_num [smallLeft,smallRight,v,L,h]
theorem far_interval (r : FarCase) : farLeft r<farRight r := by
  cases r <;> norm_num [farLeft,farRight,v,u,h]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem small_direct_certificate (r : SmallCase) (e : Split) (hr : smallQuadratic r e=false) :
    centered (smallLeft r) (smallRight r) (smallNumerator r e)=
      expansion (smallDegree r e) (centered (smallLeft r) (smallRight r) (smallNumerator r e)) ∧
    smallReserve r e<lowerOn (smallDegree r e) (smallLeft r) (smallRight r) (smallNumerator r e) := by
  cases r <;> cases e <;> norm_num [smallQuadratic] at hr <;> decide

def smallCoefficients (r : SmallCase) (e : Split) : ℕ→ℚ :=
  coefficient (smallDegree r e) (centered (smallLeft r) (smallRight r) (smallNumerator r e))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem small_quadratic_certificate (r : SmallCase) (e : Split) (hr : smallQuadratic r e=true) :
    centered (smallLeft r) (smallRight r) (smallNumerator r e)=
      C (smallCoefficients r e 0-smallCoefficients r e 2)+C (smallCoefficients r e 1)*X+
      C (2*smallCoefficients r e 2)*X^2+tail (smallCoefficients r e) 3 (smallDegree r e-2) ∧
    0<smallCoefficients r e 2 ∧
    smallReserve r e<quadraticReserve (smallCoefficients r e) (smallDegree r e-2) := by
  cases r <;> cases e <;> norm_num [smallQuadratic] at hr <;> decide

theorem small_numerator_positive (r : SmallCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) : 0<aeval θ (smallNumerator r e) := by
  have hreserve : (0:ℝ)<(smallReserve r e:ℝ) := by
    cases r <;> cases e <;> norm_num [smallReserve]
  cases hr : smallQuadratic r e
  · have hc := small_direct_certificate r e hr
    exact hreserve.trans (positive_on_interval (small_interval r) hc.1 hc.2 hθ)
  · have hc := small_quadratic_certificate r e hr
    have hh := quadratic_on_interval (small_interval r) hc.1 hc.2.1 hθ
    have hq : (smallReserve r e:ℝ)<
        (quadraticReserve (smallCoefficients r e) (smallDegree r e-2):ℝ) := by
      exact_mod_cast hc.2.2
    exact (hreserve.trans hq).trans_le hh

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem small_mass_certificate (r : SmallCase) (e : Split) (i : Fin 4) :
    centered (smallLeft r) (smallRight r) (smallMass r e i)=
      expansion 12 (centered (smallLeft r) (smallRight r) (smallMass r e i)) ∧
    (3/5:ℚ)<lowerOn 12 (smallLeft r) (smallRight r) (smallMass r e i) := by
  cases r <;> cases e <;> fin_cases i <;> decide

theorem small_mass_positive (r : SmallCase) (e : Split) (i : Fin 4) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) : 0<aeval θ (smallMass r e i) := by
  have hc := small_mass_certificate r e i
  have hh := positive_on_interval (small_interval r) hc.1 hc.2 hθ
  norm_num at hh
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem far_certificate (r : FarCase) (e : Split) :
    centered (farLeft r) (farRight r) (farNumerator r e)=
      expansion (farDegree r e) (centered (farLeft r) (farRight r) (farNumerator r e)) ∧
    farReserve r e<lowerOn (farDegree r e) (farLeft r) (farRight r) (farNumerator r e) := by
  cases r <;> cases e <;> decide

theorem far_numerator_positive (r : FarCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) : 0<aeval θ (farNumerator r e) := by
  have hc := far_certificate r e
  have hh := positive_on_interval (far_interval r) hc.1 hc.2 hθ
  have hr : (0:ℝ)<(farReserve r e:ℝ) := by cases r <;> cases e <;> norm_num [farReserve]
  exact hr.trans hh

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem far_mass_certificate (r : FarCase) (e : Split) (i : Fin 4) :
    centered (farLeft r) (farRight r) (farMass r e i)=
      expansion 12 (centered (farLeft r) (farRight r) (farMass r e i)) ∧
    (3/5:ℚ)<lowerOn 12 (farLeft r) (farRight r) (farMass r e i) := by
  cases r <;> cases e <;> fin_cases i <;> decide

theorem far_mass_positive (r : FarCase) (e : Split) (i : Fin 4) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) : 0<aeval θ (farMass r e i) := by
  have hc := far_mass_certificate r e i
  have hh := positive_on_interval (far_interval r) hc.1 hc.2 hθ
  norm_num at hh
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem far_qstar_T_certificate :
    centered u h (farQStar-farMu .high .atT)=
      expansion 6 (centered u h (farQStar-farMu .high .atT)) ∧
    (629/1000000:ℚ)<lowerOn 6 u h (farQStar-farMu .high .atT) := by decide

theorem far_qstar_T_positive {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    0<aeval θ (farQStar-farMu .high .atT) := by
  have hh := positive_on_interval (by norm_num [u,h] : u<h)
    far_qstar_T_certificate.1 far_qstar_T_certificate.2 hθ
  norm_num at hh
  linarith

theorem far_qstar_A_positive {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    0<aeval θ (farQStar-farC .high) := by
  norm_num [farQStar,farL,farC,h]
  linarith [hθ.2]

theorem small_domain (r : SmallCase) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) :
    θ∈Icc (Explicit.left .small (smallFamily r)) (Explicit.right .small (smallFamily r)) := by
  cases r <;>
    norm_num [smallLeft,smallRight,smallFamily,Explicit.left,Explicit.right,Explicit.L,L,h,v,
      Secondary.frameCap] at hθ ⊢ <;> constructor <;> linarith [hθ.1,hθ.2]

theorem far_domain (r : FarCase) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) :
    θ∈Icc (Explicit.left .far (farFamily r)) (Explicit.right .far (farFamily r)) := by
  cases r <;>
    norm_num [farLeft,farRight,farFamily,Explicit.left,Explicit.right,Explicit.u,h,v,u,
      Secondary.frameCap] at hθ ⊢ <;> constructor <;> linarith [hθ.1,hθ.2]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Certificate
