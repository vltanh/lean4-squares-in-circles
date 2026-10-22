module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2PolynomialData

/-!
# The six exact whole-interval endpoint certificates

Uncompiled transcription of (19)--(26) in the joint-negative scalar
companion. The low and middle rows retain a quadratic leading part.
The full-D rows retain the prescribed fifth and third powers, charging
only adverse higher coefficients on their nonnegative interval.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Certificate
open Polynomial PowerTailBounds DirectedPowerBounds

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_identity (e : Endpoint) :
    centered .low e=C ((centered .low e).coeff 0)+C ((centered .low e).coeff 1)*X+
      C ((centered .low e).coeff 2)*X^2+tail (centered .low e) 3 (degree .low e-2) := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_coefficients (e : Endpoint) :
    lowConstant e<(centered .low e).coeff 0 ∧
    (centered .low e).coeff 1<lowLinear e ∧
    lowQuadratic e<(centered .low e).coeff 2-
      PowerTailBounds.norm (centered .low e) 3 (degree .low e-2) (3/20) := by
  cases e <;> decide

theorem low_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc 0 (3/20:ℝ)) :
    (lowConstant e:ℝ)<aeval z (numerator .low e) := by
  let u : ℝ := z-3/20
  have hu : u≤0 := by dsimp [u]; linarith [hz.2]
  have habs : |u|≤(3/20:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hz.1],hu.trans (by norm_num)⟩
  have hp := PowerTailBounds.quadratic_lower (low_identity e) (by norm_num) habs
  have h0 : (lowConstant e:ℝ)<((centered .low e).coeff 0:ℝ) := by
    exact_mod_cast (low_coefficients e).1
  have h1 : ((centered .low e).coeff 1:ℝ)<(lowLinear e:ℝ) := by
    exact_mod_cast (low_coefficients e).2.1
  have h2 : (lowQuadratic e:ℝ)<((centered .low e).coeff 2:ℝ)-
      (PowerTailBounds.norm (centered .low e) 3 (degree .low e-2) (3/20):ℝ) := by
    exact_mod_cast (low_coefficients e).2.2
  have hc1 : (lowLinear e:ℝ)≤0 := by cases e <;> norm_num [lowLinear]
  have hc2 : 0<(lowQuadratic e:ℝ) := by cases e <;> norm_num [lowQuadratic]
  have hlin := mul_nonneg_of_nonpos_of_nonpos (h1.le.trans hc1) hu
  have hquad := mul_nonneg (hc2.le.trans h2.le) (sq_nonneg u)
  have hid : aeval u (centered .low e)=aeval z (numerator .low e) := by
    simp [centered,center,u]
  rw [hid] at hp
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middle_identity (e : Endpoint) :
    centered .transition e=C ((centered .transition e).coeff 0)+
      C ((centered .transition e).coeff 1)*X+C ((centered .transition e).coeff 2)*X^2+
      tail (centered .transition e) 3 (degree .transition e-2) := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem middle_coefficients (e : Endpoint) :
    middleConstant e<(centered .transition e).coeff 0 ∧
    |(centered .transition e).coeff 1|<middleLinear e ∧
    middleQuadratic e<(centered .transition e).coeff 2-
      PowerTailBounds.norm (centered .transition e) 3 (degree .transition e-2) (7/200) := by
  cases e <;> decide

theorem middle_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (3/20:ℝ) (19/100)) :
    (middleReserve e:ℝ)<aeval z (numerator .transition e) := by
  let u : ℝ := z-37/200
  have hu : |u|≤(7/200:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hp := PowerTailBounds.quadratic_lower (middle_identity e) (by norm_num) hu
  have h0 : (middleConstant e:ℝ)<((centered .transition e).coeff 0:ℝ) := by
    exact_mod_cast (middle_coefficients e).1
  have h1 : |((centered .transition e).coeff 1:ℝ)|<(middleLinear e:ℝ) := by
    exact_mod_cast (middle_coefficients e).2.1
  have h2 : (middleQuadratic e:ℝ)<((centered .transition e).coeff 2:ℝ)-
      (PowerTailBounds.norm (centered .transition e) 3 (degree .transition e-2) (7/200):ℝ) := by
    exact_mod_cast (middle_coefficients e).2.2
  have hc2 : 0<(middleQuadratic e:ℝ) := by cases e <;> norm_num [middleQuadratic]
  have hlin : -(middleLinear e:ℝ)*|u|≤((centered .transition e).coeff 1:ℝ)*u := by
    have hh := mul_le_mul_of_nonneg_right h1.le (abs_nonneg u)
    rw [←abs_mul] at hh
    exact (abs_le.mp hh).1
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg u)
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(middleConstant e:ℝ))
    (b:=-(middleLinear e:ℝ)) (x:=|u|) hc2
  have hr : (middleReserve e:ℝ)<(middleConstant e:ℝ)-
      (middleLinear e:ℝ)^2/(4*(middleQuadratic e:ℝ)) := by
    cases e <;> norm_num [middleReserve,middleConstant,middleLinear,middleQuadratic]
  have hid : aeval u (centered .transition e)=aeval z (numerator .transition e) := by
    simp [centered,center,u]
  rw [hid] at hp
  rw [sq_abs] at hm
  nlinarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem full_V_identity :
    centered .full .V=C ((centered .full .V).coeff 0)+C ((centered .full .V).coeff 1)*X+
      C ((centered .full .V).coeff 2)*X^2+C ((centered .full .V).coeff 3)*X^3+
      C ((centered .full .V).coeff 4)*X^4+C ((centered .full .V).coeff 5)*X^5+
      tail (centered .full .V) 6 55 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem full_V_coefficients :
    (41/500000:ℚ)<(centered .full .V).coeff 0 ∧
    (3777/500000:ℚ)<(centered .full .V).coeff 1 ∧
    (-2507/100000:ℚ)<(centered .full .V).coeff 2 ∧
    (58973/50000:ℚ)<(centered .full .V).coeff 3 ∧
    (-24597/10000:ℚ)<(centered .full .V).coeff 4 ∧
    (91789/100000:ℚ)<(centered .full .V).coeff 5-
      negativeNorm (centered .full .V) 6 55 (51/100) := by decide

theorem full_V_positive {z : ℝ} (hz : z∈Icc (19/100:ℝ) (7/10)) :
    (41/500000:ℝ)<aeval z (numerator .full .V) := by
  let u : ℝ := z-19/100
  have hu : u∈Icc (0:ℝ) (51/100:ℝ) := by
    dsimp [u]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have ht := DirectedPowerBounds.tail_lower (p:=centered .full .V) (k:=5) (n:=55) hu
  have hi := congrArg (fun p : ℚ[X] => aeval u p) full_V_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at hi
  have hc :
      (41/500000:ℝ)<((centered .full .V).coeff 0:ℝ) ∧
      (3777/500000:ℝ)<((centered .full .V).coeff 1:ℝ) ∧
      (-2507/100000:ℝ)<((centered .full .V).coeff 2:ℝ) ∧
      (58973/50000:ℝ)<((centered .full .V).coeff 3:ℝ) ∧
      (-24597/10000:ℝ)<((centered .full .V).coeff 4:ℝ) ∧
      (91789/100000:ℝ)<((centered .full .V).coeff 5:ℝ)-
        (negativeNorm (centered .full .V) 6 55 (51/100):ℝ) := by
    exact_mod_cast full_V_coefficients
  have h1 := mul_le_mul_of_nonneg_right hc.2.1.le hu.1
  have h2 := mul_le_mul_of_nonneg_right hc.2.2.1.le (sq_nonneg u)
  have h3 := mul_le_mul_of_nonneg_right hc.2.2.2.1.le (pow_nonneg hu.1 3)
  have h4 := mul_le_mul_of_nonneg_right hc.2.2.2.2.1.le (pow_nonneg hu.1 4)
  have h5 := mul_le_mul_of_nonneg_right hc.2.2.2.2.2.le (pow_nonneg hu.1 5)
  have hfactor := mul_nonneg (show 0≤51/100-u by linarith [hu.2])
    (show 0≤24597/10000-(91789/100000)*(u+51/100) by linarith [hu.2])
  have hq : (1637/10000:ℝ)≤58973/50000-(24597/10000)*u+(91789/100000)*u^2 := by
    nlinarith
  have hq3 := mul_le_mul_of_nonneg_right hq (pow_nonneg hu.1 3)
  have hinner : 0≤3777/500000-(2507/100000)*u+(1637/10000)*u^2 := by
    nlinarith [sq_nonneg (2*(1637/10000:ℝ)*u-2507/100000)]
  have hnonneg := mul_nonneg hu.1 hinner
  have hid : aeval u (centered .full .V)=aeval z (numerator .full .V) := by
    simp [centered,center,u]
  rw [hid] at hi
  nlinarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem full_F_identity :
    centered .full .F=C ((centered .full .F).coeff 0)+C ((centered .full .F).coeff 1)*X+
      C ((centered .full .F).coeff 2)*X^2+C ((centered .full .F).coeff 3)*X^3+
      tail (centered .full .F) 4 79 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem full_F_coefficients :
    (883/10000000:ℚ)<(centered .full .F).coeff 0 ∧
    (8137/1000000:ℚ)<(centered .full .F).coeff 1 ∧
    (-2479/100000:ℚ)<(centered .full .F).coeff 2 ∧
    (367/10000:ℚ)<(centered .full .F).coeff 3-
      negativeNorm (centered .full .F) 4 79 (51/100) := by decide

theorem full_F_positive {z : ℝ} (hz : z∈Icc (19/100:ℝ) (7/10)) :
    (883/10000000:ℝ)<aeval z (numerator .full .F) := by
  let u : ℝ := z-19/100
  have hu : u∈Icc (0:ℝ) (51/100:ℝ) := by
    dsimp [u]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hp := DirectedPowerBounds.cubic_lower full_F_identity hu
  have hc : (883/10000000:ℝ)<((centered .full .F).coeff 0:ℝ) ∧
      (8137/1000000:ℝ)<((centered .full .F).coeff 1:ℝ) ∧
      (-2479/100000:ℝ)<((centered .full .F).coeff 2:ℝ) ∧
      (367/10000:ℝ)<((centered .full .F).coeff 3:ℝ)-
        (negativeNorm (centered .full .F) 4 79 (51/100):ℝ) := by
    exact_mod_cast full_F_coefficients
  have h1 := mul_le_mul_of_nonneg_right hc.2.1.le hu.1
  have h2 := mul_le_mul_of_nonneg_right hc.2.2.1.le (sq_nonneg u)
  have h3 := mul_le_mul_of_nonneg_right hc.2.2.2.le (pow_nonneg hu.1 3)
  have hinner : 0≤8137/1000000-(2479/100000)*u+(367/10000)*u^2 := by
    nlinarith [sq_nonneg (2*(367/10000:ℝ)*u-2479/100000)]
  have hnonneg := mul_nonneg hu.1 hinner
  have hid : aeval u (centered .full .F)=aeval z (numerator .full .F) := by
    simp [centered,center,u]
  rw [hid] at hp
  nlinarith

/-- A uniform reserve, strictly larger than the stated Taylor allowance. -/
theorem numerator_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (left r:ℝ) (right r:ℝ)) :
    (1/25000:ℝ)<aeval z (numerator r e) := by
  cases r
  · have hh := low_positive e hz
    cases e <;> norm_num [lowConstant] at hh <;> linarith
  · have hh := middle_positive e hz
    cases e <;> norm_num [middleReserve] at hh <;> linarith
  · cases e
    · linarith [full_V_positive hz]
    · linarith [full_F_positive hz]

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Certificate
