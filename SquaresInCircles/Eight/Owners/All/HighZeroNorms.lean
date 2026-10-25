module

public import SquaresInCircles.Eight.Owners.All.HighZeroPolynomial

/-!
# Eight squares: explicit norm envelopes for the original nonpositive zero source

The two actual circle forces have polynomial upper envelopes over the
whole frame interval.  Squaring is justified by explicit positive lower
bounds for both envelope factors.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open Polynomial FramePair FrameCircleArc ZeroPolynomial

def zeroMu (z : ℝ) : ℝ := 1-z/5
def zeroN1 (z : ℝ) : ℝ := Real.sqrt (1+(zeroMu z)^2-2*zeroMu z*Real.cos z)
def zeroN2 (z : ℝ) : ℝ := Real.sqrt (1+(zeroMu z)^2)

theorem zeroMu_bounds {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (43/50:ℝ)≤zeroMu z ∧ zeroMu z≤1 := by
  dsimp [zeroMu,frameCap] at *
  constructor <;> linarith [hz.1,hz.2]

theorem zeroN1_radicand {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤1+(zeroMu z)^2-2*zeroMu z*Real.cos z := by
  have hm : 0≤zeroMu z := by linarith [(zeroMu_bounds hz).1]
  have hp := mul_nonneg hm (sub_nonneg.mpr (Real.cos_le_one z))
  nlinarith [sq_nonneg (1-zeroMu z)]

theorem zeroN1_sq {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (zeroN1 z)^2=1+(zeroMu z)^2-2*zeroMu z*Real.cos z :=
  Real.sq_sqrt (zeroN1_radicand hz)

theorem zeroN2_sq (z : ℝ) : (zeroN2 z)^2=1+(zeroMu z)^2 :=
  Real.sq_sqrt (by positivity)

theorem zero_p1_positive {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (9/10:ℝ)<aeval z p1 := by
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  norm_num [frameCap] at h2
  rw [p1_eval]
  dsimp [frameCap] at hz
  nlinarith [pow_nonneg hz.1 3,pow_nonneg hz.1 4,hz.2]

theorem zero_p2_bounds {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (93/100:ℝ)≤aeval z p2 ∧ aeval z p2≤1 := by
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  have h3 := pow_le_pow_left₀ hz.1 hz.2 3
  norm_num [frameCap] at h2 h3
  have hcoefficient : -(1/10:ℝ)+z/200+z^2/2000+z^3/20000≤0 := by
    dsimp [frameCap] at hz
    nlinarith [hz.2]
  have hprod := mul_nonpos_of_nonneg_of_nonpos hz.1 hcoefficient
  rw [p2_eval]
  dsimp [frameCap] at hz
  constructor
  · nlinarith [sq_nonneg z,pow_nonneg hz.1 3,pow_nonneg hz.1 4,hz.2]
  · nlinarith only [hprod]

theorem zero_p2_square {z : ℝ} (hz : z∈Icc 0 frameCap) :
    1-z/5+z^2/50≤(aeval z p2)^2 := by
  have hbracket : 0≤(1/40000:ℝ)-z/200000+
      3*z^2/4000000+z^3/20000000+z^4/400000000 := by
    dsimp [frameCap] at hz
    nlinarith [sq_nonneg z,pow_nonneg hz.1 3,pow_nonneg hz.1 4,hz.2]
  have hp := mul_nonneg (pow_nonneg hz.1 4) hbracket
  have hi : (1-z/10+z^2/200+z^3/2000+z^4/20000)^2-(1-z/5+z^2/50)=
      z^4*((1/40000:ℝ)-z/200000+3*z^2/4000000+z^3/20000000+z^4/400000000) := by
    ring
  rw [p2_eval]
  nlinarith only [hp,hi]

theorem zeroN1_polynomial_square {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (zeroN1 z)^2≤z^2*aeval z X1 := by
  have hmu : 0≤2*zeroMu z := by linarith [(zeroMu_bounds hz).1]
  have hc := mul_le_mul_of_nonneg_left (cos_lower_six hz.1) hmu
  rw [zeroN1_sq hz,X1_eval]
  dsimp [zeroMu] at *
  nlinarith only [hc]

theorem zeroN1_envelope {z : ℝ} (hz : z∈Icc 0 frameCap) :
    zeroN1 z≤(Real.sqrt 26/5)*z*aeval z p1 := by
  have hp : 0≤aeval z p1 := by linarith [zero_p1_positive hz]
  have he : 0≤(Real.sqrt 26/5)*z*aeval z p1 :=
    mul_nonneg (mul_nonneg (by positivity) hz.1) hp
  have hr := remainder_nonnegative hz
  have hrem : aeval z X1≤(26/25)*(aeval z p1)^2 := by
    simp only [remainder,map_sub,map_mul,map_pow,aeval_C,eq_ratCast] at hr
    push_cast at hr
    linarith
  have hm := mul_le_mul_of_nonneg_left hrem (sq_nonneg z)
  have hs := zeroN1_polynomial_square hz
  have h26 : (Real.sqrt 26)^2=(26:ℝ) := Real.sq_sqrt (by norm_num)
  have hi : ((Real.sqrt 26/5)*z*aeval z p1)^2=(26/25)*z^2*(aeval z p1)^2 := by
    calc
      _=(Real.sqrt 26)^2/25*z^2*(aeval z p1)^2 := by ring
      _=_ := by rw [h26]
  have hn : 0≤zeroN1 z := Real.sqrt_nonneg _
  nlinarith only [hm,hs,hi,he,hn]

theorem zeroN2_envelope {z : ℝ} (hz : z∈Icc 0 frameCap) :
    zeroN2 z≤Real.sqrt 2*aeval z p2 := by
  have hp : 0≤aeval z p2 := by linarith [(zero_p2_bounds hz).1]
  have he : 0≤Real.sqrt 2*aeval z p2 := by positivity
  have hs := zero_p2_square hz
  have hn := zeroN2_sq z
  have h2 : (Real.sqrt 2)^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  have hi : (Real.sqrt 2*aeval z p2)^2=2*(aeval z p2)^2 := by
    rw [mul_pow,h2]
  have hn0 : 0≤zeroN2 z := Real.sqrt_nonneg _
  dsimp [zeroMu] at hn
  nlinarith

theorem radius_sqrt_twenty_six : R*Real.sqrt 26/5<(1009/500:ℝ) := by
  have h26 : (Real.sqrt 26)^2=(26:ℝ) := Real.sq_sqrt (by norm_num)
  have he : (R*Real.sqrt 26/5)^2=(26/25)*Q0 := by
    calc
      _=R^2*(Real.sqrt 26)^2/25 := by ring
      _=_ := by rw [R_sq,h26]; ring
  have hp : 0≤R*Real.sqrt 26/5 :=
    div_nonneg (mul_nonneg R_pos.le (Real.sqrt_nonneg _)) (by norm_num)
  norm_num [Q0] at he
  nlinarith

theorem radius_sqrt_two : R*Real.sqrt 2=2*c0+1 := by
  have h2 : (Real.sqrt 2)^2=(2:ℝ) := Real.sq_sqrt (by norm_num)
  have he : (R*Real.sqrt 2)^2=2*Q0 := by rw [mul_pow,R_sq,h2]; ring
  have hp : 0≤R*Real.sqrt 2 := mul_nonneg R_pos.le (Real.sqrt_nonneg _)
  nlinarith [c0_circle,c0_bounds.1]

theorem radius_norm1_envelope {z : ℝ} (hz : z∈Icc 0 frameCap) :
    R*zeroN1 z≤(1009/500)*z*aeval z p1 := by
  have hfirst := mul_le_mul_of_nonneg_left (zeroN1_envelope hz) R_pos.le
  have hp : 0≤z*aeval z p1 := mul_nonneg hz.1 (by linarith [zero_p1_positive hz])
  have hsecond := mul_le_mul_of_nonneg_right radius_sqrt_twenty_six.le hp
  nlinarith only [hfirst,hsecond]

theorem radius_norm2_difference {z : ℝ} (hz : z∈Icc 0 frameCap) :
    R*(zeroN2 z-Real.sqrt 2)≤(139921/50000)*(aeval z p2-1) := by
  have hfirst := mul_le_mul_of_nonneg_left (zeroN2_envelope hz) R_pos.le
  have hR : (139921/50000:ℝ)≤R*Real.sqrt 2 := by
    rw [radius_sqrt_two]
    linarith [diagonal_bounds.1]
  have hsecond := mul_le_mul_of_nonpos_right hR (sub_nonpos.mpr (zero_p2_bounds hz).2)
  nlinarith only [hfirst,hsecond]

end SquaresInCircles.Eight.GlobalAllHigh
