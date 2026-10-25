module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2NegativeSlopes

/-!
# Eight squares: the two endpoint slopes in the common-gain endpoint principle

Alternating sine and cosine brackets give the two strict upper bounds of `F1` at the angles
`3/20` and `7/10` (`EndpointSlope.endpoint`); the convexity of F′ covers the whole interval
(`first_upper_long`). `zero_slope_lower` bounds the slope at `0`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary OrdinaryCurvatureBounds OrdinaryNegativeSlope
open OrdinaryAngleConcavity PairNormCalculus VaryingBFunctions
open NegativeAPositiveTD.NegativeSlope

namespace EndpointSlope
def angle : Fin 2→ℚ := ![3/20,7/10]
def rootUpper : Fin 2→ℚ := ![249111/200000,1153227/1000000]
def upper : Fin 2→ℚ := ![103/100,133/125]
def numeratorUpper (i : Fin 2) : ℚ := 13/12+sinHi (angle i)-upper i*(cosLo (angle i))^2

theorem data (i : Fin 2) :
    (0:ℚ)<rootUpper i ∧ 0<upper i ∧ 0≤ sinLo (angle i) ∧ 0<cosLo (angle i) ∧
    0<cosHi (angle i) ∧ 0<numeratorUpper i ∧
    1+(751/1000:ℚ)^2*(cosHi (angle i))^2<(rootUpper i)^2 ∧
    numeratorUpper i*rootUpper i<(1978787/1000000:ℚ)*sinLo (angle i) := by
  fin_cases i <;> norm_num [angle,rootUpper,upper,numeratorUpper,
    sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,
    PositiveTD.Certificate.S5,PositiveTD.Certificate.C10,PositiveTD.Certificate.C12,
    PositiveTD.Certificate.C4]

theorem domain (i : Fin 2) : (angle i:ℝ)∈Icc 0 frameCap := by
  fin_cases i <;> norm_num [angle,frameCap]

theorem endpoint (i : Fin 2) : F1 (751/1000) (angle i)<(upper i:ℝ) := by
  obtain ⟨d1,d2,d3,d4,-,d6,d7,d8⟩ := data i
  have c1 : (0:ℝ)<(rootUpper i:ℝ) := by exact_mod_cast d1
  have c2 : (0:ℝ)<(upper i:ℝ) := by exact_mod_cast d2
  have c3 : (0:ℝ)≤(sinLo (angle i):ℝ) := by exact_mod_cast d3
  have c4 : (0:ℝ)<(cosLo (angle i):ℝ) := by exact_mod_cast d4
  have c6 : (0:ℝ)<(numeratorUpper i:ℝ) := by exact_mod_cast d6
  have c7 : 1+(751/1000:ℝ)^2*(cosHi (angle i):ℝ)^2<(rootUpper i:ℝ)^2 := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr d7
    push_cast at h
    exact h
  have c8 : (numeratorUpper i:ℝ)*(rootUpper i:ℝ)<(1978787/1000000:ℝ)*(sinLo (angle i):ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr d8
    push_cast at h
    exact h
  obtain ⟨hsl,hsh,hcl,hch⟩ := rational_taylor (domain i)
  have hcos : 0<Real.cos (angle i:ℝ) := c4.trans_le hcl
  have hN := D_positive (751/1000) (angle i)
  have hN2 := D_square (751/1000) (angle i)
  have hcos2 := pow_le_pow_left₀ hcos.le hch 2
  have hNsq : (D (751/1000) (angle i))^2<(rootUpper i:ℝ)^2 := by
    rw [hN2]
    linarith [mul_le_mul_of_nonneg_left hcos2 (by norm_num : (0:ℝ)≤(751/1000)^2)]
  have hNup : D (751/1000) (angle i)<(rootUpper i:ℝ) := lt_of_pow_lt_pow_left₀ 2 c1.le hNsq
  have hlo2 := pow_le_pow_left₀ c4.le hcl 2
  have hbr : K+Real.sin (angle i)-(upper i:ℝ)*Real.cos (angle i)^2≤(numeratorUpper i:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlo2 c2.le
    dsimp [numeratorUpper,K]
    push_cast
    linarith
  have hfirst := mul_le_mul_of_nonneg_right hbr hN.le
  have hsecond := mul_lt_mul_of_pos_left hNup c6
  have hthird := mul_le_mul radius_tight.1.le hsl c3 (Real.sqrt_nonneg _)
  have hcross : (K+Real.sin (angle i)-(upper i:ℝ)*Real.cos (angle i)^2)*
      D (751/1000) (angle i)<R*Real.sin (angle i) := by
    linarith [c8]
  have hdiv := (lt_div_iff₀ hN).2 hcross
  dsimp [F1]
  apply (div_lt_iff₀ (sq_pos_of_pos hcos)).2
  linarith
end EndpointSlope

theorem first_upper_long {k t : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc (3/20:ℝ) frameCap) : F1 k t<(133/125:ℝ) := by
  have hdomain {x : ℝ} (hx : x∈Icc (3/20:ℝ) frameCap) : x∈Icc 0 frameCap :=
    ⟨by linarith [hx.1],hx.2⟩
  have hc : ConcaveOn ℝ (Icc (3/20:ℝ) frameCap) (fun x => -F1 (751/1000) x) := by
    apply concave_of_deriv2
      (fun x hx => (F1_derivative (k:=(751/1000:ℝ)) (hdomain hx)).neg)
      (fun x hx => (F2_derivative (k:=(751/1000:ℝ)) (hdomain hx)).neg)
    intro x hx
    have hh := third_lower (show (751/1000:ℝ)∈Icc (13/20:ℝ) (751/1000) by norm_num) (hdomain hx)
    linarith
  have hl := EndpointSlope.endpoint 0
  have hr := EndpointSlope.endpoint 1
  norm_num [EndpointSlope.angle,EndpointSlope.upper,frameCap] at hl hr
  have hh := concave_gt_of_endpoints hc ht
    (show -(133/125:ℝ)< -F1 (751/1000) (3/20) by linarith)
    (show -(133/125:ℝ)< -F1 (751/1000) frameCap by simpa [frameCap] using neg_lt_neg hr)
  have hm := (parameter_monotonicity (hdomain ht)).1 hk ⟨by norm_num,le_rfl⟩ hk.2
  linarith

theorem zero_slope_lower {k : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000)) :
    (539/500:ℝ)<Vd R k 1 0 := by
  have hlow : (539/500:ℝ)<NegativeAPositiveTD.Curvature.shapeD0q (13/20) := by
    have hs := shape_pos (13/20:ℝ)
    have hs2 := shape_sq (13/20:ℝ)
    have hr : R^2=9789/2500 := Secondary.radius_sq
    dsimp [NegativeAPositiveTD.Curvature.shapeD0q]
    apply (lt_div_iff₀ hs).2
    have hsq : ((539/500)*shape (13/20))^2<(R*(13/20))^2 := by
      rw [mul_pow,mul_pow,hs2,hr]; norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hm := NegativeAPositiveTD.Curvature.shapeD0q_monotone
    (show (13/20:ℝ)∈Icc (0:ℝ) 1 by norm_num)
    (show k∈Icc (0:ℝ) 1 by exact ⟨by linarith [hk.1],by linarith [hk.2]⟩) hk.1
  have he : Vd R k 1 0=NegativeAPositiveTD.Curvature.shapeD0q k := by
    rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
    simp [NegativeAPositiveTD.Curvature.shapeD0q]
  rw [he]
  exact hlow.trans_le hm

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
