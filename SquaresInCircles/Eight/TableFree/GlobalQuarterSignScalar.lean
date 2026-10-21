module

public import SquaresInCircles.Eight.TableFree.GlobalQuarterSignMarkers

/-!
# Continuous scalar reserves for the quarter-owner sign theorem

All five estimates hold on whole closed intervals.  The primary-owner
forms are multiplied by the positive cosine before comparison, which
avoids reciprocal estimates and keeps the original weak projections
linear in their endpoint coordinates.  Exact Taylor bounds and explicit
polynomial factors supply the positive reserves.  Uncompiled source.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalQuarterSign

open GlobalZeroSign

theorem half_pi_lower : (157/100:ℝ)<Real.pi/2 := by
  linarith [Arithmetic.pi_hand_enclosure.1]

private theorem power_bounds {x : ℝ} (hx : x∈Icc 0 (7/10:ℝ)) :
    x^2≤49/100 ∧ x^3≤(7/10)*x^2 ∧ x^4≤(49/100)*x^2 := by
  have h2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h3 := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx.2)
  have h4 := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h2)
  norm_num at h2
  exact ⟨h2,by nlinarith,by nlinarith⟩

theorem secondary_negative_scalar {d : ℝ} (hd : |d|≤frameCap) :
    1<Real.pi/2+d+93/200-(18513/20000)*Real.cos d+
      (129/200)*|Real.sin d| := by
  by_cases hp : 0≤d
  · nlinarith [half_pi_lower,Real.cos_le_one d,abs_nonneg (Real.sin d)]
  · let x := -d
    have hx : x∈Icc 0 (7/10:ℝ) := by
      exact ⟨by dsimp [x]; linarith,(neg_le_abs d).trans (by simpa [frameCap] using hd)⟩
    have ht := transport_trig (show x∈Icc 0 frameCap by simpa [frameCap] using hx)
    have hsin := sin_lower_three hx.1
    have hcos := cos_upper_four hx.1
    have hpow := power_bounds hx
    have hpoly : 1<(22187/20000:ℝ)-(71/200)*x+(9/25)*x^2 := by
      nlinarith [sq_nonneg (x-71/144)]
    have hreduce :
        (22187/20000:ℝ)-(71/200)*x+(9/25)*x^2≤
        22187/20000-(71/200)*x+(18513/40000)*x^2-
          (43/400)*x^3-(6171/160000)*x^4 := by
      nlinarith [sq_nonneg x]
    have he : d= -x := by dsimp [x]; ring
    rw [he,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg ht.2.2.1]
    nlinarith [half_pi_lower]

private theorem positive_secondary_polynomial {x : ℝ} (hx : x∈Icc 0 (7/10:ℝ)) :
    1<(619/500:ℝ)-(51/100)*x+(321/1000)*x^2-
      (49/600)*x^3-(107/4000)*x^4 := by
  let p : ℝ→ℝ := fun z => 619/500-(51/100)*z+(321/1000)*z^2-
    (49/600)*z^3-(107/4000)*z^4
  let v : ℝ := 51/100-(321/1000)*(x+7/10)+
    (49/600)*(x^2+(7/10)*x+49/100)+
    (107/4000)*(x^3+(7/10)*x^2+(49/100)*x+343/1000)
  have hv : 0≤v := by
    dsimp [v]
    nlinarith [sq_nonneg x,pow_nonneg hx.1 3]
  have hmul := mul_nonneg (sub_nonneg.mpr hx.2) hv
  have hlow : p (7/10)≤p x := by
    dsimp [p,v] at *
    nlinarith only [hmul]
  have hend : 1<p (7/10) := by norm_num [p]
  exact hend.trans_le hlow

theorem secondary_positive_scalar {d : ℝ} (hd : |d|≤frameCap) :
    1<Real.pi/2+d+31/100-(321/500)*Real.cos d+
      (49/100)*|Real.sin d| := by
  by_cases hp : 0≤d
  · nlinarith [half_pi_lower,Real.cos_le_one d,abs_nonneg (Real.sin d)]
  · let x := -d
    have hx : x∈Icc 0 (7/10:ℝ) := by
      exact ⟨by dsimp [x]; linarith,(neg_le_abs d).trans (by simpa [frameCap] using hd)⟩
    have ht := transport_trig (show x∈Icc 0 frameCap by simpa [frameCap] using hx)
    have hsin := sin_lower_three hx.1
    have hcos := cos_upper_four hx.1
    have hpoly := positive_secondary_polynomial hx
    have he : d= -x := by dsimp [x]; ring
    rw [he,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg ht.2.2.1]
    nlinarith [half_pi_lower]

/-- Negative source and negative error.  The feasible primary projection
will force the full interval `0 ≤ x ≤ 1/2` used here. -/
theorem primary_negative_negative_scaled {x : ℝ} (hx : x∈Icc 0 (1/2:ℝ)) :
    0<Real.cos x*(Real.pi/2-x-1)+(111/100)*
      ((1+Real.cos x+Real.sin x)/2-283/200+(447/800)*Real.sin x) := by
  have ht := transport_trig (show x∈Icc 0 frameCap by
    constructor <;> norm_num [frameCap] <;> linarith [hx.1,hx.2])
  have hcpos : 0<Real.cos x := by linarith [ht.1]
  have hpi := mul_lt_mul_of_pos_right half_pi_lower hcpos
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_two hx.1)
    (show 0≤(9/8:ℝ)-x by linarith)
  have hsin := sin_lower_three hx.1
  have hx2 : x^2≤x/2 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hpoly : 0<(2187/20000:ℝ)+(14017/80000)*x-(9/16)*x^2+
      (48661/160000)*x^3 := by
    nlinarith [pow_nonneg hx.1 3]
  nlinarith only [hpi,hcos,hsin,hpoly]

/-- Negative source and small positive error.  Multiplication by cosine
keeps the lower estimate polynomial in the original weak margin. -/
theorem primary_negative_positive_scaled {x : ℝ} (hx : x∈Icc 0 (1/4:ℝ)) :
    0<Real.cos x*(Real.pi/2+x-1)+(111/100)*
      ((1+Real.cos x+Real.sin x)/2-(283/200)*(1+Real.sin x)) := by
  have ht := transport_trig (show x∈Icc 0 frameCap by
    constructor <;> norm_num [frameCap] <;> linarith [hx.1,hx.2])
  have hcpos : 0<Real.cos x := by linarith [ht.1]
  have hpi := mul_lt_mul_of_pos_right half_pi_lower hcpos
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_two hx.1)
    (show 0≤(9/8:ℝ)+x by linarith)
  have hsin := Real.sin_le hx.1
  have h2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h3 := pow_le_pow_left₀ hx.1 hx.2 3
  norm_num at h2 h3
  have hpoly : 0<(2187/20000:ℝ)-(313/20000)*x-(9/16)*x^2-(1/2)*x^3 := by
    nlinarith
  nlinarith only [hpi,hcos,hsin,hpoly]

private theorem positive_primary_polynomial {x : ℝ} (hx : x∈Icc 0 (7/10:ℝ)) :
    0<(119/500:ℝ)-(63/1000)*x-(53/100)*x^2+(1793/6000)*x^3 := by
  let p : ℝ→ℝ := fun z => 119/500-(63/1000)*z-(53/100)*z^2+(1793/6000)*z^3
  let v : ℝ := 63/1000+(53/100)*(x+7/10)-
    (1793/6000)*(x^2+(7/10)*x+49/100)
  have hx2 : x^2≤(7/10)*x := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hv : 0≤v := by dsimp [v]; nlinarith
  have hmul := mul_nonneg (sub_nonneg.mpr hx.2) hv
  have hlow : p (7/10)≤p x := by
    dsimp [p,v] at *
    nlinarith only [hmul]
  have hend : 0<p (7/10) := by norm_num [p]
  exact hend.trans_le hlow

/-- Positive source and negative error, on the entire frame interval. -/
theorem primary_positive_negative_scaled {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0<Real.cos x*(Real.pi/2-x-1+(9/50)*frameCost x)+(4/5)*
      ((1+Real.cos x+Real.sin x)/2-283/200+(447/800)*Real.sin x) := by
  have hx' : x∈Icc 0 (7/10:ℝ) := by simpa only [frameCap] using hx
  have ht := transport_trig hx
  have hcpos : 0<Real.cos x := by linarith [ht.1]
  have hpi := mul_lt_mul_of_pos_right half_pi_lower hcpos
  have hcos := cos_lower_two hx.1
  have hsin := sin_lower_three hx.1
  have hsinU := Real.sin_le hx.1
  have h2 := (power_bounds hx').1
  have h3 : x^3≤(49/100)*x := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr h2)]
  have hsL : 0≤x-x^3/6 := by nlinarith
  have hcL : 0≤1-x^2/2 := by linarith
  have hcross := mul_le_mul hsin hcos hcL ht.2.2.1
  have hmain := mul_le_mul_of_nonneg_left hcos
    (show 0≤(22/25:ℝ)-x by linarith [hx'.2])
  have hs2 := pow_le_pow_left₀ ht.2.2.1 hsinU 2
  have hc2 : 1-x^2≤Real.cos x^2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hp := positive_primary_polynomial hx'
  have hx5 := pow_nonneg hx.1 5
  dsimp [frameCost]
  nlinarith only [hpi,hmain,hcross,hc2,hsin,hp,hx5]

end SquaresInCircles.Eight.TableFree.GlobalQuarterSign
