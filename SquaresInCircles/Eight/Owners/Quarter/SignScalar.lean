module

public import SquaresInCircles.Eight.Owners.Zero.SignSupport

/-!
# Eight squares: continuous scalar reserves for the quarter-owner sign theorem

All five estimates hold on whole closed intervals.  The primary-owner
forms are multiplied by the positive cosine before comparison, which
avoids reciprocal estimates and keeps the original weak projections
linear in their endpoint coordinates.  Exact Taylor bounds and explicit
polynomial factors supply the positive reserves.
-/

section
/-!
## Whole-chart marker bounds for original quarter-owner signs

These estimates use the same marker selected at each original vertex
in the complete G1 pair theorem.  They cover the two core pieces and
all three outer charts, including chart ties and zero transverse
coordinates.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalQuarterSign

open FramePair ZeroPrimary GlobalZeroSign

theorem state_norm_sq (s : State) : s.a^2+s.b^2<(283/200:ℝ)^2 := by
  let r := Real.sqrt (s.a^2+s.b^2)
  have hr : 0≤r := Real.sqrt_nonneg _
  have hr2 : r^2=s.a^2+s.b^2 := Real.sq_sqrt (by positivity)
  have hsum : r≤ s.a+s.b := by
    by_contra! hh
    nlinarith [s.a_pos,s.b_nonneg,mul_nonneg s.a_pos.le s.b_nonneg]
  have hc := state_circle s
  norm_num [Q0] at hc
  have hu : r<(283/200:ℝ) := by
    by_contra! hh
    nlinarith
  nlinarith

theorem rotated_projection_lt (s : State) (d : ℝ) :
    s.a*Real.cos d-s.b*Real.sin d<(283/200:ℝ) := by
  have hh := FrameCoreArc.projection_lt (by norm_num : (0:ℝ)<283/200)
    (state_norm_sq s) (Real.pi/2+d)
  simp only [Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two] at hh
  linarith

theorem marker_lt_four_fifths (s : State) : unsigned s<(4/5:ℝ) := by
  have ha := primary_lower s
  have hc := s.canonical
  cases hb : s.branch with
  | coreSide =>
      dsimp [unsigned]
      rw [hb]
      dsimp [FramePair.label]
      linarith
  | coreCorner =>
      dsimp [unsigned]
      rw [hb]
      dsimp [FramePair.label]
      linarith
  | low =>
      have hu := (coordinates s).2.1
      have ht : s.branch.type≠0 := by simp [hb,Branch.type]
      have hax := (CommonQuarter.outer_bounds (outer_data s ht)).2.1
      change s.a≤a0 at hax
      have hcut : 4*s.b≤ s.a := by simpa [hb,TypeMem] using s.type_mem
      dsimp [unsigned]
      rw [hb]
      dsimp [FramePair.label]
      linarith
  | middle =>
      have hsup := state_support s (1489593/1000000) (1580219/1000000)
      have hn : Real.sqrt ((1489593/1000000:ℝ)^2+(1580219/1000000)^2)<109/50 := by
        have hh := Real.sq_sqrt (show 0≤(1489593/1000000:ℝ)^2+
          (1580219/1000000)^2 by positivity)
        have hz := Real.sqrt_nonneg ((1489593/1000000:ℝ)^2+(1580219/1000000)^2)
        nlinarith
      have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
      have hprod := (mul_lt_mul_of_pos_left hn hR).trans
        (mul_lt_mul_of_pos_right (show CommonQuarter.radius<2 by
          linarith [CommonQuarter.radius_bounds.2]) (by norm_num : (0:ℝ)<109/50))
      dsimp [unsigned]
      rw [hb]
      dsimp [FramePair.label]
      linarith
  | high =>
      have ht : s.branch.type≠0 := by simp [hb,Branch.type]
      have hbounds := CommonQuarter.outer_bounds (outer_data s ht)
      have hlo : c0≤ s.a := hbounds.1
      have hhi : s.b≤c0 := hbounds.2.2.2.1
      dsimp [unsigned]
      rw [hb]
      dsimp [FramePair.label]
      linarith [pi_lt_22_over_7]

theorem marker_outer_upper (s : State) (hs : s.branch.type≠0) :
    unsigned s≤(111/100)*s.b := by
  have hh := (outer_marker_bounds s hs).2
  have ha := (CommonQuarter.outer_bounds (outer_data s hs)).2.1
  change s.a≤a0 at ha
  linarith

theorem marker_zero (s : State) (hb : s.b=0) : unsigned s=0 := by
  have hu := marker_small_upper s (by linarith)
  have hl := marker_nonneg s
  rw [hb] at hu
  linarith

theorem signed_of_nonpos (s : State) (hy : sign s.positive*s.b≤0) :
    s.signedLabel= -unsigned s := by
  change sign s.positive*unsigned s= -unsigned s
  cases hp : s.positive <;> simp [hp,FramePair.sign] at hy ⊢
  have hz : s.b=0 := le_antisymm hy s.b_nonneg
  rw [marker_zero s hz]
  ring

theorem signed_of_nonneg (s : State) (hy : 0≤ sign s.positive*s.b) :
    s.signedLabel=unsigned s := by
  change sign s.positive*unsigned s=unsigned s
  cases hp : s.positive <;> simp [hp,FramePair.sign] at hy ⊢
  have hz : s.b=0 := by linarith [s.b_nonneg]
  rw [marker_zero s hz]
  ring

theorem quarter_zero_margin (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (ht : sign t.positive*t.b≤0) :
    s.Feasible t 0 (Real.pi/2+d) ↔
      (1+Real.cos d+|Real.sin d|)/2≤
        sign s.positive*s.b+t.a*Real.cos d-t.b*Real.sin d := by
  have hty := transverse_nonpos_eq t ht
  simp only [State.Feasible,forwardMargin,Matrix.cons_val,Real.sin_add,Real.cos_add,
    Real.sin_pi_div_two,Real.cos_pi_div_two,one_mul,zero_mul,
    CommonQuarter.quarter_width (by simpa only [frameCap] using hd)]
  rw [show sign t.positive*t.b= -t.b from hty]
  constructor <;> intro hh <;> linarith

theorem quarter_one_margin (s t : State) {d : ℝ} (hd : |d|≤frameCap) :
    s.Feasible t 1 (Real.pi/2+d) ↔
      (1+Real.cos d+|Real.sin d|)/2≤
        t.a+s.a*Real.sin d+sign s.positive*s.b*Real.cos d := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val,Real.sin_add,Real.cos_add,
    Real.sin_pi_div_two,Real.cos_pi_div_two,one_mul,zero_mul,
    CommonQuarter.quarter_width (by simpa only [frameCap] using hd)]
  constructor <;> intro hh <;> linarith

end SquaresInCircles.Eight.GlobalQuarterSign
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalQuarterSign

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
    have hsin := Real.sin_ge_sub_cube hx.1
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
    have hsin := Real.sin_ge_sub_cube hx.1
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
  have hcos := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := x))
    (show 0≤(9/8:ℝ)-x by linarith [hx.2])
  have hsin := Real.sin_ge_sub_cube hx.1
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
  have hcos := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := x))
    (show 0≤(9/8:ℝ)+x by linarith [hx.1])
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
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsin := Real.sin_ge_sub_cube hx.1
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

end SquaresInCircles.Eight.GlobalQuarterSign
end
end
end
