module

public import SquaresInCircles.Eight.TableFree.OutsideDE2Reference

/-!
# Strict derivative gap on the original-radius reference contact

Uncompiled source. This completes the whole-interval scalar comparison:
the actual reference gap increases, and its left endpoint has reserve
greater than 0.0048. Both the circle identity and the contact equation
are used at the endpoint. No anchor is moved to the reference solution.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.OutsideDE2Reference
open Polynomial OutsideDE2Polynomial

theorem u_deriv (q p : ℝ) : HasDerivAt (u q) (-Real.cos p) p := by
  have h := (hasDerivAt_const p (leastPrimary q)).sub (Real.hasDerivAt_sin p)
  rw [zero_sub] at h
  exact h

theorem z_deriv {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    HasDerivAt (z q) (u q p*Real.cos p/z q p) p := by
  have hz0 : 0<z q p := lt_trans (by norm_num [Zlo]) (z_bounds hq hp).1
  have hd := ((hasDerivAt_const p q).sub ((u_deriv q p).pow 2)).sqrt
    (z_bounds hq hp).2.2.ne'
  convert hd using 1
  · rfl
  · dsimp [z]
    field_simp [show Real.sqrt (q-(u q p)^2)≠0 from hz0.ne']
    ring

theorem xy_deriv {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    HasDerivAt (x q) (-y q p*(1-Real.cos p/z q p)) p ∧
      HasDerivAt (y q) (beta q p) p := by
  have hz0 : 0<z q p := lt_trans (by norm_num [Zlo]) (z_bounds hq hp).1
  have hz := z_deriv hq hp
  have hu := u_deriv q p
  constructor
  · convert (hz.mul (Real.hasDerivAt_cos p)).sub (hu.mul (Real.hasDerivAt_sin p)) using 1
    · rfl
    · dsimp [y]
      field_simp [hz0.ne']
      ring
  · convert (hz.mul (Real.hasDerivAt_sin p)).add (hu.mul (Real.hasDerivAt_cos p)) using 1
    · rfl
    · dsimp [beta,x]
      field_simp [hz0.ne']
      ring

theorem gap_deriv {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    HasDerivAt (gap q) (gapDerivative q p) p := by
  have hb := bounds hq hp
  have hr := root_bounds hq hp
  have hx0 : 0<x q p := (factors_positive hp).2.2.1.trans_le hb.x_lower
  have hz0 : 0<z q p := lt_trans (by norm_num [Zlo]) hb.z_lower
  have hR0 : 0<radius q := lt_trans (by norm_num [Rlo]) hb.radius_lower
  have hd := xy_deriv hq hp
  have hL : HasDerivAt (ell q) (-beta q p) p := by
    have h := (hasDerivAt_const p (1+Real.cos (7/10 : ℝ))).sub hd.2
    rw [zero_sub] at h
    exact h
  have hrad : 0<q-(ell q p)^2 := Real.sqrt_pos.mp hr.2.2.1
  have hW : HasDerivAt (root q) (ell q p*beta q p/root q p) p := by
    convert ((hasDerivAt_const p q).sub (hL.pow 2)).sqrt hrad.ne' using 1
    · rfl
    · dsimp [root]
      field_simp [show Real.sqrt (q-(ell q p)^2)≠0 from hr.2.2.1.ne']
      ring
  have hfactor : HasDerivAt (fun t => 1-Real.cos t/radius q)
      (Real.sin p/radius q) p := by
    convert (hasDerivAt_const p (1:ℝ)).sub ((Real.hasDerivAt_cos p).div_const (radius q)) using 1
    ring
  convert (hW.sub_const (Real.sin (7/10 : ℝ))).sub (hd.1.mul hfactor) using 1
  · rfl
  · dsimp [gapDerivative,beta]
    field_simp [hx0.ne',hz0.ne',hR0.ne',hr.2.2.1.ne']
    ring

theorem endpoint_y_floor {q : ℝ} (hq : qLow≤q∧q≤qCap) :
    (379/625 : ℝ)<y q (11/50) := by
  have hp : (11/50 : ℝ)∈Icc (11/50 : ℝ) (7/10) := by constructor <;> norm_num
  have hb := bounds hq hp
  have he := contact_circle hq hp
  have hy0 := y_gt_half hq hp
  have hx0 : 0<x q (11/50) := (factors_positive hp).2.2.1.trans_le hb.x_lower
  have hc := taylor_bounds hp
  have hs7 := sin_lower_seven (show (0:ℝ)≤11/50 by norm_num)
  have hs7pos : 0<(11/50 : ℝ)-(11/50)^3/6+(11/50)^5/120-(11/50)^7/5040 := by norm_num
  by_contra! hybad
  have hx : (9417/5000 : ℝ)<x q (11/50) := by
    have hqlo := hq.1
    dsimp [qLow] at hqlo
    nlinarith [he.1]
  have hfirst := mul_le_mul hybad hc.2.2.2.2.2.1
    (by linarith [hc.2.2.2.1,hc.2.2.2.2.1] : 0≤Real.cos (11/50 : ℝ))
    (show (0:ℝ)≤379/625 by norm_num)
  have hsecond := mul_le_mul
    (show (4417/5000 : ℝ)≤x q (11/50)-1 by linarith)
    hs7 hs7pos.le (by linarith : 0≤x q (11/50)-1)
  rw [C4_eval] at hfirst
  norm_num at hfirst hsecond
  have hP := (constant_bounds hq).2.2.1
  dsimp [Plo] at hP
  nlinarith [he.2]

theorem endpoint_gap {q : ℝ} (hq : qLow≤q∧q≤qCap) :
    (3/625 : ℝ)<gap q (11/50) := by
  have hp : (11/50 : ℝ)∈Icc (11/50 : ℝ) (7/10) := by constructor <;> norm_num
  have hb := bounds hq hp
  have he := contact_circle hq hp
  have hy := endpoint_y_floor hq
  have hx : x q (11/50)<18837/10000 := by
    have hqu : q≤9789/2500 := hq.2
    have hy2 := pow_lt_pow_left₀ hy (by norm_num) (two_ne_zero)
    have hx2 : (x q (11/50))^2<(18837/10000)^2 := by linarith only [he.1,hy2,hqu]
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hx2
  have hr := root_bounds hq hp
  have hcH := cos_upper_four (show (0:ℝ)≤7/10 by norm_num)
  have hsH := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hL : ell q (11/50) <
      1+(1-(7/10 : ℝ)^2/2+(7/10)^4/24)-379/625 := by
    dsimp only [ell]
    linarith only [hcH,hy]
  have hroot_sq : (root q (11/50))^2=q-(ell q (11/50))^2 :=
    Real.sq_sqrt (Real.sqrt_pos.mp hr.2.2.1).le
  have hroot : (7/10 : ℝ)-(7/10)^3/6+(7/10)^5/120+4799/5000<root q (11/50) := by
    have hqlo : 19577/5000≤q := hq.1
    have hL2 := pow_lt_pow_left₀ hL hr.1.le (two_ne_zero)
    have h2 : ((7/10 : ℝ)-(7/10)^3/6+(7/10)^5/120+4799/5000)^2<(root q (11/50))^2 := by
      rw [hroot_sq]
      norm_num at hL2 ⊢
      linarith only [hL2,hqlo]
    exact lt_of_pow_lt_pow_left₀ 2 hr.2.2.1.le h2
  have hC : 4799/5000<root q (11/50)-Real.sin (7/10 : ℝ) := by linarith only [hroot,hsH]
  have hc0 := cos_lower_six (show (0:ℝ)≤11/50 by norm_num)
  have hR0 : 0<radius q := lt_trans (by norm_num [Rlo]) hb.radius_lower
  have hdiv := div_le_div₀ (le_trans (by norm_num) hc0) hc0 hR0 hb.radius_upper.le
  have hfactor : 1-Real.cos (11/50 : ℝ)/radius q≤
      1-(1-(11/50 : ℝ)^2/2+(11/50)^4/24-(11/50)^6/720)/(Rhi:ℝ) := by linarith only [hdiv]
  have hfactor0 : 0≤1-Real.cos (11/50 : ℝ)/radius q :=
    (factors_positive hp).2.2.2.2.1.le.trans hb.radius_factor
  have hprod := mul_le_mul hx.le hfactor hfactor0 (show (0:ℝ)≤18837/10000 by norm_num)
  have hB : x q (11/50)*(1-Real.cos (11/50 : ℝ)/radius q)<191/200 := by
    norm_num [Rhi] at hprod
    linarith only [hprod]
  dsimp only [gap]
  linarith only [hC,hB]

theorem gap_strictMono {q : ℝ} (hq : qLow≤q∧q≤qCap) :
    StrictMonoOn (gap q) (Icc (11/50 : ℝ) (7/10)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (11/50 : ℝ) (7/10))
  · exact fun p hp => (gap_deriv hq hp).continuousAt.continuousWithinAt
  · intro p hp
    rw [(gap_deriv hq (interior_subset hp)).deriv]
    exact derivative_pos hq (interior_subset hp)

theorem gap_positive {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) : 0<gap q p := by
  have hbase := endpoint_gap hq
  rcases hp.1.eq_or_lt with he | hlt
  · rw [← he]
    linarith
  · have hh := gap_strictMono hq (by constructor <;> norm_num) hp hlt
    linarith

/-- The actual outer reference contact has a strictly positive DE2
derivative gap on the entire long-EH interval, at the original q. -/
theorem reference_gap {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    beta q p<root q p-Real.sin (7/10 : ℝ) := by
  have hb := bounds hq hp
  have hz0 : 0<z q p := lt_trans (by norm_num [Zlo]) hb.z_lower
  have hx0 : 0≤x q p := (factors_positive hp).2.2.1.le.trans hb.x_lower
  have hc0 : 0≤Real.cos p := by
    have ht := taylor_bounds hp
    exact ht.2.2.2.1.le.trans ht.2.2.2.2.1
  have hd := div_le_div₀ hc0 le_rfl hz0 hb.z_upper
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_left hd 1) hx0
  have hg := gap_positive hq hp
  dsimp [beta,gap] at *
  linarith

end SquaresInCircles.Eight.TableFree.OutsideDE2Reference
