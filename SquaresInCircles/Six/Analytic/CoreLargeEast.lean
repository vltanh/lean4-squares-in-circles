import SquaresInCircles.Six.Analytic.CoreSmallSouth

/-!
# East markers when both central coordinates exceed c0

After excluding CE, OWN, CN, CW and SEC+, only the outward secondary separator
and the south cap remain. Each sign of the nearest-frame angle and transverse
coordinate is treated analytically. The genuine SIDE marker branch is retained
through MarkerSupport's weighted-disk estimate.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma east_secondary_large_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hxy : y ≤ x) (hx1 : x ≤ 1/2)
    (hm : 0 ≤ centralMargin .secMinus t a b x y) :
    liftedMarker t a b < -27/50 := by
  have hy1 : y ≤ 1/2 := hxy.trans hx1
  have htr := octant_trig ht
  have hc0 : 0 ≤ Real.cos t := by linarith [htr.1.1]
  dsimp [centralMargin,centralTransverse,angularWidth] at hm
  rw [abs_of_nonneg hc0] at hm
  by_cases ht0 : 0 ≤ t
  · have hs0 := sin_nonneg_octant ht0 ((le_abs_self t).trans ht)
    have hcs : 0 ≤ Real.cos t-Real.sin t := by
      rw [abs_of_nonneg hs0] at htr
      linarith [htr.2.1]
    have hfirst := mul_nonneg (show 0 ≤ 1/2-y by linarith) hcs
    have hsecond := mul_nonneg (sub_nonneg.mpr hxy) hs0
    rw [abs_of_nonneg hs0] at hm
    have hb : b < 0 := by nlinarith
    have hu : 1/2+Real.sin t ≤ |b| := by
      rw [abs_of_neg hb]
      nlinarith
    have hl := marker_offset_ahead h ht0 ((le_abs_self t).trans ht) hu
    rw [liftedMarker,signedLabel_of_neg hb]
    linarith
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hs0 := sin_nonpos_octant htneg.le (by linarith [(abs_le.mp ht).1])
    have hfirst := mul_nonneg (show 0 ≤ 1/2-y by linarith) hc0
    have hsecond := mul_nonneg (show 0 ≤ 1/2-x by linarith)
      (show 0 ≤ -Real.sin t by linarith)
    rw [abs_of_nonpos hs0] at hm
    have hb : b < 0 := by nlinarith
    have hu : 1/2 ≤ |b| := by rw [abs_of_neg hb]; nlinarith
    have hl := h.large_offset_label hu
    rw [liftedMarker,signedLabel_of_neg hb]
    linarith

lemma east_south_cap_marker {a b t y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hy1 : y ≤ 1/2)
    (hm : y-1/2-(a*Real.sin t+b*Real.cos t)-angularWidth t ≥ 0) :
    liftedMarker t a b < -27/50 := by
  have htr := octant_trig ht
  have hcpos : 0 < Real.cos t := by linarith [htr.1.1]
  dsimp [angularWidth] at hm
  rw [abs_of_pos hcpos] at hm
  by_cases ht0 : 0 ≤ t
  · have hs0 := sin_nonneg_octant ht0 ((le_abs_self t).trans ht)
    have hAs := mul_nonneg (show 0 ≤ a-1/2 by linarith [h.half_le]) hs0
    rw [abs_of_nonneg hs0] at hm
    have hL : 0 ≤ -b-1/2 := by
      by_contra! hf
      have hp := mul_neg_of_neg_of_pos hf hcpos
      nlinarith
    have hmul := mul_nonneg hL (show 0 ≤ 1-Real.cos t by linarith [Real.cos_le_one t])
    have hb : b < 0 := by linarith
    have hu : 1/2+Real.sin t ≤ |b| := by
      rw [abs_of_neg hb]
      nlinarith
    have hl := marker_offset_ahead h ht0 ((le_abs_self t).trans ht) hu
    rw [liftedMarker,signedLabel_of_neg hb]
    linarith
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hv : 0 ≤ -t := by linarith
    have hv1 : -t ≤ Real.pi/4 := by have h := abs_le.mp ht; linarith [h.1]
    have hs0 := sin_nonpos_octant htneg.le (by linarith [(abs_le.mp ht).1])
    rw [abs_of_nonpos hs0] at hm
    have hcap : (b+1/2)*Real.cos (-t) ≤ (a-1/2)*Real.sin (-t) := by
      rw [Real.cos_neg,Real.sin_neg]
      nlinarith
    by_cases hb : b < 0
    · have hcap' : (1/2-|b|)*Real.cos (-t) ≤ (a-1/2)*Real.sin (-t) := by
        simpa only [abs_of_neg hb,sub_neg_eq_add,add_comm] using hcap
      have hl := marker_offset_behind h hv hv1 hcap'
      rw [liftedMarker,signedLabel_of_neg hb]
      linarith
    · have hb0 : 0 ≤ b := le_of_not_gt hb
      have hcap' : (|b|+1/2)*Real.cos (-t) ≤ (a-1/2)*Real.sin (-t) := by
        simpa only [abs_of_nonneg hb0] using hcap
      have hl := positive_offset_cap_marker h hv hv1 hcap'
      rw [liftedMarker,signedLabel_of_nonneg hb0]
      linarith

/-- Every surviving east-quadrant marker lies strictly below -27/50. -/
theorem east_large_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : c0 < x) (hx1 : x < 1/2)
    (hy0 : 0 ≤ y) (hxy : y ≤ x)
    (hsep : ∃ k, 0 ≤ centralMargin k t a b x y) :
    liftedMarker t a b < -27/50 := by
  have hx0 : 0 ≤ x := (c0_pos.trans hx).le
  obtain ⟨k,hk⟩ := hsep
  cases k
  · have hn := own_east_margin_negative h.a_le_rho0 hx hy0
      (show y ≤ x+1/10 by linarith) ht
    change 0 ≤ a-1/2-(x*Real.cos t+y*Real.sin t)-
      (|Real.cos t|+|Real.sin t|)/2 at hk
    exact False.elim (by linarith)
  · exact False.elim ((not_le_of_gt (east_secPlus_negative h ht hx0 hx1.le hy0)) hk)
  · exact east_secondary_large_marker h ht hxy hx1.le hk
  · exact False.elim ((not_le_of_gt (east_separator_negative h hx)) hk)
  · exact False.elim (no_west_cap_in_east_quadrant h ht hx1 (west_margin_cap hk))
  · apply False.elim
    apply transverse_cap_impossible h ht
      (show coreRadius ≤ y+1/2 by linarith [half_ge_core])
    dsimp [centralMargin,centerY] at hk
    linarith
  · apply east_south_cap_marker h ht (hxy.trans hx1.le)
    exact hk

end SquaresInCircles.Six.Analytic
