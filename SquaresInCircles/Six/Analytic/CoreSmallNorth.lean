module
public import SquaresInCircles.Six.Analytic.MarkerLifts

@[expose] public section

/-!
# The north half of the small-secondary-center forbidden arc

The single budget is 3/8. Together with the south budget 2/3 it leaves an arc
of length pi-25/24 > 2*pi/3. OWN uses the affine Taylor/completed-square bounds
in CoreProfiles; a north cap uses the actual signed cap inequalities. All seven
SAT alternatives and both coordinate signs are included explicitly.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma north_small_own {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : c0 < x) (hx1 : x ≤ 1/2) (hy0 : 0 ≤ y)
    (hm : 0 ≤ centralMargin .own (Real.pi/2+t) a b x y) :
    Real.pi/2-3/8 < liftedMarker (Real.pi/2+t) a b := by
  have htr := octant_trig ht
  have hc0 : 0 ≤ Real.cos t := by linarith [htr.1.1]
  have hl := label_signed_lower h
  rw [north_own] at hm
  by_cases ht0 : 0 ≤ t
  · have hs0 := sin_nonneg_octant ht0 ((le_abs_self t).trans ht)
    have hxmul := mul_nonneg (show 0 ≤ 1/2-x by linarith) hs0
    have hymul := mul_nonneg hy0 hc0
    have ha : 1/2+(1/2)*Real.cos t ≤ a := by
      dsimp [angularWidth] at hm
      rw [abs_of_nonneg hc0,abs_of_nonneg hs0] at hm
      nlinarith
    have hb := north_own_away h ht0 ((le_abs_self t).trans ht) ha
    dsimp [liftedMarker]
    linarith
  · have htneg : t < 0 := lt_of_not_ge ht0
    have htv : 0 ≤ -t := by linarith
    have htv1 : -t ≤ Real.pi/4 := by have hh := abs_le.mp ht; linarith [hh.1]
    have hsin := sin_nonneg_octant htv htv1
    have hs0 := sin_nonpos_octant htneg.le (abs_le.mp ht).1
    have hx61 : 61/100 ≤ x+1/2 := by dsimp [c0] at hx; linarith [rho0_lower]
    have hxmul := mul_le_mul_of_nonneg_right hx61 hsin
    have hymul := mul_nonneg hy0 hc0
    have ha : 1/2+(1/2)*Real.cos (-t)+(61/100)*Real.sin (-t) ≤ a := by
      dsimp [angularWidth] at hm
      rw [abs_of_nonneg hc0,abs_of_nonpos hs0] at hm
      rw [Real.sin_neg] at hxmul
      rw [Real.cos_neg,Real.sin_neg]
      nlinarith
    have hb := north_own_towards h htv htv1 ha
    dsimp [liftedMarker]
    linarith

lemma north_small_cap {a b t y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hy0 : 0 ≤ y)
    (hm : y+1/2+angularWidth t ≤ centerX t a b) :
    Real.pi/2-3/8 < liftedMarker (Real.pi/2+t) a b := by
  have hheight : coreRadius ≤ y+1/2 := by linarith [half_ge_core]
  obtain ⟨_,_,ha,_,_,_⟩ := signed_cap_bounds ht hheight (chart_corner h) hm
  have ha1 : 1 ≤ a := by linarith
  have hprof := cap_support_bound_signed ht (chart_corner h)
    (show y+1/2+(|Real.cos t|+|Real.sin t|)/2 ≤ a*Real.cos t-b*Real.sin t by
      simpa only [angularWidth,centerX] using hm)
  have htq := cap_angle_lt_quarter (show 1/2 ≤ y+1/2 by linarith) hprof ht
  have hl := label_signed_lower h
  by_cases ht0 : 0 ≤ t
  · have hu := transverse_lt_three_tenths h ha1
    dsimp [liftedMarker]
    linarith
  · have htneg : t < 0 := lt_of_not_ge ht0
    have htv : 0 ≤ -t := by linarith
    have htv1 : -t < 1/4 := by simpa only [abs_of_neg htneg] using htq
    by_cases hb : b < 0
    · have hc0 : 0 ≤ Real.cos t := by linarith [(octant_trig ht).1.1]
      have hs0 := sin_nonpos_octant htneg.le (abs_le.mp ht).1
      have hmul := mul_nonneg (show 0 ≤ a-1/2 by linarith)
        (show 0 ≤ 1-Real.cos t by linarith [Real.cos_le_one t])
      have hrad : 1+(|b|+1/2)*Real.sin (-t) ≤ a := by
        dsimp [angularWidth,centerX] at hm
        rw [abs_of_nonneg hc0,abs_of_nonpos hs0] at hm
        rw [abs_of_neg hb,Real.sin_neg]
        nlinarith
      have hbnd := north_cap_towards h htv htv1.le hrad
      dsimp [liftedMarker]
      linarith
    · have hmark : 0 ≤ signedLabel a b := by
        rw [signedLabel_of_nonneg (le_of_not_gt hb)]
        exact h.seven_admissible.label_nonneg
      dsimp [liftedMarker]
      linarith

/-- The north bound includes every actual central separator, not merely OWN. -/
theorem north_small_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : c0 < x) (hx1 : x < 1/2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2)
    (hsep : ∃ k, 0 ≤ centralMargin k (Real.pi/2+t) a b x y) :
    Real.pi/2-3/8 < liftedMarker (Real.pi/2+t) a b := by
  have hx0 : 0 ≤ x := (c0_pos.trans hx).le
  obtain ⟨k,hk⟩ := hsep
  cases k
  · exact north_small_own h ht hx hx1.le hy0 hk
  · have hm := outward_secondary_marker h ht hx1.le hy0 hy1
      (by simpa only [north_secPlus] using hk)
    dsimp [liftedMarker]
    linarith
  · exact False.elim ((not_le_of_gt (north_secMinus_negative h ht hx0 hy0 hy1)) hk)
  · exact False.elim ((not_le_of_gt (east_separator_negative (t := Real.pi/2+t) h hx)) hk)
  · exact (by linarith : Real.pi/2-3/8 < Real.pi/2).trans (north_west_marker h ht hx1 hk)
  · apply north_small_cap h ht hy0
    rw [north_north] at hk
    dsimp [centerX]
    linarith
  · exact False.elim ((not_le_of_gt (north_south_negative h ht hy1)) hk)

end SquaresInCircles.Six.Analytic
