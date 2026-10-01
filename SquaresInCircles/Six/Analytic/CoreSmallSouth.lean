import SquaresInCircles.Six.Analytic.CoreSmallNorth
import SquaresInCircles.Six.Normalization.OwnEastExclusion

/-!
# The remaining quadrants when 0 <= cy <= c0 < cx

The south marker budget is 2/3. The east quadrant has no admissible separator:
its north/south cardinal alternatives would make the short chart axis face a
deep cap; OWN, CE and both secondary alternatives are excluded analytically.
These arguments do not assume pin assignment or the sought strong box.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma south_small_own {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : c0 < x) (hx1 : x ≤ 1/2)
    (hy : y ≤ c0)
    (hm : 0 ≤ centralMargin .own (-Real.pi/2+t) a b x y) :
    liftedMarker (-Real.pi/2+t) a b < -Real.pi/2+2/3 := by
  have htr := octant_trig ht
  have hc0 : 0 ≤ Real.cos t := by linarith [htr.1.1]
  have hylo : 77/200 ≤ 1/2-y := by linarith [c0_lt_23_200]
  have hymul := mul_le_mul_of_nonneg_right hylo hc0
  have hl := label_signed_upper h
  rw [south_own] at hm
  by_cases ht0 : 0 ≤ t
  · have hs0 := sin_nonneg_octant ht0 ((le_abs_self t).trans ht)
    have hx61 : 61/100 ≤ x+1/2 := by dsimp [c0] at hx; linarith [rho0_lower]
    have hxmul := mul_le_mul_of_nonneg_right hx61 hs0
    have ha : 1/2+(77/200)*Real.cos t+(61/100)*Real.sin t ≤ a := by
      dsimp [angularWidth] at hm
      rw [abs_of_nonneg hc0,abs_of_nonneg hs0] at hm
      nlinarith
    have hbnd := south_own_towards h ht0 ((le_abs_self t).trans ht) ha
    dsimp [liftedMarker]
    linarith
  · have htneg : t < 0 := lt_of_not_ge ht0
    have htv : 0 ≤ -t := by linarith
    have htv1 : -t ≤ Real.pi/4 := by have hh := abs_le.mp ht; linarith [hh.1]
    have hs0 := sin_nonpos_octant htneg.le (by linarith [(abs_le.mp ht).1])
    have hxmul := mul_nonneg (show 0 ≤ 1/2-x by linarith)
      (sin_nonneg_octant htv htv1)
    have ha : 1/2+(77/200)*Real.cos (-t) ≤ a := by
      dsimp [angularWidth] at hm
      rw [abs_of_nonneg hc0,abs_of_nonpos hs0] at hm
      rw [Real.sin_neg] at hxmul
      rw [Real.cos_neg]
      nlinarith
    have hbnd := south_own_away h htv htv1 ha
    dsimp [liftedMarker]
    linarith

lemma south_small_cap {a b t y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hy : y ≤ c0)
    (hm : 1/2-y+angularWidth t ≤ centerX t a b) :
    liftedMarker (-Real.pi/2+t) a b < -Real.pi/2+2/3 := by
  have hheight : coreRadius ≤ 1/2-y := by linarith [c0_add_coreRadius]
  obtain ⟨ht40,_,ha,_,hu,_⟩ := signed_cap_bounds ht hheight (chart_corner h) hm
  have hl := label_signed_upper h
  by_cases ht0 : t ≤ 0
  · dsimp [liftedMarker]
    linarith [U0_lt_117_250]
  · have htpos : 0 < t := lt_of_not_ge ht0
    have hthi : t < 2/5 := by simpa only [abs_of_pos htpos] using ht40
    by_cases hb : b ≤ 0
    · have hmark := (liftedMarker_of_nonpos (t := -Real.pi/2+t) h.seven_admissible hb).2
      linarith
    · have hbpos : 0 < b := lt_of_not_ge hb
      have hc0 : 0 ≤ Real.cos t := by linarith [(octant_trig ht).1.1]
      have hs0 := sin_nonneg_octant htpos.le ((le_abs_self t).trans ht)
      have hmul := mul_nonneg (show 0 ≤ a-1/2 by linarith [h.half_le])
        (show 0 ≤ 1-Real.cos t by linarith [Real.cos_le_one t])
      have hrad : 2-rho0+(|b|+1/2)*Real.sin t ≤ a := by
        dsimp [angularWidth,centerX] at hm
        rw [abs_of_nonneg hc0,abs_of_nonneg hs0] at hm
        rw [abs_of_pos hbpos]
        dsimp [c0] at hy
        nlinarith
      have hbnd := south_cap_towards h htpos.le hthi.le hrad
      dsimp [liftedMarker]
      linarith

theorem south_small_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : c0 < x) (hx1 : x < 1/2)
    (hy0 : 0 ≤ y) (hy : y ≤ c0)
    (hsep : ∃ k, 0 ≤ centralMargin k (-Real.pi/2+t) a b x y) :
    liftedMarker (-Real.pi/2+t) a b < -Real.pi/2+2/3 := by
  have hx0 : 0 ≤ x := (c0_pos.trans hx).le
  have hy1 : y ≤ 1/2 := by linarith [c0_lt_23_200]
  obtain ⟨k,hk⟩ := hsep
  cases k
  · exact south_small_own h ht hx hx1.le hy hk
  · exact False.elim ((not_le_of_gt (south_secPlus_negative h ht hx0 hy0 hy1)) hk)
  · have hb := south_secondary_marker h ht hx1.le hy0 hy1 hk
    linarith [Real.pi_lt_d2]
  · exact False.elim ((not_le_of_gt (east_separator_negative (t := -Real.pi/2+t) h hx)) hk)
  · exact (south_west_marker h ht hx1 hk).trans (by linarith)
  · exact False.elim ((not_le_of_gt (south_north_negative h ht hy0)) hk)
  · apply south_small_cap h ht hy
    rw [south_south] at hk
    dsimp [centerX]
    linarith

/-- A1's east quadrant is empty: every SAT alternative is excluded. -/
theorem east_small_impossible {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : c0 < x) (hx1 : x < 1/2)
    (hy0 : 0 ≤ y) (hy : y ≤ c0)
    (hsep : ∃ k, 0 ≤ centralMargin k t a b x y) : False := by
  have hx0 : 0 ≤ x := (c0_pos.trans hx).le
  obtain ⟨k,hk⟩ := hsep
  cases k
  · have hn := own_east_margin_negative h.a_le_rho0 hx hy0
      (show y ≤ x+1/10 by linarith) ht
    change 0 ≤ a-1/2-(x*Real.cos t+y*Real.sin t)-
      (|Real.cos t|+|Real.sin t|)/2 at hk
    linarith
  · exact (not_le_of_gt (east_secPlus_negative h ht hx0 hx1.le hy0)) hk
  · exact (not_le_of_gt (east_secMinus_small_negative h ht hx0 hx1.le
      (hy.trans c0_lt_23_200.le))) hk
  · exact (not_le_of_gt (east_separator_negative h hx)) hk
  · exact no_west_cap_in_east_quadrant h ht hx1 (west_margin_cap hk)
  · apply transverse_cap_impossible h ht
      (show coreRadius ≤ y+1/2 by linarith [half_ge_core])
    dsimp [centralMargin,centerY] at hk
    linarith
  · apply negative_transverse_cap_impossible h ht
      (show coreRadius ≤ 1/2-y by linarith [c0_add_coreRadius])
    dsimp [centralMargin,centerY] at hk
    linarith

end SquaresInCircles.Six.Analytic
