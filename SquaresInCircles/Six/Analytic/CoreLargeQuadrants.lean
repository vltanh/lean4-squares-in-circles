import SquaresInCircles.Six.Analytic.CoreLargeEast

/-!
# The north and south quadrants when c0 < cy <= cx < 1/2

North OWN uses the whole-octant transverse estimate u <= 4t/5, and the other
north alternatives are excluded or point west. South OWN uses the weighted
far-corner bound of SouthMarker; the south cap uses its explicit quartic chord
argument. There is no numerical subdivision of a parameter domain.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

 theorem north_large_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hy : c0 < y) (hxy : y ≤ x) (hx1 : x < 1/2)
    (hsep : ∃ k, 0 ≤ centralMargin k (Real.pi/2+t) a b x y) :
    Real.pi/2 ≤ liftedMarker (Real.pi/2+t) a b := by
  have hy0 : 0 ≤ y := (c0_pos.trans hy).le
  have hx0 : 0 ≤ x := hy0.trans hxy
  have hx : c0 < x := hy.trans_le hxy
  have hy1 : y ≤ 1/2 := hxy.trans hx1.le
  obtain ⟨k,hk⟩ := hsep
  cases k
  · have hm := north_own_large_marker h ht hy hxy hx1.le hk
    dsimp [liftedMarker]
    linarith
  · have hm := outward_secondary_marker h ht hx1.le hy0 hy1
      (by simpa only [north_secPlus] using hk)
    dsimp [liftedMarker]
    linarith
  · exact False.elim ((not_le_of_gt (north_secMinus_negative h ht hx0 hy0 hy1)) hk)
  · exact False.elim ((not_le_of_gt (east_separator_negative (t := Real.pi/2+t) h hx)) hk)
  · exact (north_west_marker h ht hx1 hk).le
  · have hbad := east_separator_negative (t := t) h hy
    rw [north_north] at hk
    dsimp [centerX] at hbad
    exact False.elim (by linarith)
  · exact False.elim ((not_le_of_gt (north_south_negative h ht hy1)) hk)

/-- The south bound holds throughout the ordered nonnegative central square;
the large-center hypothesis is not needed for this particular quadrant. -/
theorem south_large_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hx : c0 < x) (hx1 : x < 1/2)
    (hy0 : 0 ≤ y) (hxy : y ≤ x)
    (hsep : ∃ k, 0 ≤ centralMargin k (-Real.pi/2+t) a b x y) :
    liftedMarker (-Real.pi/2+t) a b < -27/50 := by
  have hx0 : 0 ≤ x := (c0_pos.trans hx).le
  have hy1 : y ≤ 1/2 := hxy.trans hx1.le
  have ht1 := (abs_le.mp ht).2
  by_cases hb : b ≤ 0
  · have hm := (liftedMarker_of_nonpos (t := -Real.pi/2+t) h.seven_admissible hb).2
    linarith [Real.pi_gt_d2]
  · have hbpos : 0 < b := lt_of_not_ge hb
    by_cases ht0 : t ≤ 0
    · have hm := (abs_le.mp (signedLabel_bounds h.seven_admissible).1).2
      dsimp [liftedMarker]
      linarith [Real.pi_gt_d2]
    · have htpos : 0 < t := lt_of_not_ge ht0
      have hs0 := sin_nonneg_octant htpos.le ht1
      have htr := octant_trig ht
      have hc0 : 0 ≤ Real.cos t := by linarith [htr.1.1]
      obtain ⟨k,hk⟩ := hsep
      cases k
      · have hcs : 0 ≤ Real.cos t-Real.sin t := by
          rw [abs_of_nonneg hs0] at htr
          linarith [htr.2.1]
        have hfirst := mul_nonneg (show 0 ≤ 1/2-y by linarith) hcs
        have hsecond := mul_nonneg (sub_nonneg.mpr hxy) hs0
        have ha : 1/2+Real.sin t ≤ a := by
          rw [south_own] at hk
          dsimp [angularWidth] at hk
          rw [abs_of_nonneg hc0,abs_of_nonneg hs0] at hk
          nlinarith
        have hm := own_south_marker h htpos.le ht1 ha
        rw [liftedMarker,signedLabel_of_nonneg hbpos.le]
        linarith
      · exact False.elim ((not_le_of_gt (south_secPlus_negative h ht hx0 hy0 hy1)) hk)
      · have hm := south_secondary_marker h ht hx1.le hy0 hy1 hk
        linarith [Real.pi_gt_d2]
      · exact False.elim ((not_le_of_gt (east_separator_negative (t := -Real.pi/2+t) h hx)) hk)
      · exact (south_west_marker h ht hx1 hk).trans (by linarith [Real.pi_gt_d2])
      · exact False.elim ((not_le_of_gt (south_north_negative h ht hy0)) hk)
      · have hcap : (|b|+1/2)*Real.sin t ≤ (a-1/2)*Real.cos t := by
          rw [south_south] at hk
          dsimp [angularWidth] at hk
          rw [abs_of_nonneg hc0,abs_of_nonneg hs0] at hk
          rw [abs_of_pos hbpos]
          nlinarith
        have hm := cap_south_marker h htpos.le ht1 hcap
        rw [liftedMarker,signedLabel_of_nonneg hbpos.le]
        linarith

end SquaresInCircles.Six.Analytic
