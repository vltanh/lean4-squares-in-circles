import SquaresInCircles.Six.Normalization.Complete

/-!
# E and N along the sides of C

If E is separated from C along the east side of C, its angle from the east
direction is less than `203/1000` in absolute value, and likewise for N and the
north side. The cap depth `capDepth t` at the angle `t` of the square is at
least the depth of the side, `1/2 + cx ≥ 1/2` for E. For `203/1000 ≤ t < 1/4`
the cap depth is `(ρ0 - 1/2) cos t - sin t/2`; the Taylor bound
`sin x ≥ x - x³/6` at `x = 203/1000`, the resulting `cos t ≤ 49/50` and
`ρ0 < 1113/1000` make it less than `1/2`.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- A cap depth of at least `1/2` at an angle `t ≤ π/4` forces
`t < 203/1000`. -/
theorem cap_angle_lt_203_1000 {height t : ℝ}
    (hh : 1 / 2 ≤ height) (hcap : height ≤ capDepth t)
    (htpi : t ≤ Real.pi / 4) : t < 203 / 1000 := by
  have htq := cap_angle_lt_quarter hh hcap htpi
  by_contra! ht
  have hlow : t ≤ capSwitch := by linarith [capSwitch_gt_29_100]
  have hsbase := Real.sin_ge_sub_cube (x := (203 : ℝ) / 1000) (by norm_num)
  have hsmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ (203 : ℝ) / 1000 by linarith [Real.pi_pos])
    (show t ≤ Real.pi / 2 by linarith [Real.pi_pos]) ht
  have hs : (1209634573 : ℝ) / 6000000000 ≤ Real.sin t := by
    nlinarith
  have hc : Real.cos t ≤ 49 / 50 := by
    by_contra! hcos
    have hp := mul_pos
      (show 0 < Real.cos t - 49 / 50 by linarith)
      (show 0 < Real.cos t + 49 / 50 by linarith)
    have hsq := mul_nonneg
      (show 0 ≤ Real.sin t - 1209634573 / 6000000000 by linarith)
      (show 0 ≤ Real.sin t + 1209634573 / 6000000000 by linarith)
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hm := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ rho0 - 1 / 2 by linarith [rho0_lower])
  rw [capDepth, ite_eq_left hlow, capFirst] at hcap
  nlinarith [rho0_upper]

/-- If E is separated from C along the east side of C, its angle is less than
`203/1000` in absolute value. -/
theorem PinPacking.east_cardinal_angle_203 {R : ℝ} (P : PinPacking R)
    (hE : 0 ≤ centralMargin .east (P.phase 0) (P.radial 0) (P.transverse 0)
      P.center.1 P.center.2) : |P.phase 0| < 203 / 1000 := by
  have hcap := P.cardinal_cap_depth 0 hE
  have hangle := P.matching_cardinal_angle 0 hE
  have h0 : matchingCardinal 0 = .east := rfl
  rw [h0] at hcap hangle
  simp only [cardinalCenter, cardinalDepth, sub_zero] at hcap hangle
  apply cap_angle_lt_203_1000
    (show (1 : ℝ) / 2 ≤ 1 / 2 + P.center.1 by linarith [P.box.1.1]) hcap
  linarith [Real.pi_gt_d2]

/-- If N is separated from C along the north side of C, its angle from the north
direction is less than `203/1000` in absolute value. -/
theorem PinPacking.north_cardinal_angle_203 {R : ℝ} (P : PinPacking R)
    (hN : 0 ≤ centralMargin .north (P.phase 1) (P.radial 1) (P.transverse 1)
      P.center.1 P.center.2) : |P.phase 1 - Real.pi / 2| < 203 / 1000 := by
  have hcap := P.cardinal_cap_depth 1 hN
  have hangle := P.matching_cardinal_angle 1 hN
  have h1 : matchingCardinal 1 = .north := rfl
  rw [h1] at hcap hangle
  simp only [cardinalCenter, cardinalDepth] at hcap hangle
  apply cap_angle_lt_203_1000
    (show (1 : ℝ) / 2 ≤ 1 / 2 + P.center.2 by linarith [P.box.2.1]) hcap
  linarith [Real.pi_gt_d2]

/-- The bound for E in a normalized packing where E is separated from C along
the east side of C. -/
theorem NormalizedPacking.east_cardinal_angle_203 {R : ℝ} (P : NormalizedPacking R)
    (hE : P.ownBits 0 = false) : |P.helperAngle 0| < 203 / 1000 := by
  have h0 : matchingCardinal 0 = .east := rfl
  simpa only [NormalizedPacking.helperAngle, h0, cardinalCenter, sub_zero]
    using P.toPinPacking.east_cardinal_angle_203 (P.cardinal_separator 0 hE)

/-- The bound for N in a normalized packing where N is separated from C along
the north side of C. -/
theorem NormalizedPacking.north_cardinal_angle_203 {R : ℝ} (P : NormalizedPacking R)
    (hN : P.ownBits 1 = false) : |P.helperAngle 1| < 203 / 1000 := by
  have h1 : matchingCardinal 1 = .north := rfl
  simpa only [NormalizedPacking.helperAngle, h1, cardinalCenter]
    using P.toPinPacking.north_cardinal_angle_203 (P.cardinal_separator 1 hN)

end SquaresInCircles.Six.Normalization
