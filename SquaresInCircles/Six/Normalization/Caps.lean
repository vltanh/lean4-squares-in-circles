import SquaresInCircles.Six.Supports

/-!
# Squares in a deep cap

A square in the closed disk of radius `R0` that lies beyond a line whose normal
makes the angle `t`, `|t| ≤ π/4`, with an axis of the square keeps the line
within `capDepth |t|` of the origin: with `A = |a| + 1/2` and `B = |b| + 1/2` on
the disk `A² + B² ≤ Q0`, the support `A cos t + B sin t` of the far corner along
the normal is at most its value at the corner `(ρ0 + 1/2, 1/2)` of the disk
below the angle `capSwitch = arcsin (1/(2 R0))`, and at most `R0` beyond it. A
cap at least `coreRadius` deep therefore forces `|t| < 2/5`, and one at least
`1/2` deep forces `|t| < 1/4`. In a cap `x ≥ h` with `h ≥ coreRadius` the square
has `|b| < a`, `h + 1/2 ≤ a ≤ ρ0`, `|b| ≤ U0` and `|b| < 1/2`
(`deep_cap_bounds`), and it contains the point `(h + 1/2, 0)` (`cap_piercing`):
otherwise its far vertex would leave the disk, by a polynomial positive on a
rectangle. A square with `a ≥ 0` and `|b| < 1/2` faces such a cap: its phase
lies within `2/5` of the normal modulo `2π` (`deep_cap_faces`), since a quarter
or a half turn would make the cap face a short or a negative coordinate.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-! ### The cap depth -/

/-- The angle `arcsin (1/(2 R0))` at which the two branches of the cap depth
meet. -/
def capSwitch : ℝ := Real.arcsin (1 / (2 * R0))

/-- The cap branch: the far corner of the square at `(ρ0 + 1/2, 1/2)`. -/
def capFirst (t : ℝ) : ℝ :=
  (rho0 - 1 / 2) * Real.cos t - (1 / 2) * Real.sin t

/-- The vertex branch: the far vertex on the circle along the normal. -/
def capSecond (t : ℝ) : ℝ := R0 - Real.cos t - Real.sin t

/-- The depth of the deepest cap that holds a square at the angle `t`,
`0 ≤ t ≤ π/4`, to the cap normal. -/
def capDepth (t : ℝ) : ℝ :=
  if t ≤ capSwitch then capFirst t else capSecond t

private lemma switch_sine_bounds : 0 < 1 / (2 * R0) ∧ 1 / (2 * R0) < 1 := by
  have hp : 0 < 2 * R0 := by linarith [R0_pos]
  exact ⟨div_pos (by norm_num) hp,
    (div_lt_one hp).mpr (by linarith [R0_bounds.1])⟩

private lemma capSwitch_nonneg : 0 ≤ capSwitch :=
  Real.arcsin_nonneg.mpr switch_sine_bounds.1.le

private lemma sin_capSwitch : Real.sin capSwitch = 1 / (2 * R0) := by
  exact Real.sin_arcsin (by linarith [switch_sine_bounds.1]) switch_sine_bounds.2.le

lemma capSwitch_gt_29_100 : (29 : ℝ) / 100 < capSwitch := by
  have hden : 0 < 2 * R0 := by linarith [R0_pos]
  have hi : (29 : ℝ) / 100 < 1 / (2 * R0) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith [R0_bounds.2]
  have hs := Real.sin_le capSwitch_nonneg
  rw [sin_capSwitch] at hs
  linarith

private lemma capSwitch_lt_two_fifths : capSwitch < (2 : ℝ) / 5 := by
  have hden : 0 < 2 * R0 := by linarith [R0_pos]
  have hi : 1 / (2 * R0) < (1 : ℝ) / 3 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [R0_bounds.1]
  by_contra! ht
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ (2 : ℝ) / 5 by linarith [Real.pi_pos])
    (show capSwitch ≤ Real.pi / 2 from Real.arcsin_le_pi_div_two _) ht
  rw [sin_capSwitch] at hs
  have hl := Real.sin_ge_sub_cube (x := (2 : ℝ) / 5) (by norm_num)
  nlinarith

private lemma cos_capSwitch : Real.cos capSwitch = (rho0 + 1 / 2) / R0 := by
  have hn : R0 ≠ 0 := ne_of_gt R0_pos
  have hid : 1 - (1 / (2 * R0)) ^ 2 = ((rho0 + 1 / 2) / R0) ^ 2 := by
    field_simp [hn]
    nlinarith [R0_sq, rho0_identity]
  rw [capSwitch, Real.cos_arcsin, hid, Real.sqrt_sq]
  exact div_nonneg (by linarith [rho0_bounds.1]) R0_pos.le

/-- Below the switch angle the corner `(ρ0 + 1/2, 1/2)` is the farthest point of
the disk along the normal: `(ρ0 + 1/2) sin t ≤ (cos t)/2`. -/
private lemma cap_low_branch_slope {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ capSwitch) :
    (rho0 + 1 / 2) * Real.sin t ≤ (1 / 2) * Real.cos t := by
  have hpi : capSwitch ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ t by linarith [Real.pi_pos]) hpi ht
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ht0
    (show capSwitch ≤ Real.pi by linarith [Real.pi_pos]) ht
  rw [sin_capSwitch] at hs
  rw [cos_capSwitch] at hc
  calc
    (rho0 + 1 / 2) * Real.sin t ≤ (rho0 + 1 / 2) * (1 / (2 * R0)) :=
      mul_le_mul_of_nonneg_left hs (by linarith [rho0_bounds.1])
    _ = (1 / 2) * ((rho0 + 1 / 2) / R0) := by
      field_simp [ne_of_gt R0_pos]
    _ ≤ (1 / 2) * Real.cos t := mul_le_mul_of_nonneg_left hc (by norm_num)

/-- A square with `h + (|cos t| + |sin t|)/2 ≤ a cos t - b sin t`, the support
inequality of a square in the cap `x ≥ h`, has `h ≤ capDepth |t|`, for
`|t| ≤ π/4`. -/
theorem cap_support_bound_signed {a b height t : ℝ}
    (ht : |t| ≤ Real.pi / 4)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : height + (|Real.cos t| + |Real.sin t|) / 2 ≤
      a * Real.cos t - b * Real.sin t) :
    height ≤ capDepth |t| := by
  have htr := east_quadrant_trig (abs_nonneg t) ht
  have hcos : Real.cos |t| = |Real.cos t| := by
    rw [Real.cos_abs, abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [(abs_le.mp ht).1, Real.pi_pos], by linarith [(abs_le.mp ht).2, Real.pi_pos]⟩)]
  have hsin : Real.sin |t| = |Real.sin t| :=
    (Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos])).symm
  have hA : a * Real.cos t ≤ |a| * Real.cos |t| := by
    rw [hcos, ← abs_mul]; exact le_abs_self _
  have hB : -(b * Real.sin t) ≤ |b| * Real.sin |t| := by
    rw [hsin, ← abs_mul]; exact neg_le_abs _
  have hab : height ≤ (|a| + 1 / 2) * Real.cos |t| + (|b| + 1 / 2) * Real.sin |t| -
      Real.cos |t| - Real.sin |t| := by
    rw [← hcos, ← hsin] at hcap
    linarith
  unfold capDepth
  split_ifs with hbranch
  · have hcorner := disk_corner_support
      (A := |a| + 1 / 2) (B := |b| + 1 / 2) (a := rho0 + 1 / 2) (b := (1 : ℝ) / 2)
      (c := Real.cos |t|) (s := Real.sin |t|)
      (by linarith [rho0_bounds.1]) (by linarith [abs_nonneg b]) (by linarith [htr.1])
      (by nlinarith [rho0_identity]) hbox (cap_low_branch_slope (abs_nonneg t) hbranch)
    dsimp [capFirst]
    linarith
  · have hround : (|a| + 1 / 2) * Real.cos |t| + (|b| + 1 / 2) * Real.sin |t| ≤ R0 := by
      nlinarith [sq_nonneg ((|a| + 1 / 2) * Real.sin |t| - (|b| + 1 / 2) * Real.cos |t|),
        Real.sin_sq_add_cos_sq |t|, R0_sq, R0_pos, abs_nonneg a, abs_nonneg b, htr.1, htr.2.1]
    dsimp [capSecond]
    linarith

/-! ### The angle of a square in a deep cap -/

private lemma capSecond_two_fifths_lt_core : capSecond (2 / 5) < coreRadius := by
  have hs := Real.sin_ge_sub_cube (x := (2 : ℝ) / 5) (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (2 : ℝ) / 5)
  dsimp [capSecond, coreRadius]
  nlinarith [rho0_bounds.2, R0_bounds.2]

private lemma capDepth_lt_core_of_two_fifths_le {t : ℝ}
    (ht : 2 / 5 ≤ t) (htpi : t ≤ Real.pi / 4) : capDepth t < coreRadius := by
  have hbranch : ¬ t ≤ capSwitch := by linarith [capSwitch_lt_two_fifths]
  rw [capDepth, ite_eq_right hbranch]
  have hm := cos_add_sin_mono (x := (2 : ℝ) / 5) (by norm_num) ht htpi
  have he := capSecond_two_fifths_lt_core
  dsimp [capSecond] at *
  linarith

/-- A cap of depth at least `coreRadius` that holds a square forces
`t < 2/5`. -/
theorem cap_angle_lt_two_fifths {height t : ℝ}
    (hh : coreRadius ≤ height) (hcap : height ≤ capDepth t)
    (htpi : t ≤ Real.pi / 4) : t < 2 / 5 := by
  by_contra! ht
  linarith [capDepth_lt_core_of_two_fifths_le ht htpi]

private lemma capFirst_lt_half_of_quarter_le {t : ℝ}
    (ht : 1 / 4 ≤ t) (htpi : t ≤ Real.pi / 4) : capFirst t < 1 / 2 := by
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ (1 : ℝ) / 4 by linarith [Real.pi_pos])
    (show t ≤ Real.pi / 2 by linarith [Real.pi_pos]) ht
  have hpoly := Real.sin_ge_sub_cube (x := (1 : ℝ) / 4) (by norm_num)
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one t)
    (show 0 ≤ rho0 - 1 / 2 by linarith [rho0_bounds.1])
  dsimp [capFirst]
  nlinarith [rho0_bounds.2]

private lemma capSecond_lt_half_of_quarter_le {t : ℝ}
    (ht : 1 / 4 ≤ t) (htpi : t ≤ Real.pi / 4) : capSecond t < 1 / 2 := by
  have hm := cos_add_sin_mono (x := (1 : ℝ) / 4) (by norm_num) ht htpi
  have hs := Real.sin_ge_sub_cube (x := (1 : ℝ) / 4) (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1 : ℝ) / 4)
  dsimp [capSecond]
  nlinarith [R0_bounds.2]

/-- A cap of depth at least `1/2` that holds a square forces `t < 1/4`. -/
theorem cap_angle_lt_quarter {height t : ℝ}
    (hh : 1 / 2 ≤ height) (hcap : height ≤ capDepth t)
    (htpi : t ≤ Real.pi / 4) : t < 1 / 4 := by
  by_contra! ht
  unfold capDepth at hcap
  split_ifs at hcap
  · linarith [capFirst_lt_half_of_quarter_le ht htpi]
  · linarith [capSecond_lt_half_of_quarter_le ht htpi]

/-! ### The chart of a square in a deep cap -/

private lemma small_cap_trig {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 / 5) :
    23 / 25 ≤ Real.cos t ∧ 0 ≤ Real.sin t ∧ Real.sin t ≤ 2 / 5 ∧
      1 ≤ Real.cos t + Real.sin t ∧ Real.cos t + Real.sin t ≤ 3 / 2 := by
  have hc : 23 / 25 ≤ Real.cos t := by
    linarith [(small_angle (show |t| ≤ 2 / 5 by rwa [abs_of_nonneg ht0])).1]
  have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0
    (by linarith [Real.pi_gt_d2])
  have hs : Real.sin t ≤ 2 / 5 := (Real.sin_le ht0).trans ht
  have hw : 1 ≤ Real.cos t + Real.sin t := by
    simpa only [abs_of_nonneg (show 0 ≤ Real.cos t by linarith),
      abs_of_nonneg hs0] using one_le_abs_cos_add_abs_sin t
  have hu : Real.cos t + Real.sin t ≤ 3 / 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.cos t - Real.sin t)]
  exact ⟨hc, hs0, hs, hw, hu⟩

/-- A square in a deep cap has `a > 0`. -/
private lemma deep_cap_primary_pos {a b h t : ℝ}
    (hh : coreRadius ≤ h) (ht0 : 0 ≤ t) (ht : t ≤ 2 / 5)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : h + (Real.cos t + Real.sin t) / 2 ≤
      a * Real.cos t - b * Real.sin t) : 0 < a := by
  have htr := small_cap_trig ht0 ht
  have hc0 : 0 ≤ Real.cos t := by linarith [htr.1]
  have hbR : |b| ≤ rho0 := coordinate_le_rho0 (a := b) (b := a) (by linarith)
  have hm := mul_le_mul hbR htr.2.2.1 htr.2.1
    (show 0 ≤ rho0 by linarith [rho0_bounds.1])
  have hbs := mul_le_mul_of_nonneg_right (neg_le_abs b) htr.2.1
  by_contra! ha
  have ha' := mul_nonpos_of_nonpos_of_nonneg ha hc0
  nlinarith [rho0_bounds.2, coreRadius_bounds.1, htr.2.2.2.1]

/-- A square in a deep cap has `|b| < a`. -/
private lemma deep_cap_primary_dominates {a b h t : ℝ}
    (hh : coreRadius ≤ h) (ht0 : 0 ≤ t) (ht : t ≤ 2 / 5)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : h + (Real.cos t + Real.sin t) / 2 ≤
      a * Real.cos t - b * Real.sin t) : |b| < a := by
  have ha := deep_cap_primary_pos hh ht0 ht hbox hcap
  have htr := small_cap_trig ht0 ht
  have hs0 := htr.2.1
  have hcs : 0 ≤ Real.cos t - Real.sin t := by
    linarith [htr.1, htr.2.2.1]
  have hw0 : 0 ≤ Real.cos t + Real.sin t := by linarith [htr.2.2.2.1]
  have hw := htr.2.2.2.2
  have hbs := mul_le_mul_of_nonneg_right (neg_le_abs b) hs0
  rw [abs_of_pos ha] at hbox
  by_contra! hab
  have hsum : a + |b| + 1 ≤ 12 / 5 := by
    have hdiff := sq_nonneg (a - |b|)
    norm_num [Q0] at hbox
    nlinarith [abs_nonneg b]
  have hp := mul_nonneg (sub_nonneg.mpr hab) hcs
  have hprod := mul_le_mul_of_nonneg_right hsum hw0
  have hupper : a * Real.cos t + |b| * Real.sin t +
      (Real.cos t + Real.sin t) / 2 ≤
      (6 / 5) * (Real.cos t + Real.sin t) := by nlinarith
  nlinarith [coreRadius_bounds.1]

private lemma deep_cap_half_le {a b h t : ℝ}
    (hh : coreRadius ≤ h) (ht0 : 0 ≤ t) (ht : t ≤ 2 / 5)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : h + (Real.cos t + Real.sin t) / 2 ≤
      a * Real.cos t - b * Real.sin t) : 1 / 2 ≤ a := by
  have hab := deep_cap_primary_dominates hh ht0 ht hbox hcap
  have htr := small_cap_trig ht0 ht
  have hbs := mul_le_mul_of_nonneg_right (neg_le_abs b) htr.2.1
  have hsort := mul_le_mul_of_nonneg_right hab.le htr.2.1
  by_contra! ha
  have hp := mul_nonpos_of_nonpos_of_nonneg
    (show a - 1 / 2 ≤ 0 by linarith)
    (show 0 ≤ Real.cos t + Real.sin t by linarith [htr.2.2.2.1])
  nlinarith [coreRadius_pos]

/-- A square in a deep cap avoids the core disk about the origin. -/
private lemma oriented_cap_avoidsCore {a b h t : ℝ}
    (ha : 1 / 2 ≤ a) (hh : coreRadius ≤ h)
    (hcap : ∀ p, closedSquare (orientedSquare t a b) p → h ≤ p.1) :
    AvoidsCore a |b| := by
  obtain ⟨p, hp, hd⟩ := exists_clipped_point (orientedSquare t a b) (0, 0)
  have hx : coreRadius ≤ p.1 := hh.trans (hcap p hp)
  have hs := mul_nonneg (sub_nonneg.mpr hx)
    (show 0 ≤ p.1 + coreRadius by linarith [coreRadius_pos])
  have hnorm : coreRadius ^ 2 ≤ normSq (sub p (0, 0)) := by
    dsimp [normSq, sub]
    nlinarith [sq_nonneg p.2]
  rw [orientedSquare_alpha, orientedSquare_beta,
    abs_of_nonneg (show 0 ≤ a by linarith),
    max_eq_left (show 0 ≤ a - 1 / 2 by linarith)] at hd
  unfold AvoidsCore
  linarith

/-- The cap bounds for `0 ≤ t ≤ π/4`. -/
private theorem deep_cap_bounds_nonneg {a b h t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ Real.pi / 4) (hh : coreRadius ≤ h)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hm : h + angularWidth t ≤ centerX t a b) :
    t < 2 / 5 ∧ |b| < a ∧ h + 1 / 2 ≤ a ∧ a ≤ rho0 ∧ |b| ≤ U0 ∧ |b| < 1 / 2 := by
  have hc0 : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])
  have hsupp : h + (Real.cos t + Real.sin t) / 2 ≤ a * Real.cos t - b * Real.sin t := by
    simpa only [angularWidth, centerX, abs_of_nonneg hc0, abs_of_nonneg hs0] using hm
  have hbound : h ≤ capDepth t := by
    simpa only [abs_of_nonneg ht0] using
      cap_support_bound_signed (by rwa [abs_of_nonneg ht0]) hbox hm
  have ht' := cap_angle_lt_two_fifths hh hbound ht
  have hab := deep_cap_primary_dominates hh ht0 ht'.le hbox hsupp
  have ha := deep_cap_half_le hh ht0 ht'.le hbox hsupp
  have havoid := oriented_cap_avoidsCore (t := t) (b := b) ha hh fun p hp => by
    have hx := (closed_center_coordinate_bounds hp).1.1
    exact le_trans (by dsimp [angularWidth, centerX] at hm ⊢; linarith) hx
  have hchart : ContainedChart a |b| :=
    ⟨ha, abs_nonneg b, hab.le, by simpa only [abs_of_nonneg (show 0 ≤ a by linarith)] using hbox⟩
  have hu := hchart.u_lt_half havoid
  have htr := small_cap_trig ht0 ht'.le
  have hbs := mul_le_mul_of_nonneg_right (neg_le_abs b) htr.2.1
  have hub := mul_nonpos_of_nonpos_of_nonneg
    (show |b| - 1 / 2 ≤ 0 by linarith) htr.2.1
  have hac := mul_nonneg (show 0 ≤ a - 1 / 2 by linarith)
    (show 0 ≤ 1 - Real.cos t by linarith [Real.cos_le_one t])
  have hdepth : h + 1 / 2 ≤ a := by nlinarith
  exact ⟨ht', hab, hdepth, hchart.a_le_rho0, hchart.u_le_U0 havoid, hu⟩

/-- Changing the signs of the angle and of the transverse coordinate reflects a
square in the `x`-axis; it keeps the margin beyond a vertical line. -/
private lemma neg_margin {a b h t : ℝ} (hm : h + angularWidth t ≤ centerX t a b) :
    h + angularWidth (-t) ≤ centerX (-t) a (-b) := by
  simpa only [angularWidth, centerX, Real.cos_neg, Real.sin_neg, abs_neg, neg_mul_neg] using hm

/-- A square in the closed disk of radius `R0` whose centre lies at least
`angularWidth t` beyond the line `x = h`, with `h ≥ coreRadius` and
`|t| ≤ π/4`, has `|t| < 2/5`, `|b| < a`, `h + 1/2 ≤ a ≤ ρ0`, `|b| ≤ U0` and
`|b| < 1/2`. -/
theorem deep_cap_bounds {a b h t : ℝ} (ht : |t| ≤ Real.pi / 4) (hh : coreRadius ≤ h)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hm : h + angularWidth t ≤ centerX t a b) :
    |t| < 2 / 5 ∧ |b| < a ∧ h + 1 / 2 ≤ a ∧ a ≤ rho0 ∧ |b| ≤ U0 ∧ |b| < 1 / 2 := by
  rcases le_total 0 t with ht0 | ht0
  · rw [abs_of_nonneg ht0] at ht ⊢
    exact deep_cap_bounds_nonneg ht0 ht hh hbox hm
  · rw [abs_of_nonpos ht0] at ht ⊢
    simpa only [abs_neg] using deep_cap_bounds_nonneg (b := -b) (by linarith) ht hh
      (by rwa [abs_neg]) (neg_margin hm)

/-! ### A point in every square of a deep cap -/

private lemma piercing_polynomial_lower {h s : ℝ}
    (hh0 : 0 ≤ h) (hh : h ≤ 5 / 8) (hs0 : 0 ≤ s) (hs : s ≤ 2 / 5) :
    (h + 1) ^ 2 + 1 ≤
      (h + 1 + (1 - (h + 1 / 2) * s) * s) ^ 2 +
      (1 - (h + 1 / 2) * s) ^ 2 := by
  let H : ℝ := h + 1 / 2
  have hH0 : 0 ≤ H := by dsimp [H]; linarith
  have hH : H ≤ 9 / 8 := by dsimp [H]; linarith
  have hHsq := mul_nonneg (sub_nonneg.mpr hH)
    (show 0 ≤ (9 : ℝ) / 8 + H by linarith)
  have hHs : H + H ^ 2 ≤ 12 / 5 := by nlinarith
  have hssq : s ^ 2 ≤ 4 / 25 := by
    have hp := mul_nonneg (sub_nonneg.mpr hs)
      (show 0 ≤ (2 : ℝ) / 5 + s by linarith)
    nlinarith
  have hlin := mul_nonneg (show 0 ≤ 12 / 5 - H - H ^ 2 by linarith) hs0
  have hquad := mul_le_mul hH hssq (sq_nonneg s) (by norm_num : (0 : ℝ) ≤ 9 / 8)
  have hcubic : 0 ≤ H ^ 2 * s ^ 3 := mul_nonneg (sq_nonneg H) (pow_nonneg hs0 3)
  have hbracket : 0 ≤ 1 + (1 - H - H ^ 2) * s - 2 * H * s ^ 2 + H ^ 2 * s ^ 3 := by
    nlinarith
  have hfactor := mul_nonneg hs0 hbracket
  have hid :
      (h + 1 + (1 - (h + 1 / 2) * s) * s) ^ 2 +
          (1 - (h + 1 / 2) * s) ^ 2 - ((h + 1) ^ 2 + 1) =
        s * (1 + (1 - H - H ^ 2) * s - 2 * H * s ^ 2 + H ^ 2 * s ^ 3) := by
    dsimp [H]
    ring
  linarith

private lemma piercing_polynomial_gt_ceiling {h s : ℝ}
    (hh0 : 77 / 200 ≤ h) (hh : h ≤ 5 / 8)
    (hs0 : 0 ≤ s) (hs : s ≤ 2 / 5) :
    Q0 < (h + 1 + (1 - (h + 1 / 2) * s) * s) ^ 2 +
      (1 - (h + 1 / 2) * s) ^ 2 := by
  have hp := piercing_polynomial_lower (by linarith : 0 ≤ h) hh hs0 hs
  have hm := mul_nonneg (sub_nonneg.mpr hh0)
    (show 0 ≤ h + 77 / 200 + 2 by linarith)
  norm_num [Q0] at *
  nlinarith

/-- A square in the disk beyond the line at depth `h`, at an angle with cosine
`c` and sine `s`, has transverse coordinate below `1/2 - (h + 1/2) s`. -/
private theorem piercing_transverse_upper {a b h c s : ℝ}
    (hh0 : 77 / 200 ≤ h) (hh : h ≤ 5 / 8)
    (hc : c ≤ 1) (hs0 : 0 ≤ s) (hs : s ≤ 2 / 5)
    (ha : h + 1 / 2 ≤ a)
    (hbox : (a + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : h + (c + s) / 2 ≤ a * c - b * s) :
    b < 1 / 2 - (h + 1 / 2) * s := by
  by_contra! hb
  let V : ℝ := 1 - (h + 1 / 2) * s
  have hprod := mul_le_mul (show h + 1 / 2 ≤ (9 : ℝ) / 8 by linarith)
    hs hs0 (by norm_num : (0 : ℝ) ≤ 9 / 8)
  have hV : 0 < V := by dsimp [V]; nlinarith
  have hb0 : 0 ≤ b := by nlinarith
  have hVb : V ≤ b + 1 / 2 := by dsimp [V]; linarith
  have hcprod := mul_nonneg
    (show 0 ≤ a - 1 / 2 by linarith) (show 0 ≤ 1 - c by linarith)
  have hVprod := mul_nonneg (sub_nonneg.mpr hVb) hs0
  have hnormal : h + 1 + V * s ≤ a + 1 / 2 := by nlinarith
  have hnormal0 : 0 ≤ h + 1 + V * s := by
    have hp := mul_nonneg hV.le hs0
    linarith
  rw [abs_of_nonneg hb0] at hbox
  have hbad := piercing_polynomial_gt_ceiling hh0 hh hs0 hs
  change Q0 < (h + 1 + V * s) ^ 2 + V ^ 2 at hbad
  linarith [corner_sq_le hnormal0 hV.le hnormal hVb hbox]

/-- A square in the closed disk of radius `R0` whose centre lies at least
`angularWidth t` beyond the line `x = h`, with `h ≥ coreRadius` and
`|t| ≤ π/4`, contains the point `(h + 1/2, 0)`. -/
theorem cap_piercing {a b h t : ℝ} (ht : |t| ≤ Real.pi / 4) (hh : coreRadius ≤ h)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hm : h + angularWidth t ≤ centerX t a b) :
    openSquare (orientedSquare t a b) (h + 1 / 2, 0) := by
  suffices key : ∀ {b t : ℝ}, 0 ≤ t → t ≤ Real.pi / 4 →
      (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0 → h + angularWidth t ≤ centerX t a b →
      openSquare (orientedSquare t a b) (h + 1 / 2, 0) by
    rcases le_total 0 t with ht0 | ht0
    · exact key ht0 (by rwa [abs_of_nonneg ht0] at ht) hbox hm
    · have hp := key (b := -b) (t := -t) (by linarith) (by rwa [abs_of_nonpos ht0] at ht)
        (by rwa [abs_neg]) (neg_margin hm)
      simp only [openSquare, orientedSquare_localX, orientedSquare_localY, Real.cos_neg,
        Real.sin_neg] at hp ⊢
      refine ⟨by simpa using hp.1, ?_⟩
      rw [show -(h + 1 / 2) * Real.sin t + 0 * Real.cos t - b =
        -(-(h + 1 / 2) * -Real.sin t + 0 * Real.cos t - -b) by ring, abs_neg]
      exact hp.2
  intro b t ht0 ht hbox hm
  obtain ⟨ht', hab, hdepth, haR, hbU, hbhalf⟩ := deep_cap_bounds_nonneg ht0 ht hh hbox hm
  have htr := small_cap_trig ht0 ht'.le
  have hh0 : 77 / 200 ≤ h := by linarith [coreRadius_bounds.1]
  have hh' : h ≤ 5 / 8 := by linarith [rho0_bounds.2]
  have ha0 : 0 ≤ a := by linarith
  have hZ : 0 ≤ h + 1 / 2 := by linarith
  have hnormal_lower := mul_le_mul
    (show (177 : ℝ) / 200 ≤ h + 1 / 2 by linarith)
    htr.1 (by norm_num : (0 : ℝ) ≤ 23 / 25) hZ
  have hnormal_upper := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hZ
  have htrans_upper := piercing_transverse_upper hh0 hh' (Real.cos_le_one t)
    htr.2.1 htr.2.2.1 hdepth (by simpa only [abs_of_nonneg ha0] using hbox)
    (by simpa only [angularWidth, centerX, abs_of_nonneg htr.2.1,
      abs_of_nonneg (show 0 ≤ Real.cos t by linarith [htr.1])] using hm)
  have htrans_nonneg := mul_nonneg hZ htr.2.1
  have hblo := (abs_le.mp hbU).1
  unfold openSquare
  rw [orientedSquare_localX, orientedSquare_localY]
  dsimp only
  constructor
  · apply abs_lt.mpr
    constructor <;> nlinarith [rho0_bounds.2]
  · apply abs_lt.mpr
    constructor <;> nlinarith [U0_upper]

/-! ### A square faces a deep cap -/

/-- Two lifts of one direction have the same cosine and sine. -/
lemma cos_sin_eq_of_coe_eq {t u : ℝ} (h : (t : Direction) = u) :
    Real.cos t = Real.cos u ∧ Real.sin t = Real.sin u := by
  have hc := congrArg Real.Angle.cos h
  have hs := congrArg Real.Angle.sin h
  simp only [Real.Angle.cos_coe, Real.Angle.sin_coe] at hc hs
  exact ⟨hc, hs⟩

/-- A square with `a ≥ 0` and `|b| < 1/2` whose centre lies at least
`angularWidth t` beyond the line `x = h`, `h ≥ coreRadius`, faces it: its phase is
`v` modulo `2π` with `|v| < 2/5`. A quarter turn, a half turn or three quarter
turns would put the deep cap in front of the coordinate `-b`, `-a` or `b`. -/
theorem deep_cap_faces {a b h t : ℝ} (ha : 0 ≤ a) (hb : |b| < 1 / 2) (hh : coreRadius ≤ h)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hm : h + angularWidth t ≤ centerX t a b) :
    ∃ v : ℝ, |v| < 2 / 5 ∧ (t : Direction) = v ∧ h + angularWidth v ≤ centerX v a b := by
  have hh0 := coreRadius_pos.trans_le hh
  have hbs := abs_lt.mp hb
  have hbox' : (|-b| + 1 / 2) ^ 2 + (|a| + 1 / 2) ^ 2 ≤ Q0 := by
    rw [abs_neg]; linarith
  rcases four_primary_quadrants t with ⟨v, hv, he⟩ | ⟨v, hv, he⟩ | ⟨v, hv, he⟩ | ⟨v, hv, he⟩
  · obtain ⟨hc, hs⟩ := cos_sin_eq_of_coe_eq he
    have hm' : h + angularWidth v ≤ centerX v a b := by
      simpa only [angularWidth, centerX, hc, hs] using hm
    exact ⟨v, (deep_cap_bounds hv hh hbox hm').1, he, hm'⟩
  · obtain ⟨hc, hs⟩ := cos_sin_eq_of_coe_eq he
    rw [Real.cos_pi_div_two_sub] at hc
    rw [Real.sin_pi_div_two_sub] at hs
    have hm' : h + angularWidth (-v) ≤ centerX (-v) (-b) a := by
      simp only [angularWidth, centerX, Real.cos_neg, Real.sin_neg, abs_neg, hc, hs] at hm ⊢
      linarith
    have := (deep_cap_bounds (by rwa [abs_neg]) hh hbox' hm').2.2.1
    linarith
  · obtain ⟨hc, hs⟩ := cos_sin_eq_of_coe_eq he
    rw [add_comm Real.pi v, Real.cos_add_pi] at hc
    rw [add_comm Real.pi v, Real.sin_add_pi] at hs
    have hm' : h + angularWidth v ≤ centerX v (-a) (-b) := by
      simp only [angularWidth, centerX, abs_neg, hc, hs] at hm ⊢
      linarith
    have := (deep_cap_bounds hv hh (by simpa only [abs_neg] using hbox) hm').2.2.1
    linarith
  · obtain ⟨hc, hs⟩ := cos_sin_eq_of_coe_eq he
    have hc' : Real.cos (-Real.pi / 2 - v) = -Real.sin v := by
      rw [show -Real.pi / 2 - v = -(Real.pi / 2 + v) by ring, Real.cos_neg, Real.cos_add,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    have hs' : Real.sin (-Real.pi / 2 - v) = -Real.cos v := by
      rw [show -Real.pi / 2 - v = -(Real.pi / 2 + v) by ring, Real.sin_neg, Real.sin_add,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    rw [hc'] at hc
    rw [hs'] at hs
    have hm' : h + angularWidth (-v) ≤ centerX (-v) b (-a) := by
      simp only [angularWidth, centerX, Real.cos_neg, Real.sin_neg, abs_neg, hc, hs] at hm ⊢
      linarith
    have := (deep_cap_bounds (by rwa [abs_neg]) hh
      (by rw [abs_neg]; linarith) hm').2.2.1
    linarith

/-- A square with `a ≥ 0` and `|b| < 1/2` in a deep cap, with phase
`|t| ≤ 3π/4`, has `|t| < 2/5`. -/
theorem primary_cap_angle {a b h t : ℝ} (ha : 0 ≤ a) (hb : |b| < 1 / 2)
    (hh : coreRadius ≤ h) (ht : |t| ≤ 3 * Real.pi / 4)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hm : h + angularWidth t ≤ centerX t a b) : |t| < 2 / 5 := by
  obtain ⟨v, hv, he, -⟩ := deep_cap_faces ha hb hh hbox hm
  rwa [phase_eq_of_short_difference he (by
    rw [abs_lt]; constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2,
      (abs_lt.mp hv).1, (abs_lt.mp hv).2, Real.pi_gt_three])]

end SquaresInCircles.Six.Normalization
