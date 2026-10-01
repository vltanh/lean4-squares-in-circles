import SquaresInCircles.Six.Normalization.Markers

/-!
# The distance of a centre from the disk centre

A square in the disk of squared radius `Q0` has `phi a b ≤ Q0` at its far
corner, and then `a² + b² ≤ rho0²`: its centre lies within `rho0` of the disk
centre. So its projection on every unit vector is at most `rho0`, and if the
centre of C has `cx > c0 = rho0 - 1`, the square is not separated from C along
the east side of C, whatever its angle.
-/
noncomputable section
namespace SquaresInCircles.Six.Normalization

lemma radial_sq_le_of_phi {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : phi a b ≤ Q0) : a ^ 2 + b ^ 2 ≤ rho0 ^ 2 := by
  by_contra! hr
  have hsum : a + b < rho0 := by
    have hid := rho0_sq
    dsimp [phi] at hc
    nlinarith
  have hp := mul_pos (sub_pos.mpr hsum)
    (show 0 < rho0 + a + b by linarith [rho0_gt_one])
  nlinarith [mul_nonneg ha hb]

/-- A square in the disk of squared radius `Q0` has its centre within `rho0`
of `o`. -/
theorem center_radius_sq {S : UnitSquare} {o : Point}
    (hc : phi (alpha S o) (beta S o) ≤ Q0) :
    normSq (sub S.center o) ≤ rho0 ^ 2 := by
  rw [local_center_norm]
  exact radial_sq_le_of_phi (alpha_nonneg S o) (beta_nonneg S o) hc

lemma projection_abs_le_rho0 {x y c s : ℝ}
    (hp : x ^ 2 + y ^ 2 ≤ rho0 ^ 2) (hu : c ^ 2 + s ^ 2 = 1) :
    |x*c + y*s| ≤ rho0 := by
  have hid : (x*c+y*s)^2 + (x*s-y*c)^2 = (x^2+y^2)*(c^2+s^2) := by ring
  rw [hu,mul_one] at hid
  have hsq : (x*c+y*s)^2 ≤ rho0^2 := by nlinarith [sq_nonneg (x*s-y*c)]
  apply abs_le.mpr
  constructor <;> nlinarith [rho0_gt_one]

lemma chart_center_radius_sq {a b : ℝ} (hc : ContainedChart a |b|) :
    a ^ 2 + b ^ 2 ≤ rho0 ^ 2 := by
  have hh := radial_sq_le_of_phi (by linarith [hc.half_le]) (abs_nonneg b) hc.containment
  simpa only [sq_abs] using hh

lemma chart_center_east_bound {a b t : ℝ} (hc : ContainedChart a |b|) :
    a * Real.cos t - b * Real.sin t ≤ rho0 := by
  have hh := projection_abs_le_rho0 (chart_center_radius_sq hc)
    (c := Real.cos t) (s := -Real.sin t)
    (by nlinarith [Real.sin_sq_add_cos_sq t])
  have hu := (abs_le.mp hh).2
  nlinarith

/-- If `cx > c0`, a square in the disk is not separated from C along the east
side of C, at any angle `t`. -/
theorem east_separator_negative {a b t cx : ℝ} (hc : ContainedChart a |b|)
    (hx : c0 < cx) :
    a * Real.cos t - b * Real.sin t -
      (|Real.cos t| + |Real.sin t|) / 2 - cx - 1 / 2 < 0 := by
  have hw := one_le_abs_cos_add_abs_sin t
  have hP := chart_center_east_bound (t := t) hc
  dsimp [c0] at hx
  linarith

end SquaresInCircles.Six.Normalization
