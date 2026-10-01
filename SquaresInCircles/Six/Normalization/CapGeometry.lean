import SquaresInCircles.Six.Normalization.CapSupport
import SquaresInCircles.Six.Normalization.CoreGeometry
import SquaresInCircles.Six.Normalization.SecondarySeparation

/-!
# Deep caps in the actual square geometry

This is K1 and the chart part of K3. The hypotheses concern the original
`closedSquare` and `inDisk` predicates. No strong-central-box conclusion,
pin, separator classification, or Python certificate is assumed. A nearest
side frame is represented by an angle in `[0, pi/4]`; local reflection for
negative angles is handled in `CapPiercing`.

These proof bodies are not yet compiler-validated.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- A square specified by a real frame angle and its center's frame coordinates. -/
def orientedSquare (t a b : ℝ) : UnitSquare where
  center := (a * Real.cos t - b * Real.sin t, a * Real.sin t + b * Real.cos t)
  cosine := Real.cos t
  sine := Real.sin t
  unit := by nlinarith [Real.sin_sq_add_cos_sq t]

lemma orientedSquare_localX (t a b : ℝ) (p : Point) :
    localX (orientedSquare t a b) p = p.1 * Real.cos t + p.2 * Real.sin t - a := by
  dsimp [localX, orientedSquare]
  linear_combination -a * (Real.sin_sq_add_cos_sq t)

lemma orientedSquare_localY (t a b : ℝ) (p : Point) :
    localY (orientedSquare t a b) p = -p.1 * Real.sin t + p.2 * Real.cos t - b := by
  dsimp [localY, orientedSquare]
  linear_combination -b * (Real.sin_sq_add_cos_sq t)

@[simp] lemma orientedSquare_alpha (t a b : ℝ) :
    alpha (orientedSquare t a b) (0, 0) = |a| := by
  simp [alpha, orientedSquare_localX]

@[simp] lemma orientedSquare_beta (t a b : ℝ) :
    beta (orientedSquare t a b) (0, 0) = |b| := by
  simp [beta, orientedSquare_localY]

/-- Exact far-corner containment, extracted from the original disk predicate. -/
lemma orientedSquare_containment {t a b : ℝ}
    (hdisk : ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0, 0) R0 p) :
    (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0 := by
  have h := phi_le_of_contained (orientedSquare t a b) (0, 0) R0 hdisk
  simpa only [orientedSquare_alpha, orientedSquare_beta, phi, R0_sq] using h

/-- K1 follows by applying the cap hypothesis to the appropriate square vertex. -/
lemma orientedSquare_cap_support {t a b h : ℝ}
    (hcap : ∀ p, closedSquare (orientedSquare t a b) p → h ≤ p.1) :
    h + (Real.cos t + Real.sin t) / 2 ≤ a * Real.cos t - b * Real.sin t := by
  let S := orientedSquare t a b
  let p := add S.center (rotate S (-1 / 2, 1 / 2))
  have hp : closedSquare S p := by
    dsimp [p]
    norm_num [closedSquare, localX_rotated, localY_rotated]
  have hh := hcap p hp
  dsimp [p, S, add, rotate, orientedSquare] at hh
  linarith

lemma coordinate_le_rho0 {a b : ℝ}
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0) : |a| ≤ rho0 := by
  have hb : 1 / 4 ≤ (|b| + 1 / 2) ^ 2 := by nlinarith [abs_nonneg b]
  have hs : (|a| + 1 / 2) ^ 2 ≤ Q0 - 1 / 4 := by linarith
  have hr := Real.le_sqrt_of_sq_le hs
  dsimp [rho0]
  linarith

/-- Fixed rational bounds after the angle has been reduced below `2/5`. -/
lemma small_cap_trig {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 / 5) :
    23 / 25 ≤ Real.cos t ∧ 0 ≤ Real.sin t ∧ Real.sin t ≤ 2 / 5 ∧
      1 ≤ Real.cos t + Real.sin t ∧ Real.cos t + Real.sin t ≤ 3 / 2 := by
  have ht2 := mul_nonneg (sub_nonneg.mpr ht)
    (show 0 ≤ (2 : ℝ) / 5 + t by linarith)
  have hc : 23 / 25 ≤ Real.cos t := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0
    (by linarith [Real.pi_gt_d2])
  have hs : Real.sin t ≤ 2 / 5 := (Real.sin_le ht0).trans ht
  have hw : 1 ≤ Real.cos t + Real.sin t := by
    simpa only [abs_of_nonneg (show 0 ≤ Real.cos t by linarith),
      abs_of_nonneg hs0] using one_le_abs_cos_add_abs_sin t
  have hu : Real.cos t + Real.sin t ≤ 3 / 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.cos t - Real.sin t)]
  exact ⟨hc, hs0, hs, hw, hu⟩

/-- A deep east-cap square must have a positive first frame coordinate. -/
lemma deep_cap_primary_pos {a b h t : ℝ}
    (hh : coreRadius ≤ h) (ht0 : 0 ≤ t) (ht : t ≤ 2 / 5)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : h + (Real.cos t + Real.sin t) / 2 ≤
      a * Real.cos t - b * Real.sin t) : 0 < a := by
  have htr := small_cap_trig ht0 ht
  have hc0 : 0 ≤ Real.cos t := by linarith [htr.1]
  have hbR : |b| ≤ rho0 := coordinate_le_rho0 (a := b) (b := a) (by linarith)
  have hm := mul_le_mul hbR htr.2.2.1 htr.2.1
    (show 0 ≤ rho0 by linarith [rho0_gt_one])
  have hbs := mul_le_mul_of_nonneg_right (neg_le_abs b) htr.2.1
  by_contra! ha
  have ha' := mul_nonpos_of_nonpos_of_nonneg ha hc0
  nlinarith [rho0_upper, coreRadius_gt_77_200, htr.2.2.2.1]

/-- The closest cap frame is necessarily the chart's primary frame. -/
lemma deep_cap_primary_dominates {a b h t : ℝ}
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
  nlinarith [coreRadius_gt_77_200]

lemma deep_cap_half_le {a b h t : ℝ}
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

/-- The cap excludes the origin-centered core without reference to a central square. -/
lemma oriented_cap_avoidsCore {a b h t : ℝ}
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

/-- K3, with containment and cap membership as geometric rather than scalar inputs. -/
theorem deep_cap_chart_bounds {a b h t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ Real.pi / 4) (hh : coreRadius ≤ h)
    (hdisk : ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0, 0) R0 p)
    (hcap : ∀ p, closedSquare (orientedSquare t a b) p → h ≤ p.1) :
    t < 2 / 5 ∧ |b| < a ∧ h + 1 / 2 ≤ a ∧
      a ≤ rho0 ∧ |b| ≤ U0 ∧ |b| < 1 / 2 := by
  have hbox := orientedSquare_containment hdisk
  have hsupp := orientedSquare_cap_support hcap
  have hbound := cap_support_bound ht0 ht hbox hsupp
  have ht' := cap_angle_lt_two_fifths hh hbound ht
  have hab := deep_cap_primary_dominates hh ht0 ht'.le hbox hsupp
  have ha := deep_cap_half_le hh ht0 ht'.le hbox hsupp
  have havoid := oriented_cap_avoidsCore ha hh hcap
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

end SquaresInCircles.Six.Normalization
