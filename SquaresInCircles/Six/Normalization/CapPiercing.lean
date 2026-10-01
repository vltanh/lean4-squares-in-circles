import SquaresInCircles.Six.Normalization.CapGeometry
import SquaresInCircles.Six.Normalization.PiercingPolynomial

/-!
# A point in every square of a deep cap

A square in the disk of radius `R0` about the origin, at the phase `t` with
`|t| ≤ π/4`, that lies in the half-plane `x ≥ h` with `h ≥ coreRadius`, contains
the point `(h + 1/2, 0)` in its interior. The chart bounds of a square in a deep
cap and a bound on its transverse offset put the point strictly between both
pairs of its edges; a negative `t` is reduced to a positive one by the
reflection in the `x`-axis.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- The case `0 ≤ t ≤ π/4`. -/
theorem cap_piercing_nonneg {a b h t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ Real.pi / 4) (hh : coreRadius ≤ h)
    (hdisk : ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0, 0) R0 p)
    (hcap : ∀ p, closedSquare (orientedSquare t a b) p → h ≤ p.1) :
    openSquare (orientedSquare t a b) (h + 1 / 2, 0) := by
  obtain ⟨ht', hab, hdepth, haR, hbU, hbhalf⟩ :=
    deep_cap_chart_bounds ht0 ht hh hdisk hcap
  have htr := small_cap_trig ht0 ht'.le
  have hh0 : 77 / 200 ≤ h := by linarith [coreRadius_gt_77_200]
  have hh' : h ≤ 5 / 8 := by linarith [rho0_upper]
  have ha0 : 0 ≤ a := by linarith
  have hZ : 0 ≤ h + 1 / 2 := by linarith
  have hnormal_lower := mul_le_mul
    (show (177 : ℝ) / 200 ≤ h + 1 / 2 by linarith)
    htr.1 (by norm_num : (0 : ℝ) ≤ 23 / 25) hZ
  have hnormal_upper := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hZ
  have htrans_upper := piercing_transverse_upper hh0 hh' (Real.cos_le_one t)
    htr.2.1 htr.2.2.1 hdepth
    (by simpa only [abs_of_nonneg ha0] using orientedSquare_containment hdisk)
    (orientedSquare_cap_support hcap)
  have htrans_nonneg := mul_nonneg hZ htr.2.1
  have hblo := (abs_le.mp hbU).1
  unfold openSquare
  rw [orientedSquare_localX, orientedSquare_localY]
  dsimp only
  constructor
  · apply abs_lt.mpr
    constructor <;> nlinarith [rho0_upper]
  · apply abs_lt.mpr
    constructor <;> nlinarith [U0_lt_half]

lemma orientedSquare_reflect_localX (t a b : ℝ) (p : Point) :
    localX (orientedSquare (-t) a (-b)) p =
      localX (orientedSquare t a b) (p.1, -p.2) := by
  simp only [orientedSquare_localX, Real.cos_neg, Real.sin_neg]
  ring

lemma orientedSquare_reflect_localY (t a b : ℝ) (p : Point) :
    localY (orientedSquare (-t) a (-b)) p =
      -localY (orientedSquare t a b) (p.1, -p.2) := by
  simp only [orientedSquare_localY, Real.cos_neg, Real.sin_neg]
  ring

lemma orientedSquare_reflect_closed (t a b : ℝ) (p : Point) :
    closedSquare (orientedSquare (-t) a (-b)) p ↔
      closedSquare (orientedSquare t a b) (p.1, -p.2) := by
  simp only [closedSquare, orientedSquare_reflect_localX,
    orientedSquare_reflect_localY, abs_neg]

lemma orientedSquare_reflect_open (t a b : ℝ) (p : Point) :
    openSquare (orientedSquare (-t) a (-b)) p ↔
      openSquare (orientedSquare t a b) (p.1, -p.2) := by
  simp only [openSquare, orientedSquare_reflect_localX,
    orientedSquare_reflect_localY, abs_neg]

lemma reflect_y_inDisk (p : Point) :
    inDisk (0, 0) R0 (p.1, -p.2) ↔ inDisk (0, 0) R0 p := by
  simp only [inDisk, normSq, sub, sub_zero, neg_sq]

/-- A square in the disk of radius `R0`, at the phase `t` with `|t| ≤ π/4`, that
lies in the half-plane `x ≥ h` with `h ≥ coreRadius` contains `(h + 1/2, 0)`. -/
theorem cap_piercing {a b h t : ℝ}
    (ht : |t| ≤ Real.pi / 4) (hh : coreRadius ≤ h)
    (hdisk : ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0, 0) R0 p)
    (hcap : ∀ p, closedSquare (orientedSquare t a b) p → h ≤ p.1) :
    openSquare (orientedSquare t a b) (h + 1 / 2, 0) := by
  by_cases ht0 : 0 ≤ t
  · exact cap_piercing_nonneg ht0 ((le_abs_self t).trans ht) hh hdisk hcap
  · have htneg : t < 0 := lt_of_not_ge ht0
    have ht' : -t ≤ Real.pi / 4 := by simpa only [abs_of_neg htneg] using ht
    have hdisk' : ∀ p, closedSquare (orientedSquare (-t) a (-b)) p →
        inDisk (0, 0) R0 p := by
      intro p hp
      exact (reflect_y_inDisk p).mp
        (hdisk (p.1, -p.2) ((orientedSquare_reflect_closed t a b p).mp hp))
    have hcap' : ∀ p, closedSquare (orientedSquare (-t) a (-b)) p → h ≤ p.1 := by
      intro p hp
      exact hcap (p.1, -p.2) ((orientedSquare_reflect_closed t a b p).mp hp)
    have hp := cap_piercing_nonneg (show 0 ≤ -t by linarith) ht' hh hdisk' hcap'
    have hr := (orientedSquare_reflect_open t a b (h + 1 / 2, 0)).mp hp
    simpa only [neg_zero] using hr

end SquaresInCircles.Six.Normalization
