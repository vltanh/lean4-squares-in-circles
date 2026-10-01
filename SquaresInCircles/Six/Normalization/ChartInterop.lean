import SquaresInCircles.Six.Normalization.MarkerGaps
import SquaresInCircles.Common.Congruence

/-!
# Signed charts

A square chart with a reversed orientation is read as a chart with the signed
transverse coordinate `signedB`. In these terms the marker of a chart is the
lifted marker of its phase and signed coordinates, its open square is the
oriented square at a real representative of its phase, and a sorted chart
`b ≤ a` of an exterior square in the disk of squared radius `Q0` gives
`ContainedChart a |signedB|`.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

lemma signedB_abs {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    |C.signedB| = C.b := by
  cases h : C.reversed <;>
    simp [SquareChart.signedB, h, abs_of_nonneg C.nonneg.2]

lemma signedB_nonneg_of_not_reversed {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (h : C.reversed = false) : 0 ≤ C.signedB := by
  simpa [SquareChart.signedB, h] using C.nonneg.2

lemma signedLabel_chart {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hC : Seven.Admissible C.a C.b) :
    signedLabel C.a C.signedB = (Seven.chartSign C).coe * Seven.label C.a C.b := by
  cases hr : C.reversed
  · have hb : 0 ≤ C.signedB := signedB_nonneg_of_not_reversed C hr
    rw [signedLabel_of_nonneg hb, signedB_abs]
    simp [Seven.chartSign, hr, Seven.TransverseSign.coe]
  · by_cases hb : C.b = 0
    · have hl := hC.label_zero_iff.mpr hb
      rw [hb] at hl
      simp [signedLabel, SquareChart.signedB, Seven.chartSign, hr, hb, hl]
    · have hpos : 0 < C.b := lt_of_le_of_ne C.nonneg.2 (Ne.symm hb)
      have hneg : C.signedB < 0 := by simp [SquareChart.signedB, hr]; linarith
      rw [signedLabel_of_neg hneg, signedB_abs]
      simp [Seven.chartSign, hr, Seven.TransverseSign.coe]

/-- The lifted marker of a signed chart is the marker of the chart. -/
theorem liftedMarker_eq_chartMarker {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hC : Seven.Admissible C.a C.b) {t : ℝ} (ht : (t : Direction) = C.phase) :
    (liftedMarker t C.a C.signedB : Direction) = Seven.chartMarker C := by
  rw [liftedMarker, Real.Angle.coe_add, ht, signedLabel_chart C hC,
    Seven.chartMarker_formula]

lemma orientedSquare_eq_modelSquare (t a b : ℝ) :
    orientedSquare t a b = modelSquare (0, 0) (t : Direction) (a, b) := by
  unfold orientedSquare modelSquare
  congr 1
  simp only [pointInDirection, Real.Angle.cos_coe, Real.Angle.sin_coe]
  ext <;> ring

/-- The open square of a chart is the model square at its phase and signed
coordinates. -/
theorem chart_same_open_model {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    ∀ p, openSquare S p ↔ openSquare (modelSquare o C.phase (C.a, C.signedB)) p := by
  intro p
  obtain ⟨q, rfl⟩ := (frameEquiv o C.phase).surjective p
  rw [frameEquiv_apply]
  have hm := modelSquare_local o C.phase (C.a, C.signedB) q.1 q.2
  simp only [openSquare, hm.1, hm.2]
  exact C.cartesian q.1 q.2

theorem chart_same_open_oriented {S : UnitSquare} (C : SquareChart S (0, 0))
    {t : ℝ} (ht : (t : Direction) = C.phase) :
    ∀ p, openSquare S p ↔ openSquare (orientedSquare t C.a C.signedB) p := by
  rw [orientedSquare_eq_modelSquare, ht]
  exact chart_same_open_model C

/-- A sorted chart of an exterior square in the disk of squared radius `Q0` is a
contained chart. -/
lemma chart_signed_containment {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o)
    (hQ : phi (alpha S o) (beta S o) ≤ Q0) :
    ContainedChart C.a |C.signedB| := by
  rw [signedB_abs]
  exact ⟨C.exterior hsort hout, C.nonneg.2, hsort, chart_phi C hQ⟩

end SquaresInCircles.Six.Normalization
