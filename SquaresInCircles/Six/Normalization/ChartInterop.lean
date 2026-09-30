import SquaresInCircles.Six.Normalization.MarkerGaps
import SquaresInCircles.Common.Congruence

/-!
# Real signed charts are the existing geometric SquareCharts

The normalization manuscript uses signed transverse coordinates and real
primary phases. This file transports the original open/closed square sets,
containment, and genuine Seven marker into that notation. Sorting or reversing
a chart never changes the geometric square.
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
      simp [signedLabel, SquareChart.signedB, Seven.chartSign, hr, hb, hl]
    · have hpos : 0 < C.b := lt_of_le_of_ne C.nonneg.2 (Ne.symm hb)
      have hneg : C.signedB < 0 := by simp [SquareChart.signedB, hr]; linarith
      rw [signedLabel_of_neg hneg, signedB_abs]
      simp [Seven.chartSign, hr, Seven.TransverseSign.coe]

/-- The real signed formula has exactly the original Seven marker as its class. -/
theorem liftedMarker_eq_chartMarker {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hC : Seven.Admissible C.a C.b) {t : ℝ} (ht : (t : Direction) = C.phase) :
    (liftedMarker t C.a C.signedB : Direction) = Seven.chartMarker C := by
  rw [liftedMarker, Real.Angle.coe_add, ht, signedLabel_chart C hC,
    Seven.chartMarker_formula]

lemma orientedSquare_eq_modelSquare (t a b : ℝ) :
    orientedSquare t a b = modelSquare (0, 0) (t : Direction) (a, b) := by
  apply UnitSquare.ext
  · apply Prod.ext <;> simp [orientedSquare, modelSquare, pointInDirection]
  · simp [orientedSquare, modelSquare]
  · simp [orientedSquare, modelSquare]

/-- A chart describes the actual square as a rotated axis-square point set. -/
theorem chart_same_open_model {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    ∀ p, openSquare S p ↔ openSquare (modelSquare o C.phase (C.a, C.signedB)) p := by
  intro p
  obtain ⟨q, rfl⟩ := (frameEquiv o C.phase).surjective p
  rw [frameEquiv_apply]
  have hm := modelSquare_local o C.phase (C.a, C.signedB) q.1 q.2
  simp only [openSquare, hm.1, hm.2]
  exact C.cartesian q.1 q.2

/-- Point-set equality includes the closed boundaries, not only interiors. -/
theorem chart_same_closed_model {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    ∀ p, closedSquare S p ↔ closedSquare (modelSquare o C.phase (C.a, C.signedB)) p :=
  same_open_same_closed S _ (chart_same_open_model C)

theorem chart_same_open_oriented {S : UnitSquare} (C : SquareChart S (0, 0))
    {t : ℝ} (ht : (t : Direction) = C.phase) :
    ∀ p, openSquare S p ↔ openSquare (orientedSquare t C.a C.signedB) p := by
  rw [orientedSquare_eq_modelSquare, ht]
  exact chart_same_open_model C

theorem chart_same_closed_oriented {S : UnitSquare} (C : SquareChart S (0, 0))
    {t : ℝ} (ht : (t : Direction) = C.phase) :
    ∀ p, closedSquare S p ↔ closedSquare (orientedSquare t C.a C.signedB) p :=
  same_open_same_closed S _ (chart_same_open_oriented C ht)

/-- Signed containment at Q0, without strong-core or axial assumptions. -/
lemma chart_signed_containment {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o)
    (hQ : phi (alpha S o) (beta S o) ≤ Q0) :
    ContainedChart C.a |C.signedB| := by
  rw [signedB_abs]
  exact ⟨C.exterior hsort hout, C.nonneg.2, hsort, chart_phi C hQ⟩

/-- Axial selection gives the signed affine marker, with chart reversals retained. -/
theorem chartMarker_affine_of_core {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hc : ContainedChart C.a C.b) (hcore : AvoidsCore C.a C.b) :
    Seven.chartMarker C = C.phase + (((5 / 4) * C.signedB : ℝ) : Direction) := by
  rw [Seven.chartMarker_formula, hc.label_eq_axial hcore]
  congr 1
  rw [← Seven.chartSign_coordinate C]
  congr 1
  ring

end SquaresInCircles.Six.Normalization
