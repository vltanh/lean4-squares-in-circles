import SquaresInCircles.Six.Normalization.PinPacking

/-!
# Genuine markers in the final signed-coordinate model

The labelled real coordinates are represented by actual SquareCharts, including
transverse reversal. After Lemma B, their genuine markers equal the affine
formula. Strict pairwise and cyclic marker gaps are consequently rederived for
the labelled model rather than assumed to survive an unexplained relabeling.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

lemma oriented_frame_centerX (t a b : ℝ) :
    frameX (orientedSquare t a b) (sub (orientedSquare t a b).center (0,0)) = a := by
  dsimp [frameX,orientedSquare,sub]
  linear_combination a*(Real.sin_sq_add_cos_sq t)

lemma oriented_frame_centerY (t a b : ℝ) :
    frameY (orientedSquare t a b) (sub (orientedSquare t a b).center (0,0)) = b := by
  dsimp [frameY,orientedSquare,sub]
  linear_combination b*(Real.sin_sq_add_cos_sq t)

/-- The signed parametrization supplies exactly the repository's chart structure. -/
def orientedChart (t a b : ℝ) (ha : 0 ≤ a) : SquareChart (orientedSquare t a b) (0,0) := by
  classical
  have hframe : ChartCondition (orientedSquare t a b) (0,0) (t:Direction) false a b := by
    simpa only [oriented_frame_centerX,oriented_frame_centerY] using
      frame_chart (orientedSquare t a b) (0,0) (θ := t) rfl rfl
  refine {
    a := a, b := |b|, phase := (t:Direction), reversed := decide (b<0),
    coordinates := Or.inl ⟨?_,?_⟩, shifted_membership := ?_ }
  · simp only [orientedSquare_alpha,abs_of_nonneg ha]
  · exact (orientedSquare_beta t a b).symm
  · by_cases hb : b<0
    · simpa [hb,abs_of_neg hb] using hframe.reflect
    · simpa [hb,abs_of_nonneg (le_of_not_gt hb)] using hframe

@[simp] lemma orientedChart_a (t a b : ℝ) (ha : 0 ≤ a) : (orientedChart t a b ha).a=a := rfl
@[simp] lemma orientedChart_b (t a b : ℝ) (ha : 0 ≤ a) : (orientedChart t a b ha).b=|b| := rfl
@[simp] lemma orientedChart_phase (t a b : ℝ) (ha : 0 ≤ a) :
    (orientedChart t a b ha).phase=(t:Direction) := rfl

lemma orientedChart_signedB (t a b : ℝ) (ha : 0 ≤ a) : (orientedChart t a b ha).signedB=b := by
  by_cases hb : b<0
  · simp [SquareChart.signedB,orientedChart,hb,abs_of_neg hb]
  · simp [SquareChart.signedB,orientedChart,hb,abs_of_nonneg (le_of_not_gt hb)]

namespace PinPacking
variable {R : ℝ} (P : PinPacking R)

def actualChart (i : Fin 5) :
    SquareChart (orientedSquare (P.phase i) (P.radial i) (P.transverse i)) (0,0) :=
  orientedChart (P.phase i) (P.radial i) (P.transverse i)
    (by linarith [(P.contained i).half_le])

def affineMarker (i : Fin 5) : Direction := (P.phase i+(5/4)*P.transverse i : ℝ)

lemma actualChart_marker (i : Fin 5) : Seven.chartMarker (P.actualChart i)=P.affineMarker i := by
  have hh := chartMarker_affine_of_core (P.actualChart i) (P.contained i) (P.avoidsCore i)
  have hs : (P.actualChart i).signedB = P.transverse i := orientedChart_signedB _ _ _ _
  have hp : (P.actualChart i).phase = (P.phase i : Direction) := rfl
  rw [hs, hp] at hh
  rw [hh, affineMarker, Real.Angle.coe_add]

lemma marker_separation (i j : Fin 5) (hij : i≠j) :
    Real.pi/3 < dist (P.affineMarker i) (P.affineMarker j) := by
  rw [← P.actualChart_marker i,← P.actualChart_marker j]
  exact strict_marker_separation (P.actualChart i) (P.actualChart j)
    (P.contained i).seven_admissible (P.contained j).seven_admissible
    (P.contained i).containment (P.contained j).containment (P.exterior_disjoint i j hij)

/-- N7 for the actual affine markers, with no extra marker hypotheses. -/
theorem marker_gaps :
    ∃ (σ : Equiv.Perm (Fin 5)) (p : Fin 5 → ℝ),
      (∀ i, (p i:Direction)=P.affineMarker (σ i)) ∧ Monotone p ∧
      (∀ i, Real.pi/3 < successiveGaps p i ∧ successiveGaps p i < 2*Real.pi/3) ∧
      (∑ i, successiveGaps p i)=2*Real.pi :=
  five_marker_gaps P.affineMarker P.marker_separation

end PinPacking
end SquaresInCircles.Six.Normalization
