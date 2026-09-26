import SquaresInCircles.Common.Charts

/-!
# Cartesian access to the square charts

Points in a rotated frame at the disk centre, and Cartesian membership
recovered from the all-radius chart identity.
-/
noncomputable section
namespace SquaresInCircles

lemma pointInDirection_polar (o : Point) (phase : Direction) (r t : ℝ) :
    pointInDirection o phase (r*Real.cos t) (r*Real.sin t) =
      circlePoint o r (phase+(t:Direction)) := by
  apply Prod.ext <;>
    simp only [pointInDirection,circlePoint,Real.Angle.cos_add,Real.Angle.sin_add,
      Real.Angle.cos_coe,Real.Angle.sin_coe] <;> ring

lemma pointInDirection_norm (o : Point) (phase : Direction) (x y : ℝ) :
    normSq (sub (pointInDirection o phase x y) o)=x^2+y^2 := by
  simp only [normSq,sub,pointInDirection]
  linear_combination (x^2+y^2)*Real.Angle.cos_sq_add_sin_sq phase

/-- Polar coordinates, from the polar form of the complex number `x + iy`. -/
lemma plane_polar (x y : ℝ) :
    ∃ r t : ℝ, r*Real.cos t=x ∧ r*Real.sin t=y :=
  ⟨_,_,Complex.norm_mul_cos_arg ⟨x,y⟩,Complex.norm_mul_sin_arg ⟨x,y⟩⟩

/-- Reversal of a chart changes only the sign of its transverse center coordinate. -/
def SquareChart.signedB {S : UnitSquare} {o : Point} (C : SquareChart S o) : ℝ :=
  if C.reversed then -C.b else C.b

lemma SquareChart.abs_signedB {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    |C.signedB|=C.b := by
  unfold SquareChart.signedB
  split_ifs <;> simp only [abs_neg,abs_of_nonneg C.nonneg.2]

/-- Without the reversal, a chart holds at `(a, signedB)`. -/
lemma SquareChart.unreversed {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    ChartCondition S o C.phase false C.a C.signedB := by
  unfold SquareChart.signedB
  cases h : C.reversed
  · simpa [h] using C.shifted_membership
  · simpa [h] using C.shifted_membership.reflect

lemma SquareChart.cartesian {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (x y : ℝ) :
    openSquare S (pointInDirection o C.phase x y) ↔
      |x-C.a| < 1/2 ∧ |y-C.signedB| < 1/2 := by
  obtain ⟨r,t,rfl,rfl⟩ := plane_polar x y
  rw [pointInDirection_polar]
  simpa [sub,scale,chartAngle] using C.unreversed r t 0

lemma pointInDirection_transition (o : Point) (φ ψ : Direction) (x y : ℝ) :
    pointInDirection o φ x y = pointInDirection o ψ
      ((ψ-φ).cos*x+(ψ-φ).sin*y)
      (-(ψ-φ).sin*x+(ψ-φ).cos*y) := by
  obtain ⟨δ,rfl⟩ : ∃ δ, φ=ψ-δ := ⟨ψ-φ,by abel⟩
  rw [sub_sub_cancel]
  simp only [pointInDirection,sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,
    Real.Angle.cos_neg,Real.Angle.sin_neg]
  apply Prod.ext <;> ring

end SquaresInCircles
