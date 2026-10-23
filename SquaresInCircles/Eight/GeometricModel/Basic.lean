module

public import SquaresInCircles.StatementEightGeometric
public import SquaresInCircles.Common.Basic

/-!
# Elementary identities for the geometric model

Uncompiled source draft. This file re-exports the pure statement layer and
relates its projections and actual angles to the repository's Euclidean
point operations. It contains no sharp-radius or packing-classification input.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel

@[simp] theorem projection_eq_dot (n p : Point) : projection n p = dot n p := rfl

@[simp] theorem e_unit (t : ℝ) : normSq (e t) = 1 := by
  simpa [normSq, e, add_comm] using Real.sin_sq_add_cos_sq t

@[simp] theorem f_unit (t : ℝ) : normSq (f t) = 1 := by
  simpa [normSq, f] using Real.sin_sq_add_cos_sq t

@[simp] theorem e_dot_f (t : ℝ) : dot (e t) (f t) = 0 := by
  dsimp [e, f, dot]
  ring

theorem projection_frame_norm (p : Point) (t : ℝ) :
    projection (e t) p ^ 2 + projection (f t) p ^ 2 = normSq p := by
  dsimp [projection, e, f, normSq]
  linear_combination (p.1 ^ 2 + p.2 ^ 2) * Real.sin_sq_add_cos_sq t

@[simp] theorem square_zero (p : Point) : square p 0 = axisSquare p := by
  simp [square, axisSquare]

theorem localX_square (p x : Point) (t : ℝ) :
    localX (square p t) x = projection (e t) (sub x p) := rfl

theorem localY_square (p x : Point) (t : ℝ) :
    localY (square p t) x = projection (f t) (sub x p) := rfl

theorem localX_square_origin (p : Point) (t : ℝ) :
    localX (square p t) (0, 0) = -projection (e t) p := by
  dsimp [localX, square, projection, e]
  ring

theorem localY_square_origin (p : Point) (t : ℝ) :
    localY (square p t) (0, 0) = -projection (f t) p := by
  dsimp [localY, square, projection, f]
  ring

theorem origin_interior_iff (p : Point) (t : ℝ) :
    openSquare (square p t) (0, 0) ↔
      |projection (e t) p| < 1 / 2 ∧ |projection (f t) p| < 1 / 2 := by
  simp only [openSquare, localX_square_origin, localY_square_origin, abs_neg]

theorem containmentCost_eq_phi (p : Point) (t : ℝ) :
    containmentCost p t = phi (alpha (square p t) (0, 0))
      (beta (square p t) (0, 0)) := by
  simp [containmentCost, phi, alpha, beta, localX_square_origin,
    localY_square_origin, abs_neg]

theorem containmentCost_nonneg (p : Point) (t : ℝ) : 0 ≤ containmentCost p t := by
  unfold containmentCost
  positivity

/-- Origin-interiority alone bounds every central vertex strictly below
squared norm two. The sharp model later supplies its structural bound 9/4. -/
theorem central_cost_lt_two {p : Point} {t : ℝ}
    (h : openSquare (square p t) (0, 0)) : containmentCost p t < 2 := by
  obtain ⟨hx, hy⟩ := (origin_interior_iff p t).mp h
  have hxp := abs_nonneg (projection (e t) p)
  have hyp := abs_nonneg (projection (f t) p)
  unfold containmentCost
  nlinarith

theorem projection_e_quarter_turn (p : Point) (t : ℝ) :
    projection (e (t + Real.pi / 2)) p = projection (f t) p := by
  simp [projection, e, f, Real.cos_add, Real.sin_add]

theorem projection_f_quarter_turn (p : Point) (t : ℝ) :
    projection (f (t + Real.pi / 2)) p = -projection (e t) p := by
  simp [projection, e, f, Real.cos_add, Real.sin_add] <;> ring

theorem openSquare_quarter_turn (p x : Point) (t : ℝ) :
    openSquare (square p (t + Real.pi / 2)) x ↔ openSquare (square p t) x := by
  simp only [openSquare, localX_square, localY_square, projection_e_quarter_turn,
    projection_f_quarter_turn, abs_neg, and_comm]

theorem closedSquare_quarter_turn (p x : Point) (t : ℝ) :
    closedSquare (square p (t + Real.pi / 2)) x ↔ closedSquare (square p t) x := by
  simp only [closedSquare, localX_square, localY_square, projection_e_quarter_turn,
    projection_f_quarter_turn, abs_neg, and_comm]

theorem containmentCost_quarter_turn (p : Point) (t : ℝ) :
    containmentCost p (t + Real.pi / 2) = containmentCost p t := by
  simp only [containmentCost, projection_e_quarter_turn, projection_f_quarter_turn,
    abs_neg, add_comm]

namespace FiveCorner

theorem fits_mono {d : FiveCorner} {R S : ℝ} (h : d.fits R) (hrs : R ≤ S) :
    d.fits S := by
  refine ⟨h.1.trans hrs, fun i => (h.2 i).trans ?_⟩
  exact pow_le_pow_left₀ h.1 hrs 2

theorem feasibleRadii_nonneg {R : ℝ} (h : R ∈ feasibleRadii) : 0 ≤ R := by
  obtain ⟨d, hd, hR⟩ := h
  exact hR.1

theorem feasibleRadii_bddBelow : BddBelow feasibleRadii :=
  ⟨0, fun _ h => feasibleRadii_nonneg h⟩

/-- The width-three corner span gives an intrinsic radius bound. -/
theorem three_halves_le {d : FiveCorner} {R : ℝ}
    (hd : d.spans) (hR : d.fits R) : 3 / 2 ≤ R := by
  have hB := hR.2 1
  have hD := hR.2 2
  have hspan := hd.2.2.2.1
  have hBx : (d.point 1).1 ≤ R := by
    have hnonneg := sq_nonneg (d.point 1).2
    dsimp [normSq] at hB
    nlinarith [hR.1]
  have hDx : -R ≤ (d.point 2).1 := by
    have hnonneg := sq_nonneg (d.point 2).2
    dsimp [normSq] at hD
    nlinarith [hR.1]
  linarith

theorem nine_quarters_le_sq {d : FiveCorner} {R : ℝ}
    (hd : d.spans) (hR : d.fits R) : 9 / 4 ≤ R ^ 2 := by
  have h := three_halves_le hd hR
  nlinarith

end FiveCorner
end SquaresInCircles.Eight.GeometricModel
