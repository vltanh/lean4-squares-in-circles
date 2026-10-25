module

public import SquaresInCircles.Eight.GeometricModel.Basic
public import SquaresInCircles.Eight.SeparatingAxis

/-!
# Containment and separating-axis semantics of the geometric model

Uncompiled source draft. The proofs connect the single containment and
separation formulas to the primitive `closedSquare` and `openSquare`
predicates. Every separating inequality is weak, including simultaneous
axis ties. No stationary or global eight-square theorem is imported.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel

theorem square_contained_iff (p : Point) (t R : ℝ) :
    (∀ x, closedSquare (turnedSquare p t) x → inDisk (0, 0) R x) ↔
      containmentCost p t ≤ R ^ 2 := by
  rw [containmentCost_eq_phi]
  exact ⟨phi_le_of_contained _ _ _, fun h _ hx => inDisk_of_phi_le h hx⟩

theorem square_sqContained_iff (p : Point) (t q : ℝ) :
    SqContained q (turnedSquare p t) ↔ containmentCost p t ≤ q := by
  rw [containmentCost_eq_phi]
  rfl

theorem square_relativeC (p q : Point) (a b : ℝ) :
    relativeC (turnedSquare p a) (turnedSquare q b) = Real.cos (a - b) := by
  dsimp [relativeC, turnedSquare]
  exact (Real.cos_sub a b).symm

theorem square_relativeS (p q : Point) (a b : ℝ) :
    relativeS (turnedSquare p a) (turnedSquare q b) = -Real.sin (a - b) := by
  dsimp [relativeS, turnedSquare]
  rw [Real.sin_sub]
  ring

theorem square_threshold (p q : Point) (a b : ℝ) :
    SAT.threshold (turnedSquare p a) (turnedSquare q b) = separationWidth a b := by
  simp [SAT.threshold, separationWidth, square_relativeC, square_relativeS]

/-- The general unsigned maximum form of the existing four-axis theorem. -/
theorem disjoint_iff_max (K L : UnitSquare) :
    (∀ x, ¬ (openSquare K x ∧ openSquare L x)) ↔
      SAT.threshold K L ≤
        max (max |frameX K (sub L.center K.center)|
                 |frameY K (sub L.center K.center)|)
            (max |frameX L (sub L.center K.center)|
                 |frameY L (sub L.center K.center)|) := by
  constructor
  · intro h
    simpa only [le_max_iff, or_assoc] using SAT.separating_axes K L h
  · intro h
    simp only [le_max_iff] at h
    rcases h with (h | h) | (h | h)
    · obtain ⟨axis, _, ha⟩ := signed_projection_exists .sourceX K L h
      exact SignedAxis.disjoint ha
    · obtain ⟨axis, _, ha⟩ := signed_projection_exists .sourceY K L h
      exact SignedAxis.disjoint ha
    · obtain ⟨axis, _, ha⟩ := signed_projection_exists .targetX K L h
      exact SignedAxis.disjoint ha
    · obtain ⟨axis, _, ha⟩ := signed_projection_exists .targetY K L h
      exact SignedAxis.disjoint ha

theorem square_disjoint_iff (p q : Point) (a b : ℝ) :
    (∀ x, ¬ (openSquare (turnedSquare p a) x ∧ openSquare (turnedSquare q b) x)) ↔
      0 ≤ separationMargin a b (sub q p) := by
  have h := disjoint_iff_max (turnedSquare p a) (turnedSquare q b)
  rw [square_threshold] at h
  simpa only [separationMargin, sub_nonneg, frameX, frameY, turnedSquare,
    projection, e, f] using h

theorem square_supportWidth (p : Point) (t : ℝ) (n : Point) :
    width (turnedSquare p t) n = supportWidth t n := rfl

theorem separationMargin_reverse (a b : ℝ) (d : Point) :
    separationMargin b a (-d) = separationMargin a b d := by
  have hc : Real.cos (b - a) = Real.cos (a - b) := by
    rw [show b - a = -(a - b) by ring, Real.cos_neg]
  have hs : Real.sin (b - a) = -Real.sin (a - b) := by
    rw [show b - a = -(a - b) by ring, Real.sin_neg]
  have hp (n : Point) : projection n (-d) = -projection n d := by
    dsimp [projection, dot]
    ring
  simp only [separationMargin, separationWidth, hp, hc, hs, abs_neg, max_comm]

theorem reflectSquare_eq_reflectDiagonalSquare (K : UnitSquare) :
    reflectSquare K = reflectDiagonalSquare K := rfl

/-- The selected square's coordinate vectors are the actual trigonometric
frame, so translating its center does not alter either normal. -/
theorem square_frame (p : Point) (t : ℝ) :
    Eight.e (turnedSquare p t) = e t ∧ Eight.f (turnedSquare p t) = f t := ⟨rfl, rfl⟩

/-- The square is unchanged as a geometric set by a quarter turn. -/
theorem square_same_quarter_turn (p : Point) (t : ℝ) :
    SameSquare (turnedSquare p (t + Real.pi / 2)) (turnedSquare p t) :=
  ⟨fun x => openSquare_quarter_turn p x t,
    fun x => closedSquare_quarter_turn p x t⟩

end SquaresInCircles.Eight.GeometricModel
