module

public import SquaresInCircles.Common.Basic

/-!
# Eight squares: the geometric model: frames, projections and the admissible family

The statement (`Geometry.lean`) gives the eight-square optimum by five corners
and a free central square. This file adds what the proof measures with: the
frame `e t`, `f t` of a turned square and projections onto it, the squared
distance of a square's farthest vertex from the origin, the separating-axis
margin of two squares, and the admissible parameters, whose models are the
optimal packings with the central square around the disk centre.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel

/-- The first axis of the frame turned by `t`. -/
def e (t : ℝ) : Point := (Real.cos t, Real.sin t)
/-- The second axis of the frame turned by `t`. -/
def f (t : ℝ) : Point := (-Real.sin t, Real.cos t)

/-- The projection of `p` on the direction `n`. -/
def projection (n p : Point) : ℝ := n.1 * p.1 + n.2 * p.2

/-- The squared distance from the origin of the farthest vertex of the unit
square centred at `p` and turned by `t`. -/
def containmentCost (p : Point) (t : ℝ) : ℝ :=
  (|projection (e t) p| + 1 / 2) ^ 2 + (|projection (f t) p| + 1 / 2) ^ 2

/-- Half the sum of the widths of two squares turned by `a` and `b`, along any
axis of either. -/
def separationWidth (a b : ℝ) : ℝ :=
  (1 + |Real.cos (a - b)| + |Real.sin (a - b)|) / 2

/-- How far an axis of one of two squares, turned by `a` and `b` with centres
`d` apart, separates them; they do not overlap when it is nonnegative. -/
def separationMargin (a b : ℝ) (d : Point) : ℝ :=
  max (max |projection (e a) d| |projection (f a) d|)
      (max |projection (e b) d| |projection (f b) d|) - separationWidth a b

/-- The squared radius of the two-height chain of upper chord width three. -/
def twoHeightRadiusSq (u v : ℝ) : ℝ :=
  ((9 + (u - v) ^ 2) * (9 + (4 - u - v) ^ 2)) / 36

end SquaresInCircles.Eight.GeometricModel

namespace SquaresInCircles.Eight.FiveCorner
open GeometricModel

/-- The centres of the seven squares of the ring, `H`, `G`, `A`, `B`, `T`, `D`,
`E`, with `T` at height `z` and `G` at offset `η`. -/
def exteriorCenter (d : FiveCorner) (z η : ℝ) : Fin 7 → Point :=
  ![d.anchorCenter 4, d.tiltedCenter η, d.anchorCenter 0, d.anchorCenter 1,
    d.topCenter z, d.anchorCenter 2, d.anchorCenter 3]

/-- The turns of the seven squares of the ring. -/
def exteriorAngle (d : FiveCorner) : Fin 7 → ℝ :=
  ![d.angle, d.angle, 0, 0, 0, 0, 0]

/-- The seven squares of the ring. -/
def exteriorSquare (d : FiveCorner) (z η : ℝ) (i : Fin 7) : UnitSquare :=
  turnedSquare (d.exteriorCenter z η i) (d.exteriorAngle i)

end SquaresInCircles.Eight.FiveCorner

namespace SquaresInCircles.Eight.Parameters
open GeometricModel

/-- The central square. -/
def centralSquare (p : Parameters) : UnitSquare := turnedSquare p.center p.angle

/-- The squares of `p` about the corners `d`, each square of the ring by its
turn: the central square, then `H`, `G`, `A`, `B`, `T`, `D`, `E`. -/
def model (d : FiveCorner) (p : Parameters) : Fin 8 → UnitSquare :=
  Fin.cons p.centralSquare (d.exteriorSquare p.top p.tilted)

/-- A turn in `[-π/4, π/4)`: every square has exactly one. -/
def AngleRepresentative (θ : ℝ) : Prop :=
  -Real.pi / 4 ≤ θ ∧ θ < Real.pi / 4

/-- The admissible parameters: `T` and `G` in the disk, `T` above and `G` below
the axis, the central square around the disk centre and separated from each
square of the ring. -/
structure Admissible (d : FiveCorner) (p : Parameters) : Prop where
  angle_mem : AngleRepresentative p.angle
  top_contained : containmentCost (d.topCenter p.top) 0 ≤ radius ^ 2
  tilted_contained : containmentCost (d.tiltedCenter p.tilted) d.angle ≤ radius ^ 2
  top_above_axis : 1 / 2 ≤ p.top
  tilted_below_axis :
    (d.tiltedCenter p.tilted).2 + (|Real.cos d.angle| + |Real.sin d.angle|) / 2 ≤ 0
  central_first : |projection (GeometricModel.e p.angle) p.center| < 1 / 2
  central_second : |projection (GeometricModel.f p.angle) p.center| < 1 / 2
  central_separated : ∀ i : Fin 7,
    0 ≤ separationMargin p.angle (d.exteriorAngle i)
      (sub (d.exteriorCenter p.top p.tilted i) p.center)

end SquaresInCircles.Eight.Parameters

namespace SquaresInCircles.Eight.GeometricModel

/-- The model of `p`, or its reflection in the diagonal. -/
def reflectedModel (reflected : Bool) (p : Parameters) : Fin 8 → UnitSquare :=
  if reflected then fun i => reflectSquare (p.model FiveCorner.selected i)
  else p.model FiveCorner.selected

/-- The models of admissible parameters and their reflections. -/
def admissibleModels : Set (Fin 8 → UnitSquare) :=
  {M | ∃ reflected : Bool, ∃ p : Parameters,
    p.Admissible FiveCorner.selected ∧ M = reflectedModel reflected p}

/-- The projection on the first axis of the frame turned by `t`, in coordinates. -/
theorem projection_e_sub (t : ℝ) (p q : Point) :
    projection (e t) (sub p q) = Real.cos t * (p.1 - q.1) + Real.sin t * (p.2 - q.2) := rfl

/-- The projection on the second axis of the frame turned by `t`, in coordinates. -/
theorem projection_f_sub (t : ℝ) (p q : Point) :
    projection (f t) (sub p q) = -Real.sin t * (p.1 - q.1) + Real.cos t * (p.2 - q.2) := rfl

@[simp] theorem projection_eq_dot (n p : Point) : projection n p = dot n p := rfl

@[simp] theorem e_unit (t : ℝ) : normSq (e t) = 1 := by
  simpa [normSq, e, add_comm] using Real.sin_sq_add_cos_sq t

@[simp] theorem f_unit (t : ℝ) : normSq (f t) = 1 := by
  simpa [normSq, f] using Real.sin_sq_add_cos_sq t

@[simp] theorem e_dot_f (t : ℝ) : dot (e t) (f t) = 0 := by
  dsimp [e, f, dot]
  ring

@[simp] theorem square_zero (p : Point) : turnedSquare p 0 = axisSquare p := by
  simp [turnedSquare, axisSquare]

theorem localX_square_origin (p : Point) (t : ℝ) :
    localX (turnedSquare p t) (0, 0) = -projection (e t) p := by
  dsimp [localX, turnedSquare, projection, dot, e]
  ring

theorem localY_square_origin (p : Point) (t : ℝ) :
    localY (turnedSquare p t) (0, 0) = -projection (f t) p := by
  dsimp [localY, turnedSquare, projection, dot, f]
  ring

theorem origin_interior_iff (p : Point) (t : ℝ) :
    openSquare (turnedSquare p t) (0, 0) ↔
      |projection (e t) p| < 1 / 2 ∧ |projection (f t) p| < 1 / 2 := by
  simp only [openSquare, localX_square_origin, localY_square_origin, abs_neg]

theorem containmentCost_eq_phi (p : Point) (t : ℝ) :
    containmentCost p t = phi (alpha (turnedSquare p t) (0, 0))
      (beta (turnedSquare p t) (0, 0)) := by
  simp [containmentCost, phi, alpha, beta, localX_square_origin,
    localY_square_origin, abs_neg]

end SquaresInCircles.Eight.GeometricModel

namespace SquaresInCircles.Eight.FiveCorner
open GeometricModel

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

end SquaresInCircles.Eight.FiveCorner

