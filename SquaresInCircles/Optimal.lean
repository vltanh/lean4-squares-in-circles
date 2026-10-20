module

public import SquaresInCircles.StatementEight
public import SquaresInCircles.StatementEightGeometric

/-!
# The pure public radius and model registries, through eight squares

The elementary square definitions remain in Geometry. The eight-square
entry uses the five-corner geometric minimum and actual-angle equality
family in StatementEightGeometric. No case proof is imported here. The
older stationary statement remains available for compatibility; downstream
geometric modules prove the exact correspondence between the two models.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles

/-- The optimal radius for `1 ≤ n ≤ 8`. Values outside this proved range
are placeholders and carry no optimality claim. -/
def optimalRadius : ℕ → ℝ
  | 1 => One.radius
  | 2 => Two.radius
  | 3 => Three.radius
  | 4 => Four.radius
  | 5 => Five.radius
  | 6 => Six.radius
  | 7 => Seven.radius
  | 8 => Eight.GeometricModel.FiveCorner.radius
  | _ => 0

/-- All normalized optimum models. At eight squares the two exterior
sliders and the central square contribute five real parameters; both
orientations are included because `Congruent` uses a positively oriented
frame. Values outside `1 ≤ n ≤ 8` are empty placeholders. -/
def optimalPackings : (n : ℕ) → Set (Fin n → UnitSquare)
  | 1 => {One.model}
  | 2 => {Two.model}
  | 3 => {Three.model}
  | 4 => {Four.model}
  | 5 => {Five.model}
  | 6 => {Six.model}
  | 7 => Set.range Seven.columnModel
  | 8 => Eight.GeometricModel.models
  | _ => ∅

end SquaresInCircles
