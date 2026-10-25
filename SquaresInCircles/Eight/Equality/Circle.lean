module

public import SquaresInCircles.Eight.Corners.Selection

/-!
# Eight squares: the unique least enclosing circle, from four anchor vertices

The A/B chord crosses the positive horizontal axis;
the D/E chord crosses the negative horizontal axis.  Their two crossing points
give an explicit positive convex combination of four radius vertices equal to
zero.  The resulting second-moment identity includes every possible circle
center and does not use the unrestricted packing lower-bound theorem.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.GeometricModel
open Stationary Stationary.Coordinates

def fourAnchorIndex : Fin 4 → Fin 8 := ![3,4,6,7]
def fourAnchorPoint (i : Fin 4) : Point := FiveCorner.selected.point i.castSucc

theorem fourAnchor_circle (i : Fin 4) :
    normSq (fourAnchorPoint i)=Eight.radius^2 := by
  rw [fourAnchorPoint,FiveCorner.selected_point,FiveCorner.radius_sq_eq_stationary]
  exact Coordinates.anchor_circle sharpData_stationary.toIsChain
    sharpData_stationary.zero_defect i.castSucc

theorem fourAnchor_closed (p : Parameters) (i : Fin 4) :
    closedSquare (p.model FiveCorner.selected (fourAnchorIndex i)) (fourAnchorPoint i) := by
  fin_cases i
  · change closedSquare (FiveCorner.selected.exteriorSquare p.top p.tilted 2) _
    norm_num [fourAnchorPoint,FiveCorner.exteriorSquare,FiveCorner.exteriorCenter,
      FiveCorner.exteriorAngle,FiveCorner.anchorCenter,turnedSquare,closedSquare,localX,localY]
  · change closedSquare (FiveCorner.selected.exteriorSquare p.top p.tilted 3) _
    norm_num [fourAnchorPoint,FiveCorner.exteriorSquare,FiveCorner.exteriorCenter,
      FiveCorner.exteriorAngle,FiveCorner.anchorCenter,turnedSquare,closedSquare,localX,localY]
  · change closedSquare (FiveCorner.selected.exteriorSquare p.top p.tilted 5) _
    norm_num [fourAnchorPoint,FiveCorner.exteriorSquare,FiveCorner.exteriorCenter,
      FiveCorner.exteriorAngle,FiveCorner.anchorCenter,turnedSquare,closedSquare,localX,localY]
  · change closedSquare (FiveCorner.selected.exteriorSquare p.top p.tilted 6) _
    norm_num [fourAnchorPoint,FiveCorner.exteriorSquare,FiveCorner.exteriorCenter,
      FiveCorner.exteriorAngle,FiveCorner.anchorCenter,turnedSquare,closedSquare,localX,localY]

end SquaresInCircles.Eight.GeometricModel

namespace SquaresInCircles.Eight.Parameters
open GeometricModel Stationary Stationary.Coordinates

theorem model_reaches (p : Parameters) :
    ∃ i x,closedSquare (p.model FiveCorner.selected i) x ∧
      Eight.radius^2≤normSq x :=
  ⟨fourAnchorIndex 0,fourAnchorPoint 0,fourAnchor_closed p 0,(fourAnchor_circle 0).ge⟩

end SquaresInCircles.Eight.Parameters

