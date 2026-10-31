module

public import SquaresInCircles.Common.Frames
public import SquaresInCircles.Eight.Bounds.Containing
public import SquaresInCircles.Eight.Corners.GeometricStationaryExistence
public import SquaresInCircles.Eight.Equality.Angles
public import SquaresInCircles.Eight.Boundary.SeparatingAxis
public import SquaresInCircles.Eight.ExactFamily.Models

/-!
# Eight squares: equivalence of the two descriptions of the family

The family of the statement (`Parameters.Admissible FiveCorner.selected`) asks of the central
square that it contain the disk centre and be separated from the ring, of T that it lie above the
axis and of G that it lie below. The family of `ExactFamily/Coordinates.lean`
(`EqualityParameters.Admissible sharpData`) asks instead for the core of radius `1/12`: the
centre of the central square within `5/12` of the origin in its frame, `7/12 ≤ z` for T and
`eta ≤ etaMax` for G. The half-angle coordinate maps the second family into the first
(`ofStationary_admissible`) and the first into the second (`toStationary_admissible`). For the
latter, the model of the statement is a packing in the disk of squared radius `qStar`, proved in
`Equality/Geometry.lean` without the core, so the core theorem `central_core_and_exteriors`
applies to it: the square that holds the core is the central square (`central_core_recovered`),
and points of the sides of T and G give `7/12 ≤ top` and `tilted ≤ etaMax`
(`top_core_rail_recovered`, `tilted_core_rail_recovered`).
-/

section
/-!
## The unique least enclosing circle, from four anchor vertices

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
open ExactFamily ExactFamily.Coordinates

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
open GeometricModel ExactFamily ExactFamily.Coordinates

theorem model_reaches (p : Parameters) :
    ∃ i x,closedSquare (p.model FiveCorner.selected i) x ∧
      Eight.radius^2≤normSq x :=
  ⟨fourAnchorIndex 0,fourAnchorPoint 0,fourAnchor_closed p 0,(fourAnchor_circle 0).ge⟩

end SquaresInCircles.Eight.Parameters
end
end
end

section
/-!
## Containment and separating-axis semantics of the geometric model

The proofs connect the single containment and
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

theorem reflectSquare_eq_reflectDiagonalSquare (K : UnitSquare) :
    reflectSquare K = reflectDiagonalSquare K := rfl

end SquaresInCircles.Eight.GeometricModel
end
end
end

section
/-!
## The models of the family are packings

The model of admissible parameters (`Parameters.Admissible FiveCorner.selected`) is a packing in
the disk of squared radius `radius²` (`model_sqPacking`, `model_packing`). The centres of
`FiveCorner.selected` are those of the stationary configuration `sharpData`
(`selected_anchorCenter`, `selected_exteriorSquare`), so the models of the two families agree
(`ofStationary_model`, `toStationary_model`). The twenty-one pairs of exterior squares are
separated for every `z ≥ 1/2` and every `η` with G below the axis (`wide_exterior_separator`,
`wide_exterior_disjoint`); the seven pairs with the central square are the separation
conditions of the family, and the central square, which contains the disk centre, lies in the
disk since `radius² ≥ 9/4` (`central_containment_automatic`, `radius_sq_ge_nine_quarters`). The
core of radius `1/12` is not used.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.FiveCorner
open GeometricModel ExactFamily ExactFamily.Coordinates

theorem selected_anchorCenter (i : Fin 5) :
    selected.anchorCenter i=sharpData.anchorCenters i := by
  have ht := ExactFamily.FiveCornerGeometry.coordinateAngle_frame sharpData
  fin_cases i <;>
    ext <;>
    simp [anchorCenter,selected_point,selected_angle,Coordinates.anchorPoints,
      Coordinates.anchorCenters,Coordinates.pA,Coordinates.pB,Coordinates.pD,
      Coordinates.pE,Coordinates.pH,Coordinates.inFrame,ht.1,ht.2] <;> ring

theorem selected_topCenter (z : ℝ) : selected.topCenter z=sharpData.pT z := by
  rw [topCenter,selected_anchorCenter]
  ext <;> simp [Coordinates.anchorCenters,Coordinates.pB,Coordinates.pT]
  ring

theorem selected_tiltedCenter (η : ℝ) : selected.tiltedCenter η=sharpData.pG η := by
  have ht := ExactFamily.FiveCornerGeometry.coordinateAngle_frame sharpData
  rw [tiltedCenter,selected_anchorCenter]
  ext <;>
    simp [Coordinates.anchorCenters,Coordinates.pH,Coordinates.pG,
      Coordinates.inFrame,selected_angle,ht.1,ht.2] <;> ring

theorem selected_exteriorCenter (z η : ℝ) (i : Fin 7) :
    selected.exteriorCenter z η i=sharpData.exteriorCenters z η i := by
  fin_cases i <;>
    simp [exteriorCenter,Coordinates.exteriorCenters,selected_anchorCenter,
      selected_topCenter,selected_tiltedCenter,Coordinates.anchorCenters]

private theorem r4_unitSquare_eq {K L : UnitSquare} (h1 : K.center=L.center)
    (h2 : K.cosine=L.cosine) (h3 : K.sine=L.sine) : K=L := by
  cases K; cases L
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem square_selected_angle (p : Point) :
    turnedSquare p selected.angle=sharpData.tiltedSquare p := by
  have ht := ExactFamily.FiveCornerGeometry.coordinateAngle_frame sharpData
  exact r4_unitSquare_eq rfl (by simp [turnedSquare,Coordinates.tiltedSquare,selected_angle,ht.1])
    (by simp [turnedSquare,Coordinates.tiltedSquare,selected_angle,ht.2])

theorem square_zero (p : Point) : turnedSquare p 0=axisSquare p :=
  r4_unitSquare_eq rfl (by simp [turnedSquare,axisSquare]) (by simp [turnedSquare,axisSquare])

theorem selected_exteriorSquare (z η : ℝ) (i : Fin 7) :
    selected.exteriorSquare z η i=sharpData.exteriorSquares z η i := by
  have hsq (p : Point) :
      turnedSquare p (FiveCornerGeometry.coordinateAngle sharpData)=sharpData.tiltedSquare p := by
    rw [← selected_angle]
    exact square_selected_angle p
  rw [exteriorSquare,selected_exteriorCenter]
  fin_cases i <;>
    simp [exteriorAngle,Coordinates.exteriorCenters,Coordinates.exteriorSquares,hsq]

/-- `radius² ≥ 9/4`: the corners of B and D on the circle have abscissas `3` apart. -/
theorem radius_sq_ge_nine_quarters : (9/4:ℝ)≤radius^2 := by
  rw [radius_sq_eq_stationary]
  have hB := sharpData_stationary.second_circle
  have hD := sharpData_stationary.third_circle
  change sharpData.x₂^2+(sharpData.y+2)^2=qStar at hB
  change (sharpData.x₂-3)^2+sharpData.y₃^2=qStar at hD
  nlinarith [sq_nonneg (sharpData.x₂-3/2),sq_nonneg (sharpData.y+2),
    sq_nonneg sharpData.y₃]

end SquaresInCircles.Eight.FiveCorner

namespace SquaresInCircles.Eight.Parameters
open GeometricModel ExactFamily ExactFamily.Coordinates

theorem ofStationary_model (p : EqualityParameters) :
    (ofStationary p).model FiveCorner.selected=p.model sharpData := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ofStationary_centralSquare p
  · simpa [model,ofStationary,EqualityParameters.model,Coordinates.exteriorSquares]
      using FiveCorner.selected_exteriorSquare p.z p.eta j

theorem toStationary_model {p : Parameters} (hp : AngleRepresentative p.angle) :
    p.toStationary.model sharpData=p.model FiveCorner.selected := by
  rw [← ofStationary_model p.toStationary,ofStationary_toStationary hp]

/-- A central square that contains the origin in its interior has containment cost below `2`,
and the radius is at least `3/2`, by the span of B and D; so it lies in the disk. -/
theorem central_containment_automatic {p : Parameters}
    (hx : |projection (GeometricModel.e p.angle) p.center|<1/2)
    (hy : |projection (GeometricModel.f p.angle) p.center|<1/2) :
    containmentCost p.center p.angle<Eight.radius^2 := by
  have ha := abs_nonneg (projection (GeometricModel.e p.angle) p.center)
  have hb := abs_nonneg (projection (GeometricModel.f p.angle) p.center)
  have hcost : containmentCost p.center p.angle<2 := by
    dsimp only [containmentCost]
    nlinarith
  exact hcost.trans_le (by linarith [FiveCorner.radius_sq_ge_nine_quarters])

theorem origin_in_central {p : Parameters}
    (hx : |projection (GeometricModel.e p.angle) p.center|<1/2)
    (hy : |projection (GeometricModel.f p.angle) p.center|<1/2) :
    openSquare p.centralSquare (0,0) := by
  exact (origin_interior_iff p.center p.angle).mpr ⟨hx,hy⟩

end SquaresInCircles.Eight.Parameters

namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily ExactFamily.Coordinates

/-- The twenty-one pairs of exterior squares are separated for `z ≥ 1/2` and G below the axis:
the ten pairs of axis-parallel squares; H–G, H–A, G–A and H–E; G–E; and the six pairs joining H
or G to B, T or D. The bounds `7/12 ≤ z` and `η ≤ etaMax` of the core are not needed. -/
theorem wide_exterior_separator {z η : ℝ} (hz : 1/2≤z)
    (hGtop : sharpData.s*(sharpData.h₁+2)+
      sharpData.c*(sharpData.h₂+1+η)≤0)
    (i j : Fin 7) (hij : i<j) :
    exteriorNormal sharpData i j≠(0,0) ∧
      width (sharpData.exteriorSquares z η i) (exteriorNormal sharpData i j)+
        width (sharpData.exteriorSquares z η j) (exteriorNormal sharpData i j)≤
      dot (exteriorNormal sharpData i j)
        (sub (sharpData.exteriorCenters z η j) (sharpData.exteriorCenters z η i)) :=
  ExactFamily.exterior_separator_wide hz hGtop i j hij

theorem wide_exterior_disjoint {z η : ℝ} (hz : 1/2≤z)
    (hGtop : sharpData.s*(sharpData.h₁+2)+
      sharpData.c*(sharpData.h₂+1+η)≤0) :
    InteriorDisjoint (sharpData.exteriorSquares z η) := by
  have hcen (k : Fin 7) : sharpData.exteriorCenters z η k=
      (sharpData.exteriorSquares z η k).center := by
    fin_cases k <;> rfl
  intro i j hij x hx
  rcases lt_or_gt_of_ne hij with hij | hji
  · obtain ⟨hn,hs⟩ := wide_exterior_separator hz hGtop i j hij
    rw [hcen,hcen] at hs
    exact separated_by_normal hn hs x hx
  · obtain ⟨hn,hs⟩ := wide_exterior_separator hz hGtop j i hji
    rw [hcen,hcen] at hs
    exact separated_by_normal hn hs x ⟨hx.2,hx.1⟩

end SquaresInCircles.Eight.GeometricModel

namespace SquaresInCircles.Eight.Parameters
open GeometricModel ExactFamily ExactFamily.Coordinates

theorem tilted_below_axis_iff (p : Parameters) :
    ((FiveCorner.selected.tiltedCenter p.tilted).2+
      (|Real.cos FiveCorner.selected.angle|+|Real.sin FiveCorner.selected.angle|)/2≤0) ↔
    sharpData.s*(sharpData.h₁+2)+sharpData.c*(sharpData.h₂+1+p.tilted)≤0 := by
  have ht := ExactFamily.FiveCornerGeometry.coordinateAngle_frame sharpData
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  rw [FiveCorner.selected_tiltedCenter,FiveCorner.selected_angle,ht.1,ht.2,
    abs_of_pos hc,abs_of_pos hs]
  dsimp [Coordinates.pG,Coordinates.inFrame]
  constructor <;> intro h <;> linarith

theorem exterior_disjoint {p : Parameters} (hp : p.Admissible FiveCorner.selected) :
    InteriorDisjoint (FiveCorner.selected.exteriorSquare p.top p.tilted) := by
  have hh := wide_exterior_disjoint hp.top_above_axis
    ((tilted_below_axis_iff p).mp hp.tilted_below_axis)
  have hsq : FiveCorner.selected.exteriorSquare p.top p.tilted=
      sharpData.exteriorSquares p.top p.tilted :=
    funext (FiveCorner.selected_exteriorSquare p.top p.tilted)
  rw [hsq]
  exact hh

theorem exterior_contained {p : Parameters} (hp : p.Admissible FiveCorner.selected)
    (i : Fin 7) : SqContained (Eight.radius^2)
      (FiveCorner.selected.exteriorSquare p.top p.tilted i) := by
  have hT := (square_sqContained_iff _ _ _).mpr hp.top_contained
  have hG := (square_sqContained_iff _ _ _).mpr hp.tilted_contained
  have ha := ExactFamily.exterior_contained Eight.sample_admissible
  fin_cases i
  · simpa [FiveCorner.selected_exteriorSquare,Coordinates.exteriorSquares,
      FiveCorner.radius_sq_eq_stationary] using ha 0
  · simpa [FiveCorner.exteriorSquare,FiveCorner.exteriorCenter,FiveCorner.exteriorAngle]
      using hG
  · simpa [FiveCorner.selected_exteriorSquare,Coordinates.exteriorSquares,
      FiveCorner.radius_sq_eq_stationary] using ha 2
  · simpa [FiveCorner.selected_exteriorSquare,Coordinates.exteriorSquares,
      FiveCorner.radius_sq_eq_stationary] using ha 3
  · simpa [FiveCorner.exteriorSquare,FiveCorner.exteriorCenter,FiveCorner.exteriorAngle]
      using hT
  · simpa [FiveCorner.selected_exteriorSquare,Coordinates.exteriorSquares,
      FiveCorner.radius_sq_eq_stationary] using ha 5
  · simpa [FiveCorner.selected_exteriorSquare,Coordinates.exteriorSquares,
      FiveCorner.radius_sq_eq_stationary] using ha 6

/-- The model of admissible parameters is a packing in the disk of squared radius `radius²`:
containment and all twenty-eight pairs, without the core of radius `1/12`. -/
theorem model_sqPacking {p : Parameters} (hp : p.Admissible FiveCorner.selected) :
    SqPacking (p.model FiveCorner.selected) (0,0) (Eight.radius^2) := by
  have hext := exterior_disjoint hp
  have hsep (j : Fin 7) : ∀ x,
      ¬(openSquare p.centralSquare x ∧
        openSquare (FiveCorner.selected.exteriorSquare p.top p.tilted j) x) := by
    exact (square_disjoint_iff _ _ _ _).mpr (hp.central_separated j)
  refine ⟨sq_nonneg _,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro x hx
      have hc : SqContained (Eight.radius^2) p.centralSquare :=
        (square_sqContained_iff _ _ _).mpr
          (central_containment_automatic hp.central_first hp.central_second).le
      simpa [sub] using
        ((SqContained.iff_points (sq_nonneg _) _).mp hc) x hx
    · intro x hx
      simpa [sub] using
        ((SqContained.iff_points (sq_nonneg _) _).mp (exterior_contained hp j)) x hx
  · intro i
    refine Fin.cases ?_ (fun a => ?_) i
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact (hij rfl).elim
      · intro hij x hx
        exact hsep b x hx
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij x hx
        exact hsep a x ⟨hx.2,hx.1⟩
      · intro hij x hx
        exact hext a b (by simpa using hij) x hx

theorem model_packing {p : Parameters} (hp : p.Admissible FiveCorner.selected) :
    Packing (p.model FiveCorner.selected) (0,0) Eight.radius := by
  have hs := model_sqPacking hp
  refine ⟨?_,hs.2⟩
  rw [FiveCorner.radius_eq_stationary]
  positivity

end SquaresInCircles.Eight.Parameters
end
end
end

section
@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Parameters
open GeometricModel ExactFamily ExactFamily.Coordinates

theorem ofStationary_admissible {p : EqualityParameters} (hp : p.Admissible sharpData) :
    (ofStationary p).Admissible FiveCorner.selected := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  have hframe := halfToAngle_frame p.w
  have hpack : SqPacking ((ofStationary p).model FiveCorner.selected) (0,0) qStar := by
    rw [ofStationary_model]
    exact ExactFamily.model_sqPacking hp
  have hT := ExactFamily.exterior_contained hp 4
  have hG := ExactFamily.exterior_contained hp 1
  have hη : sharpData.h₂+p.eta≤ -13/12 := by
    have h := hp.tilted_upper
    dsimp [Coordinates.etaMax] at h
    linarith
  have hηc := mul_le_mul_of_nonneg_left hη hc.le
  have htop := sharp_exterior_bounds.2.2.2.2.2.2.2.2.2.2.1
  refine {
    angle_mem := halfToAngle_mem ⟨hp.frame_lower,hp.frame_upper⟩
    top_contained := ?_
    tilted_contained := ?_
    top_above_axis := by dsimp [ofStationary]; linarith [hp.top_lower]
    tilted_below_axis := ?_
    central_first := ?_
    central_second := ?_
    central_separated := ?_ }
  · apply (square_sqContained_iff _ _ _).mp
    simpa [ofStationary,FiveCorner.selected_topCenter,FiveCorner.square_zero,
      FiveCorner.radius_sq_eq_stationary,Coordinates.exteriorSquares] using hT
  · have hsq := FiveCorner.square_selected_angle (sharpData.pG p.eta)
    rw [FiveCorner.selected_angle] at hsq
    apply (square_sqContained_iff _ _ _).mp
    simpa [ofStationary,FiveCorner.selected_tiltedCenter,hsq,
      FiveCorner.radius_sq_eq_stationary,Coordinates.exteriorSquares] using hG
  · apply (tilted_below_axis_iff _).mpr
    dsimp [ofStationary]
    linarith
  · have hh : |p.C*p.x+p.S*p.y|<1/2 := by linarith [hp.core_first]
    simpa [ofStationary,projection,GeometricModel.e,EqualityParameters.center,EqualityParameters.C,
      EqualityParameters.S,hframe.1,hframe.2] using hh
  · have hh : |-p.S*p.x+p.C*p.y|<1/2 := by linarith [hp.core_second]
    simpa [ofStationary,projection,GeometricModel.f,EqualityParameters.center,EqualityParameters.C,
      EqualityParameters.S,hframe.1,hframe.2] using hh
  · intro i
    apply (square_disjoint_iff _ _ _ _).mp
    simpa only [model,Fin.cons_zero,Fin.cons_succ,centralSquare,
      FiveCorner.exteriorSquare] using
      hpack.2.2 0 i.succ (Fin.succ_ne_zero i).symm

/-- In the model of admissible parameters the central square holds the core, and the other
squares avoid it strictly: the square of the core theorem is the central one, which contains the
origin in its interior. -/
theorem central_core_recovered {p : Parameters}
    (hp : p.Admissible FiveCorner.selected) :
    ContainsCore p.toStationary.centralSquare ∧
      ∀ j : Fin 8, j≠0 → StrictCoreAvoiding (p.toStationary.model sharpData j) := by
  have hpack : SqPacking (p.toStationary.model sharpData) (0,0) qStar := by
    rw [toStationary_model hp.angle_mem,← FiveCorner.radius_sq_eq_stationary]
    exact model_sqPacking hp
  obtain ⟨i,hi,hext⟩ := central_core_and_exteriors hpack
    (by simpa [Q0] using qStar_limits.2.2.le)
  have h0 : openSquare (p.toStationary.model sharpData 0) (0,0) := by
    change openSquare p.toStationary.centralSquare (0,0)
    rw [toStationary_centralSquare hp.angle_mem]
    exact origin_in_central hp.central_first hp.central_second
  have hiz : i=0 := central_square_unique hpack.2.2
    (hi (0,0) (by norm_num [normSq,coreRadius])) h0
  subst i
  exact ⟨hi,fun j hj => hext j hj.symm⟩

/-- `7/12 ≤ top`: the point `(0, top - 1/2)` of the lower side of T avoids the core. -/
theorem top_core_rail_recovered {p : Parameters}
    (hp : p.Admissible FiveCorner.selected) : 7/12≤p.top := by
  have hclear := (central_core_recovered hp).2 5 (by decide)
  obtain ⟨hAB,hABu,hTx,hTxu,hGx,hGxu,hED,hBbot,hDbot,hHtop,hGtop,hGleft⟩ :=
    sharp_exterior_bounds
  have hclosed : closedSquare (p.toStationary.model sharpData 5) (0,p.top-1/2) := by
    change closedSquare (axisSquare (sharpData.pT p.top)) (0,p.top-1/2)
    have hx : localX (axisSquare (sharpData.pT p.top)) (0,p.top-1/2)=
        -(sharpData.x₂-3/2) := by
      dsimp [localX,axisSquare,Coordinates.pT]
      ring
    have hy : localY (axisSquare (sharpData.pT p.top)) (0,p.top-1/2)=
        -(1/2:ℝ) := by
      dsimp [localY,axisSquare,Coordinates.pT]
      ring
    rw [closedSquare,hx,hy,abs_neg,abs_of_pos hTx]
    exact ⟨hTxu.le,by norm_num⟩
  have hh := hclear (0,p.top-1/2) hclosed
  dsimp [coreRadius,normSq] at hh
  have hz := hp.top_above_axis
  nlinarith

/-- `tilted ≤ etaMax`: a point of the upper side of G avoids the core; the condition that G lies
below the axis fixes the sign of its coordinate in the frame of G. -/
theorem tilted_core_rail_recovered {p : Parameters}
    (hp : p.Admissible FiveCorner.selected) : p.tilted≤ sharpData.etaMax := by
  have hclear := (central_core_recovered hp).2 2 (by decide)
  have htop := (tilted_below_axis_iff p).mp hp.tilted_below_axis
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,
    hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  let b := sharpData.h₂+1+p.tilted
  have hb : b≤0 := by
    by_contra! h
    have h₁ := mul_pos (show 0<sharpData.c by linarith) h
    have h₂ := mul_pos (show 0<sharpData.s by linarith)
      (show 0<sharpData.h₁+2 by linarith)
    dsimp [b] at h₁
    linarith
  have hx : localX (sharpData.tiltedSquare (sharpData.pG p.tilted))
      (sharpData.inFrame 0 b)= -(sharpData.h₁+3/2) := by
    dsimp [localX,Coordinates.tiltedSquare,Coordinates.pG,Coordinates.inFrame,b]
    linear_combination -(sharpData.h₁+3/2)*sharpData.unit
  have hy : localY (sharpData.tiltedSquare (sharpData.pG p.tilted))
      (sharpData.inFrame 0 b)=1/2 := by
    dsimp [localY,Coordinates.tiltedSquare,Coordinates.pG,Coordinates.inFrame,b]
    linear_combination (1/2:ℝ)*sharpData.unit
  have hclosed : closedSquare (p.toStationary.model sharpData 2) (sharpData.inFrame 0 b) := by
    change closedSquare (sharpData.tiltedSquare (sharpData.pG p.tilted)) _
    rw [closedSquare,hx,hy,abs_neg,abs_of_pos (by linarith : 0<sharpData.h₁+3/2)]
    constructor <;> norm_num
    linarith
  have hh := hclear (sharpData.inFrame 0 b) hclosed
  rw [sharpData.normSq_inFrame] at hh
  dsimp [coreRadius] at hh
  dsimp [Coordinates.etaMax]
  dsimp [b] at hb hh
  nlinarith

/-- Admissible parameters of the statement give admissible parameters of
`ExactFamily/Coordinates.lean` under the half-angle coordinate; the conditions of the core come
from the squares of the model. -/
theorem toStationary_admissible {p : Parameters} (hp : p.Admissible FiveCorner.selected) :
    p.toStationary.Admissible sharpData := by
  apply Eight.admissible_of_original_geometry
  · rw [toStationary_model hp.angle_mem,← FiveCorner.radius_sq_eq_stationary]
    exact model_sqPacking hp
  · exact (central_core_recovered hp).1
  · exact angleToHalf_mem hp.angle_mem
  · exact top_core_rail_recovered hp
  · exact tilted_core_rail_recovered hp

end SquaresInCircles.Eight.Parameters
end
end
end
