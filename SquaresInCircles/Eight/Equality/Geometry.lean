module

public import SquaresInCircles.Eight.Stationary.Family
public import SquaresInCircles.Eight.Equality.Angles
public import SquaresInCircles.Eight.Corners.Selection
public import SquaresInCircles.Eight.Equality.SquareGeometry

/-!
# Eight squares: the models of the family are packings

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
open GeometricModel Stationary Stationary.Coordinates

theorem selected_anchorCenter (i : Fin 5) :
    selected.anchorCenter i=sharpData.anchorCenters i := by
  have ht := Stationary.FiveCornerGeometry.coordinateAngle_frame sharpData
  fin_cases i <;>
    ext <;>
    simp [anchorCenter,selected_point,selected_angle,Coordinates.anchorPoints,
      Coordinates.anchorCenters,Coordinates.pA,Coordinates.pB,Coordinates.pD,
      Coordinates.pE,Coordinates.pH,Coordinates.inFrame,ht.1,ht.2] <;> ring

theorem selected_topCenter (z : ℝ) : selected.topCenter z=sharpData.pT z := by
  rw [topCenter,selected_anchorCenter]
  ext <;> simp [Coordinates.anchorCenters,Coordinates.pB,Coordinates.pT] <;> ring

theorem selected_tiltedCenter (η : ℝ) : selected.tiltedCenter η=sharpData.pG η := by
  have ht := Stationary.FiveCornerGeometry.coordinateAngle_frame sharpData
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
  have ht := Stationary.FiveCornerGeometry.coordinateAngle_frame sharpData
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
open GeometricModel Stationary Stationary.Coordinates

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
open Stationary Stationary.Coordinates

private theorem width_tilted_e (p : Point) :
    width (sharpData.tiltedSquare p) sharpData.e=1/2 := by
  have hx : frameX (sharpData.tiltedSquare p) sharpData.e=1 := by
    dsimp [frameX,Coordinates.tiltedSquare,Coordinates.e]
    linear_combination sharpData.unit
  have hy : frameY (sharpData.tiltedSquare p) sharpData.e=0 := by
    dsimp [frameY,Coordinates.tiltedSquare,Coordinates.e]
    ring
  simp [width,hx,hy]

private theorem width_tilted_f (p : Point) :
    width (sharpData.tiltedSquare p) sharpData.f=1/2 := by
  have hx : frameX (sharpData.tiltedSquare p) sharpData.f=0 := by
    dsimp [frameX,Coordinates.tiltedSquare,Coordinates.f]
    ring
  have hy : frameY (sharpData.tiltedSquare p) sharpData.f=1 := by
    dsimp [frameY,Coordinates.tiltedSquare,Coordinates.f]
    nlinarith [sharpData.unit]
  simp [width,hx,hy]

private theorem width_axis_e (p : Point) :
    width (axisSquare p) sharpData.e=(sharpData.c+sharpData.s)/2 := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  simp [width,frameX,frameY,axisSquare,Coordinates.e,abs_of_pos hc,abs_of_pos hs]

private theorem width_axis_f (p : Point) :
    width (axisSquare p) sharpData.f=(sharpData.c+sharpData.s)/2 := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  simp [width,frameX,frameY,axisSquare,Coordinates.f,abs_of_pos hc,abs_of_pos hs,
    abs_neg,add_comm]

private theorem width_tilted_horizontal (p : Point) :
    width (sharpData.tiltedSquare p) (-1,0)=(sharpData.c+sharpData.s)/2 := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  simp [width,frameX,frameY,Coordinates.tiltedSquare,abs_of_pos hc,abs_of_pos hs,abs_neg]

private theorem width_tilted_vertical (p : Point) :
    width (sharpData.tiltedSquare p) (0,1)=(sharpData.c+sharpData.s)/2 := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  simp [width,frameX,frameY,Coordinates.tiltedSquare,abs_of_pos hc,abs_of_pos hs,add_comm]

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
        (sub (sharpData.exteriorCenters z η j) (sharpData.exteriorCenters z η i)) := by
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,
    hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  obtain ⟨hAB,hABu,hTx,hTxu,hGx,hGxu,hED,hBbot,hDbot,hHtop,hGcore,hGleftCore⟩ :=
    sharp_exterior_bounds
  have hneg : sharpData.h₂+1+η≤0 := by
    by_contra! h
    have hp := mul_pos (show 0<sharpData.c by linarith only [hc]) h
    have hp' := mul_pos (show 0<sharpData.s by linarith only [hs])
      (show 0<sharpData.h₁+2 by linarith only [hh₁])
    linarith only [hp,hp',hGtop]
  have hGleft : -1/2<sharpData.c*(sharpData.h₁+1)-
      sharpData.s*(sharpData.h₂+1+η) := by
    have h₁ := mul_nonneg (show 0≤1-sharpData.c by linarith only [hcu])
      (show 0≤-(sharpData.h₁+1) by linarith only [hh₁u])
    have h₂ := mul_nonpos_of_nonneg_of_nonpos (show 0≤ sharpData.s by linarith only [hs]) hneg
    linarith only [h₁,h₂,hh₁]
  have hHG := sharpData.HG_contact η
  have hHA := sharpData.HA_contact
  have hGA := sharpData.GA_contact η
  have hHE := sharpData.HE_contact
  have he : sharpData.e≠(0,0) := by
    intro h
    have hc₀ := congrArg Prod.fst h
    dsimp [Coordinates.e] at hc₀
    linarith only [hc₀,hc]
  have hf : sharpData.f≠(0,0) := by
    intro h
    have hc₀ := congrArg Prod.snd h
    dsimp [Coordinates.f] at hc₀
    linarith only [hc₀,hc]
  have hy : ((0,1):Point)≠(0,0) := by simp
  have hmy : ((0,-1):Point)≠(0,0) := by simp
  have hmx : ((-1,0):Point)≠(0,0) := by simp
  have wAy (v : Point) : width (axisSquare v) ((0,1):Point)=1/2 := by
    simp [width,frameX,frameY,axisSquare]
  have wAmy (v : Point) : width (axisSquare v) ((0,-1):Point)=1/2 := by
    simp [width,frameX,frameY,axisSquare]
  have wAmx (v : Point) : width (axisSquare v) ((-1,0):Point)=1/2 := by
    simp [width,frameX,frameY,axisSquare]
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · refine ⟨he,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) sharpData.e+
      width (sharpData.tiltedSquare (sharpData.pG η)) sharpData.e≤
        dot sharpData.e (sub (sharpData.pG η) sharpData.pH)
    rw [width_tilted_e,width_tilted_e,hHG]
    norm_num
  · refine ⟨he,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) sharpData.e+
      width (axisSquare sharpData.pA) sharpData.e≤dot sharpData.e (sub sharpData.pA sharpData.pH)
    rw [width_tilted_e,width_axis_e,hHA]
    linarith only []
  · refine ⟨hy,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) ((0,1):Point)+
      width (axisSquare sharpData.pB) ((0,1):Point)≤
        dot ((0,1):Point) (sub sharpData.pB sharpData.pH)
    rw [width_tilted_vertical,wAy]
    simp only [dot,sub,Coordinates.pB,Coordinates.pH,Coordinates.inFrame]
    linarith only [hBbot,hHtop]
  · refine ⟨hy,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) ((0,1):Point)+
      width (axisSquare (sharpData.pT z)) ((0,1):Point)≤
        dot ((0,1):Point) (sub (sharpData.pT z) sharpData.pH)
    rw [width_tilted_vertical,wAy]
    simp only [dot,sub,Coordinates.pT,Coordinates.pH,Coordinates.inFrame]
    linarith only [hHtop,hz]
  · refine ⟨hy,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) ((0,1):Point)+
      width (axisSquare sharpData.pD) ((0,1):Point)≤
        dot ((0,1):Point) (sub sharpData.pD sharpData.pH)
    rw [width_tilted_vertical,wAy]
    simp only [dot,sub,Coordinates.pD,Coordinates.pH,Coordinates.inFrame]
    linarith only [hDbot,hHtop]
  · refine ⟨hf,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) sharpData.f+
      width (axisSquare sharpData.pE) sharpData.f≤dot sharpData.f (sub sharpData.pE sharpData.pH)
    rw [width_tilted_f,width_axis_f,hHE]
    linarith only []
  · refine ⟨he,?_⟩
    show width (sharpData.tiltedSquare (sharpData.pG η)) sharpData.e+
      width (axisSquare sharpData.pA) sharpData.e≤
        dot sharpData.e (sub sharpData.pA (sharpData.pG η))
    rw [width_tilted_e,width_axis_e,hGA]
    linarith only []
  · refine ⟨hy,?_⟩
    show width (sharpData.tiltedSquare (sharpData.pG η)) ((0,1):Point)+
      width (axisSquare sharpData.pB) ((0,1):Point)≤
        dot ((0,1):Point) (sub sharpData.pB (sharpData.pG η))
    rw [width_tilted_vertical,wAy]
    simp only [dot,sub,Coordinates.pB,Coordinates.pG,Coordinates.inFrame]
    linarith only [hBbot,hGtop]
  · refine ⟨hy,?_⟩
    show width (sharpData.tiltedSquare (sharpData.pG η)) ((0,1):Point)+
      width (axisSquare (sharpData.pT z)) ((0,1):Point)≤
        dot ((0,1):Point) (sub (sharpData.pT z) (sharpData.pG η))
    rw [width_tilted_vertical,wAy]
    simp only [dot,sub,Coordinates.pT,Coordinates.pG,Coordinates.inFrame]
    linarith only [hz,hGtop]
  · refine ⟨hy,?_⟩
    show width (sharpData.tiltedSquare (sharpData.pG η)) ((0,1):Point)+
      width (axisSquare sharpData.pD) ((0,1):Point)≤
        dot ((0,1):Point) (sub sharpData.pD (sharpData.pG η))
    rw [width_tilted_vertical,wAy]
    simp only [dot,sub,Coordinates.pD,Coordinates.pG,Coordinates.inFrame]
    linarith only [hDbot,hGtop]
  · refine ⟨hmx,?_⟩
    show width (sharpData.tiltedSquare (sharpData.pG η)) ((-1,0):Point)+
      width (axisSquare sharpData.pE) ((-1,0):Point)≤
        dot ((-1,0):Point) (sub sharpData.pE (sharpData.pG η))
    rw [width_tilted_horizontal,wAmx]
    simp only [dot,sub,Coordinates.pE,Coordinates.pG,Coordinates.inFrame]
    linarith only [hGleft,hx₄u]
  · refine ⟨hy,?_⟩
    show width (axisSquare sharpData.pA) ((0,1):Point)+width (axisSquare sharpData.pB) ((0,1):Point)≤
      dot ((0,1):Point) (sub sharpData.pB sharpData.pA)
    rw [wAy,wAy]
    simp only [dot,sub,Coordinates.pA,Coordinates.pB]
    linarith only []
  · refine ⟨hmx,?_⟩
    show width (axisSquare sharpData.pA) ((-1,0):Point)+
      width (axisSquare (sharpData.pT z)) ((-1,0):Point)≤
        dot ((-1,0):Point) (sub (sharpData.pT z) sharpData.pA)
    rw [wAmx,wAmx]
    simp only [dot,sub,Coordinates.pA,Coordinates.pT]
    linarith only [hAB]
  · refine ⟨hmx,?_⟩
    show width (axisSquare sharpData.pA) ((-1,0):Point)+
      width (axisSquare sharpData.pD) ((-1,0):Point)≤
        dot ((-1,0):Point) (sub sharpData.pD sharpData.pA)
    rw [wAmx,wAmx]
    simp only [dot,sub,Coordinates.pA,Coordinates.pD,Coordinates.x₃]
    linarith only [hAB]
  · refine ⟨hmx,?_⟩
    show width (axisSquare sharpData.pA) ((-1,0):Point)+
      width (axisSquare sharpData.pE) ((-1,0):Point)≤
        dot ((-1,0):Point) (sub sharpData.pE sharpData.pA)
    rw [wAmx,wAmx]
    simp only [dot,sub,Coordinates.pA,Coordinates.pE]
    linarith only [hx₁,hx₄u]
  · refine ⟨hmx,?_⟩
    show width (axisSquare sharpData.pB) ((-1,0):Point)+
      width (axisSquare (sharpData.pT z)) ((-1,0):Point)≤
        dot ((-1,0):Point) (sub (sharpData.pT z) sharpData.pB)
    rw [wAmx,wAmx]
    simp only [dot,sub,Coordinates.pB,Coordinates.pT]
    linarith only []
  · refine ⟨hmx,?_⟩
    show width (axisSquare sharpData.pB) ((-1,0):Point)+
      width (axisSquare sharpData.pD) ((-1,0):Point)≤
        dot ((-1,0):Point) (sub sharpData.pD sharpData.pB)
    rw [wAmx,wAmx]
    simp only [dot,sub,Coordinates.pB,Coordinates.pD,Coordinates.x₃]
    linarith only []
  · refine ⟨hmx,?_⟩
    show width (axisSquare sharpData.pB) ((-1,0):Point)+
      width (axisSquare sharpData.pE) ((-1,0):Point)≤
        dot ((-1,0):Point) (sub sharpData.pE sharpData.pB)
    rw [wAmx,wAmx]
    simp only [dot,sub,Coordinates.pB,Coordinates.pE]
    linarith only [hx₂,hx₄u]
  · refine ⟨hmx,?_⟩
    show width (axisSquare (sharpData.pT z)) ((-1,0):Point)+
      width (axisSquare sharpData.pD) ((-1,0):Point)≤
        dot ((-1,0):Point) (sub sharpData.pD (sharpData.pT z))
    rw [wAmx,wAmx]
    simp only [dot,sub,Coordinates.pD,Coordinates.pT,Coordinates.x₃]
    linarith only []
  · refine ⟨hmx,?_⟩
    show width (axisSquare (sharpData.pT z)) ((-1,0):Point)+
      width (axisSquare sharpData.pE) ((-1,0):Point)≤
        dot ((-1,0):Point) (sub sharpData.pE (sharpData.pT z))
    rw [wAmx,wAmx]
    simp only [dot,sub,Coordinates.pE,Coordinates.pT]
    linarith only [hx₂,hx₄u]
  · refine ⟨hmy,?_⟩
    show width (axisSquare sharpData.pD) ((0,-1):Point)+
      width (axisSquare sharpData.pE) ((0,-1):Point)≤
        dot ((0,-1):Point) (sub sharpData.pE sharpData.pD)
    rw [wAmy,wAmy]
    simp only [dot,sub,Coordinates.pD,Coordinates.pE,Coordinates.x₃,Coordinates.y₄]
    linarith only []

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
open GeometricModel Stationary Stationary.Coordinates

theorem tilted_below_axis_iff (p : Parameters) :
    ((FiveCorner.selected.tiltedCenter p.tilted).2+
      (|Real.cos FiveCorner.selected.angle|+|Real.sin FiveCorner.selected.angle|)/2≤0) ↔
    sharpData.s*(sharpData.h₁+2)+sharpData.c*(sharpData.h₂+1+p.tilted)≤0 := by
  have ht := Stationary.FiveCornerGeometry.coordinateAngle_frame sharpData
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
  have ha := Stationary.exterior_contained Eight.sample_admissible
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

