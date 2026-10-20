module

public import SquaresInCircles.Eight.GeometricModel.EqualityAngles
public import SquaresInCircles.Eight.GeometricModel.FiveCornerSelection

/-!
# All twenty-eight pairs in the geometric family

Uncompiled source draft.  The twenty-one exterior pairs are separated on the
wider half-plane rails.  This proof precedes every use of the central-core
theorem: the seven remaining pairs are exactly the geometric SAT conditions.
The one-twelfth core is consequently unnecessary for packing sufficiency.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily ExactFamily.Coordinates

namespace FiveCorner

theorem selected_anchorCenter (i : Fin 5) :
    selected.anchorCenter i=sharpData.anchorCenters i := by
  have ht := ExactFamily.FiveCornerGeometry.coordinateAngle_frame sharpData
  fin_cases i <;>
    ext <;>
    simp [anchorCenter,selected_point,selected_angle,Coordinates.anchorPoints,
      Coordinates.anchorCenters,Coordinates.pA,Coordinates.pB,Coordinates.pD,
      Coordinates.pE,Coordinates.pH,Coordinates.inFrame,e,f,ht.1,ht.2] <;> ring

theorem selected_topCenter (z : ℝ) : selected.topCenter z=sharpData.pT z := by
  rw [topCenter,selected_anchorCenter]
  ext <;> simp [Coordinates.anchorCenters,Coordinates.pB,Coordinates.pT] <;> ring

theorem selected_tiltedCenter (η : ℝ) : selected.tiltedCenter η=sharpData.pG η := by
  have ht := ExactFamily.FiveCornerGeometry.coordinateAngle_frame sharpData
  rw [tiltedCenter,selected_anchorCenter]
  ext <;>
    simp [Coordinates.anchorCenters,Coordinates.pH,Coordinates.pG,
      Coordinates.inFrame,e,f,selected_angle,ht.1,ht.2] <;> ring

theorem selected_exteriorCenter (z η : ℝ) (i : Fin 7) :
    selected.exteriorCenter z η i=sharpData.exteriorCenters z η i := by
  fin_cases i <;>
    simp [exteriorCenter,Coordinates.exteriorCenters,selected_anchorCenter,
      selected_topCenter,selected_tiltedCenter,Coordinates.anchorCenters]

theorem square_selected_angle (p : Point) :
    square p selected.angle=sharpData.tiltedSquare p := by
  have ht := ExactFamily.FiveCornerGeometry.coordinateAngle_frame sharpData
  ext <;> simp [square,Coordinates.tiltedSquare,selected_angle,ht.1,ht.2]

theorem square_zero (p : Point) : square p 0=axisSquare p := by
  ext <;> simp [square,axisSquare]

theorem selected_exteriorSquare (z η : ℝ) (i : Fin 7) :
    selected.exteriorSquare z η i=sharpData.exteriorSquares z η i := by
  rw [exteriorSquare,selected_exteriorCenter]
  fin_cases i <;>
    simp [exteriorAngle,Coordinates.exteriorCenters,Coordinates.exteriorSquares,
      square_selected_angle,square_zero]

/-- This coarse lower bound is structural: B and D have selected vertices
whose first coordinates differ by three.  No decimal enclosure is used. -/
theorem radius_sq_ge_nine_quarters : (9/4:ℝ)≤radius^2 := by
  rw [radius_sq_eq_stationary]
  have hB := sharpData_stationary.second_circle
  have hD := sharpData_stationary.third_circle
  change sharpData.x₂^2+(sharpData.y+2)^2=qStar at hB
  change (sharpData.x₂-3)^2+sharpData.y₃^2=qStar at hD
  nlinarith [sq_nonneg (sharpData.x₂-3/2),sq_nonneg (sharpData.y+2),
    sq_nonneg sharpData.y₃]

end FiveCorner

namespace Parameters

theorem fromOld_model (p : EqualityParameters) :
    (fromOld p).model FiveCorner.selected=p.model sharpData := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact fromOld_centralSquare p
  · simpa [model,fromOld,EqualityParameters.model,Coordinates.exteriorSquares]
      using FiveCorner.selected_exteriorSquare p.z p.eta j

theorem toOld_model {p : Parameters} (hp : AngleRepresentative p.angle) :
    p.toOld.model sharpData=p.model FiveCorner.selected := by
  rw [← fromOld_model p.toOld,fromOld_toOld hp]

/-- The square containing the origin strictly has squared circle cost less
than two.  The model's radius is at least three halves by its fixed span. -/
theorem central_containment_automatic {p : Parameters}
    (hx : |projection (e p.angle) p.center|<1/2)
    (hy : |projection (f p.angle) p.center|<1/2) :
    containmentCost p.center p.angle<FiveCorner.radius^2 := by
  have ha := abs_nonneg (projection (e p.angle) p.center)
  have hb := abs_nonneg (projection (f p.angle) p.center)
  have hcost : containmentCost p.center p.angle<2 := by
    dsimp [containmentCost]
    nlinarith
  exact hcost.trans_le (by linarith [FiveCorner.radius_sq_ge_nine_quarters])

theorem origin_in_central {p : Parameters}
    (hx : |projection (e p.angle) p.center|<1/2)
    (hy : |projection (f p.angle) p.center|<1/2) :
    openSquare p.centralSquare (0,0) := by
  exact (origin_interior_iff p.center p.angle).mpr ⟨hx,hy⟩

end Parameters

private theorem width_tilted_e (p : Point) :
    width (sharpData.tiltedSquare p) sharpData.e=1/2 := by
  have hx : frameX (sharpData.tiltedSquare p) sharpData.e=1 := by
    simpa [frameX,Coordinates.tiltedSquare,Coordinates.e] using sharpData.unit
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

/-- All twenty-one exterior pairs on the enlarged rails.  Their partition is:
ten standard-frame pairs; HG, HA, GA and HE; GE; and the six pairs joining H/G
to B/T/D.  In particular neither old one-twelfth rail endpoint is assumed. -/
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
    have hp := mul_pos (show 0<sharpData.c by linarith) h
    have hp' := mul_pos (show 0<sharpData.s by linarith)
      (show 0<sharpData.h₁+2 by linarith)
    linarith
  have hGleft : -1/2<sharpData.c*(sharpData.h₁+1)-
      sharpData.s*(sharpData.h₂+1+η) := by
    have h₁ := mul_nonneg (show 0≤1-sharpData.c by linarith)
      (show 0≤-(sharpData.h₁+1) by linarith)
    have h₂ := mul_nonpos_of_nonneg_of_nonpos (show 0≤sharpData.s by linarith) hneg
    nlinarith
  have hHG := sharpData.HG_contact η
  have hHA := sharpData.HA_contact
  have hGA := sharpData.GA_contact η
  have hHE := sharpData.HE_contact
  have hst := sharpData.standard_contacts z
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    constructor
    · simp [exteriorNormal,Coordinates.e,Coordinates.f]
      first | norm_num | intro h; nlinarith [hc,hs]
    · norm_num [exteriorNormal,Coordinates.exteriorSquares,
        Coordinates.exteriorCenters]
      simp only [width_tilted_e,width_tilted_f,width_axis_e,width_axis_f,
        width_tilted_horizontal,width_tilted_vertical]
      simp [width,frameX,frameY,axisSquare,dot,sub,Coordinates.e,Coordinates.f,
        Coordinates.pA,Coordinates.pB,Coordinates.pD,Coordinates.pE,
        Coordinates.pH,Coordinates.pT,Coordinates.pG,Coordinates.inFrame,
        Coordinates.x₃,Coordinates.y₄] at hHG hHA hGA hHE hst ⊢
      first | linarith | nlinarith

theorem wide_exterior_disjoint {z η : ℝ} (hz : 1/2≤z)
    (hGtop : sharpData.s*(sharpData.h₁+2)+
      sharpData.c*(sharpData.h₂+1+η)≤0) :
    InteriorDisjoint (sharpData.exteriorSquares z η) := by
  intro i j hij x hx
  rcases lt_or_gt_of_ne hij with hij | hji
  · obtain ⟨hn,hs⟩ := wide_exterior_separator hz hGtop i j hij
    exact separated_by_normal hn hs x hx
  · obtain ⟨hn,hs⟩ := wide_exterior_separator hz hGtop j i hji
    exact separated_by_normal hn hs x ⟨hx.2,hx.1⟩

namespace Parameters

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
  simpa only [FiveCorner.selected_exteriorSquare] using hh

theorem exterior_contained {p : Parameters} (hp : p.Admissible FiveCorner.selected)
    (i : Fin 7) : SqContained (FiveCorner.radius^2)
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

/-- Actual containment and all twenty-eight pairs, established on the wider
rails before applying the core theorem or recovering old admissibility. -/
theorem model_sqPacking {p : Parameters} (hp : p.Admissible FiveCorner.selected) :
    SqPacking (p.model FiveCorner.selected) (0,0) (FiveCorner.radius^2) := by
  have hext := exterior_disjoint hp
  have hsep (j : Fin 7) : ∀ x,
      ¬(openSquare p.centralSquare x ∧
        openSquare (FiveCorner.selected.exteriorSquare p.top p.tilted j) x) := by
    exact (square_disjoint_iff _ _ _ _).mpr (hp.central_separated j)
  refine ⟨sq_nonneg _,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro x hx
      have hc : SqContained (FiveCorner.radius^2) p.centralSquare :=
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
    Packing (p.model FiveCorner.selected) (0,0) FiveCorner.radius := by
  have hs := model_sqPacking hp
  refine ⟨?_,hs.2⟩
  rw [FiveCorner.radius_eq_stationary]
  positivity

end Parameters

end SquaresInCircles.Eight.GeometricModel
