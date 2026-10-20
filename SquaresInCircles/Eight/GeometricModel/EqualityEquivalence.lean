module

public import SquaresInCircles.Eight.GeometricModel.EqualityGeometry
public import SquaresInCircles.Eight.CentralCore

/-!
# Exact equivalence of the geometric and stationary equality domains

Uncompiled source draft.  Sufficiency on the enlarged geometric rails is
already proved in `EqualityGeometry`.  Only then is the strict central-core
theorem used to recover the old one-twelfth conditions.  Thus the new domain
does not silently inherit a packing or a core-clearance hypothesis.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily ExactFamily.Coordinates

namespace Parameters

theorem fromOld_admissible {p : EqualityParameters} (hp : p.Admissible sharpData) :
    (fromOld p).Admissible FiveCorner.selected := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  have hframe := halfToAngle_frame p.w
  have hpack : SqPacking ((fromOld p).model FiveCorner.selected) (0,0) qStar := by
    rw [fromOld_model]
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
    top_above_axis := by dsimp [fromOld]; linarith [hp.top_lower]
    tilted_below_axis := ?_
    central_first := ?_
    central_second := ?_
    central_separated := ?_ }
  · apply (square_sqContained_iff _ _ _).mp
    simpa [fromOld,FiveCorner.selected_topCenter,FiveCorner.square_zero,
      FiveCorner.radius_sq_eq_stationary,Coordinates.exteriorSquares] using hT
  · apply (square_sqContained_iff _ _ _).mp
    simpa [fromOld,FiveCorner.selected_tiltedCenter,FiveCorner.square_selected_angle,
      FiveCorner.radius_sq_eq_stationary,Coordinates.exteriorSquares] using hG
  · apply (tilted_below_axis_iff _).mpr
    dsimp [fromOld]
    linarith
  · have hh : |p.C*p.x+p.S*p.y|<1/2 := by linarith [hp.core_first]
    simpa [fromOld,projection,e,EqualityParameters.center,EqualityParameters.C,
      EqualityParameters.S,hframe.1,hframe.2] using hh
  · have hh : |-p.S*p.x+p.C*p.y|<1/2 := by linarith [hp.core_second]
    simpa [fromOld,projection,f,EqualityParameters.center,EqualityParameters.C,
      EqualityParameters.S,hframe.1,hframe.2] using hh
  · intro i
    apply (square_disjoint_iff _ _ _ _).mp
    simpa only [model,Fin.cons_zero,Fin.cons_succ,centralSquare,
      FiveCorner.exteriorSquare] using
      hpack.2.2 0 i.succ (by omega)

/-- The core recovered from an actual geometric model is its named central
square, because this square already contains the origin strictly. -/
theorem central_core_recovered {p : Parameters}
    (hp : p.Admissible FiveCorner.selected) :
    ContainsCore p.toOld.centralSquare ∧
      ∀ j : Fin 8, j≠0 → StrictCoreAvoiding (p.toOld.model sharpData j) := by
  have hpack : SqPacking (p.toOld.model sharpData) (0,0) qStar := by
    rw [toOld_model hp.angle_mem,← FiveCorner.radius_sq_eq_stationary]
    exact model_sqPacking hp
  obtain ⟨i,hi,hext⟩ := central_core_and_exteriors hpack
    (by simpa [Q0] using qStar_limits.2.2.le)
  have h0 : openSquare (p.toOld.model sharpData 0) (0,0) := by
    change openSquare p.toOld.centralSquare (0,0)
    rw [toOld_centralSquare hp.angle_mem]
    exact origin_in_central hp.central_first hp.central_second
  have hiz : i=0 := central_square_unique hpack.2.2
    (hi (0,0) (by norm_num [normSq,coreRadius])) h0
  subst i
  exact ⟨hi,fun j hj => hext j hj.symm⟩

/-- The nearest point on T's lower side recovers the old top rail. -/
theorem top_core_rail_recovered {p : Parameters}
    (hp : p.Admissible FiveCorner.selected) : 7/12≤p.top := by
  have hclear := (central_core_recovered hp).2 5 (by decide)
  obtain ⟨hAB,hABu,hTx,hTxu,hGx,hGxu,hED,hBbot,hDbot,hHtop,hGtop,hGleft⟩ :=
    sharp_exterior_bounds
  have hclosed : closedSquare (p.toOld.model sharpData 5) (0,p.top-1/2) := by
    norm_num [EqualityParameters.model,toOld,axisSquare,Coordinates.pT,
      closedSquare,localX,localY]
    rw [abs_of_neg (by linarith : -(sharpData.x₂-3/2)<0)]
    linarith
  have hh := hclear (0,p.top-1/2) hclosed
  dsimp [coreRadius,normSq] at hh
  have hz := hp.top_above_axis
  nlinarith

/-- The nearest point on G's upper side recovers the old tilted rail.
The half-plane condition fixes the sign of this ordinary frame coordinate. -/
theorem tilted_core_rail_recovered {p : Parameters}
    (hp : p.Admissible FiveCorner.selected) : p.tilted≤sharpData.etaMax := by
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
  have hclosed : closedSquare (p.toOld.model sharpData 2) (sharpData.inFrame 0 b) := by
    change closedSquare (sharpData.tiltedSquare (sharpData.pG p.tilted)) _
    rw [closedSquare,hx,hy,abs_neg,abs_of_pos (by linarith : 0<sharpData.h₁+3/2)]
    constructor <;> norm_num <;> linarith
  have hh := hclear (sharpData.inFrame 0 b) hclosed
  rw [sharpData.normSq_inFrame] at hh
  dsimp [coreRadius] at hh
  dsimp [Coordinates.etaMax]
  dsimp [b] at hb hh
  nlinarith

/-- Every geometric parameter record lies in the old exact domain after the
coordinate change; every premise is recovered from actual squares. -/
theorem toOld_admissible {p : Parameters} (hp : p.Admissible FiveCorner.selected) :
    p.toOld.Admissible sharpData := by
  apply Eight.admissible_of_original_geometry
  · rw [toOld_model hp.angle_mem,← FiveCorner.radius_sq_eq_stationary]
    exact model_sqPacking hp
  · exact (central_core_recovered hp).1
  · exact angleToHalf_mem hp.angle_mem
  · exact top_core_rail_recovered hp
  · exact tilted_core_rail_recovered hp

theorem admissible_iff_old (p : Parameters) :
    p.Admissible FiveCorner.selected ↔
      AngleRepresentative p.angle ∧ p.toOld.Admissible sharpData := by
  constructor
  · intro hp
    exact ⟨hp.angle_mem,toOld_admissible hp⟩
  · rintro ⟨hangle,hp⟩
    simpa only [fromOld_toOld hangle] using fromOld_admissible hp

theorem fromOld_admissible_iff (p : EqualityParameters) :
    (fromOld p).Admissible FiveCorner.selected ↔ p.Admissible sharpData := by
  constructor
  · intro hp
    simpa only [toOld_fromOld] using toOld_admissible hp
  · exact fromOld_admissible

/-- An exact bijection of the complete weak parameter domains. -/
def admissibleEquiv :
    {p : Parameters // p.Admissible FiveCorner.selected} ≃
      {p : EqualityParameters // p.Admissible sharpData} where
  toFun p := ⟨p.1.toOld,toOld_admissible p.2⟩
  invFun p := ⟨fromOld p.1,fromOld_admissible p.2⟩
  left_inv p := Subtype.ext (fromOld_toOld p.2.angle_mem)
  right_inv p := Subtype.ext (toOld_fromOld p.1)

/-- With only the half-plane condition imposed, the top rail has exactly the
larger geometric interval.  This statement does not invoke the core theorem. -/
theorem top_geometric_rail_iff (z : ℝ) :
    (containmentCost (FiveCorner.selected.topCenter z) 0≤FiveCorner.radius^2 ∧
      1/2≤z) ↔ 1/2≤z ∧ z≤sharpData.zMax := by
  have hb := sharp_exterior_bounds
  have hx : 0<sharpData.x₂-3/2 := hb.2.2.1
  have hq : sharpData.q=qStar := rfl
  have hrad : 0≤qStar-(sharpData.x₂-1)^2 := by
    obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,
      hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
    nlinarith [qStar_limits.1]
  have hroot := Real.sqrt_nonneg (qStar-(sharpData.x₂-1)^2)
  have hroot2 := Real.sq_sqrt hrad
  constructor
  · rintro ⟨hc,hz⟩
    have hs : SqContained qStar (axisSquare (sharpData.pT z)) := by
      apply (square_sqContained_iff (FiveCorner.selected.topCenter z) 0 _).mpr at hc
      simpa [FiveCorner.selected_topCenter,FiveCorner.square_zero,
        FiveCorner.radius_sq_eq_stationary] using hc
    rw [axis_containment] at hs
    simp [Coordinates.pT,abs_of_pos hx,abs_of_pos (by linarith : 0<z)] at hs
    refine ⟨hz,?_⟩
    dsimp [Coordinates.zMax]
    rw [hq]
    nlinarith
  · rintro ⟨hz,hupper⟩
    refine ⟨?_,hz⟩
    apply (square_sqContained_iff _ _ _).mp
    rw [FiveCorner.selected_topCenter,FiveCorner.square_zero,
      FiveCorner.radius_sq_eq_stationary,axis_containment]
    simp [Coordinates.pT,abs_of_pos hx,abs_of_pos (by linarith : 0<z)]
    dsimp [Coordinates.zMax] at hupper
    rw [hq] at hupper
    nlinarith

/-- The other enlarged geometric rail, with its exact oblique half-plane
endpoint.  This is a containment calculation, independent of the core. -/
theorem tilted_geometric_rail_iff (η : ℝ) :
    (containmentCost (FiveCorner.selected.tiltedCenter η) FiveCorner.selected.angle≤
        FiveCorner.radius^2 ∧
      (FiveCorner.selected.tiltedCenter η).2+
        (|Real.cos FiveCorner.selected.angle|+|Real.sin FiveCorner.selected.angle|)/2≤0) ↔
    sharpData.etaMin≤η ∧
      η≤ -sharpData.h₂-1-(sharpData.h₁+2)*Real.tan FiveCorner.selected.angle := by
  have ht := ExactFamily.FiveCornerGeometry.coordinateAngle_frame sharpData
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hcl,hcu,hsl,hsu,
    hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hrad : 0≤qStar-(sharpData.h₁+2)^2 := by nlinarith [qStar_limits.1]
  have hroot := Real.sqrt_nonneg (qStar-(sharpData.h₁+2)^2)
  have hroot2 := Real.sq_sqrt hrad
  have hx : 0<sharpData.h₁+3/2 := by linarith
  have hangle : Real.tan FiveCorner.selected.angle=sharpData.s/sharpData.c := by
    rw [Real.tan_eq_sin_div_cos,FiveCorner.selected_angle,ht.1,ht.2]
  have hproduct : sharpData.c*((sharpData.h₁+2)*(sharpData.s/sharpData.c))=
      sharpData.s*(sharpData.h₁+2) := by
    field_simp [ne_of_gt hc]
    ring
  have hpositive : 0<(sharpData.h₁+2)*(sharpData.s/sharpData.c) :=
    mul_pos (by linarith) (div_pos hs hc)
  have htop := tilted_below_axis_iff (⟨(0,0),0,0,η⟩ : Parameters)
  have hcost :
      containmentCost (FiveCorner.selected.tiltedCenter η) FiveCorner.selected.angle≤
        FiveCorner.radius^2 ↔
      (|sharpData.h₁+3/2|+1/2)^2+(|sharpData.h₂+1/2+η|+1/2)^2≤qStar := by
    rw [← square_sqContained_iff,FiveCorner.selected_tiltedCenter,
      FiveCorner.square_selected_angle,FiveCorner.radius_sq_eq_stationary,
      Coordinates.pG,tilted_containment]
  rw [hcost,htop,hangle]
  constructor
  · rintro ⟨hcircle,hbelow⟩
    have hneg : sharpData.h₂+1+η<0 := by
      by_contra! h
      have hh := mul_nonneg hc.le h
      have hh' := mul_pos hs (show 0<sharpData.h₁+2 by linarith)
      linarith
    rw [abs_of_pos hx,abs_of_neg (by linarith : sharpData.h₂+1/2+η<0)] at hcircle
    refine ⟨?_,?_⟩
    · dsimp [Coordinates.etaMin]
      change -sharpData.h₂-Real.sqrt (qStar-(sharpData.h₁+2)^2)≤η
      nlinarith
    · have hh :
          sharpData.c*(η-(-sharpData.h₂-1-
            (sharpData.h₁+2)*(sharpData.s/sharpData.c)))≤0 := by
        nlinarith
      exact le_of_sub_nonpos ((mul_nonpos_iff_of_pos_left hc).mp hh)
  · rintro ⟨hl,hu⟩
    have hneg : sharpData.h₂+1+η<0 := by linarith
    have hl' : -Real.sqrt (qStar-(sharpData.h₁+2)^2)≤sharpData.h₂+η := by
      dsimp [Coordinates.etaMin] at hl
      change -sharpData.h₂-Real.sqrt (qStar-(sharpData.h₁+2)^2)≤η at hl
      linarith
    have hsq := mul_nonneg
      (show 0≤Real.sqrt (qStar-(sharpData.h₁+2)^2)+(sharpData.h₂+η) by linarith)
      (show 0≤Real.sqrt (qStar-(sharpData.h₁+2)^2)-(sharpData.h₂+η) by linarith)
    constructor
    · rw [abs_of_pos hx,abs_of_neg (by linarith : sharpData.h₂+1/2+η<0)]
      nlinarith
    · have hh := mul_le_mul_of_nonneg_left hu hc.le
      nlinarith

end Parameters

end SquaresInCircles.Eight.GeometricModel
