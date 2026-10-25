module

public import SquaresInCircles.Eight.Equality.Geometry
public import SquaresInCircles.Eight.Containing

/-!
# Eight squares: equivalence of the two descriptions of the family

The family of the statement (`Parameters.Admissible FiveCorner.selected`) asks of the central
square that it contain the disk centre and be separated from the ring, of T that it lie above the
axis and of G that it lie below. The family of `Stationary/Coordinates.lean`
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

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Parameters
open GeometricModel Stationary Stationary.Coordinates

theorem ofStationary_admissible {p : EqualityParameters} (hp : p.Admissible sharpData) :
    (ofStationary p).Admissible FiveCorner.selected := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  have hframe := halfToAngle_frame p.w
  have hpack : SqPacking ((ofStationary p).model FiveCorner.selected) (0,0) qStar := by
    rw [ofStationary_model]
    exact Stationary.model_sqPacking hp
  have hT := Stationary.exterior_contained hp 4
  have hG := Stationary.exterior_contained hp 1
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
    constructor <;> norm_num <;> linarith
  have hh := hclear (sharpData.inFrame 0 b) hclosed
  rw [sharpData.normSq_inFrame] at hh
  dsimp [coreRadius] at hh
  dsimp [Coordinates.etaMax]
  dsimp [b] at hb hh
  nlinarith

/-- Admissible parameters of the statement give admissible parameters of
`Stationary/Coordinates.lean` under the half-angle coordinate; the conditions of the core come
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

