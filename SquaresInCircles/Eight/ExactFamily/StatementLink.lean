module

public import SquaresInCircles.StatementEight
public import SquaresInCircles.Eight.Equality

/-!
# The pure statement root and the analytically selected root agree

Uncompiled source draft. The statement uses ordinary epsilon selection from
its explicit stationary equations. This module supplies the actual
existence and uniqueness proof from F2, identifies the selected coordinates,
and transports the complete equality domain and both model branches.

The analytic definitions are unchanged: this bridge keeps the pure
Mathlib-only challenge independent of the proof modules and their interval
certificate infrastructure.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ExactFamily.StatementLink
open Coordinates EqualityParameters

def toCoordinates (d : EightStatement.Root) : Coordinates :=
  ⟨d.q,d.y,d.z,d.x₁,d.x₂,d.y₃,d.x₄⟩

def fromCoordinates (d : Coordinates) : EightStatement.Root :=
  ⟨d.q,d.y,d.z,d.x₁,d.x₂,d.y₃,d.x₄⟩

@[simp] theorem to_from_coordinates (d : Coordinates) : toCoordinates (fromCoordinates d)=d := by
  cases d
  rfl

@[simp] theorem from_to_coordinates (d : EightStatement.Root) :
    fromCoordinates (toCoordinates d)=d := by
  cases d
  rfl

theorem stationary_iff (d : EightStatement.Root) :
    d.IsStationary↔(toCoordinates d).IsStationary := by
  constructor
  · intro h
    exact {
      toIsChain := {
        x₁_pos := h.x₁_pos
        x₂_pos := h.x₂_pos
        y₃_pos := h.y₃_pos
        x₄_neg := h.x₄_neg
        first_circle := h.first_circle
        second_circle := h.second_circle
        third_circle := h.third_circle
        fourth_circle := h.fourth_circle }
      q_lower := h.q_lower
      q_upper := h.q_upper
      y_lower := h.y_lower
      y_upper := h.y_upper
      y₄_lower := h.y₄_lower
      y₄_upper := h.y₄_upper
      position_order := h.position_order
      z_pos := h.z_pos
      tilt_range := h.tilt_range
      z_lt_one := h.z_lt_one
      zero_defect := h.zero_defect
      position_stationary := h.position_stationary
      tilt_stationary := h.tilt_stationary }
  · intro h
    exact {
      toIsChain := {
        x₁_pos := h.x₁_pos
        x₂_pos := h.x₂_pos
        y₃_pos := h.y₃_pos
        x₄_neg := h.x₄_neg
        first_circle := h.first_circle
        second_circle := h.second_circle
        third_circle := h.third_circle
        fourth_circle := h.fourth_circle }
      q_lower := h.q_lower
      q_upper := h.q_upper
      y_lower := h.y_lower
      y_upper := h.y_upper
      y₄_lower := h.y₄_lower
      y₄_upper := h.y₄_upper
      position_order := h.position_order
      z_pos := h.z_pos
      tilt_range := h.tilt_range
      z_lt_one := h.z_lt_one
      zero_defect := h.zero_defect
      position_stationary := h.position_stationary
      tilt_stationary := h.tilt_stationary }

theorem statement_stationary_existsUnique : ∃! d : EightStatement.Root,d.IsStationary := by
  refine ⟨fromCoordinates sharpData,?_,?_⟩
  · apply (stationary_iff _).mpr
    simpa only [to_from_coordinates] using sharpData_stationary
  · intro d hd
    have he := stationary_unique ((stationary_iff d).mp hd)
    simpa only [from_to_coordinates] using congrArg fromCoordinates he

theorem selected_stationary : EightStatement.selected.IsStationary := by
  apply Classical.epsilon_spec
  obtain ⟨d,hd,hunique⟩ := statement_stationary_existsUnique
  exact ⟨d,hd⟩

theorem selected_coordinates : toCoordinates EightStatement.selected=sharpData :=
  stationary_unique ((stationary_iff _).mp selected_stationary)

theorem selected_eq : EightStatement.selected=fromCoordinates sharpData := by
  simpa only [from_to_coordinates] using congrArg fromCoordinates selected_coordinates

theorem qStar_eq : EightStatement.qStar=qStar :=
  congrArg Coordinates.q selected_coordinates

theorem radius_eq : EightStatement.radius=Eight.radius :=
  congrArg Real.sqrt qStar_eq

def toParameters (p : EightStatement.Parameters) : EqualityParameters :=
  ⟨p.x,p.y,p.w,p.z,p.eta⟩

def fromParameters (p : EqualityParameters) : EightStatement.Parameters :=
  ⟨p.x,p.y,p.w,p.z,p.eta⟩

@[simp] theorem to_from_parameters (p : EqualityParameters) : toParameters (fromParameters p)=p := by
  cases p
  rfl

@[simp] theorem from_to_parameters (p : EightStatement.Parameters) :
    fromParameters (toParameters p)=p := by
  cases p
  rfl

theorem admissible_iff (d : EightStatement.Root) (p : EightStatement.Parameters) :
    p.Admissible d↔(toParameters p).Admissible (toCoordinates d) := by
  constructor
  · intro h
    exact {
      frame_lower := h.frame_lower
      frame_upper := h.frame_upper
      top_lower := h.top_lower
      top_upper := h.top_upper
      tilted_lower := h.tilted_lower
      tilted_upper := h.tilted_upper
      core_first := h.core_first
      core_second := h.core_second
      A_sep := h.A_sep
      B_sep := h.B_sep
      D_sep := h.D_sep
      E_sep := h.E_sep
      T_sep := h.T_sep
      H_sep := h.H_sep
      G_sep := h.G_sep }
  · intro h
    exact {
      frame_lower := h.frame_lower
      frame_upper := h.frame_upper
      top_lower := h.top_lower
      top_upper := h.top_upper
      tilted_lower := h.tilted_lower
      tilted_upper := h.tilted_upper
      core_first := h.core_first
      core_second := h.core_second
      A_sep := h.A_sep
      B_sep := h.B_sep
      D_sep := h.D_sep
      E_sep := h.E_sep
      T_sep := h.T_sep
      H_sep := h.H_sep
      G_sep := h.G_sep }

theorem root_model_eq (d : EightStatement.Root) (p : EightStatement.Parameters) :
    p.model d=(toParameters p).model (toCoordinates d) := rfl

theorem selected_admissible_iff (p : EightStatement.Parameters) :
    p.Admissible EightStatement.selected↔(toParameters p).Admissible sharpData := by
  rw [admissible_iff,selected_coordinates]

theorem model_eq (p : EightStatement.Parameters) :
    p.model EightStatement.selected=(toParameters p).model sharpData := by
  rw [root_model_eq,selected_coordinates]

theorem reflected_model_eq (b : Bool) (p : EightStatement.Parameters) :
    EightStatement.reflectedModel b p=Eight.reflectedModel b (toParameters p) := by
  cases b
  · exact model_eq p
  · funext i
    change EightStatement.reflectSquare (p.model EightStatement.selected i)=
      reflectDiagonalSquare ((toParameters p).model sharpData i)
    rw [model_eq]
    rfl

theorem models_eq : EightStatement.models=Eight.models := by
  ext M
  constructor
  · rintro ⟨b,p,hp,hM⟩
    exact ⟨b,toParameters p,(selected_admissible_iff p).mp hp,
      hM.trans (reflected_model_eq b p)⟩
  · rintro ⟨b,p,hp,hM⟩
    refine ⟨b,fromParameters p,?_,?_⟩
    · apply (selected_admissible_iff _).mpr
      simpa only [to_from_parameters] using hp
    · have hm := reflected_model_eq b (fromParameters p)
      rw [to_from_parameters] at hm
      exact hM.trans hm.symm

end SquaresInCircles.Eight.ExactFamily.StatementLink

namespace SquaresInCircles.Eight

/-- The analytic optimum agrees with the pure Mathlib-only statement radius. -/
theorem radius_statement : radius=EightStatement.radius :=
  ExactFamily.StatementLink.radius_eq.symm

/-- The full weak equality family agrees with the pure statement model set. -/
theorem models_statement : models=EightStatement.models :=
  ExactFamily.StatementLink.models_eq.symm

end SquaresInCircles.Eight
