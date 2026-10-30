module

public import SquaresInCircles.Eight.Equality.Equivalence

/-!
# Eight squares: construction

The admissible models (`admissibleModels`), the models of the parameters of the statement with
the central square around the disk centre, are the models of the stationary chart
(`models_eq_stationary`): `Parameters.ofStationary` and `Parameters.toStationary` translate the
five parameters of the chart into the centre and angle of the central square, the height of `T`
and the offset of `G`, for both mirror images. Every admissible model is a packing in the disk of
radius `Eight.radius` (`model_packing`) with a point of a square on the circle (`model_reaches`),
and the sample parameters of the chart give one (`models_nonempty`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily

theorem reflectedModel_ofStationary (b : Bool) (p : EqualityParameters) :
    reflectedModel b (Parameters.ofStationary p)=stationaryReflectedModel b p := by
  cases b
  · simpa [reflectedModel,stationaryReflectedModel] using Parameters.ofStationary_model p
  · funext i
    simp [reflectedModel,stationaryReflectedModel,Parameters.ofStationary_model,
      reflectSquare_eq_reflectDiagonalSquare]

theorem reflectedModel_toStationary (b : Bool) {p : Parameters}
    (hp : Parameters.AngleRepresentative p.angle) :
    stationaryReflectedModel b p.toStationary=reflectedModel b p := by
  rw [← reflectedModel_ofStationary,Parameters.ofStationary_toStationary hp]

/-- The admissible models are the models of the stationary chart, mirror images and contact
endpoints included. -/
theorem models_eq_stationary : admissibleModels=stationaryModels := by
  ext M
  constructor
  · rintro ⟨b,p,hp,hM⟩
    refine ⟨b,p.toStationary,Parameters.toStationary_admissible hp,?_⟩
    exact hM.trans (reflectedModel_toStationary b hp.angle_mem).symm
  · rintro ⟨b,p,hp,hM⟩
    refine ⟨b,Parameters.ofStationary p,Parameters.ofStationary_admissible hp,?_⟩
    exact hM.trans (reflectedModel_ofStationary b p).symm

def attainingParameters : Parameters := Parameters.ofStationary sampleParameters
def attainingModel : Fin 8 → UnitSquare := attainingParameters.model FiveCorner.selected

theorem attainingParameters_admissible :
    attainingParameters.Admissible FiveCorner.selected :=
  Parameters.ofStationary_admissible Eight.sample_admissible

theorem models_nonempty : admissibleModels.Nonempty :=
  ⟨attainingModel,false,attainingParameters,attainingParameters_admissible,rfl⟩

theorem model_packing (M : Fin 8 → UnitSquare) (hM : M∈admissibleModels) :
    Packing M (0,0) Eight.radius := by
  obtain ⟨b,p,hp,rfl⟩ := hM
  have h := Parameters.model_packing hp
  cases b
  · simpa [reflectedModel] using h
  · simpa [reflectedModel,reflectSquare_eq_reflectDiagonalSquare]
      using packing_reflectDiagonal h

theorem model_reaches (M : Fin 8 → UnitSquare) (hM : M∈admissibleModels) :
    ∃ i x,closedSquare (M i) x ∧ Eight.radius^2≤normSq x := by
  obtain ⟨b,p,hp,rfl⟩ := hM
  obtain ⟨i,x,hx,hr⟩ := Parameters.model_reaches p
  cases b
  · exact ⟨i,x,hx,hr⟩
  · refine ⟨i,diagonalPoint x,?_,?_⟩
    · simpa [reflectedModel,reflectSquare_eq_reflectDiagonalSquare,
        reflectDiagonal_closed] using hx
    · simpa [normSq,diagonalPoint,add_comm] using hr

end SquaresInCircles.Eight.GeometricModel
