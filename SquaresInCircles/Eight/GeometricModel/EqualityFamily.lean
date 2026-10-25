module

public import SquaresInCircles.Eight.GeometricModel.EqualityCircle

/-!
# The complete geometric family and its five genuine freedoms

Uncompiled source draft.  This is the equality-model bridge only.  It does
not import the old unrestricted theorem: the public classification is joined
to the fresh sharp-radius boundary argument in `GeometricModel.Theorem`.

The explicit product box below is expressed in center coordinates, an actual
angle interval, and the two sliders.  Its rigidity theorem permits every
ambient Euclidean isometry and every permutation of the eight squares.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily

theorem reflectedModel_fromOld (b : Bool) (p : EqualityParameters) :
    reflectedModel b (Parameters.fromOld p)=stationaryReflectedModel b p := by
  cases b
  · simpa [reflectedModel,stationaryReflectedModel] using Parameters.fromOld_model p
  · funext i
    simp [reflectedModel,stationaryReflectedModel,Parameters.fromOld_model,
      reflectSquare_eq_reflectDiagonalSquare]

theorem reflectedModel_toOld (b : Bool) {p : Parameters}
    (hp : Parameters.AngleRepresentative p.angle) :
    stationaryReflectedModel b p.toOld=reflectedModel b p := by
  rw [← reflectedModel_fromOld,Parameters.fromOld_toOld hp]

/-- Set equality includes both chiral copies and every weak contact endpoint. -/
theorem models_eq_stationary : admissibleModels=stationaryModels := by
  ext M
  constructor
  · rintro ⟨b,p,hp,hM⟩
    refine ⟨b,p.toOld,Parameters.toOld_admissible hp,?_⟩
    exact hM.trans (reflectedModel_toOld b hp.angle_mem).symm
  · rintro ⟨b,p,hp,hM⟩
    refine ⟨b,Parameters.fromOld p,Parameters.fromOld_admissible hp,?_⟩
    exact hM.trans (reflectedModel_fromOld b p).symm

def attainingParameters : Parameters := Parameters.fromOld sampleParameters
def attainingModel : Fin 8 → UnitSquare := attainingParameters.model FiveCorner.selected

theorem attainingParameters_admissible :
    attainingParameters.Admissible FiveCorner.selected :=
  Parameters.fromOld_admissible Eight.sample_admissible

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

theorem attainingPacking : Packing attainingModel (0,0) Eight.radius :=
  Parameters.model_packing attainingParameters_admissible

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

theorem halfToAngle_strictMono : StrictMono halfToAngle := by
  intro x y hxy
  dsimp [halfToAngle]
  exact mul_lt_mul_of_pos_left (Real.arctan_strictMono hxy) (by norm_num)

theorem halfToAngle_le_iff (x y : ℝ) : halfToAngle x≤halfToAngle y ↔ x≤y :=
  halfToAngle_strictMono.le_iff_le

theorem continuous_halfToAngle : Continuous halfToAngle :=
  continuous_const.mul Real.continuous_arctan

end SquaresInCircles.Eight.GeometricModel

namespace SquaresInCircles.Eight.Parameters
open GeometricModel ExactFamily

/-- A full product of five nondegenerate intervals in geometric coordinates. -/
def InBox (p : Parameters) : Prop :=
  (139/1000≤p.center.1 ∧ p.center.1≤141/1000) ∧
  (-(1/1000)≤p.center.2 ∧ p.center.2≤1/1000) ∧
  (halfToAngle (99/1000)≤p.angle ∧ p.angle≤halfToAngle (101/1000)) ∧
  (1349/1000≤p.top ∧ p.top≤1351/1000) ∧
  (-(321/1000)≤p.tilted ∧ p.tilted≤ -(319/1000))

theorem fromOld_inBox_iff (p : EqualityParameters) :
    (fromOld p).InBox ↔ p.InBox := by
  simp only [InBox,fromOld,EqualityParameters.InBox,EqualityParameters.center,
    halfToAngle_le_iff]

theorem inBox_angle_mem {p : Parameters} (hp : p.InBox) :
    AngleRepresentative p.angle := by
  have hs := Real.sqrt_nonneg (2:ℝ)
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hl : AngleRepresentative (halfToAngle (99/1000)) :=
    halfToAngle_mem ⟨by nlinarith,by nlinarith⟩
  have hu : AngleRepresentative (halfToAngle (101/1000)) :=
    halfToAngle_mem ⟨by nlinarith,by nlinarith⟩
  exact ⟨hl.1.trans hp.2.2.1.1,hp.2.2.1.2.trans_lt hu.2⟩

theorem toOld_inBox {p : Parameters} (hp : p.InBox) : p.toOld.InBox := by
  apply (fromOld_inBox_iff _).mp
  rw [fromOld_toOld (inBox_angle_mem hp)]
  exact hp

theorem inBox_iff_old (p : Parameters) :
    p.InBox ↔ AngleRepresentative p.angle ∧ p.toOld.InBox := by
  constructor
  · intro hp
    exact ⟨inBox_angle_mem hp,toOld_inBox hp⟩
  · rintro ⟨hangle,hp⟩
    have hh := (fromOld_inBox_iff p.toOld).mpr hp
    simpa only [fromOld_toOld hangle] using hh

theorem box_admissible {p : Parameters} (hp : p.InBox) :
    p.Admissible FiveCorner.selected := by
  apply (admissible_iff_old p).mpr
  exact ⟨inBox_angle_mem hp,Eight.box_admissible (toOld_inBox hp)⟩

theorem whole_box_packing {p : Parameters} (hp : p.InBox) :
    Packing (p.model FiveCorner.selected) (0,0) Eight.radius :=
  model_packing (box_admissible hp)

theorem box_rigidlyCongruent_iff {p r : Parameters} (hp : p.InBox) (hr : r.InBox) :
    ExactFamily.BoxRigidity.RigidlyCongruent
      (p.model FiveCorner.selected) (r.model FiveCorner.selected) ↔ p=r := by
  constructor
  · intro h
    have h' : ExactFamily.BoxRigidity.RigidlyCongruent
        (p.toOld.model sharpData) (r.toOld.model sharpData) := by
      rw [toOld_model (inBox_angle_mem hp),toOld_model (inBox_angle_mem hr)]
      exact h
    have he := ExactFamily.BoxRigidity.box_rigid_parameters (toOld_inBox hp) (toOld_inBox hr) h'
    calc
      p=fromOld p.toOld := (fromOld_toOld (inBox_angle_mem hp)).symm
      _=fromOld r.toOld := congrArg fromOld he
      _=r := fromOld_toOld (inBox_angle_mem hr)
  · rintro rfl
    exact ⟨Equiv.refl _,Equiv.refl _,by simp,by simp⟩

private theorem r4_halfAngle_inv (w : ℝ) : halfAngleSin w/(1+halfAngleCos w)=w := by
  have hd := halfAngle_den_pos w
  have h1 : 1+halfAngleCos w=2/(1+w^2) := by
    unfold halfAngleCos
    field_simp
    ring
  rw [h1]
  unfold halfAngleSin
  field_simp

/-- The old parameters are read off the central square, `G` and `T` of the old model. -/
private theorem r4_old_model_injective {p r : EqualityParameters}
    (h : p.model sharpData=r.model sharpData) : p=r := by
  have h0 : p.centralSquare=r.centralSquare := congrFun h 0
  have h2 : sharpData.tiltedSquare (sharpData.pG p.eta)=
      sharpData.tiltedSquare (sharpData.pG r.eta) := congrFun h 2
  have h5 : axisSquare (sharpData.pT p.z)=axisSquare (sharpData.pT r.z) := congrFun h 5
  have hc := congrArg UnitSquare.center h0
  have hC : halfAngleCos p.w=halfAngleCos r.w := congrArg UnitSquare.cosine h0
  have hS : halfAngleSin p.w=halfAngleSin r.w := congrArg UnitSquare.sine h0
  have hG₁ := congrArg (fun K : UnitSquare => K.center.1) h2
  have hG₂ := congrArg (fun K : UnitSquare => K.center.2) h2
  have hT := congrArg (fun K : UnitSquare => K.center.2) h5
  simp only [EqualityParameters.centralSquare,EqualityParameters.center,Prod.mk.injEq] at hc
  simp only [Coordinates.tiltedSquare,Coordinates.pG,Coordinates.inFrame] at hG₁ hG₂
  simp only [axisSquare,Coordinates.pT] at hT
  have hw : p.w=r.w := by
    rw [← r4_halfAngle_inv p.w,← r4_halfAngle_inv r.w,hC,hS]
  have heta : p.eta=r.eta := by
    linear_combination sharpData.c*hG₂-sharpData.s*hG₁-(p.eta-r.eta)*sharpData.unit
  cases p
  cases r
  simp only at hc hw hT heta
  simp only [EqualityParameters.mk.injEq]
  exact ⟨hc.1,hc.2,hw,hT,heta⟩

theorem model_injective_on_representatives {p r : Parameters}
    (hp : AngleRepresentative p.angle) (hr : AngleRepresentative r.angle)
    (he : p.model FiveCorner.selected=r.model FiveCorner.selected) : p=r := by
  have he' : p.toOld.model sharpData=r.toOld.model sharpData := by
    rw [toOld_model hp,toOld_model hr]
    exact he
  have hold := r4_old_model_injective he'
  calc
    p=fromOld p.toOld := (fromOld_toOld hp).symm
    _=fromOld r.toOld := congrArg fromOld hold
    _=r := fromOld_toOld hr

theorem box_nonempty : ∃ p : Parameters,p.InBox :=
  ⟨fromOld sampleParameters,(fromOld_inBox_iff _).mpr sampleParameters_inBox⟩

theorem box_interval_widths :
    (139/1000:ℝ)<141/1000 ∧ -(1/1000:ℝ)<1/1000 ∧
      halfToAngle (99/1000)<halfToAngle (101/1000) ∧
      (1349/1000:ℝ)<1351/1000 ∧ -(321/1000:ℝ)< -(319/1000) := by
  have ha := halfToAngle_strictMono (show (99/1000:ℝ)<101/1000 by norm_num)
  norm_num
  exact ha

/-- Five independent geometric intervals survive after all rigid motions,
reflections and square relabelings have been factored out. -/
theorem five_freedoms :
    (∀ p : Parameters,p.InBox →
      Packing (p.model FiveCorner.selected) (0,0) Eight.radius) ∧
    (∀ p r : Parameters,p.InBox → r.InBox →
      (ExactFamily.BoxRigidity.RigidlyCongruent
        (p.model FiveCorner.selected) (r.model FiveCorner.selected) ↔ p=r)) :=
  ⟨fun _ hp => whole_box_packing hp,fun _ _ hp hr => box_rigidlyCongruent_iff hp hr⟩

end SquaresInCircles.Eight.Parameters

