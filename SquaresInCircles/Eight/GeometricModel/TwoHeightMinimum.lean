module

public import SquaresInCircles.Eight.GeometricModel.TwoHeights
public import SquaresInCircles.Eight.GeometricModel.FiveCornerSelection

/-!
# The two-height minimum and the selected five-corner configuration

Uncompiled source draft. The polynomial radius is an exact coordinate
elimination of the same natural five-corner problem below radius two.
Arbitrary feasible points first undergo the already proved scalar capping;
the upper chord then recovers both upper coordinates and the radius.

The selected triple has the actual selected angle. Its two heights are the
negatives of the lower stationary corner heights. Attainment and uniqueness
are consequences of the natural five-corner minimum, not new root-selection
assumptions.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GeometricModel.TwoHeights

open Set ExactFamily

private theorem fiveCorner_eq_of_fields {p q : FiveCorner}
    (ht : p.angle=q.angle) (hp : p.point=q.point) : p=q := by
  cases p
  cases q
  cases ht
  cases hp
  rfl

/-- The angle and the two lower vertical coordinates recover the triple.
This injectivity has no circle, stationarity, or domain hypothesis. -/
theorem chain_injective : Function.Injective chain := by
  intro p q h
  have hu : p.u=q.u := by
    simpa [chain] using
      congrArg (fun d : FiveCorner => -(d.point 0).2) h
  have hv : p.v=q.v := by
    simpa [chain] using
      congrArg (fun d : FiveCorner => -(d.point 3).2) h
  have ht : p.angle=q.angle := congrArg FiveCorner.angle h
  cases p
  cases q
  simp_all

/-! ## The exact stationary-coordinate adapter -/

def ofCoordinates (d : Coordinates) : TwoHeights where
  u := -d.y
  v := -d.y₄
  angle := FiveCornerGeometry.coordinateAngle d

theorem ofCoordinates_radiusSq {d : Coordinates} (hd : d.IsChain) :
    (ofCoordinates d).radiusSq=d.q :=
  (coordinate_chain_two_heights hd).2.2.symm

theorem ofCoordinates_values {d : Coordinates} (hd : d.IsChain) :
    (ofCoordinates d).r=d.x₁ ∧
    (ofCoordinates d).w=-d.x₄ ∧
    (ofCoordinates d).U=d.x₂ ∧
    (ofCoordinates d).V=-d.x₃ := by
  refine ⟨?_, ?_, (coordinate_chain_two_heights hd).1.symm,
    (coordinate_chain_two_heights hd).2.1.symm⟩
  · change Real.sqrt ((ofCoordinates d).radiusSq-(-d.y)^2)=d.x₁
    rw [ofCoordinates_radiusSq hd]
    simpa only [neg_sq] using hd.radicals.1.symm
  · change Real.sqrt ((ofCoordinates d).radiusSq-(-d.y₄)^2)=-d.x₄
    rw [ofCoordinates_radiusSq hd, neg_sq]
    linarith [hd.radicals.2.2.2]

theorem ofCoordinates_components {d : Coordinates} (hd : d.IsChain) :
    (ofCoordinates d).K₁=-d.h₁ ∧
    (ofCoordinates d).K₂=-d.h₂ := by
  obtain ⟨hr, hw, -, -⟩ := ofCoordinates_values hd
  obtain ⟨hc, hs⟩ := FiveCornerGeometry.coordinateAngle_frame d
  constructor
  · change 2-Real.cos (FiveCornerGeometry.coordinateAngle d)*
        ((ofCoordinates d).r-1)+
        Real.sin (FiveCornerGeometry.coordinateAngle d)*(-d.y)=-d.h₁
    rw [hc, hs, hr]
    dsimp [Coordinates.h₁]
    ring
  · change 1+Real.cos (FiveCornerGeometry.coordinateAngle d)*(-d.y₄)-
        Real.sin (FiveCornerGeometry.coordinateAngle d)*
        ((ofCoordinates d).w-1)=-d.h₂
    rw [hc, hs, hw]
    dsimp [Coordinates.h₂]
    ring

theorem ofCoordinates_defect {d : Coordinates} (hd : d.IsChain) :
    (ofCoordinates d).defect=d.defect := by
  obtain ⟨h₁, h₂⟩ := ofCoordinates_components hd
  rw [defect, h₁, h₂, ofCoordinates_radiusSq hd]
  simp only [neg_sq, Coordinates.defect]

/-- This is equality of all five original points, including the tilted
fifth point, rather than equality only of the radius formula. -/
theorem ofCoordinates_chain {d : Coordinates} (hd : d.IsChain) :
    (ofCoordinates d).chain=FiveCorner.ofCoordinates d := by
  obtain ⟨hr, hw, hU, hV⟩ := ofCoordinates_values hd
  obtain ⟨h₁, h₂⟩ := ofCoordinates_components hd
  apply fiveCorner_eq_of_fields rfl
  funext i
  fin_cases i
  · change ((ofCoordinates d).r,-(ofCoordinates d).u)=(d.x₁,d.y)
    rw [hr]
    simp [ofCoordinates]
  · change ((ofCoordinates d).U,2-(ofCoordinates d).u)=(d.x₂,d.y+2)
    rw [hU]
    ext <;> simp [ofCoordinates] <;> ring
  · change (-(ofCoordinates d).V,2-(ofCoordinates d).v)=(d.x₃,d.y₃)
    rw [hV]
    ext <;> simp [ofCoordinates, Coordinates.y₄] <;> ring
  · change (-(ofCoordinates d).w,-(ofCoordinates d).v)=(d.x₄,d.y₄)
    rw [hw]
    simp [ofCoordinates]
  · change framePoint (FiveCornerGeometry.coordinateAngle d)
        (-(ofCoordinates d).K₁) (-(ofCoordinates d).K₂)=
      d.inFrame d.h₁ d.h₂
    rw [h₁, h₂]
    obtain ⟨hc, hs⟩ := FiveCornerGeometry.coordinateAngle_frame d
    ext <;> simp [framePoint, Coordinates.inFrame, hc, hs]

theorem ofCoordinates_inDomain {d : Coordinates} (hd : d.IsStationary) :
    (ofCoordinates d).InDomain := by
  have ht := FiveCorner.small_tilt_subset_quarter
    (show FiveCornerGeometry.coordinateAngle d ∈
        Icc (0:ℝ) (Real.arctan (1/5)) from
      ⟨(FiveCornerGeometry.stationary_angle_mem hd).1.le,
        (FiveCornerGeometry.stationary_angle_mem hd).2.le⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, ht.1, ht.2⟩
  · change 0 ≤ -d.y
    linarith [hd.y_upper]
  · change 0 ≤ -d.y₄
    linarith [hd.y₄_upper]
  · rw [ofCoordinates_radiusSq hd.toIsChain]
    change (-d.y)^2 ≤ d.q
    nlinarith [hd.first_circle, sq_nonneg d.x₁]
  · rw [ofCoordinates_radiusSq hd.toIsChain]
    change (-d.y₄)^2 ≤ d.q
    nlinarith [hd.fourth_circle, sq_nonneg d.x₄]
  · rw [ofCoordinates_radiusSq hd.toIsChain]
    linarith [hd.q_upper]

/-! ## Capping any feasible chain into the two-height model -/

def ofScalar (q u t : ℝ) : TwoHeights where
  u := u
  v := FiveCornerGeometry.lowerHeight q u
  angle := t

/-- Both upper circle equations hold in the full radical domain, including
its endpoints. Their difference gives the polynomial coordinate formula. -/
theorem ofScalar_upper_data {q u t : ℝ}
    (hu : FiveCornerGeometry.Domain q u) :
    (ofScalar q u t).U=FiveCornerGeometry.topRight q u ∧
    (ofScalar q u t).V=FiveCornerGeometry.topLeft q u ∧
    (ofScalar q u t).radiusSq=q := by
  have hU : FiveCornerGeometry.topRight q u^2+(2-u)^2=q := by
    exact FiveCornerGeometry.upper_circle hu.second_radicand
  have hY : FiveCornerGeometry.topLeft q u^2+
      FiveCornerGeometry.topHeight q u^2=q := by
    simpa only [FiveCornerGeometry.topHeight, add_comm] using
      FiveCornerGeometry.upper_circle hu.third_radicand
  have hV : FiveCornerGeometry.topLeft q u^2+
      (2-FiveCornerGeometry.lowerHeight q u)^2=q := by
    simpa only [FiveCornerGeometry.lowerHeight, sub_sub_cancel] using hY
  have hspan : FiveCornerGeometry.topRight q u+
      FiveCornerGeometry.topLeft q u=3 := by
    dsimp [FiveCornerGeometry.topLeft]
    ring
  obtain ⟨hU', hV', hq⟩ := twoHeight_of_upper_circles hU hV hspan
  exact ⟨hU'.symm, hV'.symm, hq.symm⟩

theorem ofScalar_lower_data {q u t : ℝ}
    (hu : FiveCornerGeometry.Domain q u) :
    (ofScalar q u t).r=FiveCornerGeometry.lowerRight q u ∧
    (ofScalar q u t).w=FiveCornerGeometry.lowerLeft q u := by
  constructor
  · change Real.sqrt ((ofScalar q u t).radiusSq-u^2)=
      FiveCornerGeometry.lowerRight q u
    rw [(ofScalar_upper_data hu).2.2]
    rfl
  · change Real.sqrt ((ofScalar q u t).radiusSq-
        FiveCornerGeometry.lowerHeight q u^2)=
      FiveCornerGeometry.lowerLeft q u
    rw [(ofScalar_upper_data hu).2.2]
    rfl

theorem ofScalar_components {q u t : ℝ}
    (hu : FiveCornerGeometry.Domain q u) :
    (ofScalar q u t).K₁=
      FiveCornerGeometry.firstComponent q (Real.cos t) (Real.sin t) u ∧
    (ofScalar q u t).K₂=
      FiveCornerGeometry.secondComponent q (Real.cos t) (Real.sin t) u := by
  obtain ⟨hr, hw⟩ := ofScalar_lower_data hu
  constructor
  · change 2-Real.cos t*((ofScalar q u t).r-1)+Real.sin t*u=_
    rw [hr]
    rfl
  · change 1+Real.cos t*FiveCornerGeometry.lowerHeight q u-
        Real.sin t*((ofScalar q u t).w-1)=_
    rw [hw]
    rfl

theorem ofScalar_defect {q u t : ℝ}
    (hu : FiveCornerGeometry.Domain q u) :
    (ofScalar q u t).defect=
      FiveCornerGeometry.defect q (Real.cos t) (Real.sin t) u := by
  obtain ⟨h₁, h₂⟩ := ofScalar_components hu
  rw [defect, h₁, h₂, (ofScalar_upper_data hu).2.2]
  rfl

theorem ofScalar_inDomain {q u t : ℝ} (hq : q<4)
    (hu : FiveCornerGeometry.Domain q u) (ht : t ∈ Icc 0 (Real.pi/4)) :
    (ofScalar q u t).InDomain := by
  refine ⟨hu.height_nonneg, (hu.lowerHeight_pos hq).le, ?_, ?_, ?_, ht.1, ht.2⟩
  · rw [(ofScalar_upper_data hu).2.2]
    exact hu.first_radicand
  · rw [(ofScalar_upper_data hu).2.2]
    exact hu.fourth_radicand
  · rw [(ofScalar_upper_data hu).2.2]
    exact hq

theorem ofScalar_radius {R u t : ℝ} (hR : 0 ≤ R)
    (hu : FiveCornerGeometry.Domain (R^2) u) :
    (ofScalar (R^2) u t).radius=R := by
  rw [radius, (ofScalar_upper_data hu).2.2,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hR]

/-- Feasibility below radius two is exactly the explicit two-height
condition, with the source radius retained exactly. -/
theorem fiveCorner_feasible_iff {R : ℝ} (hR : R<2) :
    R ∈ FiveCorner.feasibleRadii ↔
      ∃ p : TwoHeights, p.InDomain ∧ p.defect ≤ 0 ∧ p.radius=R := by
  constructor
  · rintro ⟨d, hd, hfit⟩
    obtain ⟨hu, hF⟩ := FiveCorner.scalar_reduction hd hfit hR
    let p := ofScalar (R^2) (-(d.point 0).2) d.angle
    have hq : R^2<4 := by nlinarith [hfit.1]
    refine ⟨p, ofScalar_inDomain hq hu ⟨hd.1, hd.2.1⟩, ?_, ?_⟩
    · change (ofScalar (R^2) (-(d.point 0).2) d.angle).defect ≤ 0
      rw [ofScalar_defect hu]
      exact hF
    · exact ofScalar_radius hfit.1 hu
  · rintro ⟨p, hp, hdef, hr⟩
    rw [← hr]
    exact feasible_radius hp hdef

def feasibleRadii : Set ℝ :=
  {R | ∃ p : TwoHeights, p.InDomain ∧ p.defect ≤ 0 ∧ p.radius=R}

theorem mem_feasibleRadii_iff (R : ℝ) :
    R ∈ feasibleRadii ↔ R ∈ FiveCorner.feasibleRadii ∧ R<2 := by
  constructor
  · rintro ⟨p, hp, hdef, hr⟩
    have hR : R<2 := hr ▸ hp.radius_lt_two
    exact ⟨(fiveCorner_feasible_iff hR).mpr ⟨p, hp, hdef, hr⟩, hR⟩
  · rintro ⟨hfeas, hR⟩
    exact (fiveCorner_feasible_iff hR).mp hfeas

theorem feasibleRadii_eq :
    feasibleRadii=FiveCorner.feasibleRadii ∩ Iio (2:ℝ) := by
  ext R
  exact mem_feasibleRadii_iff R

/-! ## The selected triple, its radius, and its zero defect -/

def selected : TwoHeights where
  u := -sharpData.y
  v := -sharpData.y₄
  angle := FiveCorner.selected.angle

@[simp] theorem selected_u : selected.u=-sharpData.y := rfl
@[simp] theorem selected_v : selected.v=-sharpData.y₄ := rfl
@[simp] theorem selected_angle : selected.angle=FiveCorner.selected.angle := rfl

theorem selected_eq_ofCoordinates : selected=ofCoordinates sharpData := by
  unfold selected
  rw [FiveCorner.selected_angle]
  rfl

theorem selected_chain : selected.chain=FiveCorner.selected := by
  rw [selected_eq_ofCoordinates, ofCoordinates_chain sharpData_stationary.toIsChain]
  exact FiveCorner.selected_eq_stationary.symm

theorem canonical_eq_selected_chain : FiveCorner.canonical=selected.chain :=
  FiveCorner.selected_eq_canonical.symm.trans selected_chain.symm

theorem selected_inDomain : selected.InDomain := by
  rw [selected_eq_ofCoordinates]
  exact ofCoordinates_inDomain sharpData_stationary

theorem selected_zero_defect : selected.defect=0 := by
  rw [selected_eq_ofCoordinates, ofCoordinates_defect sharpData_stationary.toIsChain]
  exact sharpData_stationary.zero_defect

theorem selected_radiusSq : selected.radiusSq=sharpData.q := by
  rw [selected_eq_ofCoordinates]
  exact ofCoordinates_radiusSq sharpData_stationary.toIsChain

theorem selected_radius : selected.radius=FiveCorner.radius := by
  rw [radius, selected_radiusSq, FiveCorner.radius_eq_stationary]

/-- The geometric minimum has the symmetric two-height polynomial radius. -/
theorem geometric_radius_sq_formula :
    FiveCorner.radius^2=twoHeightRadiusSq (-sharpData.y) (-sharpData.y₄) := by
  rw [← selected_radius, radius_sq]
  rfl

theorem geometric_radius_sq_polynomial :
    FiveCorner.radius^2=
      ((9+(selected.u-selected.v)^2)*
        (9+(4-selected.u-selected.v)^2))/36 := by
  rw [← selected_radius, radius_sq]
  rfl

theorem geometric_radius_formula :
    FiveCorner.radius=
      Real.sqrt (twoHeightRadiusSq (-sharpData.y) (-sharpData.y₄)) := by
  rw [← selected_radius]
  rfl

/-! ## Equivalent minimization and uniqueness -/

/-- The direct minimization predicate for the explicit model. -/
def IsMinimizer (p : TwoHeights) : Prop :=
  p.InDomain ∧ p.defect ≤ 0 ∧
    ∀ r : TwoHeights, r.InDomain → r.defect ≤ 0 → p.radius ≤ r.radius

theorem geometric_radius_le {p : TwoHeights}
    (hp : p.InDomain) (hdef : p.defect ≤ 0) :
    FiveCorner.radius ≤ p.radius := by
  rw [FiveCorner.radius_eq_stationary]
  exact FiveCorner.stationary_radius_le sharpData_stationary
    (chain_spans hp) ((chain_fits_iff hp).mpr hdef)

theorem selected_isMinimizer : selected.IsMinimizer := by
  refine ⟨selected_inDomain, selected_zero_defect.le, ?_⟩
  intro p hp hdef
  rw [selected_radius]
  exact geometric_radius_le hp hdef

theorem isMinimizer_iff_radius_eq (p : TwoHeights) :
    p.IsMinimizer ↔
      p.InDomain ∧ p.defect ≤ 0 ∧ p.radius=FiveCorner.radius := by
  constructor
  · rintro ⟨hp, hdef, hmin⟩
    refine ⟨hp, hdef, le_antisymm ?_ (geometric_radius_le hp hdef)⟩
    simpa only [selected_radius] using
      hmin selected selected_inDomain selected_zero_defect.le
  · rintro ⟨hp, hdef, hr⟩
    refine ⟨hp, hdef, ?_⟩
    intro r hrd hrdef
    rw [hr]
    exact geometric_radius_le hrd hrdef

theorem chain_isMinimizer {p : TwoHeights} (hp : p.IsMinimizer) :
    p.chain.IsMinimizer := by
  obtain ⟨hdom, hdef, hr⟩ := (isMinimizer_iff_radius_eq p).mp hp
  refine ⟨chain_spans hdom, ?_⟩
  rw [← hr]
  exact (chain_fits_iff hdom).mpr hdef

/-- The five-corner uniqueness theorem also distinguishes the two heights:
they can be read from the first and fourth original points. -/
theorem minimizer_eq_selected {p : TwoHeights} (hp : p.IsMinimizer) :
    p=selected := by
  apply chain_injective
  rw [selected_chain]
  obtain ⟨d, hd, hunique⟩ := FiveCorner.existsUnique_minimizer
  exact (hunique _ (chain_isMinimizer hp)).trans
    (hunique _ FiveCorner.selected_isMinimizer).symm

theorem existsUnique_minimizer : ∃! p : TwoHeights, p.IsMinimizer :=
  ⟨selected, selected_isMinimizer, fun _ hp => minimizer_eq_selected hp⟩

theorem isMinimizer_iff_eq_selected (p : TwoHeights) :
    p.IsMinimizer ↔ p=selected := by
  constructor
  · exact minimizer_eq_selected
  · rintro rfl
    exact selected_isMinimizer

theorem radius_eq_iff_eq_selected {p : TwoHeights}
    (hp : p.InDomain) (hdef : p.defect ≤ 0) :
    p.radius=FiveCorner.radius ↔ p=selected := by
  constructor
  · intro hr
    exact minimizer_eq_selected ((isMinimizer_iff_radius_eq p).mpr ⟨hp, hdef, hr⟩)
  · rintro rfl
    exact selected_radius

theorem minimizing_parameters {p : TwoHeights} (hp : p.IsMinimizer) :
    p.u=-sharpData.y ∧ p.v=-sharpData.y₄ ∧
      p.angle=FiveCorner.selected.angle := by
  rw [minimizer_eq_selected hp]
  exact ⟨rfl, rfl, rfl⟩

theorem minimum_defect_zero {p : TwoHeights} (hp : p.IsMinimizer) :
    p.defect=0 := by
  rw [minimizer_eq_selected hp]
  exact selected_zero_defect

theorem feasibleRadii_nonempty : feasibleRadii.Nonempty :=
  ⟨FiveCorner.radius, selected, selected_inDomain,
    selected_zero_defect.le, selected_radius⟩

theorem feasibleRadii_bddBelow : BddBelow feasibleRadii := by
  refine ⟨0, ?_⟩
  rintro R ⟨p, hp, hdef, hr⟩
  rw [← hr]
  exact p.radius_pos.le

/-- Restricting to the explicit branch below two leaves the natural
geometric infimum unchanged, and the selected triple attains it. -/
theorem sInf_feasibleRadii : sInf feasibleRadii=FiveCorner.radius := by
  apply le_antisymm
  · exact csInf_le feasibleRadii_bddBelow
      (show FiveCorner.radius ∈ feasibleRadii from
        ⟨selected, selected_inDomain, selected_zero_defect.le, selected_radius⟩)
  · apply le_csInf feasibleRadii_nonempty
    rintro R ⟨p, hp, hdef, hr⟩
    rw [← hr]
    exact geometric_radius_le hp hdef

end SquaresInCircles.Eight.GeometricModel.TwoHeights
