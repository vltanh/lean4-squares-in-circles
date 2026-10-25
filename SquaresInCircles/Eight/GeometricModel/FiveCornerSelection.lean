module

public import SquaresInCircles.Eight.GeometricModel.FiveCornerNominalTrial
public import SquaresInCircles.Eight.ExactFamily.CenterCompletion
public import SquaresInCircles.Eight.ExactFamily.Stationary

/-!
# The natural five-corner minimum and its unique selected configuration

Uncompiled draft. The global support estimates put every potentially
smaller chain in the interval where the actual stationary envelope is
nonnegative. Strict radius decrease then proves the global lower bound.
The stationary chain attains that bound, so the natural infimum is a
minimum. Positive original-point force completion supplies its rigidity.

No extra minimizer, numerical localization, or equality conclusion is an
assumption. The imported stationary witness is the existing exact witness;
its whole-domain comparison is the geometric envelope theorem.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology

namespace SquaresInCircles.Eight.FiveCorner
open GeometricModel

open Set Filter ExactFamily
open Scalar

def canonical : FiveCorner := ofCoordinates sharpData

@[simp] theorem canonical_angle :
    canonical.angle=FiveCornerGeometry.coordinateAngle sharpData := rfl

@[simp] theorem canonical_point : canonical.point=sharpData.anchorPoints := rfl

theorem canonical_spans : canonical.spans := by
  have ht := FiveCornerGeometry.stationary_angle_mem sharpData_stationary
  exact ofCoordinates_spans sharpData (small_tilt_subset_quarter ⟨ht.1.le, ht.2.le⟩)

theorem canonical_fits : canonical.fits (Real.sqrt sharpData.q) :=
  ofCoordinates_fits sharpData_stationary.toIsChain sharpData_stationary.zero_defect

private theorem r4_q_pos {d : Coordinates} (hd : d.IsChain) : 0 < d.q := by
  rw [← hd.first_circle]
  linarith [pow_pos hd.x₁_pos 2, sq_nonneg d.y]

theorem stationary_sqrt_lt_two {d : Coordinates} (hd : d.IsStationary) :
    Real.sqrt d.q < 2 := by
  have hs := Real.sq_sqrt (r4_q_pos hd.toIsChain).le
  have hn := Real.sqrt_nonneg d.q
  nlinarith [hd.q_upper]

/-- Any natural five-point realization has at least the stationary radius.
The source radius itself needs no artificial lower cutoff. -/
theorem stationary_radius_le {d : Coordinates} (hd : d.IsStationary)
    {p : FiveCorner} {R : ℝ} (hp : p.spans) (hfit : p.fits R) :
    Real.sqrt d.q ≤ R := by
  by_contra! hsmall
  have hsq := Real.sq_sqrt (r4_q_pos hd.toIsChain).le
  have hR : R < 2 := hsmall.trans (stationary_sqrt_lt_two hd)
  have hq : R^2 < d.q := by
    have hh := FiveCornerGeometry.square_strict_mono_nonneg hfit.1 hsmall
    rwa [hsq] at hh
  have hceiling : R^2 ≤ Nominal.ceiling :=
    (hq.trans (stationary_q_lt_nominalCeiling hd)).le
  have ht := Nominal.tilt_localization hp hfit hceiling
  obtain ⟨hu, hF⟩ := scalar_reduction hp hfit hR
  have hqu : d.q < 4 := by linarith [hd.q_upper]
  have hdom := (FiveCornerGeometry.domain_radius_inclusion hq hqu hu).1
  have hn := stationary_defect_nonneg hd ht hdom
  obtain ⟨hc, hs, -⟩ := FiveCornerGeometry.tiltInterval_bounds ht
  have hdec := FiveCornerGeometry.defect_radius_decrease hq hqu hu
    hc (Real.cos_le_one _) hs.le (Real.sin_le_one _)
  linarith

theorem feasibleRadii_nonempty : feasibleRadii.Nonempty :=
  ⟨Real.sqrt sharpData.q, canonical, canonical_spans, canonical_fits⟩

theorem radius_eq_stationary : radius=Real.sqrt sharpData.q := by
  apply le_antisymm
  · exact csInf_le feasibleRadii_bddBelow
      (show Real.sqrt sharpData.q ∈ feasibleRadii from
        ⟨canonical, canonical_spans, canonical_fits⟩)
  · apply le_csInf feasibleRadii_nonempty
    rintro R ⟨p, hp, hfit⟩
    exact stationary_radius_le sharpData_stationary hp hfit

theorem radius_sq_eq_stationary : radius^2=ExactFamily.qStar := by
  rw [radius_eq_stationary, Real.sq_sqrt (r4_q_pos sharpData_stationary.toIsChain).le]
  rfl

theorem canonical_isMinimizer : canonical.IsMinimizer := by
  refine ⟨canonical_spans, ?_⟩
  rw [radius_eq_stationary]
  exact canonical_fits

theorem exists_minimizer : ∃ d : FiveCorner, d.IsMinimizer :=
  ⟨canonical, canonical_isMinimizer⟩

theorem radius_nonneg : 0 ≤ radius := canonical_isMinimizer.2.1

theorem radius_lt_two : radius < 2 := by
  rw [radius_eq_stationary]
  exact stationary_sqrt_lt_two sharpData_stationary

theorem three_halves_le_radius : (3/2:ℝ) ≤ radius :=
  three_halves_le canonical_isMinimizer.1 canonical_isMinimizer.2

theorem nine_quarters_le_radius_sq : (9/4:ℝ) ≤ radius^2 :=
  nine_quarters_le_sq canonical_isMinimizer.1 canonical_isMinimizer.2

theorem radius_pos : 0 < radius := by linarith [three_halves_le_radius]

/-- Equality of the envelope value supplies an actual local minimum,
so every minimizing source has the stationary tilt. -/
theorem stationary_angle_of_fits {d : Coordinates} (hd : d.IsStationary)
    {p : FiveCorner} (hp : p.spans) (hfit : p.fits (Real.sqrt d.q)) :
    p.angle=FiveCornerGeometry.coordinateAngle d := by
  have hsq := Real.sq_sqrt (r4_q_pos hd.toIsChain).le
  have hceiling : (Real.sqrt d.q)^2 ≤ Nominal.ceiling := by
    rw [hsq]
    exact (stationary_q_lt_nominalCeiling hd).le
  have ht := Nominal.tilt_localization hp hfit hceiling
  obtain ⟨hu, hF⟩ := scalar_reduction hp hfit (stationary_sqrt_lt_two hd)
  rw [hsq] at hu hF
  obtain ⟨hc, hs, htan⟩ := FiveCornerGeometry.tiltInterval_bounds ht
  have hmin := (FiveCornerGeometry.windowMinimizer_geometric hd.q_lower hd.q_upper
    hc hs.le (Real.cos_sq_add_sin_sq p.angle) htan.le).2.2.2 _ hu
  have hnonneg := FiveCornerGeometry.stationary_envelope_nonneg hd ⟨ht.1.le, ht.2.le⟩
  have henv : FiveCornerGeometry.positionEnvelope d.q p.angle=0 := by
    rw [FiveCornerGeometry.positionEnvelope_eq] at hnonneg ⊢
    linarith
  have hlocal : IsLocalMin (FiveCornerGeometry.positionEnvelope d.q) p.angle := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t ht'
    rw [henv]
    exact FiveCornerGeometry.stationary_envelope_nonneg hd ⟨ht'.1.le, ht'.2.le⟩
  exact FiveCornerGeometry.positionEnvelope_critical_unique hd.q_lower hd.q_upper ht
    (FiveCornerGeometry.stationary_angle_mem hd) hlocal.deriv_eq_zero
    (FiveCornerGeometry.stationary_envelope_critical hd)

/-- Split the width-three and width-(2+cos t) spans by zero-force
intermediate positions. These are formal positions, not extra squares. -/
def sourcePositions (d : Coordinates) (p : FiveCorner) : OriginalDual.Positions :=
  ![sub (p.point 0) (d.anchorOffsets 0),
    sub (p.point 1) (d.anchorOffsets 1),
    sub (p.point 2) (d.anchorOffsets 2),
    sub (p.point 3) (d.anchorOffsets 3),
    sub (p.point 4) (d.anchorOffsets 4),
    ((p.point 1).1-3/2,0),
    add (sub (p.point 4) (d.anchorOffsets 4)) d.e]

theorem sourcePositions_vertex (d : Coordinates) (p : FiveCorner) (i : Fin 5) :
    add (sourcePositions d p i.castSucc.castSucc) (d.anchorOffsets i)=p.point i := by
  fin_cases i <;> ext <;>
    simp [sourcePositions, Coordinates.anchorOffsets, add, sub]

theorem sourcePositions_gap (d : Coordinates) (p : FiveCorner) (i : Fin 7) :
    OriginalDual.gap d (sourcePositions d p) i =
      ![(p.point 1).2-(p.point 0).2-2,
        0,
        (p.point 1).1-(p.point 2).1-3,
        (p.point 2).2-(p.point 3).2-2,
        dot d.e (sub (p.point 0) (p.point 4))-2-d.c,
        0,
        dot d.f (sub (p.point 3) (p.point 4))-1-d.s] i := by
  fin_cases i <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', OriginalDual.gap, sourcePositions,
      Coordinates.anchorOffsets, Coordinates.e, Coordinates.f, Coordinates.inFrame, dot, add, sub,
      Fin.isValue, Matrix.cons_val]
  · ring
  · ring
  · ring
  · ring
  · linear_combination (-3/2:ℝ)*d.unit
  · linear_combination d.unit
  · linear_combination (-1/2:ℝ)*d.unit

theorem sourcePositions_gap_nonneg {d : Coordinates} {p : FiveCorner}
    (hp : p.spans) (ht : p.angle=FiveCornerGeometry.coordinateAngle d)
    (i : Fin 7) : 0 ≤ OriginalDual.gap d (sourcePositions d p) i := by
  have h := (spans_iff_spanBounds p).1 hp
  obtain ⟨hc, hs⟩ := FiveCornerGeometry.coordinateAngle_frame d
  have heh : 1+d.s ≤ dot d.f (sub (p.point 3) (p.point 4)) := by
    simpa [ht, coordinate_f, hs] using h.eh
  have hah : 2+d.c ≤ dot d.e (sub (p.point 0) (p.point 4)) := by
    simpa [ht, coordinate_e, hc] using h.ah
  rw [sourcePositions_gap]
  fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  · linarith [h.ab]
  · norm_num
  · linarith [h.bd]
  · linarith [h.de]
  · linarith
  · norm_num
  · linarith

/-- Positive original-point force completion fixes all five source points.
No conclusion about a canonical descendant is substituted for this claim. -/
theorem stationary_points_of_fits {d : Coordinates} (hd : d.IsStationary)
    {p : FiveCorner} (hp : p.spans) (hfit : p.fits (Real.sqrt d.q))
    (ht : p.angle=FiveCornerGeometry.coordinateAngle d) :
    p.point=d.anchorPoints := by
  have hvertices (i : Fin 5) :
      normSq (add (sourcePositions d p i.castSucc.castSucc) (d.anchorOffsets i)) ≤ d.q := by
    rw [sourcePositions_vertex]
    simpa [Real.sq_sqrt (r4_q_pos hd.toIsChain).le] using hfit.2 i
  have hrigid := (OriginalDual.original_centers_rigid hd.toIsChain hd.weightDomain
    hd.zero_defect hd.position_stationary hvertices (sourcePositions_gap_nonneg hp ht)).1
  funext i
  calc
    p.point i = add (sourcePositions d p i.castSucc.castSucc) (d.anchorOffsets i) :=
      (sourcePositions_vertex d p i).symm
    _ = add (d.anchorCenters i) (d.anchorOffsets i) := by rw [hrigid i]
    _ = d.anchorPoints i := d.anchor_vertex i

private theorem eq_of_angle_point {p q : FiveCorner}
    (ht : p.angle=q.angle) (hp : p.point=q.point) : p=q := by
  cases p
  cases q
  cases ht
  cases hp
  rfl

theorem minimizer_eq_canonical {p : FiveCorner} (hp : p.IsMinimizer) :
    p=canonical := by
  have hfit : p.fits (Real.sqrt sharpData.q) := by
    simpa [radius_eq_stationary] using hp.2
  have ht := stationary_angle_of_fits sharpData_stationary hp.1 hfit
  have hpoints := stationary_points_of_fits sharpData_stationary hp.1 hfit ht
  exact eq_of_angle_point ht hpoints

theorem existsUnique_minimizer : ∃! d : FiveCorner, d.IsMinimizer :=
  ⟨canonical, canonical_isMinimizer, fun _ h => minimizer_eq_canonical h⟩

theorem selected_isMinimizer : selected.IsMinimizer :=
  Classical.epsilon_spec exists_minimizer

theorem selected_eq_canonical : selected=canonical :=
  minimizer_eq_canonical selected_isMinimizer

theorem selected_eq_stationary : selected=ofCoordinates sharpData :=
  selected_eq_canonical

@[simp] theorem selected_angle :
    selected.angle=FiveCornerGeometry.coordinateAngle sharpData := by
  rw [selected_eq_canonical]
  rfl

@[simp] theorem selected_point : selected.point=sharpData.anchorPoints := by
  rw [selected_eq_canonical]
  rfl

theorem selected_spans : selected.spans := selected_isMinimizer.1
theorem selected_fits : selected.fits radius := selected_isMinimizer.2

/-- The old stationary equations describe exactly the naturally selected
minimum; their broad bracket is a proved adapter, not a model definition. -/
theorem isMinimizer_iff_stationary (p : FiveCorner) :
    p.IsMinimizer ↔ ∃ d : Coordinates, d.IsStationary ∧ p=ofCoordinates d := by
  constructor
  · intro hp
    exact ⟨sharpData, sharpData_stationary, minimizer_eq_canonical hp⟩
  · rintro ⟨d, hd, rfl⟩
    rw [ExactFamily.stationary_unique hd]
    exact canonical_isMinimizer

end SquaresInCircles.Eight.FiveCorner
