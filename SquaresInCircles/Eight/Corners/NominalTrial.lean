module

public import SquaresInCircles.Eight.Corners.Nominal

/-!
# Eight squares: the rational trial

A chain gives a five-corner configuration (`ofCoordinates`) with tight contacts
(`coordinate_contacts`); it spans for a tilt in `[0, π/4]` (`ofCoordinates_spans`) and fits in
the disk of radius `√q` when its defect vanishes (`ofCoordinates_fits`). A stationary chain has a
nonnegative defect at every position of the radical domain and every tilt of the tilt interval
(`stationary_defect_nonneg`), by the envelope theorem
`FiveCornerGeometry.stationary_envelope_nonneg`.

The rational trial `RationalTrial.chain`, at the squared radius `Nominal.ceiling`, has its five
corners strictly inside the circle (`RationalTrial.strict_circles`), so the defect at its
position and tilt is negative (`RationalTrial.defect_negative`). Since the defect decreases as
the radius grows, every stationary chain has `q < Nominal.ceiling`
(`stationary_q_lt_nominalCeiling`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.FiveCorner
open GeometricModel

open Set Stationary
open Scalar

def ofCoordinates (d : Coordinates) : FiveCorner where
  angle := FiveCornerGeometry.coordinateAngle d
  point := d.anchorPoints

theorem coordinate_e (d : Coordinates) :
    GeometricModel.e (FiveCornerGeometry.coordinateAngle d)=d.e := by
  obtain ⟨hc, hs⟩ := FiveCornerGeometry.coordinateAngle_frame d
  ext <;> simp [GeometricModel.e, Coordinates.e, hc, hs]

theorem coordinate_f (d : Coordinates) :
    GeometricModel.f (FiveCornerGeometry.coordinateAngle d)=d.f := by
  obtain ⟨hc, hs⟩ := FiveCornerGeometry.coordinateAngle_frame d
  ext <;> simp [GeometricModel.f, Coordinates.f, hc, hs]

theorem coordinate_contacts (d : Coordinates) :
    (d.anchorPoints 1).2-(d.anchorPoints 0).2=2 ∧
    (d.anchorPoints 1).1-(d.anchorPoints 2).1=3 ∧
    (d.anchorPoints 2).2-(d.anchorPoints 3).2=2 ∧
    dot d.f (sub (d.anchorPoints 3) (d.anchorPoints 4))=1+d.s ∧
    dot d.e (sub (d.anchorPoints 0) (d.anchorPoints 4))=2+d.c := by
  have h4 : d.anchorPoints 4 = d.inFrame d.h₁ d.h₂ := rfl
  constructor
  · simp [Coordinates.anchorPoints]
  constructor
  · simp [Coordinates.anchorPoints, Coordinates.x₃]
  constructor
  · simp [Coordinates.anchorPoints, Coordinates.y₄]
  constructor
  · rw [dot_sub_right, h4, Coordinates.dot_f_inFrame]
    simp only [Coordinates.anchorPoints, Matrix.cons_val, dot, Coordinates.f,
      Coordinates.h₂]
    ring
  · rw [dot_sub_right, h4, Coordinates.dot_e_inFrame]
    simp only [Coordinates.anchorPoints, Matrix.cons_val, dot, Coordinates.e,
      Coordinates.h₁]
    ring

theorem ofCoordinates_spans (d : Coordinates)
    (ht : FiveCornerGeometry.coordinateAngle d ∈ Icc 0 (Real.pi/4)) :
    (ofCoordinates d).spans := by
  obtain ⟨hab, hbd, hde, heh, hah⟩ := coordinate_contacts d
  obtain ⟨hc, hs⟩ := FiveCornerGeometry.coordinateAngle_frame d
  apply (spans_iff_spanBounds _).2
  refine ⟨ht.1, ht.2, hab.ge, hbd.ge, hde.ge, ?_, ?_⟩
  · simpa [ofCoordinates, coordinate_f, hs] using heh.ge
  · simpa [ofCoordinates, coordinate_e, hc] using hah.ge

theorem ofCoordinates_fits {d : Coordinates} (hd : d.IsChain)
    (hzero : d.defect=0) : (ofCoordinates d).fits (Real.sqrt d.q) := by
  have hq : 0 ≤ d.q := by
    rw [← hd.first_circle]
    positivity
  refine ⟨Real.sqrt_nonneg _, fun i => ?_⟩
  rw [Real.sq_sqrt hq]
  exact (Coordinates.anchor_circle hd hzero i).le

theorem small_tilt_subset_quarter :
    Icc (0:ℝ) (Real.arctan (1/5)) ⊆ Icc 0 (Real.pi/4) := by
  have hα : Real.arctan (1/5:ℝ) < Real.pi/4 := by
    simpa only [Real.arctan_one] using
      Real.arctan_strictMono (show (1/5:ℝ) < 1 by norm_num)
  exact Icc_subset_Icc le_rfl hα.le

/-- At a stationary chain the defect is nonnegative at every position of the radical domain and
every tilt of the tilt interval. -/
theorem stationary_defect_nonneg {d : Coordinates} (hd : d.IsStationary)
    {t u : ℝ} (ht : t ∈ FiveCornerGeometry.tiltInterval) (hu : Domain d.q u) :
    0 ≤ defect d.q (Real.cos t) (Real.sin t) u := by
  obtain ⟨hc, hs, htan⟩ := FiveCornerGeometry.tiltInterval_bounds ht
  have hnonneg := FiveCornerGeometry.stationary_envelope_nonneg hd ⟨ht.1.le, ht.2.le⟩
  have hmin := (FiveCornerGeometry.windowMinimizer_geometric
    hd.q_lower hd.q_upper hc hs.le (Real.cos_sq_add_sin_sq t) htan.le).2.2.2 u hu
  rw [FiveCornerGeometry.positionEnvelope_eq] at hnonneg
  exact hnonneg.trans hmin

namespace RationalTrial

def data : Coordinates where
  q := Nominal.ceiling
  y := -920656678000/1000000000000
  z := 61897411/1000000000
  x₁ := 1751549433859/1000000000000
  x₂ := 1658478860659/1000000000000
  y₃ := 1454597941254/1000000000000
  x₄ := -1902122691183/1000000000000

def chain : FiveCorner := ofCoordinates data
def angle : ℝ := FiveCornerGeometry.coordinateAngle data
def height : ℝ := 920656678000/1000000000000

theorem angle_mem : angle ∈ FiveCornerGeometry.tiltInterval := by
  have hz : 0 < data.z := by norm_num [data]
  have hz₁ : data.z < 1 := by norm_num [data]
  have hratio : 2*data.z/(1-data.z^2) < 1/5 := by norm_num [data]
  have hpos := Real.arctan_pos.mpr hz
  have htwo := Real.two_mul_arctan (by linarith : -1 < data.z) hz₁
  change 0 < 2*Real.arctan data.z ∧
    2*Real.arctan data.z < Real.arctan (1/5)
  constructor
  · linarith
  · rw [htwo]
    exact Real.arctan_strictMono hratio

theorem spans : chain.spans :=
  ofCoordinates_spans data (small_tilt_subset_quarter ⟨angle_mem.1.le, angle_mem.2.le⟩)

/-- The five corners of the trial lie strictly inside the circle of squared radius
`Nominal.ceiling`. -/
theorem strict_circles (i : Fin 5) : normSq (chain.point i) < Nominal.ceiling := by
  fin_cases i
  · norm_num [chain, ofCoordinates, Coordinates.anchorPoints, data, normSq, Nominal.ceiling]
  · norm_num [chain, ofCoordinates, Coordinates.anchorPoints, data, normSq, Nominal.ceiling]
  · norm_num [chain, ofCoordinates, Coordinates.anchorPoints, Coordinates.x₃,
      data, normSq, Nominal.ceiling]
  · norm_num [chain, ofCoordinates, Coordinates.anchorPoints, Coordinates.y₄,
      data, normSq, Nominal.ceiling]
  · change normSq (data.inFrame data.h₁ data.h₂) < Nominal.ceiling
    rw [Coordinates.normSq_inFrame]
    norm_num [data, Coordinates.h₁, Coordinates.h₂, Coordinates.y₄, Coordinates.c,
      Coordinates.s, halfAngleCos, halfAngleSin, Nominal.ceiling]

theorem fits : chain.fits (Real.sqrt Nominal.ceiling) := by
  refine ⟨Real.sqrt_nonneg _, fun i => ?_⟩
  rw [Real.sq_sqrt (by norm_num [Nominal.ceiling])]
  exact (strict_circles i).le

private theorem chain_height : -(chain.point 0).2 = height := by
  change -(-920656678000/1000000000000 : ℝ) = 920656678000/1000000000000
  norm_num

private theorem sqrt_ceiling_lt_two : Real.sqrt Nominal.ceiling < 2 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num [Nominal.ceiling])

theorem domain : Domain Nominal.ceiling height := by
  have hR : Real.sqrt Nominal.ceiling < 2 := sqrt_ceiling_lt_two
  have h := radial_domain_of_spans spans fits hR
  rwa [Real.sq_sqrt (show 0 ≤ Nominal.ceiling by norm_num [Nominal.ceiling]),
    chain_height] at h

theorem defect_negative :
    defect Nominal.ceiling (Real.cos angle) (Real.sin angle) height < 0 := by
  have hR : Real.sqrt Nominal.ceiling < 2 := sqrt_ceiling_lt_two
  have h := defect_le_last_corner spans fits hR
  have he : (Real.sqrt Nominal.ceiling)^2=Nominal.ceiling :=
    Real.sq_sqrt (by norm_num [Nominal.ceiling])
  rw [he, chain_height] at h
  have h' : defect Nominal.ceiling (Real.cos angle) (Real.sin angle) height ≤
      normSq (chain.point 4)-Nominal.ceiling := h
  linarith [strict_circles 4]

end RationalTrial

/-- Every stationary chain has `q < Nominal.ceiling`: at a radius at least `Nominal.ceiling` its
defect would be negative at the position and the tilt of the trial, against
`stationary_defect_nonneg`. -/
theorem stationary_q_lt_nominalCeiling {d : Coordinates} (hd : d.IsStationary) :
    d.q < Nominal.ceiling := by
  by_contra! hq
  rcases eq_or_lt_of_le hq with he | hlt
  · have hdom : Domain d.q RationalTrial.height := he ▸ RationalTrial.domain
    have hn := stationary_defect_nonneg hd RationalTrial.angle_mem hdom
    rw [← he] at hn
    linarith [RationalTrial.defect_negative]
  · have hqu : d.q < 4 := by linarith [hd.q_upper]
    have hdom := (FiveCornerGeometry.domain_radius_inclusion hlt hqu RationalTrial.domain).1
    have hn := stationary_defect_nonneg hd RationalTrial.angle_mem hdom
    obtain ⟨hc, hs, -⟩ := FiveCornerGeometry.tiltInterval_bounds RationalTrial.angle_mem
    have hdec := FiveCornerGeometry.defect_radius_decrease hlt hqu RationalTrial.domain
      hc (Real.cos_le_one _) hs.le (Real.sin_le_one _)
    linarith [RationalTrial.defect_negative]

end SquaresInCircles.Eight.FiveCorner
