module

public import SquaresInCircles.Eight.Corners.Nominal
public import SquaresInCircles.Eight.ExactFamily.Envelope
public import SquaresInCircles.Eight.ExactFamily.Stationary
public import SquaresInCircles.Eight.ExactFamily.CenterCompletion

/-!
# Eight squares: existence of the stationary chain

The minimum `positionEnvelope q t` of the defect over the position window is continuous in
`(q, t)`, and so is its minimum `radiusEnvelope q` over the closed tilts, which is attained
(`radius_minimum`). It is positive at `lowerRadius` and negative at `upperRadius`
(`lower_radius_minimum_positive`, `upper_radius_minimum_negative`), so it vanishes at some `q`
between them (`radius_zero_exists`). At that radius the minimizing tilt is interior, since the
defect is positive at both ends of the tilt interval, and Fermat's rule gives the two stationary
equations: a stationary chain exists with `lowerRadius < q < upperRadius` (`stationary_exists`).
The stationary chain is unique (`stationary_chain_unique`), so every stationary chain has its
squared radius in that bracket (`stationary_radius_bounds`, `stationary_radius_strip`,
`stationary_radius_ceiling`).
-/

section
/-!
## The single circle stress at the existence boundaries

One algebraic square
completion bounds the nominal polynomial over its entire small-tilt
interval.  The same stress excludes the lower trial radius and both
geometric tilt endpoints.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GeometricExistence
open ExactFamily.FiveCornerGeometry Eight.FiveCorner

def lowerRadius : ℝ := 19577/5000
def upperRadius : ℝ := Nominal.ceiling
def closedTilts : Set ℝ := Icc 0 (Real.arctan (1/5))

theorem radius_order :
    (79/40:ℝ)^2<lowerRadius ∧ lowerRadius<upperRadius ∧ upperRadius<9789/2500 := by
  norm_num [lowerRadius,upperRadius,Nominal.ceiling]

theorem tilt_quarter {t : ℝ} (ht : t∈closedTilts) : t∈Icc 0 (Real.pi/4) := by
  have ha : Real.arctan (1/5:ℝ)<Real.pi/4 := by
    simpa only [Real.arctan_one] using Real.arctan_strictMono (show (1/5:ℝ)<1 by norm_num)
  exact ⟨ht.1,(lt_of_le_of_lt ht.2 ha).le⟩

theorem tilt_trig {t : ℝ} (ht : t∈closedTilts) :
    0<Real.cos t ∧ Real.sin t∈Icc 0 (1/5:ℝ) := by
  have ha := Real.arctan_lt_pi_div_two (1/5:ℝ)
  have hmem : t∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [ht.1,ht.2,Real.pi_pos]
  have hc := Real.cos_pos_of_mem_Ioo hmem
  have htan := Real.strictMonoOn_tan.monotoneOn hmem
    (Real.arctan_mem_Ioo (1/5:ℝ)) ht.2
  rw [Real.tan_arctan,Real.tan_eq_sin_div_cos] at htan
  have hsc := (div_le_iff₀ hc).mp htan
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [hmem.2,Real.pi_pos])
  exact ⟨hc,hs,by linarith [Real.cos_le_one t]⟩

theorem nominal_mass_gt_one {s : ℝ} (hs : s∈Icc 0 (1/5:ℝ)) :
    1<Nominal.massSum s := by
  have hswide : s∈Icc 0 (3/10:ℝ) := ⟨hs.1,by linarith [hs.2]⟩
  obtain ⟨hdA,hdB,hdD,hdH,hdE⟩ := Nominal.denominator_bounds hswide
  have hA : (1/4:ℝ)<Nominal.mA s := by
    dsimp [Nominal.mA]
    rw [lt_div_iff₀ hdA]
    linarith [hs.2]
  have hB : (1/4:ℝ)<Nominal.mB s := by
    dsimp [Nominal.mB]
    rw [lt_div_iff₀ hdB]
    linarith [hs.1]
  have hD : (1/4:ℝ)<Nominal.mD s := by
    dsimp [Nominal.mD]
    rw [lt_div_iff₀ hdD]
    linarith [hs.2]
  have hH : (1/4:ℝ)<Nominal.mH s := by
    dsimp [Nominal.mH]
    rw [lt_div_iff₀ hdH]
    linarith [hs.2]
  have hE : 0≤Nominal.mE s := Nominal.mass_nonneg hswide 3
  simp only [Nominal.massSum,Nominal.mass,Fin.sum_univ_five,Matrix.cons_val]
  linarith

/-- A single square completion on the whole interval.  The cubic
remainder is the exact divided Taylor remainder at 13/100. -/
theorem nominal_polynomial_lower {s : ℝ} (hs : s∈Icc 0 (1/5:ℝ)) :
    -(1/8000:ℝ)<Nominal.polynomial s := by
  let Q : ℝ := 1180373/5000000-(9541/100000)*s-(87/250)*s^2-(3/10)*s^3
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hs3 := pow_le_pow_left₀ hs.1 hs.2 3
  have hQ : 4/25≤Q := by
    dsimp [Q]
    nlinarith [hs.2]
  have hrem := mul_nonneg (sq_nonneg (s-13/100)) (sub_nonneg.mpr hQ)
  have hid : Nominal.polynomial s-
      (Nominal.polynomial (13/100)-(25/16)*Nominal.polynomialD (13/100)^2)=
      (4/25)*(s-13/100+(25/8)*Nominal.polynomialD (13/100))^2+
        (s-13/100)^2*(Q-4/25) := by
    dsimp [Nominal.polynomial,Nominal.polynomialD,Q]
    ring
  have hbase : -(1/8000:ℝ)<
      Nominal.polynomial (13/100)-(25/16)*Nominal.polynomialD (13/100)^2 := by
    norm_num [Nominal.polynomial,Nominal.polynomialD]
  nlinarith [sq_nonneg (s-13/100+(25/8)*Nominal.polynomialD (13/100))]

theorem lower_radius_gap_positive {t : ℝ} (ht : t∈closedTilts) :
    0<Nominal.gap lowerRadius t := by
  have hs := (tilt_trig ht).2
  have hswide : Real.sin t∈Icc 0 (3/10:ℝ) := ⟨hs.1,by linarith [hs.2]⟩
  have hpoly := Nominal.gap_ge_polynomial (q:=Nominal.ceiling) le_rfl (tilt_quarter ht) hswide
  have hlower := nominal_polynomial_lower hs
  have hmass := nominal_mass_gt_one hs
  have hdiff : 0<Nominal.ceiling-lowerRadius := by
    norm_num [Nominal.ceiling,lowerRadius]
  have hgain := mul_lt_mul_of_pos_left hmass hdiff
  rw [Nominal.gap_radius_identity lowerRadius Nominal.ceiling t]
  have hreserve : (1/8000:ℝ)<Nominal.ceiling-lowerRadius := by
    norm_num [Nominal.ceiling,lowerRadius]
  linarith

theorem zero_tilt_gap_positive {q : ℝ} (hq : q≤upperRadius) :
    0<Nominal.gap q 0 := by
  have hp := Nominal.gap_ge_polynomial hq
    (show (0:ℝ)∈Icc 0 (Real.pi/4) by exact ⟨le_rfl,by positivity⟩)
    (show Real.sin 0∈Icc 0 (3/10:ℝ) by norm_num)
  have hpos : 0<Nominal.polynomial (Real.sin 0) := by
    norm_num [Nominal.polynomial]
  linarith

theorem last_tilt_sine : (19/100:ℝ)<Real.sin (Real.arctan (1/5:ℝ)) := by
  have hp : 0<Real.sqrt (1+(1/5:ℝ)^2) := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt (1+(1/5:ℝ)^2)^2=1+(1/5:ℝ)^2 :=
    Real.sq_sqrt (by norm_num)
  have hu : Real.sqrt (1+(1/5:ℝ)^2)<20/19 := by nlinarith
  rw [Real.sin_arctan,lt_div_iff₀ hp]
  linarith

theorem last_tilt_gap_positive {q : ℝ} (hq : q≤upperRadius) :
    0<Nominal.gap q (Real.arctan (1/5)) := by
  have ht : Real.arctan (1/5:ℝ)∈closedTilts :=
    ⟨(Real.arctan_pos.mpr (by norm_num)).le,le_rfl⟩
  have hs := (tilt_trig ht).2
  have hswide : Real.sin (Real.arctan (1/5:ℝ))∈Icc 0 (3/10:ℝ) :=
    ⟨hs.1,by linarith [hs.2]⟩
  have hp := Nominal.gap_ge_polynomial hq (tilt_quarter ht) hswide
  have hpos := Nominal.polynomial_right_positive
    (show Real.sin (Real.arctan (1/5:ℝ))∈Icc (79/500:ℝ) (3/10) from
      ⟨by linarith [last_tilt_sine],hswide.2⟩)
  linarith

end SquaresInCircles.Eight.GeometricExistence
end
end
end

section
/-!
## The rational trial

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

open Set ExactFamily
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
end
end
end

section
/-!
## The radical chain as a chain of corners

For a squared radius `q`, a position `u` and a tilt `t`, `data q u t` is the chain of
`Coordinates` with the position `y = -u`, `z = tan (t/2)` and the corners at the square roots of
the radical chain (`lowerRight`, `topRight`, `topHeight`, `lowerLeft`). For `t ∈ closedTilts`
its angle is `t` and its defect is `defect q (cos t) (sin t) u` (`data_angle`, `data_defect`);
for `(79/40)² ≤ q ≤ 9789/2500` and `u` in the position window it is a chain (`data_chain`), the
four circle equations coming from the positive square roots. Its corners form a five-corner
configuration that spans (`circleModel_spans`) and, when the defect is nonpositive, fits in the
disk of radius `√q` (`circleModel_fits`), so that the circle stress of `Nominal` gives
`Nominal.gap q t ≤ 0` (`actual_gap_nonpos`). A common zero of the defect and of its derivatives
in the position and in the tilt, inside the window and the open tilt interval, satisfies the
stationary system `IsStationary` (`data_stationary`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GeometricExistence
open ExactFamily ExactFamily.FiveCornerGeometry Eight.FiveCorner

def data (q u t : ℝ) : Coordinates where
  q := q
  y := -u
  z := Real.tan (t/2)
  x₁ := lowerRight q u
  x₂ := topRight q u
  y₃ := topHeight q u
  x₄ := -lowerLeft q u

theorem data_angle {q u t : ℝ} (ht : t∈closedTilts) : coordinateAngle (data q u t)=t := by
  have hpi := Real.arctan_lt_pi_div_two (1/5:ℝ)
  have hl : -(Real.pi/2)<t/2 := by linarith [ht.1,Real.pi_pos]
  have hu : t/2<Real.pi/2 := by linarith [ht.2,Real.pi_pos]
  dsimp [coordinateAngle,data]
  rw [Real.arctan_tan hl hu]
  ring

theorem data_frame {q u t : ℝ} (ht : t∈closedTilts) :
    (data q u t).c=Real.cos t ∧ (data q u t).s=Real.sin t := by
  have hf := coordinateAngle_frame (data q u t)
  rw [data_angle ht] at hf
  exact ⟨hf.1.symm,hf.2.symm⟩

theorem data_x₃ (q u t : ℝ) : (data q u t).x₃= -topLeft q u := by
  dsimp [Coordinates.x₃,data,topLeft]
  ring

theorem data_y₄ (q u t : ℝ) : (data q u t).y₄= -lowerHeight q u := by
  dsimp [Coordinates.y₄,data,lowerHeight]
  ring

theorem data_components {q u t : ℝ} (ht : t∈closedTilts) :
    (data q u t).h₁= -firstComponent q (Real.cos t) (Real.sin t) u ∧
      (data q u t).h₂= -secondComponent q (Real.cos t) (Real.sin t) u := by
  obtain ⟨hc,hs⟩ := data_frame (q:=q) (u:=u) ht
  constructor
  · rw [Coordinates.h₁,hc,hs]
    dsimp [data,firstComponent]
    ring
  · rw [Coordinates.h₂,hc,hs,data_y₄]
    dsimp [data,secondComponent]
    ring

theorem data_defect {q u t : ℝ} (ht : t∈closedTilts) :
    (data q u t).defect=defect q (Real.cos t) (Real.sin t) u := by
  rw [Coordinates.defect,(data_components ht).1,(data_components ht).2]
  dsimp [data,defect]
  ring

theorem data_chain {q u t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500) (hu : u∈positionWindow) :
    (data q u t).IsChain := by
  have hb := window_bounds hql hqu hu
  have hA : lowerRight q u^2+u^2=q := upper_circle hb.domain.first_radicand
  have hB : topRight q u^2+(2-u)^2=q := upper_circle hb.domain.second_radicand
  have hD : topHeight q u^2+topLeft q u^2=q := upper_circle hb.domain.third_radicand
  have hE : lowerLeft q u^2+lowerHeight q u^2=q := upper_circle hb.domain.fourth_radicand
  refine ⟨by dsimp [data]; linarith [hb.r_lower],
    by dsimp [data]; linarith [hb.U_lower],
    by dsimp [data]; linarith [hb.Y_lower],
    by dsimp [data]; linarith [hb.w_lower],?_,?_,?_,?_⟩
  · dsimp [data]
    nlinarith
  · dsimp [data]
    nlinarith
  · rw [data_x₃]
    dsimp [data]
    nlinarith
  · rw [data_y₄]
    dsimp [data]
    nlinarith

def circleModel (q u t : ℝ) : Eight.FiveCorner := ofCoordinates (data q u t)

theorem circleModel_angle {q u t : ℝ} (ht : t∈closedTilts) :
    (circleModel q u t).angle=t := data_angle ht

theorem circleModel_spans {q u t : ℝ} (ht : t∈closedTilts) :
    (circleModel q u t).spans := by
  apply ofCoordinates_spans
  rw [data_angle ht]
  exact tilt_quarter ht

theorem circleModel_fits {q u t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500)
    (hu : u∈positionWindow) (ht : t∈closedTilts)
    (hF : defect q (Real.cos t) (Real.sin t) u≤0) :
    (circleModel q u t).fits (Real.sqrt q) := by
  have hc := data_chain (t:=t) hql hqu hu
  have hqp : 0≤q := by nlinarith
  have hlast : (data q u t).defect≤0 := by rw [data_defect ht]; exact hF
  refine ⟨Real.sqrt_nonneg _,fun i => ?_⟩
  rw [Real.sq_sqrt hqp]
  change normSq ((data q u t).anchorPoints i)≤q
  fin_cases i
  · simpa [Coordinates.anchorPoints,normSq,data] using hc.first_circle.le
  · simpa [Coordinates.anchorPoints,normSq,data] using hc.second_circle.le
  · simpa [Coordinates.anchorPoints,normSq,data] using hc.third_circle.le
  · simpa [Coordinates.anchorPoints,normSq,data] using hc.fourth_circle.le
  · change normSq ((data q u t).inFrame (data q u t).h₁ (data q u t).h₂)≤q
    rw [Coordinates.normSq_inFrame]
    have hq : (data q u t).q=q := rfl
    dsimp only [Coordinates.defect] at hlast
    linarith

/-- A nonpositive defect gives the five-point stress inequality `Nominal.gap q t ≤ 0`, also at
the tilt `0`, where the mass of E degenerates. -/
theorem actual_gap_nonpos {q u t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500)
    (hu : u∈positionWindow) (ht : t∈closedTilts)
    (hF : defect q (Real.cos t) (Real.sin t) u≤0) : Nominal.gap q t≤0 := by
  have hs : Real.sin (circleModel q u t).angle≤3/10 := by
    rw [circleModel_angle ht]
    linarith [(tilt_trig ht).2.2]
  have hg := Nominal.gap_nonpos_of_spans (circleModel_spans ht)
    (circleModel_fits hql hqu hu ht hF) hs
  rw [circleModel_angle ht,Real.sq_sqrt (by nlinarith : 0≤q)] at hg
  exact hg

/-- A common zero of the defect and of its derivatives in the position and in the tilt, for `u`
in the position window and `t` in the open tilt interval, satisfies the stationary system with
all its branch conditions. -/
theorem data_stationary {q u t : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500)
    (hu : u∈positionWindow) (ht : t∈tiltInterval)
    (hF : defect q (Real.cos t) (Real.sin t) u=0)
    (hP : positionHalf q (Real.cos t) (Real.sin t) u=0)
    (hT : tiltFirst q (Real.cos t) (Real.sin t) u=0) :
    (data q u t).IsStationary := by
  have htclosed : t∈closedTilts := ⟨ht.1.le,ht.2.le⟩
  obtain ⟨hc,hs,hratio⟩ := tiltInterval_bounds ht
  have hunit := Real.cos_sq_add_sin_sq t
  have hupper := window_critical_below_one hql hqu hc hs.le hunit hu hP hT
  have hstrip : CriticalStrip q u := ⟨hql,hqu,hu.1,hupper.le⟩
  have hb := hstrip.bounds
  have hchain := data_chain (t:=t) hql hqu hu
  have hhalf : t/2∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    have ha := Real.arctan_lt_pi_div_two (1/5:ℝ)
    constructor <;> linarith [ht.1,ht.2,Real.pi_pos]
  have hzpos : 0<(data q u t).z := by
    change 0<Real.tan (t/2)
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
      (by linarith [hhalf.2,Real.pi_pos])) (Real.cos_pos_of_mem_Ioo hhalf)
  have hzlt : (data q u t).z<1 := by
    apply Real.arctan_strictMono.lt_iff_lt.mp
    rw [Real.arctan_one]
    change Real.arctan (Real.tan (t/2))<Real.pi/4
    rw [Real.arctan_tan hhalf.1 hhalf.2]
    have ha := Real.arctan_lt_pi_div_two (1/5:ℝ)
    linarith [ht.2]
  have hzrange : 2*(data q u t).z/(1-(data q u t).z^2)<1/5 := by
    have hang : 2*Real.arctan (data q u t).z<Real.arctan (1/5) := by
      change coordinateAngle (data q u t)<Real.arctan (1/5)
      rw [data_angle htclosed]
      exact ht.2
    rw [Real.two_mul_arctan (by linarith : -1<(data q u t).z) hzlt] at hang
    exact Real.arctan_strictMono.lt_iff_lt.mp hang
  have hposzero : (data q u t).positionDerivative=0 := by
    have hcoord := coordinate_positionHalf hchain
    rw [(data_frame htclosed).1,(data_frame htclosed).2] at hcoord
    change 2*positionHalf q (Real.cos t) (Real.sin t) (-(-u))=
      -(data q u t).positionDerivative at hcoord
    rw [neg_neg,hP] at hcoord
    linarith
  have htiltzero : (data q u t).tiltDerivative=0 := by
    have hcoord := coordinate_tiltFirst hchain
    rw [(data_frame htclosed).1,(data_frame htclosed).2] at hcoord
    change tiltFirst q (Real.cos t) (Real.sin t) (-(-u))=
      (data q u t).tiltDerivative at hcoord
    rw [neg_neg,hT] at hcoord
    exact hcoord.symm
  refine ⟨hchain,hql,hqu,?_,?_,?_,?_,?_,hzpos,hzrange,hzlt,?_,hposzero,htiltzero⟩
  · change -1< -u
    linarith
  · change -u< -(1/2:ℝ)
    linarith [hu.1]
  · rw [data_y₄]
    linarith [hb.v_upper]
  · rw [data_y₄]
    linarith [hb.v_lower]
  · rw [data_y₄]
    change -u< -lowerHeight q u
    linarith [hu.1,hb.v_upper]
  · rw [data_defect htclosed]
    exact hF

end SquaresInCircles.Eight.GeometricExistence
end
end
end

section
/-!
## Boundary signs for the actual compact circle minimum

The nominal circle stress is applied to
the actual radical chain at every point of the fixed position window.
The rational trial supplies the opposite sign at the upper radius.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GeometricExistence
open ExactFamily.FiveCornerGeometry Eight.FiveCorner

theorem lower_radius_defect_positive {u t : ℝ}
    (hu : u∈positionWindow) (ht : t∈closedTilts) :
    0<defect lowerRadius (Real.cos t) (Real.sin t) u := by
  by_contra! hF
  have hg := actual_gap_nonpos radius_order.1.le
    (radius_order.2.1.le.trans radius_order.2.2.le) hu ht hF
  linarith [lower_radius_gap_positive ht]

theorem endpoint_defect_positive {q u : ℝ}
    (hq : q∈Icc lowerRadius upperRadius) (hu : u∈positionWindow) :
    0<defect q (Real.cos 0) (Real.sin 0) u ∧
      0<defect q (Real.cos (Real.arctan (1/5))) (Real.sin (Real.arctan (1/5))) u := by
  have hql : (79/40:ℝ)^2≤q := radius_order.1.le.trans hq.1
  have hqu : q≤9789/2500 := hq.2.trans radius_order.2.2.le
  have ha : 0<Real.arctan (1/5:ℝ) := Real.arctan_pos.mpr (by norm_num)
  constructor
  · by_contra! hF
    have hg := actual_gap_nonpos hql hqu hu (show (0:ℝ)∈closedTilts from ⟨le_rfl,ha.le⟩) hF
    linarith [zero_tilt_gap_positive hq.2]
  · by_contra! hF
    have hg := actual_gap_nonpos hql hqu hu
      (show Real.arctan (1/5:ℝ)∈closedTilts from ⟨ha.le,le_rfl⟩) hF
    linarith [last_tilt_gap_positive hq.2]

theorem lower_radius_positionEnvelope_positive {t : ℝ} (ht : t∈closedTilts) :
    0<positionEnvelope lowerRadius t := by
  rw [positionEnvelope_eq]
  exact lower_radius_defect_positive (windowMinimizer_mem _ _ _) ht

theorem endpoint_positionEnvelope_positive {q : ℝ}
    (hq : q∈Icc lowerRadius upperRadius) :
    0<positionEnvelope q 0 ∧ 0<positionEnvelope q (Real.arctan (1/5)) := by
  constructor
  · rw [positionEnvelope_eq]
    exact (endpoint_defect_positive hq (windowMinimizer_mem _ _ _)).1
  · rw [positionEnvelope_eq]
    exact (endpoint_defect_positive hq (windowMinimizer_mem _ _ _)).2

theorem upper_radius_positionEnvelope_negative :
    positionEnvelope upperRadius RationalTrial.angle<0 := by
  have hu : RationalTrial.height∈positionWindow := by
    norm_num [RationalTrial.height,positionWindow]
  have hm := windowMinimizer_le upperRadius (Real.cos RationalTrial.angle)
    (Real.sin RationalTrial.angle) hu
  rw [positionEnvelope_eq]
  exact lt_of_le_of_lt hm RationalTrial.defect_negative

end SquaresInCircles.Eight.GeometricExistence
end
end
end

section
/-!
## The natural five-corner minimum and its unique selected configuration

The global support estimates put every potentially
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

theorem three_halves_le_radius : (3/2:ℝ) ≤ radius :=
  three_halves_le canonical_isMinimizer.1 canonical_isMinimizer.2

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

end SquaresInCircles.Eight.FiveCorner
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GeometricExistence
open ExactFamily ExactFamily.FiveCornerGeometry Eight.FiveCorner

theorem closedTilts_nonempty : closedTilts.Nonempty :=
  ⟨0,le_rfl,(Real.arctan_pos.mpr (by norm_num : (0:ℝ)<1/5)).le⟩

theorem positionEnvelope_joint_continuous :
    Continuous (fun p : ℝ×ℝ => positionEnvelope p.1 p.2) := by
  change Continuous (fun p : ℝ×ℝ =>
    sInf ((fun u => defect p.1 (Real.cos p.2) (Real.sin p.2) u) '' positionWindow))
  apply (isCompact_Icc : IsCompact positionWindow).continuous_sInf
  dsimp [defect,firstComponent,secondComponent,lowerRight,lowerLeft,
    lowerHeight,topHeight,topLeft,topRight,upper]
  fun_prop

def radiusEnvelope (q : ℝ) : ℝ := sInf ((positionEnvelope q) '' closedTilts)

theorem radiusEnvelope_continuous : Continuous radiusEnvelope := by
  unfold radiusEnvelope
  apply (isCompact_Icc : IsCompact closedTilts).continuous_sInf
  exact positionEnvelope_joint_continuous

theorem radius_minimum (q : ℝ) :
    ∃t∈closedTilts, radiusEnvelope q=positionEnvelope q t ∧
      ∀s∈closedTilts,positionEnvelope q t≤positionEnvelope q s := by
  exact (isCompact_Icc : IsCompact closedTilts).exists_sInf_image_eq_and_le
    closedTilts_nonempty (positionEnvelope_continuous q).continuousOn

theorem lower_radius_minimum_positive : 0<radiusEnvelope lowerRadius := by
  obtain ⟨t,ht,he,_⟩ := radius_minimum lowerRadius
  rw [he]
  exact lower_radius_positionEnvelope_positive ht

theorem upper_radius_minimum_negative : radiusEnvelope upperRadius<0 := by
  obtain ⟨t,ht,he,hm⟩ := radius_minimum upperRadius
  have htrial : RationalTrial.angle∈closedTilts :=
    ⟨RationalTrial.angle_mem.1.le,RationalTrial.angle_mem.2.le⟩
  rw [he]
  exact lt_of_le_of_lt (hm _ htrial) upper_radius_positionEnvelope_negative

theorem radius_zero_exists :
    ∃q∈Ioo lowerRadius upperRadius,radiusEnvelope q=0 := by
  have hcont : ContinuousOn (fun q : ℝ => -radiusEnvelope q)
      (Icc lowerRadius upperRadius) := radiusEnvelope_continuous.neg.continuousOn
  obtain ⟨q,hq,hzero⟩ := intermediate_value_Icc radius_order.2.1.le hcont
    (show (0:ℝ)∈Icc (-radiusEnvelope lowerRadius) (-radiusEnvelope upperRadius) from
      ⟨by linarith [lower_radius_minimum_positive],by linarith [upper_radius_minimum_negative]⟩)
  have hz : radiusEnvelope q=0 := by linarith
  have hql : lowerRadius<q := by
    by_contra! hbad
    have he : q=lowerRadius := le_antisymm hbad hq.1
    rw [he] at hz
    linarith [lower_radius_minimum_positive]
  have hqu : q<upperRadius := by
    by_contra! hbad
    have he : q=upperRadius := le_antisymm hq.2 hbad
    rw [he] at hz
    linarith [upper_radius_minimum_negative]
  exact ⟨q,⟨hql,hqu⟩,hz⟩

/-- A stationary chain exists with `lowerRadius < q < upperRadius`: the minimum of the defect at
the radius where `radiusEnvelope` vanishes. -/
theorem stationary_exists :
    ∃d : Coordinates,d.IsStationary ∧ lowerRadius<d.q ∧ d.q<upperRadius := by
  obtain ⟨q,hq,hzero⟩ := radius_zero_exists
  obtain ⟨t,ht,he,hm⟩ := radius_minimum q
  have hM : positionEnvelope q t=0 := by linarith
  have hqclosed : q∈Icc lowerRadius upperRadius := ⟨hq.1.le,hq.2.le⟩
  have hend := endpoint_positionEnvelope_positive hqclosed
  have htl : 0<t := by
    by_contra! hbad
    have htzero : t=0 := le_antisymm hbad ht.1
    rw [htzero] at hM
    linarith [hend.1]
  have htu : t<Real.arctan (1/5) := by
    by_contra! hbad
    have htlast : t=Real.arctan (1/5) := le_antisymm ht.2 hbad
    rw [htlast] at hM
    linarith [hend.2]
  have htilt : t∈tiltInterval := ⟨htl,htu⟩
  have hql : (79/40:ℝ)^2≤q := radius_order.1.le.trans hq.1.le
  have hqu : q≤9789/2500 := hq.2.le.trans radius_order.2.2.le
  let u := minimizingPosition q t
  have hu : u∈positionWindow := windowMinimizer_mem q (Real.cos t) (Real.sin t)
  have hF : defect q (Real.cos t) (Real.sin t) u=0 := by
    rw [positionEnvelope_eq] at hM
    exact hM
  have hP : positionHalf q (Real.cos t) (Real.sin t) u=0 := by
    have hp := minimizingPosition_root hql hqu htilt
    change 2*positionHalf q (Real.cos t) (Real.sin t) u=0 at hp
    linarith
  have hmin : IsMinOn (positionEnvelope q) closedTilts t := by
    intro s hs
    exact hm s hs
  have hT : tiltFirst q (Real.cos t) (Real.sin t) u=0 :=
    (hmin.isLocalMin (Icc_mem_nhds htl htu)).hasDerivAt_eq_zero
      (positionEnvelope_hasDerivAt hql hqu htilt)
  exact ⟨data q u t,data_stationary hql hqu hu htilt hF hP hT,hq.1,hq.2⟩

/-- The stationary chain of `stationary_exists`. -/
def stationaryDatum : Coordinates := Classical.choose stationary_exists

theorem stationaryDatum_stationary : stationaryDatum.IsStationary :=
  (Classical.choose_spec stationary_exists).1

theorem stationaryDatum_radius : lowerRadius<stationaryDatum.q ∧
    stationaryDatum.q<upperRadius := (Classical.choose_spec stationary_exists).2

theorem stationaryDatum_unique {d : Coordinates} (hd : d.IsStationary) :
    d=stationaryDatum := stationary_chain_unique hd stationaryDatum_stationary

/-- Every stationary chain has `lowerRadius < q < upperRadius`, since it is the chain of
`stationary_exists`. -/
theorem stationary_radius_bounds {d : Coordinates} (hd : d.IsStationary) :
    lowerRadius<d.q ∧ d.q<upperRadius := by
  rw [stationaryDatum_unique hd]
  exact stationaryDatum_radius

theorem stationary_radius_strip {d : Coordinates} (hd : d.IsStationary) :
    d.q∈Icc (19577/5000:ℝ) (9789/2500) := by
  have hq := stationary_radius_bounds hd
  exact ⟨hq.1.le,hq.2.le.trans radius_order.2.2.le⟩

theorem stationary_radius_ceiling {d : Coordinates} (hd : d.IsStationary) :
    d.q<Nominal.ceiling := (stationary_radius_bounds hd).2

end SquaresInCircles.Eight.GeometricExistence
end
end
end
