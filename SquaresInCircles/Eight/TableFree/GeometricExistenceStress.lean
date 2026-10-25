module

public import SquaresInCircles.Eight.GeometricModel.FiveCornerNominal

/-!
# The single circle stress at the existence boundaries

Uncompiled reconstruction of Section 3 of
HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md.  One algebraic square
completion bounds the nominal polynomial over its entire small-tilt
interval.  The same stress excludes the lower trial radius and both
geometric tilt endpoints.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GeometricExistence
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

end SquaresInCircles.Eight.TableFree.GeometricExistence
