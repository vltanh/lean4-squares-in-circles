module

public import SquaresInCircles.Eight.Owners.Positive.PrimaryBaselines
public import SquaresInCircles.Eight.Owners.Positive.StressCoefficients

/-!
# Eight squares: comparing the two positive T baselines and the split endpoints

The comparison rationalizes two square-root increments (`norm_increment_comparison`). It decides
which endpoint of the split gives the baseline `familyPBaseline` (`td_endpoint_comparison`,
`familyP_endpoint_le`, `familyP_bt_ge_td`); concavity in the split is proved separately.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveSplitComparison
open PositiveAngularEnvelope PositivePrimaryBaselines SecondaryEStress

/-- Increasing the second coordinate increases the norm more when the first coordinate is smaller;
the increments themselves are compared. -/
theorem norm_increment_comparison {l k m : ℝ}
    (hl : 0≤l) (hl1 : l≤1) (hk : 0<k) (hkm : k≤ m) :
    Real.sqrt (1+m^2)-Real.sqrt (1+k^2)≤
      Real.sqrt (l^2+m^2)-Real.sqrt (l^2+k^2) := by
  have hm : 0≤m := hk.le.trans hkm
  have hl2 : l^2≤1 := by nlinarith
  have hkm2 : k^2≤m^2 := pow_le_pow_left₀ hk.le hkm 2
  have hLM : 0≤l^2+m^2 := by positivity
  have hLK : 0<l^2+k^2 := by positivity
  have h1M : 0≤1+m^2 := by positivity
  have h1K : 0≤1+k^2 := by positivity
  have hA := Real.sq_sqrt hLM
  have hB := Real.sq_sqrt hLK.le
  have hC := Real.sq_sqrt h1M
  have hD := Real.sq_sqrt h1K
  have hAC : Real.sqrt (l^2+m^2)≤Real.sqrt (1+m^2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hBD : Real.sqrt (l^2+k^2)≤Real.sqrt (1+k^2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hDC : Real.sqrt (1+k^2)≤Real.sqrt (1+m^2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsum : Real.sqrt (l^2+m^2)+Real.sqrt (l^2+k^2)≤
      Real.sqrt (1+m^2)+Real.sqrt (1+k^2) := add_le_add hAC hBD
  have hprod := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hDC)
  have hsumpos : 0<Real.sqrt (l^2+m^2)+Real.sqrt (l^2+k^2) :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr hLK)
  apply le_of_mul_le_mul_right _ hsumpos
  linarith

theorem btBaseline_ge_tdBaseline {R k l η x z : ℝ}
    (hR : 0≤R) (hl : 0≤l) (hl1 : l≤1) (hk : 0<k)
    (hm : k≤tiltedWeight k η z) :
    tdBaseline R k l η x z≤btBaseline R k l η x z := by
  have h := mul_le_mul_of_nonneg_left (norm_increment_comparison hl hl1 hk hm) hR
  simp only [tdBaseline,btBaseline,zeroNorms,pairNorm_zero,one_pow]
  nlinarith

/-- With `x + z = d`, the endpoint `x = 0`, `z = d` has the smaller baseline. -/
theorem td_endpoint_comparison {R k l η d : ℝ}
    (hR : 0≤R) (hl : 0≤l) (hl1 : l≤1) (hk : 0<k)
    (hn : k≤tiltedWeight k η d) :
    tdBaseline R k l η 0 d≤tdBaseline R k l η d 0 := by
  have h := mul_le_mul_of_nonneg_left (norm_increment_comparison hl hl1 hk hn) hR
  have hsym : Real.sqrt (k^2+l^2)=Real.sqrt (l^2+k^2) := by congr 1; ring
  simp only [tdBaseline,zeroNorms,pairNorm_zero,one_pow,
    tiltedWeight,Real.cos_zero,Real.sin_zero,mul_zero,add_zero,mul_one] at *
  rw [hsym]
  nlinarith

def familyPBaseline (d : ℝ) : ℝ :=
  tdBaseline (Real.sqrt qCap) PositiveStressCoefficients.k
    (PositiveStressCoefficients.lP d) (PositiveStressCoefficients.etaP d) 0 d

theorem familyP_endpoint_le {d : ℝ} (hd : d∈Icc 0 frameCap) :
    familyPBaseline d≤
      tdBaseline (Real.sqrt qCap) PositiveStressCoefficients.k
        (PositiveStressCoefficients.lP d) (PositiveStressCoefficients.etaP d) d 0 := by
  have hb := PositiveStressCoefficients.coefficient_bounds hd
  apply td_endpoint_comparison (Real.sqrt_nonneg _) (by linarith [hb.1])
    (by have := hb.2.1; norm_num [PositiveStressCoefficients.k] at this; linarith)
    (by norm_num [PositiveStressCoefficients.k])
  exact (PositiveStressCoefficients.tiltedWeight_bounds hd ⟨hd.1,le_rfl⟩).1

theorem familyP_bt_ge_td {d x z : ℝ} (hd : d∈Icc 0 frameCap)
    (hz : z∈Icc 0 d) :
    tdBaseline (Real.sqrt qCap) PositiveStressCoefficients.k
      (PositiveStressCoefficients.lP d) (PositiveStressCoefficients.etaP d) x z≤
    btBaseline (Real.sqrt qCap) PositiveStressCoefficients.k
      (PositiveStressCoefficients.lP d) (PositiveStressCoefficients.etaP d) x z := by
  have hb := PositiveStressCoefficients.coefficient_bounds hd
  exact btBaseline_ge_tdBaseline (Real.sqrt_nonneg _) (by linarith [hb.1])
    (by have := hb.2.1; norm_num [PositiveStressCoefficients.k] at this; linarith)
    (by norm_num [PositiveStressCoefficients.k])
    (PositiveStressCoefficients.tiltedWeight_bounds hd hz).1

end SquaresInCircles.Eight.PositiveSplitComparison
