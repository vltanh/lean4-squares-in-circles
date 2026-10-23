module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2CoefficientBounds

/-!
# Actual trigonometric coefficient ranges for the negative-A stress

Uncompiled transcription of equations (12)--(14) and (27)--(36) in the
scalar companion. Polynomial bounds are transferred to the actual
tilted BT multiplier, including the low secant-weight comparison and
the restricted high-interval comparisons at the original angle cuts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Explicit
open Candidate Secondary Polynomial
open Certificate (Family)

theorem tilted_bounds (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    0<aeval z (Certificate.mLo f) ∧ aeval z (Certificate.mLo f)≤m f z ∧
      m f z≤aeval z (Certificate.mHi f) := by
  have hh := PositiveTD.Certificate.tilted_polynomial_bounds
    (c:=Certificate.c f) (family_frame_domain f hz)
    (by simpa using (family_positive f hz).2.2.1)
  simpa [Certificate.mLo,Certificate.mHi,m] using hh

theorem coarse_tilted_lower (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    aeval z (Certificate.mCoarse f)≤m f z := by
  have hz0 := (family_frame_domain f hz).1
  have hc := (family_positive f hz).2.2.1
  have hs := Real.sin_ge_sub_cube hz0
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hbase : 1-z^2/2+(293/1000)*(z-z^3/6)≤
      Real.cos z+(293/1000)*Real.sin z := by linarith
  have hh := mul_le_mul_of_nonneg_left hbase hc.le
  norm_num [Certificate.mCoarse,Certificate.C2,Certificate.S3,
    PositiveTD.Certificate.etaQ,m,PositiveTD.tilted,PositiveTD.eta] at ⊢
  nlinarith only [hh]

theorem low_tilted {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    l .low z<m .low z ∧ m .low z<(71/50)*l .low z := by
  have hpoly := Certificate.coarse_low_positive .tilted hz
  have hcoarse := coarse_tilted_lower .low hz
  have hupper := Certificate.comparison_positive .lowMUpper hz
  have hb := (tilted_bounds .low hz).2.2
  norm_num [Certificate.coarseLowPolynomial] at hpoly
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hupper
  exact ⟨by linarith,by linarith⟩

theorem AB_cut_cosine {s : ℝ} (hs : s∈Icc 0 (19/50:ℝ)) :
    (4643/5000:ℝ)<Real.cos s := by
  have hh := trig_bracket (l:=(0:ℝ)) (u:=(19/50:ℝ)) (x:=s)
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  norm_num at hh
  linarith [hh.2.2.1]

theorem GA_cut_cosine {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    (9689/10000:ℝ)<Real.cos s := by
  have hh := trig_bracket (l:=(0:ℝ)) (u:=(1/4:ℝ)) (x:=s)
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  norm_num at hh
  linarith [hh.2.2.1]

theorem low_secant {z s : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 (19/50:ℝ)) : l .low z/Real.cos s<m .low z+(2/5)*z := by
  have hpoly := Certificate.coarse_low_positive .secant hz
  have hcoarse := coarse_tilted_lower .low hz
  have hcos := AB_cut_cosine hs
  have hm : 0<m .low z+(2/5)*z := by
    have hpos := (family_positive .low hz).2.2.2
    nlinarith [hz.1]
  have h0 : 0<Real.cos s := by linarith
  apply (div_lt_iff₀ h0).2
  have hp := mul_lt_mul_of_pos_right hcos hm
  norm_num [Certificate.coarseLowPolynomial] at hpoly
  nlinarith

theorem high_tilted {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    (77/100)*l .high z<m .high z ∧ m .high z<(129/125)*l .high z ∧
      k .high z<(41/50)*l .high z := by
  have hlo := Certificate.coarse_high_positive hz
  have hcoarse := coarse_tilted_lower .high hz
  have hupper := Certificate.comparison_positive .highMUpper hz
  have hkupper := Certificate.comparison_positive .highKUpper hz
  have hb := (tilted_bounds .high hz).2.2
  norm_num [Certificate.coarseHighDifference] at hlo
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hupper hkupper
  exact ⟨by linarith,by linarith,by linarith⟩

theorem high_tilted_quarter {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    m .high z<l .high z := by
  have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := ⟨by linarith [hz.1],hz.2⟩
  have hh := Certificate.comparison_positive .highMQuarter hz
  have hb := (tilted_bounds .high hz').2.2
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hh
  linarith

theorem high_tilted_three_tenths {z : ℝ} (hz : z∈Icc (3/10:ℝ) (7/10:ℝ)) :
    m .high z<(47/50)*l .high z := by
  have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := ⟨by linarith [hz.1],hz.2⟩
  have hh := Certificate.comparison_positive .highMThreeTenths hz
  have hb := (tilted_bounds .high hz').2.2
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hh
  linarith

theorem high_tilted_third {z : ℝ} (hz : z∈Icc (1/3:ℝ) (7/10:ℝ)) :
    m .high z<(23/25)*l .high z := by
  have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := ⟨by linarith [hz.1],hz.2⟩
  have hh := Certificate.comparison_positive .highMThird hz
  have hb := (tilted_bounds .high hz').2.2
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hh
  linarith

theorem high_tilted_lower_to_AB_cut {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (19/50:ℝ)) : (4/5)*l .high z<m .high z := by
  have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := ⟨hz.1,by linarith [hz.2]⟩
  have hh := Certificate.comparison_positive .highMLower hz
  have hb := (tilted_bounds .high hz').2.1
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hh
  linarith

theorem high_tilted_envelope {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    max (l .high z) (m .high z)≤l .high z+(3/100)*(frameCap-z) := by
  have hh := Certificate.comparison_positive .highMEnvelope hz
  have hb := (tilted_bounds .high hz).2.2
  norm_num [Certificate.comparison,Certificate.comparisonReserve,Certificate.qStar,
    PositiveTD.Certificate.h] at hh
  dsimp [frameCap]
  apply max_le
  · linarith [hz.2]
  · linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Explicit
