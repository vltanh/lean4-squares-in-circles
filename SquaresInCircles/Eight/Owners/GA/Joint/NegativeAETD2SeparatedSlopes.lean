module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2BlockBounds

/-!
# Eight squares: the remaining unit-pair chord reserve

The low row uses the actual chord from 0.15 to the angular cap and
concavity on the entire interval to extend that chord to every smaller
left endpoint. The high rows use the uniform 0.64 derivative reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.BlockBounds
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope OrdinaryNegativeSlope
open Certificate (Row)

theorem low_V_cap : (611/1000:ℝ)<V R (13/20) 1 frameCap := by
  have hN := pairNorm_pos (p:=(13/20:ℝ)) (q:=1) (t:=-frameCap)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p:=(13/20:ℝ)) (q:=1) (t:=-frameCap)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hZ := pairNorm_pos (p:=(13/20:ℝ)) (q:=1) (t:=0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hZ2 := pairNorm_sq (p:=(13/20:ℝ)) (q:=1) (t:=0)
    (by norm_num) (by norm_num) (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_neg,Real.sin_zero] at hN2 hZ2
  have hZlo : (5963/5000:ℝ)<pairNorm (13/20) 1 0 := by nlinarith
  have hNhi : pairNorm (13/20) 1 (-frameCap)<7649/10000 := by
    nlinarith [cap_sin_lower]
  have hgap : (4277/10000:ℝ)<pairNorm (13/20) 1 0-pairNorm (13/20) 1 (-frameCap) := by
    linarith
  have hprod := mul_lt_mul_of_pos_left hgap (by norm_num : (0:ℝ)<19787/10000)
  have hR := mul_lt_mul_of_pos_right sqrt_cap_lower
    (show 0<pairNorm (13/20) 1 0-pairNorm (13/20) 1 (-frameCap) by linarith)
  have hc := (transport_trig (show frameCap∈Icc 0 frameCap from
    ⟨by norm_num [frameCap],le_rfl⟩)).1
  dsimp [V]
  nlinarith

theorem low_V_short : V R (13/20) 1 (3/20)<81/500 := by
  have hs : (5963/5000:ℝ)<shape (13/20) := by
    nlinarith [shape_sq (13/20:ℝ),shape_pos (13/20:ℝ)]
  have hd : Vd R (13/20) 1 0<27/25 := by
    rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
    simp only [Real.sin_zero,Real.cos_zero,div_one,neg_zero,zero_add,mul_one,one_mul,
      VaryingBFunctions.root_zero]
    apply (div_lt_iff₀ (shape_pos _)).2
    linarith [Secondary.radius_bounds.2]
  have ht := V_tangent_zero (p:=(13/20:ℝ)) (q:=1)
    (by norm_num) (by norm_num) (by norm_num)
    (show (3/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  linarith

theorem low_unit_chord {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    (4/5)*(frameCap-z)<V R (13/20) 1 frameCap-V R (13/20) 1 z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩
  have hcapIcc : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hconc := V_concave (R:=R) (p:=(13/20:ℝ)) (q:=1)
    (Real.sqrt_nonneg qCap) radius_sq.le (by norm_num) (by norm_num) (by norm_num)
  have hcap := low_V_cap
  have hshort := low_V_short
  have hfc : frameCap=(7/10:ℝ) := rfl
  rw [hfc] at hz' hcapIcc hconc hcap ⊢
  obtain ⟨w,hw⟩ : ∃ w : ℝ, w=7/10-z := ⟨_,rfl⟩
  have hw0 : 0<w := by rw [hw]; linarith [hz.2]
  have ha : 0≤(7/10-3/20)/w := div_nonneg (by norm_num) hw0.le
  have hb : 0≤(3/20-z)/w := div_nonneg (by linarith [hz.2]) hw0.le
  have hab : (7/10-3/20)/w+(3/20-z)/w=1 := by
    rw [← add_div,div_eq_one_iff_eq hw0.ne',hw]; ring
  have hh := hconc.2 hz' hcapIcc ha hb hab
  have hpoint : (7/10-3/20)/w*z+(3/20-z)/w*(7/10)=3/20 := by
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,← add_div,div_eq_iff hw0.ne',hw]; ring
  simp only [smul_eq_mul,hpoint] at hh
  have hmul := mul_le_mul_of_nonneg_left hh hw0.le
  have hidentity : w*((7/10-3/20)/w*V R (13/20) 1 z+(3/20-z)/w*V R (13/20) 1 (7/10))=
      (7/10-3/20)*V R (13/20) 1 z+(3/20-z)*V R (13/20) 1 (7/10) := by
    field_simp
  rw [hidentity,hw] at hmul
  have hgap : (449/1000:ℝ)<V R (13/20) 1 (7/10)-V R (13/20) 1 (3/20) := by linarith
  have hprod := mul_lt_mul_of_pos_left hgap (show (0:ℝ)<7/10-z by linarith [hz.2])
  linarith

theorem separated_V_charge (f : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    charge f z*(frameCap-z)≤V R (Explicit.k f z) 1 frameCap-V R (Explicit.k f z) 1 z := by
  have hz' := Explicit.frame_domain f hz
  have hp : 0≤frameCap-z := sub_nonneg.mpr hz'.2
  rcases eq_or_ne f .low with rfl|hf
  · have hz0 : z∈Icc (0:ℝ) (3/20) := by
      have h := hz
      norm_num [Certificate.left,Certificate.right] at h
      exact h
    have hh := low_unit_chord hz0
    have hc := mul_le_mul_of_nonneg_right (charge_bounds .low hz).2.1 hp
    have hk : Explicit.k .low z=13/20 := by simp [Explicit.k,Certificate.k]
    rw [hk]
    simp only [frameCap] at hh hc hp ⊢
    linarith
  · have hh := unit_negative_growth (Explicit.ranges f hz).1 hz'
      (show frameCap∈Icc 0 frameCap from ⟨by norm_num [frameCap],le_rfl⟩) hz'.2
    rw [(charge_bounds f hz).2.2 hf]
    simp only [frameCap] at hh hp ⊢
    linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.BlockBounds
