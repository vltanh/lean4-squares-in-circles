module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3Penalty
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2SeparatedSlopes

/-!
# Eight squares: the three unit-pair chord reserves for the BT3 penalty endpoints

The two short-left-endpoint chords are established at k = .65 and
extended to the whole k interval by monotonicity of the exact angle
derivative in k. The cost at zero is then compared with the relevant
chord; no derivative of the weight family is used here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Chords
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope OrdinaryNegativeEnvelope PairNormCalculus
open JointNegativeAETD2.BlockBounds

theorem right_chord {f : ℝ→ℝ} {a z b : ℝ}
    (hc : ConcaveOn ℝ (Icc 0 frameCap) f) (ha : a∈Ico 0 frameCap)
    (hz : z∈Icc 0 a) (hgap : b*(frameCap-a)≤f frameCap-f a) :
    b*(frameCap-z)≤f frameCap-f z := by
  have hT0 : (0:ℝ)≤frameCap := by norm_num [frameCap]
  generalize frameCap=T at *
  have hden : 0<T-z := by linarith [hz.2,ha.2]
  have hpos : 0<T-a := by linarith [ha.2]
  set u : ℝ := (T-a)/(T-z) with hu_def
  set v : ℝ := (a-z)/(T-z) with hv_def
  have hu : 0≤u := div_nonneg hpos.le hden.le
  have hv : 0≤v := div_nonneg (by linarith [hz.2]) hden.le
  have huv : u+v=1 := by rw [hu_def,hv_def]; field_simp; ring
  have hp : u*z+v*T=a := by rw [hu_def,hv_def]; field_simp; ring
  have hh := hc.2 (show z∈Icc 0 T from ⟨hz.1,hz.2.trans ha.2.le⟩)
    (show T∈Icc 0 T from ⟨hT0,le_rfl⟩) hu hv huv
  simp only [smul_eq_mul,hp] at hh
  have hm := mul_le_mul_of_nonneg_left hh hden.le
  have he : (T-z)*(u*f z+v*f T)=(T-a)*f z+(a-z)*f T := by
    rw [hu_def,hv_def]
    field_simp
  rw [he] at hm
  have hg := mul_le_mul_of_nonneg_left hgap hden.le
  have hfinal : 0≤(T-a)*(f T-f z-b*(T-z)) := by linarith
  have hh' := (mul_nonneg_iff_of_pos_left hpos).mp hfinal
  linarith

theorem chord_k_monotone {k z : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hz : z∈Icc 0 frameCap) :
    V R (13/20) 1 frameCap-V R (13/20) 1 z≤V R k 1 frameCap-V R k 1 z := by
  have hk0 : 0<k := by linarith [hk.1]
  have hh := derivative_reserve
    (f:=fun t => V R k 1 t-V R (13/20) 1 t)
    (df:=fun t => Vd R k 1 t-Vd R (13/20) 1 t) (k:=0)
    (fun t ht => ((V_hasDerivAt hk0 (by norm_num) ht).sub
      (V_hasDerivAt (by norm_num : (0:ℝ)<13/20) (by norm_num) ht)).continuousAt.continuousWithinAt)
    (fun t ht => (V_hasDerivAt hk0 (by norm_num) (Ioo_subset_Icc_self ht)).sub
      (V_hasDerivAt (by norm_num : (0:ℝ)<13/20) (by norm_num) (Ioo_subset_Icc_self ht)))
    (fun t ht => sub_nonneg.mpr (NegativeAPositiveTD.NegativeSlope.normalized_slope_mono
      (by norm_num) hk.1 (by linarith [hk.2]) (Ioo_subset_Icc_self ht)))
    hz (show frameCap∈Icc 0 frameCap from ⟨by norm_num [frameCap],le_rfl⟩) hz.2
  linarith

theorem low_chord {k z : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hz : z∈Icc (0:ℝ) (3/20)) :
    (4/5)*(frameCap-z)≤V R k 1 frameCap-V R k 1 z := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩
  exact (low_unit_chord hz).le.trans (chord_k_monotone hk hz')

theorem V_three_tenths : V R (13/20) 1 (3/10)<3/10 := by
  have ht : |-(3/10:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos (p:=(13/20:ℝ)) (q:=1) (t:=-(3/10)) (by norm_num) (by norm_num) ht
  have hn2 := pairNorm_sq (p:=(13/20:ℝ)) (q:=1) (t:=-(3/10)) (by norm_num) (by norm_num) ht
  have hz := pairNorm_pos (p:=(13/20:ℝ)) (q:=1) (t:=0) (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hz2 := pairNorm_sq (p:=(13/20:ℝ)) (q:=1) (t:=0) (by norm_num) (by norm_num) (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_neg,Real.sin_zero] at hn2 hz2
  have hs : Real.sin (3/10:ℝ)<739/2500 := by
    have hh := sin_upper_five (x:=(3/10:ℝ)) (by norm_num)
    norm_num at hh
    linarith
  have hc : Real.cos (3/10:ℝ)<4777/5000 := by
    have hh := cos_upper_four (x:=(3/10:ℝ)) (by norm_num)
    norm_num at hh
    linarith
  have hzhi : pairNorm (13/20) 1 0<11927/10000 := by nlinarith
  have hnlo : (10189/10000:ℝ)<pairNorm (13/20) 1 (-(3/10)) := by nlinarith
  have hgap : pairNorm (13/20) 1 0-pairNorm (13/20) 1 (-(3/10))<869/5000 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hgap.le (Real.sqrt_nonneg qCap)
  have hR := mul_le_mul_of_nonneg_right
    (show R≤4947/2500 by linarith [Secondary.radius_bounds.2]) (by norm_num : (0:ℝ)≤869/5000)
  dsimp [V]
  nlinarith

theorem middle_chord {k z : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hz : z∈Icc (0:ℝ) (3/10)) :
    (3/4)*(frameCap-z)≤V R k 1 frameCap-V R k 1 z := by
  have hc := V_concave (R:=R) (p:=(13/20:ℝ)) (q:=1)
    (Real.sqrt_nonneg qCap) radius_sq.le (by norm_num) (by norm_num) (by norm_num)
  have hfc : frameCap=7/10 := rfl
  have hgap : (3/4)*(frameCap-3/10)≤V R (13/20) 1 frameCap-V R (13/20) 1 (3/10) := by
    linarith [low_V_cap,V_three_tenths]
  have hh := right_chord hc (show (3/10:ℝ)∈Ico 0 frameCap by norm_num [frameCap]) hz hgap
  exact hh.trans (chord_k_monotone hk ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩)

theorem cost_zero_chord {k c z : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hc : c≤7/5) (hz : z∈Icc 0 frameCap)
    (hdiag : 1≤c → z≤3/10) (hlater : 3/20≤z → c≤6/5) :
    Penalty.cost c 0*(frameCap-z)≤V R k 1 frameCap-V R k 1 z := by
  have hP : 0≤frameCap-z := sub_nonneg.mpr hz.2
  by_cases hc1 : c<1
  · have hh := unit_negative_growth hk hz
      (show frameCap∈Icc 0 frameCap from ⟨by norm_num [frameCap],le_rfl⟩) hz.2
    simp only [Penalty.cost,ite_eq_left hc1,SecantNormCurvature.secant,Real.cos_zero,div_one]
    simp only [frameCap] at hh hP ⊢
    linarith
  · have hc1' : 1≤c := le_of_not_gt hc1
    by_cases hzlow : z≤3/20
    · have hh := low_chord hk ⟨hz.1,hzlow⟩
      have hcost := (Penalty.cost_bounds hc (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).2
      have hp := mul_le_mul_of_nonneg_right hcost hP
      simp only [frameCap] at hh hP hp ⊢
      linarith
    · have hh := middle_chord hk ⟨hz.1,hdiag hc1'⟩
      have hcsmall := hlater (le_of_lt (lt_of_not_ge hzlow))
      have hcost : Penalty.cost c 0≤327/500 := by
        simp only [Penalty.cost,ite_eq_right hc1,SecantNormCurvature.secant,Real.cos_zero,div_one]
        exact max_le (by norm_num) (max_le (by linarith) (by norm_num))
      have hp := mul_le_mul_of_nonneg_right hcost hP
      simp only [frameCap] at hh hP hp ⊢
      linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Chords
