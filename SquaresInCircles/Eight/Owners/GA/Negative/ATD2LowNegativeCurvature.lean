module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowNegativeComparison
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2UnaffectedCurvature

/-!
# Eight squares: the low pure-negative secant curvature

The baseline is enlarged to
the exact ratio `1.42`; its third derivative has the prescribed single
positive-square endpoint test. The H contribution has upper bound
`.117`, leaving the stated `.022` reserve in the total curvature.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowNegativeCurvature
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope PairNormCalculus OrdinaryCurvatureBounds
open SecantCoordinate SecantBounds

theorem tan_low_cut : Real.tan (1/5:ℝ)<203/1000 := by
  have hb := trig_bracket (l:=(1/5:ℝ)) (u:=(1/5:ℝ)) (x:=(1/5:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  have hc : 0<Real.cos (1/5:ℝ) := by norm_num at hb; linarith [hb.2.2.1]
  rw [Real.tan_eq_sin_div_cos,div_lt_iff₀ hc]
  norm_num at hb
  linarith [hb.2.1,hb.2.2.1]

theorem base_at_zero : baseSecond (71/50) 0< -(139/1000:ℝ) := by
  have hh := normalized_radius_bounds (A:=1+(71/50:ℝ)^2)
    (L:=1139/1000) (U:=57/50) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCap]) (by norm_num [qCap])
  have hS := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<1+(71/50:ℝ)^2)
  have hS2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤1+(71/50:ℝ)^2)
  have h1 : radical 1 0=1 := by rw [radical]; norm_num
  have h2 : radical (1+(71/50:ℝ)^2) 0=Real.sqrt (1+(71/50:ℝ)^2) := by
    rw [radical]; congr 1; ring
  have h3 : Real.sqrt (1+(71/50:ℝ)^2)^3=(1+(71/50:ℝ)^2)*Real.sqrt (1+(71/50:ℝ)^2) := by
    rw [pow_succ,hS2]
  have he : baseSecond (71/50) 0=1-R/Real.sqrt (1+(71/50:ℝ)^2) := by
    simp only [baseSecond]
    rw [h1,h2,h3]
    field_simp
  rw [he]
  linarith [hh.1]

theorem base_antitone :
    AntitoneOn (baseSecond (71/50)) (Icc (0:ℝ) (203/1000)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (baseSecond_hasDerivAt (71/50) x).continuousAt.continuousWithinAt)
    (fun x _ => baseSecond_hasDerivAt (71/50) x)
  intro x hx
  apply baseThird_nonpos_of_endpoint (u:=(203/1000:ℝ)) (by norm_num) (Ioo_subset_Icc_self hx)
  norm_num [qCap]

theorem base_curvature {r x : ℝ} (hr : r∈Icc 0 (71/50:ℝ))
    (hx : x∈Icc 0 (203/1000:ℝ)) : baseSecond r x< -(139/1000:ℝ) := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  exact (baseSecond_ratio_mono hr.1 hr.2 (by nlinarith)).trans_lt
    ((base_antitone (show (0:ℝ)∈Icc 0 (203/1000:ℝ) by norm_num) hx hx.1).trans_lt base_at_zero)

theorem H_curvature {k z x : ℝ} (hk : k∈Icc (2/3:ℝ) (187/250:ℝ))
    (hx : x∈Icc 0 (203/1000:ℝ))
    (hθ : z-Real.arctan x∈Icc 0 (1/5:ℝ)) :
    negativeSecond k 1 z x<(117/1000:ℝ) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hk1 : k≤1 := by linarith [hk.2]
  obtain ⟨hC,hD⟩ := Curvature.restricted_constants .middle hk0 hk1
    (show k≤(Curvature.ratioEnd .middle:ℝ)*1 by
      rw [show ((Curvature.ratioEnd .middle:ℚ):ℝ)=187/250 by norm_num [Curvature.ratioEnd]]
      linarith [hk.2])
  rw [show ((Curvature.C0End .middle:ℚ):ℝ)=569/1000 by norm_num [Curvature.C0End]] at hC
  rw [show ((Curvature.D0End .middle:ℚ):ℝ)=593/500 by norm_num [Curvature.D0End]] at hD
  have hE := curvatureSlope_nonneg (Real.sqrt_nonneg qCap) hk0 (by norm_num : (0:ℝ)<1)
  have hθframe : z-Real.arctan x∈Icc 0 frameCap :=
    ⟨hθ.1,by dsimp [frameCap]; linarith [hθ.2]⟩
  have hn := UnaffectedCurvature.numerator_upper hk0 hk1
    (show (1:ℝ)≤2*k by linarith [hk.1]) hx.1 hθframe
    (show curvatureZero R k 1≤(569/1000)*1 by linarith)
    (show Curvature.slopeZero k 1≤(593/500)*1 by linarith)
    (show (0:ℝ)*1≤curvatureSlope R k 1 by simpa using hE)
  have htr := LowNegativeComparison.small_trig hθ
  have hθ2 := pow_le_pow_left₀ hθ.1 hθ.2 2
  have hc : (49/50:ℝ)≤Real.cos (z-Real.arctan x) := by
    linarith [htr.2.1]
  have hsin := mul_nonneg (show 0≤2*x by linarith [hx.1]) htr.2.2.1
  have hxt := mul_le_mul hx.2 hθ.2 hθ.1 (by norm_num : (0:ℝ)≤203/1000)
  have hb : UnaffectedCurvature.bracket (569/1000) (593/500) 0 x (z-Real.arctan x)<117/1000 := by
    dsimp [UnaffectedCurvature.bracket]
    nlinarith only [hc,hsin,hxt,hx.2]
  have hnum : curvature R k 1 (-(z-Real.arctan x))-1*Real.cos (z-Real.arctan x)+
      2*x*Vd R k 1 (z-Real.arctan x)<117/1000 := by
    linarith only [hn,hb]
  have hden : 1≤(1+x^2)^2 := by nlinarith [sq_nonneg x,sq_nonneg (x^2)]
  unfold negativeSecond
  apply (div_lt_iff₀ (by positivity : 0<(1+x^2)^2)).2
  nlinarith only [hnum,hden]

theorem pure_curvature {l r k z x : ℝ} (hl : 1≤l)
    (hr : r∈Icc 0 (71/50:ℝ)) (hk : k∈Icc (2/3:ℝ) (187/250:ℝ))
    (hx : x∈Icc 0 (203/1000:ℝ))
    (hθ : z-Real.arctan x∈Icc 0 (1/5:ℝ)) :
    pureSecond l r k 1 z x< -(11/500:ℝ) := by
  have hb := base_curvature hr hx
  have hH := H_curvature hk hx hθ
  have hm := mul_lt_mul_of_pos_left hb (by linarith : 0<l)
  dsimp [pureSecond]
  nlinarith only [hm,hH,hl]

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowNegativeCurvature
