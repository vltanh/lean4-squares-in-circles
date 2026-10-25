module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.CoreTwoScalars

/-!
# Eight squares: every negative-core to negative-outer original role-two owner

One affine lower bound for T is enough for the whole family.  Each
original lower owner gives a direct comparison with the proved harmonic
scalars; the late estimate includes the complete upper quarter half.
The argument retains both core pieces and all weak axes.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width)

lemma core_transverse_upper {a b : ℝ} (hs : CoreState a b) : b<(559/1000:ℝ) :=
  (CoreAngleEndpoint.state_bounds hs).2.2.2.2.trans_lt
    (by linarith [CoreAngleEndpoint.diagonal_bounds.2])

lemma first_original {a b A B φ : ℝ} (_hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -b+A*Real.sin φ+B*Real.cos φ) :
    (49/50:ℝ)<value b B φ := by
  have htr := lower_trig hφ
  have hcircle := mul_le_mul_of_nonneg_right (target_axial_chord ht)
    (by linarith [htr.1] : 0≤Real.sin φ)
  have hcoef : 0≤609/1000-g*(Real.cos φ-(261/1000)*Real.sin φ) := by
    norm_num [g]
    linarith [htr.1,htr.2.2.2.1]
  have hpaid := mul_nonneg ht.1 hcoef
  have hT := target_affine ht
  have hh := first_lower hφ
  dsimp [value,MixedAffine.first,MixedAffine.κ,g,c] at *
  nlinarith

lemma second_original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -a*Real.cos φ-b*Real.sin φ+A) :
    (49/50:ℝ)<value b B φ := by
  have htr := lower_trig hφ
  have hsine : 0<Real.sin φ := by linarith [htr.1]
  have hreserve := mul_nonneg htr.2.2.1 (core_norm_reserve hs hφ).le
  have he :
      (outerAxial*Real.sin φ-(1+Real.sin φ+Real.cos φ)/2)*Real.sin φ-
        (outerAxial-a*Real.cos φ-(1+Real.sin φ+Real.cos φ)/2)=
      Real.cos φ*(a+1/2-Real.sin φ/2-MixedAffine.κ*Real.cos φ) := by
    dsimp [MixedAffine.κ]
    linear_combination (outerAxial-1/2)*(Real.sin_sq_add_cos_sq φ)
  have hcut : b≤outerAxial*Real.sin φ-(1+Real.sin φ+Real.cos φ)/2 := by
    apply (mul_le_mul_iff_left₀ hsine).mp
    nlinarith [(NegativeTwo.primary_mem ht).2]
  have hweighted := mul_le_mul_of_nonneg_left hcut (show (0:ℝ)≤g by norm_num [g])
  have hT := T_lower (NegativeTwo.source_mem ht)
  have hh := first_lower hφ
  dsimp [value,MixedAffine.first,MixedAffine.κ,g,c] at *
  nlinarith

lemma third_original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ+B) :
    (49/50:ℝ)<value b B φ := by
  have htr := lower_trig hφ
  have hcore := CoreAngleEndpoint.state_bounds hs
  have ha := mul_le_mul_of_nonneg_right hcore.2.1 (by linarith [htr.1] : 0≤Real.sin φ)
  have hcut : 1/2+Real.cos φ/2-Real.sin φ/12+b*Real.cos φ≤B := by nlinarith
  have hcut' := mul_le_mul_of_nonneg_left hcut (by norm_num : (0:ℝ)≤609/1000)
  have hcoef : 0≤g-(609/1000)*Real.cos φ := by norm_num [g]; linarith [Real.cos_le_one φ]
  have hpaid := mul_nonneg (show 0≤559/1000-b by linarith [core_transverse_upper hs]) hcoef
  have hT := target_affine ht
  have hh := third_lower hφ
  dsimp [value,third] at *
  nlinarith

lemma fourth_original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) :
    (9/10:ℝ)<value b B φ := by
  have htr := lower_trig hφ
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hBhi : B≤9/10 := (NegativeTwo.source_mem ht).2.trans outer_endpoint_bounds.2.2.2.le
  have hAB := mul_nonneg (sub_nonneg.mpr ht.2.1) htr.2.2.1
  have hsc : 0≤Real.sin φ-Real.cos φ := by linarith [htr.1,htr.2.2.2.1]
  have hdiag := mul_nonneg (sub_nonneg.mpr hBhi) hsc
  have hangle : (123/100:ℝ)<φ := by
    by_contra hn
    have hr := fourth_early_trig hφ (le_of_not_gt hn)
    nlinarith [hr.1,hr.2,hcore.2.1]
  have hAc := mul_nonneg (show 0≤A by linarith [ht.1,ht.2.1]) htr.2.2.1
  have hBs := mul_le_mul_of_nonneg_left (Real.sin_le_one φ) ht.1
  have hB : (5/12:ℝ)≤B := by nlinarith [htr.2.2.2.2,hcore.2.1]
  have hT := target_affine ht
  have hb := core_transverse_upper hs
  dsimp [value,g,c]
  linarith

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (17953/20000:ℝ)<value b B φ := by
  by_cases hlate : (147/100:ℝ)≤φ
  · have hT := T_lower (NegativeTwo.source_mem ht)
    have hb := core_transverse_upper hs
    dsimp [value,g,c]
    linarith
  have hlow : Lower φ :=
    ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],
      by linarith [pi_hand_enclosure.1]⟩
  fin_cases j
  · have hh := first_original hs ht hlow (by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith)
    linarith
  · have hh := second_original hs ht hlow (by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith)
    linarith
  · have hh := third_original hs ht hlow (by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith)
    linarith
  · have hh := fourth_original hs ht hlow (by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith)
    linarith

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    SecondWord.threshold 2<cost 2 kind .outer false false a b A B φ := by
  rw [threshold_value,core_outer_negative_negative hk ht]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeCore
