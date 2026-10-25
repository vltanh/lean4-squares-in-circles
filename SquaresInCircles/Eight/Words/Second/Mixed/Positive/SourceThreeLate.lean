module

public import SquaresInCircles.Eight.Words.Second.Mixed.LEnvelopes
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeLateReferences

/-!
# Eight squares: every late positive-core transverse owner

Below the affine dividing curve the label envelope pays the required
cost directly. Above it, the concave target derivative leaves only the
dividing point and the diagonal. Both endpoints are proved on the whole
angle interval. The actual source and target are unchanged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Late
open CommonQuarter CorePairGeometry Arithmetic

lemma source_positive {φ : ℝ} (hφ : φ∈angles) : 0<f φ := by
  have hh := MinimumCalculus.endpoint_minimum hφ
    (fun θ hθ => f_hasDerivAt hθ) (fun θ hθ => f1_hasDerivAt hθ)
    (fun θ hθ => f2_hasDerivAt hθ) (fun θ hθ => (source_third_positive hθ).le)
    terminal_source_slope
  exact (lt_min left_reference.1 terminal_source).trans_le hh

lemma derivative_positive {φ : ℝ} (hφ : φ∈angles) : 0<D φ := by
  have hc : ConcaveOn ℝ angles D :=
    concave_of_deriv2 (fun θ hθ => D_hasDerivAt hθ) (fun θ hθ => D1_hasDerivAt hθ)
      (fun θ hθ => (derivative_second_negative hθ).le)
  exact concave_gt_of_endpoints hc hφ left_reference.2 terminal_derivative

lemma dividing_identity (φ : ℝ) : φ-e-111/1000-(69/100)*cut φ=γ := by
  dsimp [cut,e,γ,EdgeThreeAligned.ep,EdgeThreeAligned.threshold]
  ring

lemma dividing_value {φ : ℝ} (hφ : φ∈angles) : γ<F (cut φ) φ := by
  have hb := cut_bounds hφ
  have hL := MixedLEnvelopes.late_transverse
    (show cut φ∈Icc (0:ℝ) (397/500) from ⟨by linarith [hb.1],hb.2.le⟩)
  have hp := mul_nonneg (by norm_num [g,EdgeThreeAligned.gp] : 0≤g) (source_positive hφ).le
  have he := dividing_identity φ
  dsimp [F,f] at *
  linarith

theorem original {b A B φ : ℝ} (hb : 0≤b) (ht : OuterState A B) (hφ : φ∈angles)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ) : γ<value b B φ := by
  have hB := NegativeTwo.source_mem ht
  by_cases he : B≤cut φ
  · have hL := MixedLEnvelopes.late_transverse
      (show B∈Icc (0:ℝ) (397/500) from ⟨hB.1,he.trans (cut_bounds hφ).2.le⟩)
    have hp := mul_nonneg (by norm_num [g,EdgeThreeAligned.gp] : 0≤g) hb
    have hi := dividing_identity φ
    dsimp [value,EdgeThreeAligned.positiveCost]
    linarith
  · have hdom {y : ℝ} (hy : y∈Icc (cut φ) outerDiagonal) : y∈Icc 0 outerDiagonal :=
      ⟨(cut_domain hφ).1.trans hy.1,hy.2⟩
    have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos
      (f := fun y => F y φ) (d := fun y => FB y φ) (dd := fun y => FBB y φ)
      (ddd := fun y => FBBB y φ)
      (show B∈Icc (cut φ) outerDiagonal from ⟨by linarith,hB.2⟩)
      (fun y hy => F_hasDerivAt (hdom hy)) (fun y hy => FB_hasDerivAt (hdom hy))
      (fun y hy => FBB_hasDerivAt (hdom hy)) (fun y hy => (FBBB_negative (φ := φ) (hdom hy)).le)
      (derivative_positive hφ)
    have hlo := (lt_min (dividing_value hφ) (PositiveSource.diagonal_lower (lower_mem hφ))).trans_le hh
    exact hlo.trans_le (PositiveSource.original_lower ht hsep)

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Late
