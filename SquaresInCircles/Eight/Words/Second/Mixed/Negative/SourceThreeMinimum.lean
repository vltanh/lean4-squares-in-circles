module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.SourceThreeMinimumReferences

/-!
# Eight squares: the complete small-target negative-core minimum

One quadratic tangent controls the unique tight minimum. A concave
first derivative then gives the increasing continuation, followed by
two intervals whose costs are concave and have strictly positive
endpoint reserves. Every dividing point belongs to the proved domains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower)

lemma early_lower {B : ℝ} (hB : B∈Icc (0:ℝ) (8/25)) : γ<E g B := by
  have hdom {y : ℝ} (hy : y∈Icc (0:ℝ) (8/25)) : y∈targets :=
    ⟨hy.1,by linarith [hy.2]⟩
  have hc (y : ℝ) (hy : y∈Icc (0:ℝ) (8/25)) : (11/50:ℝ)≤E2 g y := by
    have hm := first_second_antitone (hdom hy) (show (8/25:ℝ)∈targets by norm_num [targets]) hy.2
    linarith [References.early_terminal.2.2]
  have ht := curvature_tangent (κ := (11/50:ℝ)) (f := E g) (d := E1 g) (dd := E2 g)
    hB (show (607/2000:ℝ)∈Icc (0:ℝ) (8/25) by norm_num)
    (fun y hy => E_hasDerivAt first_slope (hdom hy))
    (fun y hy => E1_hasDerivAt first_slope (hdom hy)) hc
  have hd := abs_lt.mp References.minimum_reference.2
  have hp := mul_pos (show 0<E1 g (607/2000)+3/500000 by linarith [hd.1])
    (show 0<(3/500000:ℝ)-E1 g (607/2000) by linarith [hd.2])
  have hsq := sq_nonneg ((11/50)*(B-607/2000)+E1 g (607/2000))
  dsimp [γ,EdgeThreeAligned.threshold]
  nlinarith [References.minimum_reference.1]

lemma middle_slope {B : ℝ} (hB : B∈Icc (8/25:ℝ) (2/5)) : 0<E1 g B := by
  have hdom {y : ℝ} (hy : y∈Icc (8/25:ℝ) (2/5)) : y∈targets :=
    ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hc : ConcaveOn ℝ (Icc (8/25:ℝ) (2/5)) (E1 g) :=
    concave_of_deriv2 (fun y hy => E1_hasDerivAt first_slope (hdom hy))
      (fun y hy => E2_hasDerivAt first_slope (hdom hy))
      (fun y hy => (first_third_negative (hdom hy)).le)
  exact concave_gt_of_endpoints hc hB References.early_terminal.2.1 References.middle_terminal.2.1

lemma middle_lower {B : ℝ} (hB : B∈Icc (8/25:ℝ) (2/5)) : γ<E g B := by
  have hdom {y : ℝ} (hy : y∈Icc (8/25:ℝ) (2/5)) : y∈targets :=
    ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hm : MonotoneOn (E g) (Icc (8/25:ℝ) (2/5)) :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => (E_hasDerivAt first_slope (hdom hy)).continuousAt.continuousWithinAt)
      (fun y hy => E_hasDerivAt first_slope (hdom (Ioo_subset_Icc_self hy)))
      (fun y hy => (middle_slope (Ioo_subset_Icc_self hy)).le)
  have he := hm (show (8/25:ℝ)∈Icc (8/25:ℝ) (2/5) by norm_num) hB hB.1
  dsimp [γ,EdgeThreeAligned.threshold]
  linarith [References.early_terminal.1]

lemma first_late_lower {B : ℝ} (hB : B∈Icc (2/5:ℝ) (9/20)) : γ<E g B := by
  have hdom {y : ℝ} (hy : y∈Icc (2/5:ℝ) (9/20)) : y∈targets :=
    ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hc : ConcaveOn ℝ (Icc (2/5:ℝ) (9/20)) (E g) :=
    concave_of_deriv2 (fun y hy => E_hasDerivAt first_slope (hdom hy))
      (fun y hy => E1_hasDerivAt first_slope (hdom hy)) (fun y hy => by
        have hm := first_second_antitone (show (2/5:ℝ)∈targets by norm_num [targets]) (hdom hy) hy.1
        linarith [References.middle_terminal.2.2])
  apply concave_gt_of_endpoints hc hB
  · dsimp [γ,EdgeThreeAligned.threshold]
    linarith [References.middle_terminal.1]
  · dsimp [γ,EdgeThreeAligned.threshold]
    linarith [References.first_terminal]

theorem first_lower {B : ℝ} (hB : B∈Icc (0:ℝ) (9/20)) : γ<E g B := by
  by_cases he : B≤8/25
  · exact early_lower ⟨hB.1,he⟩
  · by_cases hm : B≤2/5
    · exact middle_lower ⟨by linarith,hm⟩
    · exact first_late_lower ⟨by linarith,hB.2⟩

theorem second_lower {B : ℝ} (hB : B∈Icc (9/20:ℝ) (27/50)) : γ<E (39/40) B := by
  have hdom {y : ℝ} (hy : y∈Icc (9/20:ℝ) (27/50)) : y∈targets :=
    ⟨by linarith [hy.1],hy.2⟩
  have hc : ConcaveOn ℝ (Icc (9/20:ℝ) (27/50)) (E (39/40)) :=
    concave_of_deriv2 (fun y hy => E_hasDerivAt second_slope (hdom hy))
      (fun y hy => E1_hasDerivAt second_slope (hdom hy)) (fun y hy => by
        have hm := second_second_antitone
          (show (9/20:ℝ)∈Icc (9/20:ℝ) (27/50) by norm_num) hy hy.1
        linarith [References.second_initial.2])
  apply concave_gt_of_endpoints hc hB
  · dsimp [γ,EdgeThreeAligned.threshold]
    linarith [References.second_initial.1]
  · dsimp [γ,EdgeThreeAligned.threshold]
    linarith [References.second_terminal]

theorem contact_lower {B φ : ℝ} (hB : B∈targets) (hφ : Lower φ)
    (hb : 0≤contact B φ) : γ<C B φ := by
  by_cases he : B≤9/20
  · exact (first_lower ⟨hB.1,he⟩).trans_le (angle_lower first_slope hB hφ hb)
  · exact (second_lower ⟨by linarith,hB.2⟩).trans_le (angle_lower second_slope hB hφ hb)

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum
