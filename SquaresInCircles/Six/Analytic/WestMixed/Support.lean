import SquaresInCircles.Six.Analytic.WestMixed.Reduction

/-!
# Common support facts for the two remaining OWN-W mixed families

The W force is (41/20+sin q,-cos q), with 1<=q<=pi/2. Its axial force cone
is proved from cos q<=cos 1<=13/24, not selected without justification.
The central support helper preserves both actual force signs as hypotheses.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestMixed
open Normalization

lemma west_support {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1 ≤ q ∧ q ≤ Real.pi/2) :
    (beta+Real.sin q)*a-Real.cos q*b ≤
      CandidateWestTail.rhoBound*(beta+Real.sin q) := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ q by linarith [hq.1])
    (show q ≤ Real.pi by linarith [hq.2,Real.pi_pos])
  have hcq := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hq.1,Real.pi_pos],hq.2⟩
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ) ≤ 1)
    (show q ≤ Real.pi by linarith [hq.2,Real.pi_pos]) hq.1
  have ht := Seven.cos_upper_four (x := (1:ℝ)) (by norm_num)
  have hcos : Real.cos q ≤ 13/24 := by nlinarith only [hm,ht]
  have hU : 0 ≤ beta+Real.sin q := by dsimp [beta]; linarith
  have hV : |-Real.cos q| ≤ (31/100)*(beta+Real.sin q) := by
    rw [abs_neg,abs_of_nonneg hcq]
    dsimp [beta]
    linarith
  have h := axial_cone_support hc hU hV
  have hR := mul_le_mul_of_nonneg_right CandidateWestTail.ceiling_bounds.2.1 hU
  nlinarith only [h,hR]

lemma central_support {X Y cx cy : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hx : cx ≤ CandidateWestTail.coreUpper) (hy : cy ≤ CandidateWestTail.coreUpper) :
    X*cx+Y*cy ≤ CandidateWestTail.coreUpper*(X+Y) := by
  have h0 := mul_le_mul_of_nonneg_left hx hX
  have h1 := mul_le_mul_of_nonneg_left hy hY
  nlinarith only [h0,h1]

lemma width_formula {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
    angularWidth x=(Real.cos x+Real.sin x)/2 := by
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])
  simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs]

end SquaresInCircles.Six.Analytic.WestMixed
