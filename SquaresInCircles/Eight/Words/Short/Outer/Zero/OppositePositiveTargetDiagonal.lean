module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeAligned
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeNegativeGeometry

/-!
# Eight squares: the positive target-diagonal boundary

Its source contact decreases from `1-d` to zero. The uniform original source slope bound `1.2`
and `d-.5 < .4` give a positive angular derivative on that whole physical interval
(`target_diagonal_angle_positive`, `target_diagonal_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open SecondWord (outer_zero_mem)

lemma target_diagonal_domain_before {x y : ℝ} (hd : PlusDomain outerDiagonal x)
    (hy : y∈Icc 0 x) : PlusDomain outerDiagonal y := by
  have hyi : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hd.2.1.2⟩
  have hlo := SecondWord.OppositeZero.plus_angle_antitone hd.1 hyi hd.2.1 hy.2
  have hhi := SecondWord.OppositeZero.plus_angle_antitone hd.1 (by norm_num) hyi hy.1
  have h0 : SecondWord.OppositeZero.plus outerDiagonal 0=1-outerDiagonal := by
    simp only [SecondWord.OppositeZero.plus,Real.cos_zero,Real.sin_zero]
    ring
  rw [h0] at hhi
  exact ⟨hd.1,hyi,⟨hd.2.2.1.trans hlo,by linarith [outer_endpoint_bounds.2.2.1]⟩⟩

lemma target_diagonal_angle_positive (r : Row) {x : ℝ} (hd : PlusDomain outerDiagonal x) :
    0<plusAngle r outerDiagonal x := by
  have tr := positive_trig hd.2.1
  have hs : plusSpeed outerDiagonal x≤outerDiagonal-1/2 := by
    have hp := mul_nonneg
      (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1])
      (show 0≤1-(Real.cos x-Real.sin x) by linarith [tr.2.1,tr.2.2.1])
    norm_num [plusSpeed,SecondWord.OppositeZero.plusSpeed,
      ShortOuterOne.SameContact.arc_diagonal]
    nlinarith
  have hs0 := (SecondWord.OppositeZero.positive_data hd.1 hd.2.1).1
  have hL := slope_bounds r hd.2.2
  have hp := mul_le_mul hL.2.1 hs hs0.le (by norm_num : (0:ℝ)≤6/5)
  dsimp [plusAngle]
  nlinarith [outer_endpoint_bounds.2.2.2]

/-- The whole target-diagonal portion, including source coordinate zero. -/
theorem target_diagonal_lower (r : Row) {x : ℝ} (hd : PlusDomain outerDiagonal x) :
    (89809/100000:ℝ)<plusCost r outerDiagonal x := by
  have hm : MonotoneOn (plusCost r outerDiagonal) (Icc 0 x) :=
    monoOn_of_hasDeriv_nonneg
      (fun y hy => (plusCost_angle_hasDerivAt r (target_diagonal_domain_before hd hy)).continuousAt.continuousWithinAt)
      (fun y hy => plusCost_angle_hasDerivAt r
        (target_diagonal_domain_before hd (Ioo_subset_Icc_self hy)))
      (fun y hy => (target_diagonal_angle_positive r
        (target_diagonal_domain_before hd (Ioo_subset_Icc_self hy))).le)
  have hh := hm ⟨le_rfl,hd.2.1.1⟩ ⟨hd.2.1.1,le_rfl⟩ hd.2.1.1
  have hl := aligned_original r low_mem Negative.diagonal_mem (by dsimp [low]; ring)
  have hvalue : (89809/100000:ℝ)<plusCost r outerDiagonal 0 := by
    have h0 : plus outerDiagonal 0=low := by
      simp only [plus,SecondWord.OppositeZero.plus,Real.cos_zero,Real.sin_zero,low]
      ring
    rw [plusCost,h0,zero_add]
    exact hl
  exact hvalue.trans_le hh

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive
