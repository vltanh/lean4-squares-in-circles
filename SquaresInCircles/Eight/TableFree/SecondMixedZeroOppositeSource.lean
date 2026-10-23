module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeSourceData

/-!
# All three opposite mixed zero rows with their original source owner

Uncompiled source draft.  The P row is paid directly by the sum of the
two original transverse coordinates.  J and L use the continuous
supports and aligned bounds.  The negative-angle geometric cap is
derived from the same weak owner before it is used analytically.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Source
open CommonQuarter CorePairGeometry Arithmetic

lemma positive_sum {b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    1-(109/100)*x≤b+B := by
  have tr := positive_trig hx
  have hA := mul_le_mul_of_nonneg_right (outer_bounds ht).2.1 tr.2.2.1
  have hAx := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.1.le tr.2.2.1
  have hB := mul_nonneg ht.1 (sub_nonneg.mpr tr.2.1)
  have hcos := cos_lower_two hx.1
  have hsin := Real.sin_le hx.1
  have hquad := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  nlinarith

lemma negative_sum {b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (8/25))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    1+(259/200)*x≤b+B := by
  have tr := positive_trig (show x∈Icc 0 (7/10) from ⟨hx.1,by linarith [hx.2]⟩)
  have hA : (899/1000:ℝ)≤A := by
    linarith [(outer_bounds ht).1,fine_outer_endpoint_bounds.2]
  have hAs := mul_le_mul_of_nonneg_right hA tr.2.2.1
  have hB := mul_nonneg ht.1 (sub_nonneg.mpr tr.2.1)
  have hcos := cos_lower_two hx.1
  have hsin := Real.sin_ge_sub_cube hx.1
  have hquad := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hsquare := pow_le_pow_left₀ hx.1 hx.2 2
  have hcube := mul_le_mul_of_nonneg_right hsquare hx.1
  nlinarith

lemma P_positive {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (17953/20000:ℝ)<x+c 1+g 1*b+(F 1).outer B := by
  have hsum := positive_sum ht hx hm
  have hP := P_line ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hb : b<(559/1000:ℝ) := by
    linarith [(CoreAngleEndpoint.state_bounds hs).2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
  change (17953/20000:ℝ)<x+19555/100000+(63132/100000)*b+P B
  nlinarith [hx.1]

lemma P_negative {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (8/25))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (17953/20000:ℝ)<-x+c 1+g 1*b+(F 1).outer B := by
  have hsum := negative_sum ht hx hm
  have hP := P_line ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hb : b<(559/1000:ℝ) := by
    linarith [(CoreAngleEndpoint.state_bounds hs).2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
  change (17953/20000:ℝ)<-x+19555/100000+(63132/100000)*b+P B
  nlinarith [hx.1]

theorem positive_original (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (17953/20000:ℝ)<x+c r+g r*b+(F r).outer B := by
  by_cases hP : r=1
  · subst r
    exact P_positive hs ht hx hm
  · have hsep := mul_nonneg (slope_bounds r).1.le (sub_nonneg.mpr hm)
    have he : positive r A B x≤x+c r+g r*b+(F r).outer B := by
      dsimp [positive]
      nlinarith only [hsep]
    by_cases hJ : r=0 ∧ B≤3/20
    · obtain ⟨rfl,hB⟩ := hJ
      exact (J_small_positive ht hB hx).trans_le he
    · have hr : r=2 ∨ (r=0 ∧ (3/20:ℝ)≤B) := by
        fin_cases r <;> simp_all <;> linarith
      exact (by linarith [positive_lower r hr ht hx] :
        (17953/20000:ℝ)<positive r A B x).trans_le he

theorem negative_original (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (17953/20000:ℝ)<-x+c r+g r*b+(F r).outer B := by
  have hcap := ShortMixedZero.CoreContact.original_angle_cut hs ht hx hm
  have hsmall : x∈Icc (0:ℝ) (8/25) := ⟨hx.1,by simpa [ShortMixedZero.CoreContact.cap] using hcap.le⟩
  by_cases hP : r=1
  · subst r
    exact P_negative hs ht hsmall hm
  · have hsep := mul_nonneg (slope_bounds r).1.le (sub_nonneg.mpr hm)
    have hl := negative_lower r hP ht hsmall
    dsimp [negative] at hl
    nlinarith only [hl,hsep]

theorem original (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (17953/20000:ℝ)<x+c r+g r*b+(F r).outer B := by
  have hm' : pairWidth x≤b+A*Real.sin x+B*Real.cos x := by
    norm_num [Eight.forwardMargin] at hm
    linarith
  by_cases hp : 0≤x
  · have hx' : x∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hx).2⟩
    have hw := signed_width hx
    rw [abs_of_nonneg (positive_trig hx').2.2.1] at hw
    apply positive_original r hs ht hx'
    rw [hw] at hm'
    linarith
  · have hx' : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have hsin : Real.sin x≤0 := by
      have hh := (positive_trig hx').2.2.1
      simpa only [Real.sin_neg,neg_nonneg] using hh
    have hw := signed_width hx
    rw [abs_of_nonpos hsin] at hw
    have hh := negative_original r hs ht hx' (by
      rw [hw] at hm'
      simp only [Real.sin_neg,Real.cos_neg,mul_neg,sub_neg_eq_add]
      linarith)
    simpa only [neg_neg] using hh

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Source
