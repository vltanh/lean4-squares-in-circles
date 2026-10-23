module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveNegativeThreeData

/-!
# Every original owner for positive-to-negative outer edge three

The two secondary owners give a lower bound for the sum of the
transverse coordinates.  If that sum is small, either primary owner
contradicts its original weak separator.  The two global circle
chords and one increasing scalar cover the entire quarter interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveNegativeThree

open CommonQuarter CorePairGeometry Arithmetic

lemma secondary_sum {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : Early φ) (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    pairWidth φ-outerAxial*Real.sin φ≤b+B := by
  have htr := PositiveThree.lower_trig (early_lower hφ)
  have hs0 : 0≤Real.sin φ := by linarith [htr.1]
  have hc1 : Real.cos φ≤1 := by linarith [htr.2.2.2.1]
  have ha := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem hs).2 hs0
  have hA := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem ht).2 hs0
  have hb := mul_le_mul_of_nonneg_left hc1 hs.1
  have hB := mul_le_mul_of_nonneg_left hc1 ht.1
  rcases hj with rfl | rfl <;> norm_num [Eight.forwardMargin] at hm <;> nlinarith

lemma secondary_value {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : Early φ) (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (9119/10000:ℝ)<value b B φ := by
  have hsum := secondary_sum hs ht hφ j hj hm
  rw [PositiveThree.lower_width (early_lower hφ)] at hsum
  have hh := chord (φ := φ) (NegativeTwo.source_mem hs) (NegativeTwo.source_mem ht)
  have hcost : scalar φ≤value b B φ := by
    dsimp [scalar]
    nlinarith
  exact (scalar_lower hφ).trans_le hcost

lemma primary_impossible {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : Early φ) (hsum : b+B≤1/5) (j : Fin 4) (hj : j=1 ∨ j=3)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) : False := by
  have htr := PositiveThree.lower_trig (early_lower hφ)
  have hw : 1≤pairWidth φ := by
    rw [PositiveThree.lower_width (early_lower hφ)]
    linarith [htr.2.2.2.2]
  have hb : b≤1/5 := by linarith [ht.1]
  have hB : B≤1/5 := by linarith [hs.1]
  have ha := small_primary hs hb
  have hA := small_primary ht hB
  have hc := early_cos hφ
  have hp := mul_lt_mul ha hc (by norm_num : (0:ℝ)<587/1000)
    (show 0≤a by linarith [ha])
  have hP := mul_lt_mul hA hc (by norm_num : (0:ℝ)<587/1000)
    (show 0≤A by linarith [hA])
  have hbSin := mul_le_mul_of_nonneg_left htr.2.1 hs.1
  have hBSin := mul_le_mul_of_nonneg_left htr.2.1 ht.1
  have hau : a<(283/200:ℝ) := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
  have hAu : A<(283/200:ℝ) := (NegativeTwo.primary_mem ht).2.trans_lt outer_endpoint_bounds.2.1
  rcases hj with rfl | rfl <;> norm_num [Eight.forwardMargin] at hm <;> nlinarith

theorem original_at_angle {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (4493/5000:ℝ)<value b B φ := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  by_cases hlate : (943/1000:ℝ)≤φ
  · exact late_value hb hB hlate
  · have hangle : PositiveThree.lowerAngle≤φ := by
      have hh := (abs_le.mp hφ).1
      dsimp [PositiveThree.lowerAngle]
      linarith
    have hearly : Early φ := ⟨hangle,le_of_not_ge hlate⟩
    by_cases hsum : (1/5:ℝ)≤b+B
    · linarith [large_sum hb hB hangle hsum]
    · have hsmall : b+B≤1/5 := le_of_not_ge hsum
      fin_cases j
      · linarith [secondary_value hs ht hearly 0 (Or.inl rfl) hm]
      · exact (primary_impossible hs ht hearly hsmall 1 (Or.inl rfl) hm).elim
      · linarith [secondary_value hs ht hearly 2 (Or.inr rfl) hm]
      · exact (primary_impossible hs ht hearly hsmall 3 (Or.inr rfl) hm).elim

theorem original_scalar {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (-(7/10)) (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) (Real.pi/2+x)) :
    (4493/5000:ℝ)<value b B (Real.pi/2+x) := by
  apply original_at_angle hs ht ?_ j hm
  have he : Real.pi/2+x-Real.pi/2=x := by ring
  rw [he]
  exact abs_le.mpr hx

theorem original_some_axis {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10)
    (hm : ∃j : Fin 4, 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (4493/5000:ℝ)<value b B φ := by
  obtain ⟨j,hj⟩ := hm
  exact original_at_angle hs ht hφ j hj

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveNegativeThree
