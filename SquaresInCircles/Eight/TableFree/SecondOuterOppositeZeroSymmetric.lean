module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroLPositive
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroLNegativeMinimum

/-!
# The original symmetric opposite-sign outer zero-quarter pair

Uncompiled transcription of the contact reduction in Section 4 and the
positive/negative joins of the symmetric whole-angle hand proof. The
unchanged original labels are restored after lowering to first contact.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma label_monotone : MonotoneOn LLabel.outer (Icc 0 outerDiagonal) := L_monotone

theorem original_positive {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (17953/20000:ℝ)<x+LLabel.eval a b+LLabel.eval A B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hm' : plus B x≤b := by
    have hw := signed_width (show |x|≤7/10 from abs_le.mpr ⟨by linarith [hx.1],hx.2⟩)
    rw [abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin] at hm
    rw [hw] at hm
    dsimp [plus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hcontact : ∃C, C∈Icc 0 B ∧ PlusDomain C x ∧ plus C x≤b := by
    by_cases hp : 0≤plus B x
    · exact ⟨B,⟨hB.1,le_rfl⟩,⟨hB,hx,⟨hp,hm'.trans hb.2⟩⟩,hm'⟩
    · have hzero : 0<plus 0 x := by
        have hh := SameZero.b_lower outer_zero_mem hx
        change (293/1000:ℝ)<plus 0 x at hh
        linarith
      have hc : Continuous (fun C => plus C x) := by dsimp [plus,arc]; fun_prop
      obtain ⟨C,hC,he⟩ := intermediate_value_Icc hB.1 hc.neg.continuousOn
        (show (0:ℝ)∈Icc (-plus 0 x) (-plus B x) by constructor <;> linarith)
      have hplus : plus C x=0 := by linarith
      refine ⟨C,hC,⟨⟨hC.1,hC.2.trans hB.2⟩,hx,?_⟩,?_⟩
      · rw [hplus]
        exact outer_zero_mem
      · rw [hplus]
        exact hb.1
  obtain ⟨C,hC,hd,hbC⟩ := hcontact
  have h1 := label_monotone hd.2.2 hb hbC
  have h2 := label_monotone hd.1 hB hC.2
  have hh := plus_lower hd
  rw [LLabel.outer_actual hs] at h1
  rw [LLabel.outer_actual ht] at h2
  dsimp [plusCost] at hh
  linarith

theorem original_negative {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) (-x)) :
    (17953/20000:ℝ)<-x+LLabel.eval a b+LLabel.eval A B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hm' : minus B x≤b := by
    have hw := signed_width (show |-x|≤7/10 by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2)
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin,Real.sin_neg,Real.cos_neg] at hm
    rw [hw] at hm
    dsimp [minus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hd : MinusDomain B x := ⟨hB,hx,⟨by
    linarith [minus_aligned_le hB hx,hB.2,outer_endpoint_bounds.2.2.2],hm'.trans hb.2⟩⟩
  have h1 := label_monotone hd.2.2 hb hm'
  rw [LLabel.outer_actual hs] at h1
  have hh := minus_lower hd
  dsimp [minusCost] at hh
  rw [LLabel.outer_actual ht] at hh
  linarith

theorem original {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (17953/20000:ℝ)<x+LLabel.eval a b+LLabel.eval A B := by
  rcases le_total 0 x with hpos | hneg
  · exact original_positive hs ht ⟨hpos,(abs_le.mp hx).2⟩ hm
  · have hxn : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    simpa only [neg_neg] using original_negative hs ht hxn (by simpa using hm)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Symmetric
