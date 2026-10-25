module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeData

/-!
# The last two original upper owners for positive edge three

The target-secondary owner caps its actual target coordinate on the
whole upper interval.  The source-primary owner has a sharper cap on
the initial strip; all later angles were closed by the original label
bounds.  Both arguments retain weak separators and actual states.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic

theorem original_upper_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 1 (Real.pi/2+x)) :
    (51/50:ℝ)<value b B (Real.pi/2+x) := by
  have hcut := upper_target_secondary_cut hx hm
  have htr := positive_trig hx
  have ha := NegativeTwo.primary_mem hs
  have hprod := mul_le_mul_of_nonneg_left htr.2.1
    (show 0≤a-1/2 by linarith [ha.1,fine_outer_endpoint_bounds.2])
  have hneg := mul_nonneg (show 0≤b+1/2 by linarith [hs.1]) htr.2.2.1
  have hB : B<(83/200:ℝ) := by linarith [ha.2,outer_endpoint_bounds.2.1]
  have hL := L_axial_line (NegativeTwo.source_mem ht)
  have hV := V_lower (NegativeTwo.source_mem hs)
  dsimp [value]
  linarith [pi_hand_enclosure.1,hx.1]

lemma upper_primary_small_target {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (11/100))
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 (Real.pi/2+x)) :
    B<(523/1000:ℝ) := by
  have hcap : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have hcut := upper_source_primary_cut hcap hm
  have htr := positive_trig hcap
  have ha := NegativeTwo.primary_mem hs
  have hA := NegativeTwo.primary_mem ht
  have hh : a-1/2<(57161/62500:ℝ) ∧ A-1/2<57161/62500 := by
    constructor <;> linarith [ha.2,hA.2,ShortOuterZero.fine_axial_bounds.2]
  have hc : (19879/20000:ℝ)≤Real.cos x := by
    have hbase := Real.one_sub_sq_div_two_le_cos (x := x)
    have hsq := pow_le_pow_left₀ hx.1 hx.2 2
    linarith
  have hprod := mul_le_mul hh.2.le
    (show Real.sin x≤11/100 from htr.2.2.2.2.1.trans hx.2)
    htr.2.2.1 (by norm_num : (0:ℝ)≤57161/62500)
  have hlow := mul_le_mul_of_nonneg_left hc
    (show 0≤B+1/2 by linarith [ht.1])
  linarith [hh.1]

theorem original_upper_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases he : x≤11/100
  · have hB := upper_primary_small_target hs ht ⟨hx.1,he⟩ hm
    have hL := L_axial_line (NegativeTwo.source_mem ht)
    have hV := V_lower (NegativeTwo.source_mem hs)
    dsimp [value]
    linarith [pi_hand_enclosure.1,hx.1]
  · have hh := late_angle hs ht
      (show (419/250:ℝ)≤Real.pi/2+x by linarith [pi_hand_enclosure.1])
    linarith

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree
