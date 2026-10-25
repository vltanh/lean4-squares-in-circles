module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeAligned
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeUpperEasy

/-!
# Both upper first owners by finite displacement from alignment

The first upper owner loses at most `.4*x` in aligned source coordinate.
For the second upper owner on `x≤.11`, the loss is at most `.942076*x`.
The source slope is below `1.061`, and `1.061*.942076<1`, so the actual
angle increase pays the entire label loss.  No implicit contact
minimizer or contact-curve endpoint is assumed.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic

lemma V_increment_upper {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (h : b≤B) :
    V B-V b≤(1061/1000)*(B-b) := by
  have hm : AntitoneOn (fun t => V t-(1061/1000)*t) (Icc 0 outerDiagonal) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => ((VLabel.outer_hasDerivAt (outer_domain ht)).sub
        ((hasDerivAt_id t).const_mul (1061/1000))).continuousAt.continuousWithinAt)
      (fun t ht => (VLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self ht))).sub
        ((hasDerivAt_id t).const_mul (1061/1000)))
      (fun t ht => by linarith [V_first_upper (Ioo_subset_Icc_self ht)])
  have hh := hm hb hB h
  linarith

namespace PositiveThree

lemma upper_of_displacement {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : 0≤x)
    (hdisp : (1061/1000)*(1-A-b)≤x) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases halign : 1≤b+A
  · have hh := original_aligned hs ht halign
    dsimp [value] at *
    linarith
  · have hA : A≤1 := by linarith [hs.1]
    have hdom : 1-A∈Icc 0 outerDiagonal := by
      constructor <;> linarith [(NegativeTwo.primary_mem ht).1,fine_outer_endpoint_bounds.2]
    have hs0 := ShortOuterOne.SameContact.arc_state hdom
    have hbase := original_aligned hs0 ht (show 1≤(1-A)+A by linarith)
    have hinc := V_increment_upper (NegativeTwo.source_mem hs) hdom (by linarith)
    dsimp [value] at *
    linarith

lemma upper_first_displacement {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 (Real.pi/2+x)) :
    1-A-b≤(2/5)*x := by
  have hcut := upper_source_secondary_cut hx hm
  have htr := positive_trig hx
  have hcos := mul_nonneg
    (show 0≤A-1/2 by linarith [(NegativeTwo.primary_mem ht).1,fine_outer_endpoint_bounds.2])
    (sub_nonneg.mpr htr.2.1)
  have hsin := mul_le_mul_of_nonneg_right
    (show B-1/2≤2/5 by linarith [(NegativeTwo.source_mem ht).2,outer_endpoint_bounds.2.2.2])
    htr.2.2.1
  nlinarith [htr.2.2.2.2.1]

theorem original_upper_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  have hdisp := upper_first_displacement hs ht hx hm
  have hh := upper_of_displacement hs ht hx.1
    (show (1061/1000)*(1-A-b)≤x by nlinarith [hx.1])
  linarith

lemma upper_second_displacement {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (11/100))
    (hm : 0≤Eight.forwardMargin 1 a b A B 1 1 (Real.pi/2+x)) :
    1-A-b≤(235519/250000)*x := by
  have hcap : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have hcut := upper_target_primary_cut hcap hm
  have htr := positive_trig hcap
  have ha : a-1/2<(57161/62500:ℝ) := by
    linarith [(NegativeTwo.primary_mem hs).2,ShortOuterZero.fine_axial_bounds.2]
  have hsin := mul_le_mul ha.le htr.2.2.2.2.1
    htr.2.2.1 (by norm_num : (0:ℝ)≤57161/62500)
  have hb := mul_nonneg hs.1 (sub_nonneg.mpr htr.2.1)
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsquare := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  linarith

theorem original_upper_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B 1 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases he : x≤11/100
  · have hdisp := upper_second_displacement hs ht ⟨hx.1,he⟩ hm
    have hh := upper_of_displacement hs ht hx.1
      (show (1061/1000)*(1-A-b)≤x by nlinarith [hx.1])
    linarith
  · have hh := late_angle hs ht
      (show (419/250:ℝ)≤Real.pi/2+x by linarith [pi_hand_enclosure.1])
    linarith

end PositiveThree

end SquaresInCircles.Eight.TableFree.SecondWord
