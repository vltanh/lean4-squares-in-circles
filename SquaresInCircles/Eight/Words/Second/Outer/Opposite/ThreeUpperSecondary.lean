module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeAligned

/-!
# Eight squares: both original upper-secondary opposite edge-three owners

The original weak separator bounds the total transverse and primary
displacement by two fifths of the angle.  At primary height at least
one the comparison is with the corresponding aligned state.  Below
one the actual circle slope compares with its primary-one endpoint.
The angular gain pays the entire label loss in both cases.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma upper_secondary_displacement {a b x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) : upperSecondary b x+1-a≤(2/5)*x := by
  have ht := positive_trig hx
  have hprimary := NegativeTwo.primary_mem hs
  have htransverse := NegativeTwo.source_mem hs
  have ha : 0≤a-1/2 := by linarith [hprimary.1,fine_outer_endpoint_bounds.2]
  have hc := mul_nonneg ha (sub_nonneg.mpr ht.2.1)
  have hsine := mul_le_mul_of_nonneg_right
    (show b-1/2≤2/5 by linarith [htransverse.2,outer_endpoint_bounds.2.2.2]) ht.2.2.1
  dsimp [upperSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  nlinarith [ht.2.2.2.2.1]

lemma tail_coordinate {a b : ℝ} (hs : OuterState a b) (ha : a≤1) :
    bOne≤b ∧ (43/50)*(b-bOne)≤1-a := by
  have hb := NegativeTwo.source_mem hs
  have hstate := ShortOuterOne.SameContact.primary_state primary_one_mem
  change OuterState 1 bOne at hstate
  have ha0 : 0≤a := hs.1.trans hs.2.1
  have horder : bOne≤b := by
    by_contra hh
    have hsq : (b+1/2)^2<(bOne+1/2)^2 := by
      nlinarith [mul_pos (sub_pos.2 (lt_of_not_ge hh))
        (show 0<bOne+b+1 by linarith [OppositeTwo.bOne_mem.1,hb.1])]
    nlinarith [hs.2.2,hstate.2.2,mul_nonneg (sub_nonneg.2 ha) (show 0≤a+2 by linarith)]
  have hr : (43/50:ℝ)<ratio bOne := by
    norm_num [ratio,OppositeTwo.bOne_arc]
    linarith [OppositeTwo.bOne_bounds.1]
  have hdom {t : ℝ} (ht : t∈Icc bOne outerDiagonal) : t∈Icc 0 outerDiagonal :=
    ⟨OppositeTwo.bOne_mem.1.trans ht.1,ht.2⟩
  have hmon : MonotoneOn (fun t => -arc t-(43/50)*t) (Icc bOne outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (((ShortOuterOne.SameContact.arc_hasDerivAt
        (outer_domain (hdom ht))).fun_neg).fun_sub
          ((hasDerivAt_id' t).const_mul (43/50))).continuousAt.continuousWithinAt)
      (fun t ht => ((ShortOuterOne.SameContact.arc_hasDerivAt
        (outer_domain (hdom (Ioo_subset_Icc_self ht)))).fun_neg).fun_sub
          ((hasDerivAt_id' t).const_mul (43/50)))
      (fun t ht => by
        have hh := ShortOuterOne.SameContact.ratio_monotone
          (outer_domain OppositeTwo.bOne_mem)
          (outer_domain (hdom (Ioo_subset_Icc_self ht))) ht.1.le
        linarith)
  have hh := hmon ⟨le_rfl,OppositeTwo.bOne_mem.2⟩ ⟨horder,hb.2⟩ horder
  dsimp only at hh
  rw [OppositeTwo.bOne_arc,(ShortOuterOne.SameContact.actual_arc hs).1] at hh
  exact ⟨horder,by linarith⟩

lemma T_tail_loss {a b : ℝ} (hs : OuterState a b) (ha : a≤1) :
    T b-T bOne≤(7/5)*(1-a) := by
  have hc := tail_coordinate hs ha
  have hh := T_increment_upper OppositeTwo.bOne_mem (NegativeTwo.source_mem hs) hc.1
  nlinarith

lemma L_tail_loss {a b : ℝ} (hs : OuterState a b) (ha : a≤1) :
    L b-L bOne≤(7/5)*(1-a) := by
  have hc := tail_coordinate hs ha
  have hh := L_increment_upper OppositeTwo.bOne_mem (NegativeTwo.source_mem hs) hc.1
  nlinarith

lemma primary_minus_one_mem {a b : ℝ} (hs : OuterState a b) (ha : 1≤a) :
    a-1∈Icc 0 outerDiagonal := by
  have hp := NegativeTwo.primary_mem hs
  constructor
  · linarith
  · linarith [hp.2,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]

theorem original_upper_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hcut := upper_source_secondary ht hx hm
  have hdisp : b+1-A≤(2/5)*x := by
    linarith [upper_secondary_displacement ht hx]
  by_cases hA : 1≤A
  · let j := A-1
    have hj : j∈Icc 0 outerDiagonal := primary_minus_one_mem ht hA
    have hstate := ShortOuterOne.SameContact.arc_state hj
    have haligned := aligned_first hstate ht (show 1≤A-j by dsimp [j]; linarith)
    by_cases hbj : b≤j
    · have hT := T_monotone hb hj hbj
      dsimp [value] at *
      linarith [hx.1]
    · have hT := T_increment_upper hj hb (le_of_not_ge hbj)
      have hd : b-j≤(2/5)*x := by dsimp [j]; linarith
      dsimp [value] at *
      nlinarith [hx.1]
  · have hzero := ShortOuterOne.SameContact.arc_state outer_zero_mem
    have hone := ShortOuterOne.SameContact.primary_state primary_one_mem
    change OuterState 1 bOne at hone
    have haligned := aligned_first hzero hone (by norm_num)
    have hT := T_increment_upper outer_zero_mem hb hb.1
    have hL := L_tail_loss ht (le_of_not_ge hA)
    have hsmall : T b-T 0≤(7/5)*b := by nlinarith [hb.1]
    dsimp [value] at *
    nlinarith [hx.1]

theorem original_upper_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hcut := upper_target_secondary hs hx hm
  have hdisp : B+1-a≤(2/5)*x := by
    linarith [upper_secondary_displacement hs hx]
  by_cases ha : 1≤a
  · let j := a-1
    have hj : j∈Icc 0 outerDiagonal := primary_minus_one_mem hs ha
    have hstate := ShortOuterOne.SameContact.arc_state hj
    have haligned := aligned_last hs hstate (show 1≤a-j by dsimp [j]; linarith)
    by_cases hBj : B≤j
    · have hL := L_monotone hB hj hBj
      dsimp [value] at *
      linarith [hx.1]
    · have hL := L_increment_upper hj hB (le_of_not_ge hBj)
      have hd : B-j≤(2/5)*x := by dsimp [j]; linarith
      dsimp [value] at *
      nlinarith [hx.1]
  · have hzero := ShortOuterOne.SameContact.arc_state outer_zero_mem
    have hone := ShortOuterOne.SameContact.primary_state primary_one_mem
    change OuterState 1 bOne at hone
    have haligned := aligned_last hone hzero (by norm_num)
    have hT := T_tail_loss hs (le_of_not_ge ha)
    have hL := L_increment_upper outer_zero_mem hB hB.1
    have hsmall : L B-L 0≤(7/5)*B := by nlinarith [hB.1]
    dsimp [value] at *
    nlinarith [hx.1]

end SquaresInCircles.Eight.SecondWord.OppositeThree
