module

public import SquaresInCircles.Eight.TableFree.FrameLowHighSecondaryNegative

/-!
# Low-source angle cuts from the original weak margins

The cuts are geometric exclusions on complete angular intervals.
Their endpoint values are controlled by alternating Taylor estimates;
they do not presume an already concentrated frame word.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighCuts
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameLowHighGeometry

theorem trig_sum_short {x : ℝ} (hx : x∈Icc (0:ℝ) (3/10)) :
    Real.sin x+Real.cos x<1251/1000 := by
  have hm : MonotoneOn (fun z => Real.sin z+Real.cos z) (Icc (0:ℝ) (3/10)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => ((Real.hasDerivAt_sin z).add
        (Real.hasDerivAt_cos z)).continuousAt.continuousWithinAt
    · exact fun z _ => (Real.hasDerivAt_sin z).add (Real.hasDerivAt_cos z)
    · intro z hz
      have hs := Real.sin_le hz.1.le
      have hc := Real.one_sub_sq_div_two_le_cos (x := z)
      have hsq := pow_le_pow_left₀ hz.1.le hz.2.le 2
      nlinarith
  have hh := hm hx ⟨by norm_num,le_rfl⟩ hx.2
  have hs := sin_upper_five (show (0:ℝ)≤3/10 by norm_num)
  have hc := cos_upper_four (show (0:ℝ)≤3/10 by norm_num)
  norm_num at hs hc
  linarith

theorem negative_secondary_cut {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary false false b B x) : (3/10:ℝ)<x := by
  by_contra! hsmall
  by_cases hn : x≤0
  · have hh := nonpositive_secondary_owners false false
      ⟨hb.1,hb.2.trans b1_mem.2⟩ ⟨b2_mem.1.trans hB.1,hB.2⟩ ⟨hx,hn⟩ hm
    cases hh.1
  · have hx0 : 0≤x := (lt_of_not_ge hn).le
    have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨hx0,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hsin := Real.sin_le hx0
    have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
    have hsq := pow_le_pow_left₀ hx0 hsmall 2
    have htarget : MonotoneOn (linear (Real.sin x) (Real.cos x)) (Icc b2 c0) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact fun z hz => (linear_hasDerivAt
          ⟨b2_mem.1.trans hz.1,hz.2⟩ _ _).continuousAt.continuousWithinAt
      · exact fun z hz => linear_hasDerivAt
          ⟨b2_mem.1.trans hz.1.le,hz.2.le⟩ _ _
      · intro z hz
        have hr := slope_high_bounds (Ioo_subset_Icc_self hz)
        have hmul := mul_le_mul_of_nonneg_left hr.2 ht.1
        simp only [Ad,FrameLowArc.slope,neg_div] at hmul ⊢
        nlinarith
    have hp := htarget hB ⟨b2_mem.2,le_rfl⟩ hB.2
    dsimp [linear] at hp
    rw [A_c0] at hp
    have hsum := trig_sum_short ⟨hx0,hsmall⟩
    have hcoef : 0≤c0-1/2 := by linarith [c0_bounds.1]
    have hbound := mul_le_mul
      (show c0-1/2≤399215/1000000 by linarith [diagonal_precise.2]) hsum.le
      (by linarith [ht.1,ht.2.2.1] : 0≤Real.sin x+Real.cos x)
      (by norm_num : (0:ℝ)≤399215/1000000)
    dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hm
    rw [(first_width hxq).1] at hm
    nlinarith [hb.1]

def positiveCut (i : Bool) : ℝ := if i then 11/10 else 27/20

theorem positive_secondary_cut (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary i true b B x) : positiveCut i<x := by
  by_contra! hsmall
  by_cases hn : x≤0
  · have hh := nonpositive_secondary_owners i true
      ⟨hb.1,hb.2.trans b1_mem.2⟩ ⟨b2_mem.1.trans hB.1,hB.2⟩ ⟨hx,hn⟩ hm
    cases hh.2
  · have hx0 : 0≤x := (lt_of_not_ge hn).le
    have hcap : positiveCut i∈Icc 0 (Real.pi/2) := by
      cases i <;> dsimp [positiveCut] <;> constructor <;> linarith [FrameLowPair.pi_lower]
    have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx0,hsmall.trans hcap.2⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤x) hcap.2 hsmall
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx0
      (by linarith [hcap.2,Real.pi_pos]) hsmall
    have hsE := sin_upper_five hcap.1
    have hcE := cos_lower_six hcap.1
    have ha := A_high_bounds hB
    have hAs := mul_le_mul_of_nonneg_right
      (show A B-1/2≤7/10 by linarith [ha.2,a2_bounds.2]) ht.1
    have hBc := mul_le_mul_of_nonneg_right
      (show (10139/10000:ℝ)≤B+1/2 by linarith [hB.1,b2_bounds.1]) ht.2.2.1
    dsimp [secondary,FrameLowMidGeometry.secondary] at hm
    rw [(first_width hxq).1] at hm
    cases i <;> norm_num [positiveCut,sign] at *
    all_goals nlinarith [hb.1,hb.2,b1_bounds.2]

theorem negative_primary_cut {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤primary false b B x) : (3/5:ℝ)<x := by
  by_contra! hsmall
  by_cases hn : x≤0
  · exact (not_lt_of_ge hm) (nonpositive_primary_false false
      ⟨hb.1,hb.2.trans b1_mem.2⟩ ⟨b2_mem.1.trans hB.1,hB.2⟩ ⟨hx,hn⟩)
  · have hx0 : 0≤x := (lt_of_not_ge hn).le
    have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨hx0,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤x)
      (by linarith [FrameLowPair.pi_lower] : (3/5:ℝ)≤Real.pi/2) hsmall
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx0
      (by linarith [FrameLowPair.pi_lower] : (3/5:ℝ)≤Real.pi) hsmall
    have hsE := sin_upper_five (show (0:ℝ)≤3/5 by norm_num)
    have hcE := cos_lower_six (show (0:ℝ)≤3/5 by norm_num)
    norm_num at hsE hcE
    have hAc := mul_le_mul_of_nonneg_right
      (show (1399/1000:ℝ)≤A B+1/2 by linarith [(A_high_bounds hB).1,c0_bounds.1]) ht.2.2.1
    have hBs := mul_le_mul_of_nonneg_right
      (show B-1/2≤2/5 by linarith [hB.2,c0_bounds.2]) ht.1
    dsimp [primary,FrameLowMidGeometry.primary,sign] at hm
    rw [(first_width hxq).1] at hm
    nlinarith [(A_low_bounds hb).2,a0_precise.2]

theorem positive_primary_cut {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤primary true b B x) : Real.pi/2<x := by
  by_contra! hsmall
  by_cases hn : x≤0
  · exact (not_lt_of_ge hm) (nonpositive_primary_false true
      ⟨hb.1,hb.2.trans b1_mem.2⟩ ⟨b2_mem.1.trans hB.1,hB.2⟩ ⟨hx,hn⟩)
  · have hxq : x∈Icc 0 (Real.pi/2) := ⟨(lt_of_not_ge hn).le,hsmall⟩
    have ht := FrameLowPair.quadrant hxq
    have hw := FrameCoreArc.width_one_le x
    rw [(first_width hxq).1] at hw
    have hAc := mul_le_mul_of_nonneg_right
      (show (1013/1000:ℝ)≤A B+1/2 by linarith [(A_high_bounds hB).1,c0_bounds.1]) ht.2.2.1
    have hBs := mul_le_mul_of_nonneg_right
      (show (1013/1000:ℝ)≤B+1/2 by linarith [hB.1,b2_bounds.1]) ht.1
    dsimp [primary,FrameLowMidGeometry.primary,sign] at hm
    rw [(first_width hxq).1] at hm
    nlinarith [(A_low_bounds hb).2,a0_precise.2]

/-- One full original sign branch, including every angular tail. -/
theorem negative_negative_secondary {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary false false b B x) :
    (8833/10000:ℝ)<lowHighCost false false b B x := by
  have hcut := negative_secondary_cut hb hB hx hm
  by_cases htail : (4/5:ℝ)≤x
  · exact low_high_tail false false hb hB (by simpa [lowHighTail] using htail)
  · exact FrameLowHighSecondaryNegative.weak_separator false hb hB
      (by simpa [FrameLowHighSecondaryNegative.left,FrameLowHighSecondaryNegative.right]
        using (show x∈Icc (3/10:ℝ) (4/5) from ⟨hcut.le,(lt_of_not_ge htail).le⟩)) hm

end SquaresInCircles.Eight.TableFree.FrameLowHighCuts
