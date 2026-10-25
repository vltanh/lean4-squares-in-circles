module

public import SquaresInCircles.Eight.TableFree.FrameLowHighParallelBounds

/-!
# The full low/high parallel strip from an original weak separator

The original target is held fixed.  The source coordinate on secondary
contact is explicit, and its marker derivative has the required sign
on the whole segment to zero.  Enlarged scalar marker domains allow
the comparison to cross an intrinsic type cut without replacing the
original physical pair or choosing a different feasible axis.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighParallel
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameLowHighParallelCalculus FrameLowHighParallelBounds

theorem segment_self (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    x∈segment positive x := by
  cases positive <;> simp only [angleDomain,FrameLowHighParallelBounds.segment,Bool.false_eq_true,ite_false,ite_true] at *
  · exact ⟨le_rfl,hx.2⟩
  · exact ⟨hx.1,le_rfl⟩

theorem segment_zero (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    (0:ℝ)∈segment positive x := by
  cases positive <;> simp only [angleDomain,FrameLowHighParallelBounds.segment,Bool.false_eq_true,ite_false,ite_true] at *
  · exact ⟨hx.2,le_rfl⟩
  · exact ⟨le_rfl,hx.1⟩

@[simp] theorem lowCost_zero (positive : Bool) (B : ℝ) :
    lowCost positive B 0=L (1-B)+H B := by
  cases positive <;> simp [lowCost,height,FrameLowHighParallelCalculus.width]

@[simp] theorem highCost_zero (positive : Bool) (B : ℝ) :
    highCost positive B 0=H (1-B)+L B := by
  cases positive <;> simp [highCost,height,FrameLowHighParallelCalculus.width]

theorem low_move_to_zero (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true false b B x) :
    lowCost positive B 0≤lowCost positive B x := by
  have hd t (ht : t∈segment positive x) :=
    lowCost_deriv positive (low_height_domain positive hb hB hx hm ht)
  cases positive with
  | false =>
      have hc : AntitoneOn (lowCost false B) (Icc x 0) := by
        apply antiOn_of_hasDeriv_nonpos
        · intro t ht
          exact (hd t (by simpa [FrameLowHighParallelBounds.segment] using ht)).continuousAt.continuousWithinAt
        · intro t ht
          exact hd t (by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht)
        · intro t ht
          have hts : t∈segment false x := by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht
          exact (lowD_sign false hB (segment_angle false hx hts)
            (low_height_domain false hb hB hx hm hts)).le
      exact hc ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2
  | true =>
      have hc : MonotoneOn (lowCost true B) (Icc 0 x) := by
        apply monoOn_of_hasDeriv_nonneg
        · intro t ht
          exact (hd t (by simpa [FrameLowHighParallelBounds.segment] using ht)).continuousAt.continuousWithinAt
        · intro t ht
          exact hd t (by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht)
        · intro t ht
          have hts : t∈segment true x := by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht
          exact (lowD_sign true hB (segment_angle true hx hts)
            (low_height_domain true hb hB hx hm hts)).le
      exact hc ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1

theorem high_move_to_zero (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true false b B x) :
    highCost positive B 0≤highCost positive B x := by
  have hBl := low_target_cut positive hb hB hx hm
  have hd t (ht : t∈segment positive x) :=
    highCost_deriv positive (high_height_domain positive hb hB hx hm ht)
  cases positive with
  | false =>
      have hc : AntitoneOn (highCost false B) (Icc x 0) := by
        apply antiOn_of_hasDeriv_nonpos
        · intro t ht
          exact (hd t (by simpa [FrameLowHighParallelBounds.segment] using ht)).continuousAt.continuousWithinAt
        · intro t ht
          exact hd t (by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht)
        · intro t ht
          have hts : t∈segment false x := by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht
          exact (highD_sign false hB hBl (segment_angle false hx hts)
            (high_height_domain false hb hB hx hm hts)).le
      exact hc ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2
  | true =>
      have hc : MonotoneOn (highCost true B) (Icc 0 x) := by
        apply monoOn_of_hasDeriv_nonneg
        · intro t ht
          exact (hd t (by simpa [FrameLowHighParallelBounds.segment] using ht)).continuousAt.continuousWithinAt
        · intro t ht
          exact hd t (by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht)
        · intro t ht
          have hts : t∈segment true x := by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht
          exact (highD_sign true hB hBl (segment_angle true hx hts)
            (high_height_domain true hb hB hx hm hts)).le
      exact hc ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1

theorem low_phase (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<lowHighCost true false b B x := by
  have hcut := high_target_cut positive hb hB hx hm
  have haligned : 1-B∈FrameLowHighExtendedAligned.domain := by
    constructor <;> linarith [hB.2,c0_bounds.2]
  have hz := FrameLowHighExtendedAligned.strict_lower haligned
  have hcancel : 1-(1-B)=B := by ring
  rw [hcancel] at hz
  have hzero : (8833/10000:ℝ)<lowCost positive B 0 := by
    simpa only [lowCost_zero] using hz
  have hmove := low_move_to_zero positive hb hB hx hm
  have hpath := low_height_domain positive hb hB hx hm (segment_self positive hx)
  have hbwide : b∈Icc (0:ℝ) (7/20) := ⟨hb.1,by linarith [hb.2,b1_bounds.2]⟩
  have hlabel := low_label_monotone hpath hbwide (height_le_source positive hx hm)
  have hcontact : lowCost positive B x≤lowHighCost true false b B x := by
    dsimp [lowCost,lowHighCost,sign]
    rw [width_charge positive hx]
    linarith
  exact hzero.trans_le (hmove.trans hcontact)

theorem high_phase (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<highLowCost true false b B x := by
  have hcut := low_target_cut positive hb hB hx hm
  have haligned : B∈FrameLowHighExtendedAligned.domain := by
    constructor <;> linarith [hB.2,b1_bounds.2]
  have hz := FrameLowHighExtendedAligned.strict_lower haligned
  have hzero : (8833/10000:ℝ)<highCost positive B 0 := by
    rw [highCost_zero]
    linarith
  have hmove := high_move_to_zero positive hb hB hx hm
  have hpath := high_height_domain positive hb hB hx hm (segment_self positive hx)
  have hheight := height_le_source positive hx hm
  have hbwide : b∈Icc (16/25:ℝ) (93/100) := by
    constructor <;> linarith [hpath.1,hb.2,c0_bounds.2]
  have hlabel := high_label_monotone hpath hbwide hheight
  have hcontact : highCost positive B x≤highLowCost true false b B x := by
    dsimp [highCost,highLowCost,sign]
    rw [width_charge positive hx]
    linarith
  exact hzero.trans_le (hmove.trans hcontact)

theorem low_high_strip {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(1/50:ℝ)) (1/50)) (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<lowHighCost true false b B x := by
  by_cases hsign : x≤0
  · exact low_phase false hb hB ⟨hx.1,hsign⟩ hm
  · exact low_phase true hb hB ⟨le_of_not_ge hsign,hx.2⟩ hm

theorem high_low_strip {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (-(1/50:ℝ)) (1/50)) (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<highLowCost true false b B x := by
  by_cases hsign : x≤0
  · exact high_phase false hb hB ⟨hx.1,hsign⟩ hm
  · exact high_phase true hb hB ⟨le_of_not_ge hsign,hx.2⟩ hm

end SquaresInCircles.Eight.TableFree.FrameLowHighParallel
