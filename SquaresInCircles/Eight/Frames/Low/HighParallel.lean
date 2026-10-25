module

public import SquaresInCircles.Eight.Frames.Low.HighExtendedAligned
public import SquaresInCircles.Eight.Frames.Low.HighParallelBounds

/-!
# Eight squares: the low/high parallel strip

A positive low source and a negative high target separated along the secondary axis of the low
square, at a frame angle `|x| ≤ 1/50`, have the cost of the pair above `8833/10000`
(`low_high_strip`). The target is held fixed, and the source moves along its segment of secondary
contact to the angle `0`, where the cost is that of an aligned contact; along the segment the
source coordinate is given by a formula, and the derivative of its marker has the sign that lowers
the cost (`low_move_to_zero`, `low_phase`). The markers are extended beyond the cuts of the types,
so the segment may cross a cut while the pair and its axis stay the same.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighParallel
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameLowHighParallelCalculus FrameLowHighParallelBounds

theorem segment_self (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    x∈segment positive x := by
  cases positive <;> simp only [angleDomain,FrameLowHighParallelBounds.segment,Bool.false_eq_true,ite_false,ite_true] at *
  · exact ⟨le_rfl,hx.2⟩
  · exact ⟨hx.1,le_rfl⟩

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

theorem low_high_strip {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(1/50:ℝ)) (1/50)) (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<lowHighCost true false b B x := by
  by_cases hsign : x≤0
  · exact low_phase false hb hB ⟨hx.1,hsign⟩ hm
  · exact low_phase true hb hB ⟨le_of_not_ge hsign,hx.2⟩ hm

end SquaresInCircles.Eight.FrameLowHighParallel
