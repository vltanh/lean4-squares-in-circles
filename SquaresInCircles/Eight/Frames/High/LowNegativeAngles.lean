module

public import SquaresInCircles.Eight.Frames.Low.HighParallel

/-!
# Eight squares: the whole negative-angle high/low secondary contact deformation

The source contact coordinate is explicit and remains on the original
high arc while the angle moves to zero.  The derivative is strictly
negative on the complete interval `[-.272,0]`.  No continuation or
alignment conclusion is supplied as an input.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowNegativeAngles
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameLowHighParallelCalculus FrameLowHighParallelBounds

def domain : Set ℝ := Icc (-(34/125:ℝ)) 0

theorem width_actual {x : ℝ} (hx : x∈domain) :
    FrameLowHighParallelCalculus.width false x=pairWidth x ∧ FrameLowHighParallelCalculus.width false x-1=periodicFrameCost x := by
  have hh := negative_width (show x∈Icc (-(54/125:ℝ)) 0 from
    ⟨by linarith [hx.1],hx.2⟩)
  constructor
  · simpa [FrameLowHighParallelCalculus.width] using hh.1.symm
  · rw [hh.2]
    dsimp [FrameLowHighParallelCalculus.width]
    ring

theorem P_lower {B x : ℝ} (hB : B∈Icc 0 b1) (hx : x∈domain) :
    (159/100:ℝ)<P false B x := by
  have ht := negative_trig hx
  have hA := A_low_bounds hB
  have hAc := mul_le_mul
    (show (899/500:ℝ)≤A B+1/2 by linarith [hA.1,a1_precise.1]) ht.2.2.le
    (by norm_num : (0:ℝ)≤963/1000) (by linarith [hA.1,a1_precise.1] : 0≤A B+1/2)
  have hcoef : 0≤1/2-B := by linarith [hB.2,b1_bounds.2]
  have hBs := mul_le_mul_of_nonneg_left
    (show -(34/125:ℝ)≤Real.sin x by linarith [ht.2.1]) hcoef
  dsimp [P,widthD]
  nlinarith [hB.1]

theorem height_antitone {B : ℝ} (hB : B∈Icc 0 b1) :
    AntitoneOn (height false B) domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (height_deriv false B x).continuousAt.continuousWithinAt
  · exact fun x _ => height_deriv false B x
  · intro x hx
    have hh := P_lower hB (Ioo_subset_Icc_self hx)
    linarith

theorem source_contact_le {b B x : ℝ} (hx : x∈domain)
    (hm : 0≤ secondary true false b B x) : height false B x≤b := by
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hm
  dsimp [height]
  rw [(width_actual hx).1]
  linarith

theorem contact_high {b B x t : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true false b B x) (ht : t∈Icc x 0) :
    height false B t∈Icc b2 c0 := by
  have htd : t∈domain := ⟨hx.1.trans ht.1,ht.2⟩
  have h0 := height_antitone hB htd (show (0:ℝ)∈domain by constructor <;> norm_num) ht.2
  have h1 := height_antitone hB hx htd ht.1
  rw [height_zero] at h0
  have hsource := source_contact_le hx hm
  exact ⟨by linarith [hB.2,b1_bounds.2,b2_bounds.2],by linarith [hb.2]⟩

theorem contact_wide {b B x t : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true false b B x) (ht : t∈Icc x 0) :
    height false B t∈Icc (16/25:ℝ) (93/100) := by
  have htd : t∈domain := ⟨hx.1.trans ht.1,ht.2⟩
  have h0 := height_antitone hB htd (show (0:ℝ)∈domain by constructor <;> norm_num) ht.2
  rw [height_zero] at h0
  have hh := contact_high hb hB hx hm ht
  constructor <;> linarith [hB.2,b1_bounds.2,hh.2,c0_bounds.2]

theorem cost_derivative_negative {B x : ℝ} (hB : B∈Icc 0 b1) (hx : x∈domain)
    (hz : height false B x∈Icc b2 c0) : highD false B x<0 := by
  have hp := P_lower hB hx
  have hd := high_Hd_lower hz
  have hm := mul_le_mul hd.le hp.le (by norm_num : (0:ℝ)≤159/100)
    (by linarith : 0≤Hd (height false B x))
  have hs := (negative_trig hx).1
  have hc := Real.cos_le_one x
  dsimp [highD,widthD]
  nlinarith

theorem move_to_zero {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true false b B x) :
    highCost false B 0≤highCost false B x := by
  have ha : AntitoneOn (highCost false B) (Icc x 0) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro t ht
      exact (highCost_deriv false (contact_wide hb hB hx hm ht)).continuousAt.continuousWithinAt
    · intro t ht
      exact highCost_deriv false (contact_wide hb hB hx hm (Ioo_subset_Icc_self ht))
    · intro t ht
      exact (cost_derivative_negative hB ⟨hx.1.trans ht.1.le,ht.2.le⟩
        (contact_high hb hB hx hm (Ioo_subset_Icc_self ht))).le
  exact ha ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2

theorem weak_separator {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<highLowCost true false b B x := by
  have hzero := contact_high hb hB hx hm (show (0:ℝ)∈Icc x 0 from ⟨hx.2,le_rfl⟩)
  rw [height_zero] at hzero
  have ha := FrameLowHighAligned.parallel_contact hB hzero (by linarith : (1:ℝ)≤B+(1-B))
  have hinitial : (8833/10000:ℝ)<highCost false B 0 := by
    rw [FrameLowHighParallel.highCost_zero]
    linarith [FrameLowHighAligned.F0_lower]
  have hmove := move_to_zero hb hB hx hm
  have hheight := source_contact_le hx hm
  have hlabel := H_monotone (contact_high hb hB hx hm ⟨le_rfl,hx.2⟩) hb hheight
  have hcost : highCost false B x≤highLowCost true false b B x := by
    dsimp [highCost,highLowCost,sign]
    rw [(width_actual hx).2]
    linarith
  exact hinitial.trans_le (hmove.trans hcost)

end SquaresInCircles.Eight.FrameHighLowNegativeAngles
