module

public import SquaresInCircles.Eight.TableFree.FrameHighLowPrimaryNegativeTarget
public import SquaresInCircles.Eight.TableFree.FrameHighLowUpperConstant
public import SquaresInCircles.Eight.TableFree.FrameHighLowUpperAffine

/-!
# Every original high-source primary axis in the high/low pair

Both target signs and every rotated angle are covered by the
continuous contact, constant support, affine support, and direct
tail arguments.  The quarter rotation and the restoration of the
original source sign are exact comparisons on the same two states.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowPrimary
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry
open FrameHighLowPrimaryGeometry

theorem upper_positive {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : -(2/5:ℝ)≤x) (hm : 0≤upperMargin true z B x) :
    (8833/10000:ℝ)<upperCost true z B x := by
  by_cases hnegative : x≤0
  · exact FrameHighLowPrimaryNegative.weak_separator true hz hB ⟨hx,hnegative⟩ hm
  by_cases hearly : x≤2/25
  · exact FrameHighLowPrimaryPositiveEarly.weak_separator hz hB
      ⟨le_of_not_ge hnegative,hearly⟩ hm
  by_cases hconstant : x≤11/100
  · exact FrameHighLowUpperConstant.weak_separator hz hB
      ⟨le_of_not_ge hearly,hconstant⟩ hm
  by_cases haffine : x≤23/50
  · exact FrameHighLowUpperAffine.weak_separator hz hB
      ⟨le_of_not_ge hconstant,haffine⟩ hm
  · exact positive_target_tail hz hB (le_of_not_ge haffine)

theorem upper_all (k : Bool) {z B x : ℝ} (hz : z∈sourceDomain)
    (hB : B∈Icc 0 b1) (hx : -(2/5:ℝ)≤x) (hm : 0≤upperMargin k z B x) :
    (8833/10000:ℝ)<upperCost k z B x := by
  cases k
  · exact FrameHighLowPrimaryNegativeTarget.weak_separator hz hB hx hm
  · exact upper_positive hz hB hx hm

theorem weak_separator (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤primary k b B x) : (8833/10000:ℝ)<highLowCost i k b B x := by
  apply lt_of_lt_of_le _ (high_low_weaken_source i k hb)
  have he := rotated_angle k hb hB hx hm
  have heq : Real.pi/2+(x-Real.pi/2)=x := by ring
  have hrotated : 0≤upperMargin k (A b) B (x-Real.pi/2) := by
    rw [← rotated_margin,heq]
    exact hm
  have hh := upper_all k (source_chart hb) hB he.le hrotated
  rw [← rotated_cost k hb,heq] at hh
  exact hh

theorem source_primary_high_low (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 3 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hb := (state_high_chart s hs).2
  have hB := (state_low_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_primary s t
    (by simp [hs,Branch.type]) (by simp [ht,Branch.type]) x).mp hm
  have hx := high_low_angle s t ht hgap
  rw [state_high_low_cost s t hs ht]
  exact weak_separator s.positive t.positive hb hB hx.le hmargin

theorem target_primary_low_high (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 1 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hh := source_primary_high_low t.flip s.flip
    (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
    (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
  simpa using hh

end SquaresInCircles.Eight.TableFree.FrameHighLowPrimary
