module

public import SquaresInCircles.Eight.Frames.High.LowPrimaryNegative
public import SquaresInCircles.Eight.Frames.High.LowUpperAffine
public import SquaresInCircles.Eight.Frames.High.LowUpperConstant
public import SquaresInCircles.Eight.Frames.High.LowUpperMinimum

/-!
# Eight squares: every original high-source primary axis in the high/low pair

Both target signs and every rotated angle are covered by the
continuous contact, constant support, affine support, and direct
tail arguments.  The quarter rotation and the restoration of the
original source sign are exact comparisons on the same two states.
-/

section
/-!
## Every original high-source primary with negative target

Weak separators first reach the actual explicit contact, or a
diagonal contact after decreasing the target coordinate.  If the
diagonal/axial corner still has slack, the angle decreases until
that corner reaches contact.  Every comparison retains its signed
cost and the original radius.  The remaining angular tail is direct.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowPrimaryNegativeTarget
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus
open FrameHighLowPrimaryGeometry FrameHighLowUpperSurface

def angular (x : ℝ) : ℝ := x-(9/100)*(Real.sin x+Real.cos x-1)

theorem cost_eq {z B x : ℝ} (hx : x∈domain) :
    upperCost false z B x=angular x+G z+L B := by
  dsimp [upperCost,sign,angular]
  rw [(first_width (FrameHighLowAxialGeometry.quadrant (domain_axial hx))).2]
  ring

theorem angular_monotone : MonotoneOn angular domain := by
  apply monoOn_of_hasDeriv_nonneg
  · intro x _
    exact ((hasDerivAt_id x).sub ((((Real.hasDerivAt_sin x).add
      (Real.hasDerivAt_cos x)).sub_const 1).const_mul (9/100))).continuousAt.continuousWithinAt
  · intro x _
    exact (hasDerivAt_id x).sub ((((Real.hasDerivAt_sin x).add
      (Real.hasDerivAt_cos x)).sub_const 1).const_mul (9/100))
  · intro x hx
    have ht := trig_bounds (Ioo_subset_Icc_self hx)
    linarith [ht.1,ht.2.2.2]

theorem source_contact_le {z B x : ℝ} (hx : x∈domain)
    (hm : 0≤upperMargin false z B x) : height x B≤z := by
  dsimp [upperMargin,sign] at hm
  rw [(first_width (FrameHighLowAxialGeometry.quadrant (domain_axial hx))).1] at hm
  dsimp [height,FrameHighLowContactSurface.height]
  linarith

theorem direct_contact {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤upperMargin false z B x) (hc : c0≤height x B) :
    (8833/10000:ℝ)<upperCost false z B x := by
  have hcontact := FrameHighLowUpperMinimum.contact_lower hx hB hc
  have hbound := (physical_contact_bounds hx hB hc).2
  have hG := FrameLowHighQuarterCalculus.G_monotone
    (source_extended ⟨hbound.1,by linarith [hbound.2,a2_bounds.1]⟩)
    (source_extended hz) (source_contact_le hx hm)
  rw [cost_eq hx]
  dsimp [F,angular] at *
  linarith

theorem diagonal_contact {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hbelow : height x B≤c0) (hzero : c0≤height x 0) :
    (8833/10000:ℝ)<upperCost false z B x := by
  have hc : ContinuousOn (fun t => -height x t) (Icc 0 B) := by
    intro t ht
    exact (FrameHighLowContactSurface.height_deriv
      (target_extended (show t∈Icc 0 b1 from ⟨ht.1,ht.2.trans hB.2⟩)) x).neg.continuousAt.continuousWithinAt
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hB.1 hc
    (show -c0∈Icc (-height x 0) (-height x B) by constructor <;> linarith)
  have heq : height x t=c0 := by linarith
  have htlow : t∈Icc 0 b1 := ⟨ht.1,ht.2.trans hB.2⟩
  have hcontact := FrameHighLowUpperMinimum.contact_lower hx htlow heq.ge
  have hL := L_monotone htlow hB ht.2
  have hG := source_G_lower hz
  rw [F,heq,G_c0] at hcontact
  rw [cost_eq hx]
  dsimp [angular]
  linarith

theorem slack_corner {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hbelow : height x 0≤c0) :
    (8833/10000:ℝ)<upperCost false z B x := by
  have hc : ContinuousOn (fun t => -height t 0) (Icc 0 x) := by
    exact fun t _ => (height_x_deriv t 0).neg.continuousAt.continuousWithinAt
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hx.1 hc
    (show -c0∈Icc (-height 0 0) (-height x 0) by
      rw [height_at_zero]
      constructor <;> linarith [c0_bounds.2])
  have heq : height t 0=c0 := by linarith
  have htdom : t∈domain := ⟨ht.1,ht.2.trans hx.2⟩
  have hcontact := FrameHighLowUpperMinimum.contact_lower htdom
    (show (0:ℝ)∈Icc 0 b1 from ⟨le_rfl,b1_mem.1⟩) heq.ge
  have hmove := angular_monotone htdom hx ht.2
  have hG := source_G_lower hz
  have hL := (L_bounds hB).1
  rw [F,heq,G_c0,L_zero,add_zero] at hcontact
  rw [cost_eq hx]
  dsimp [angular] at *
  linarith

theorem positive_angle {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤upperMargin false z B x) :
    (8833/10000:ℝ)<upperCost false z B x := by
  by_cases hc : c0≤height x B
  · exact direct_contact hz hB hx hm hc
  by_cases hzero : c0≤height x 0
  · exact diagonal_contact hz hB hx (le_of_not_ge hc) hzero
  · exact slack_corner hz hB hx (le_of_not_ge hzero)

theorem weak_separator {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : -(2/5:ℝ)≤x) (hm : 0≤upperMargin false z B x) :
    (8833/10000:ℝ)<upperCost false z B x := by
  by_cases hneg : x≤0
  · exact FrameHighLowPrimaryNegative.weak_separator false hz hB ⟨hx,hneg⟩ hm
  by_cases htail : (27/250:ℝ)≤x
  · exact negative_target_tail hz hB htail
  · exact positive_angle hz hB ⟨le_of_not_ge hneg,le_of_not_ge htail⟩ hm

end SquaresInCircles.Eight.FrameHighLowPrimaryNegativeTarget
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowPrimary
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
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
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
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 1 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hh := source_primary_high_low t.flip s.flip
    (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
    (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
  simpa using hh

end SquaresInCircles.Eight.FrameHighLowPrimary
end
end
end
