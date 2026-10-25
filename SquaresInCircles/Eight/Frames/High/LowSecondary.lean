module

public import SquaresInCircles.Eight.Frames.High.LowContactSelection
public import SquaresInCircles.Eight.Frames.High.LowNegativeAngles
public import SquaresInCircles.Eight.Frames.High.LowPositiveCircle

/-!
# Eight squares: the secondary axis of a high source in a high/low pair

A high state and a low state separated along the secondary axis of the high square, at a frame
angle `x ≥ -34/125`, have the cost of the pair above `8833/10000` (`secondary_all`,
`source_secondary_high_low`; `target_secondary_low_high` for the reversed pair); the source is
positive (`high_source_secondary_positive`). For a negative target and `0 < x < 23/50`, the weak
separator is compared with a contact of the two arcs (`interval_weak_separator`): when the
contact height `height x B` reaches the high arc, the cost is at least that of the contact
(`contact_cost_le`); otherwise the continuity of the height and its value at the lower corner
give a contact at the cut `b2`. The diagonal and axial costs of `FrameHighLowContactSelection`
cover the contacts, negative angles follow by `FrameHighLowNegativeAngles.weak_separator`,
angles beyond `23/50` by the tail `high_low_tail`, and a positive target by
`FrameHighLowPositiveCircle.weak_separator`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowSecondary
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameHighLowContactSurface

theorem contact_cost_le {b B x : ℝ} (hb : b∈Icc b2 c0) (_hB : B∈Icc 0 b1)
    (hx : x∈FrameHighLowAxialGeometry.domain) (hz : height x B∈Icc b2 c0)
    (hheight : height x B≤b) : F x B≤highLowCost true false b B x := by
  have hh := H_monotone hz hb hheight
  dsimp [F,highLowCost,sign]
  rw [(first_width (FrameHighLowAxialGeometry.quadrant hx)).2]
  linarith

theorem interval_weak_separator {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : x∈FrameHighLowAxialGeometry.domain) (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<highLowCost true false b B x := by
  have hheight := height_le_source hx hm
  by_cases hcontact : b2≤height x B
  · have hz : height x B∈Icc b2 c0 := ⟨hcontact,hheight.trans hb.2⟩
    exact (FrameHighLowContactSelection.contact_lower hx hB hz).trans_le
      (contact_cost_le hb hB hx hz hheight)
  · have hcorner : b2<height x 0 := by
      rw [height_zero]
      linarith [(FrameHighLowAxialGeometry.Z_bounds hx).1,b2_bounds.2]
    have hc : ContinuousOn (fun t => -height x t) (Icc 0 B) := by
      intro t ht
      exact (height_deriv (show t∈lowDomain from
        ⟨by linarith [ht.1],ht.2.trans hB.2⟩) x).neg.continuousAt.continuousWithinAt
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc hB.1 hc
      (show -b2∈Icc (-height x 0) (-height x B) by constructor <;> linarith)
    have heq : height x t=b2 := by linarith
    have htlow : t∈Icc 0 b1 := ⟨ht.1,ht.2.trans hB.2⟩
    have hthigh : height x t∈Icc b2 c0 := by rw [heq]; exact ⟨le_rfl,b2_mem.2⟩
    have hbound := FrameHighLowContactSelection.contact_lower hx htlow hthigh
    have hH := H_monotone (show b2∈Icc b2 c0 from ⟨le_rfl,b2_mem.2⟩) hb hb.1
    have hL := L_monotone htlow hB ht.2
    have hcost : F x t≤highLowCost true false b B x := by
      dsimp [F,highLowCost,sign]
      rw [heq,(first_width (FrameHighLowAxialGeometry.quadrant hx)).2]
      linarith
    exact hbound.trans_le hcost

theorem positive_negative {b B x : ℝ} (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : -(34/125:ℝ)≤x) (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<highLowCost true false b B x := by
  by_cases htail : (23/50:ℝ)≤x
  · exact high_low_tail true false hb hB htail
  by_cases hnegative : x≤0
  · exact FrameHighLowNegativeAngles.weak_separator hb hB ⟨hx,hnegative⟩ hm
  · exact interval_weak_separator hb hB ⟨le_of_not_ge hnegative,le_of_not_ge htail⟩ hm

theorem secondary_all (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤ secondary i k b B x) : (8833/10000:ℝ)<highLowCost i k b B x := by
  have hi := high_source_secondary_positive i k hb hB hm
  subst i
  cases k
  · exact positive_negative hb hB hx hm
  · exact FrameHighLowPositiveCircle.weak_separator hb hB hx hm

theorem source_secondary_high_low (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hb := (state_high_chart s hs).2
  have hB := (state_low_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_secondary s t
    (by simp [ht,Branch.type]) x).mp hm
  have hx := high_low_angle s t ht hgap
  rw [state_high_low_cost s t hs ht]
  exact secondary_all s.positive t.positive hb hB hx.le hmargin

theorem target_secondary_low_high (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 2 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hh := source_secondary_high_low t.flip s.flip
    (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
    (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
  simpa using hh

end SquaresInCircles.Eight.FrameHighLowSecondary
