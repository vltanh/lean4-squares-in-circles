module

public import SquaresInCircles.Eight.TableFree.FrameLowHighPositiveLate
public import SquaresInCircles.Eight.TableFree.FrameLowHighNegativeAngles
public import SquaresInCircles.Eight.TableFree.FrameLowHighSecondaryOpposite
public import SquaresInCircles.Eight.TableFree.FrameLowHighPrimaryPositive

/-!
# Every original low-source axis in a low/high pair

Both source axes and all four original sign choices are joined here.
Exact reflected reversal also supplies both target-owned high/low
axes.  Weak witnesses and intrinsic arc endpoint ties are retained.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighSourceAxes
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameHighArc FrameLowHighGeometry

theorem secondary_all (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : -(34/125:ℝ)≤x)
    (hm : 0≤secondary i k b B x) : (8833/10000:ℝ)<lowHighCost i k b B x := by
  cases i <;> cases k
  · exact FrameLowHighCuts.negative_negative_secondary hb hB hx hm
  · exact FrameLowHighSecondaryOpposite.weak_separator hb hB hx hm
  · exact FrameLowHighNegativeAngles.positive_negative_secondary hb hB hx hm
  · exact FrameLowHighPositiveLate.positive_positive_secondary hb hB hx hm

theorem source_secondary_low_high (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 0 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hb := (state_low_chart s hs).2
  have hB := (state_high_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_secondary s t
    (by simp [ht,Branch.type]) x).mp hm
  have hx := low_high_angle s t hs hgap
  rw [state_low_high_cost s t hs ht]
  exact secondary_all s.positive t.positive hb hB hx.le hmargin

theorem source_primary_low_high (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 3 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hb := (state_low_chart s hs).2
  have hB := (state_high_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_primary s t
    (by simp [hs,Branch.type]) (by simp [ht,Branch.type]) x).mp hm
  have hx := low_high_angle s t hs hgap
  rw [state_low_high_cost s t hs ht]
  exact FrameLowHighPrimaryPositive.low_high_primary s.positive t.positive hb hB hx.le hmargin

theorem target_secondary_high_low (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 2 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hh := source_secondary_low_high t.flip s.flip
    (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
    (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
  simpa using hh

theorem target_primary_high_low (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 1 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hh := source_primary_low_high t.flip s.flip
    (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
    (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
  simpa using hh

end SquaresInCircles.Eight.TableFree.FrameLowHighSourceAxes
