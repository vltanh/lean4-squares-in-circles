module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighCoreSecondary

/-!
# The complete original core/high frame-pair inequality

Both orientations, both original tangent signs and every weak forward
separating axis are included.  The angle restrictions used internally
are derived from the original exterior gap and the original witnesses.
No concentrated frame, selected owner or strict separation is assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighPair
open FramePair FrameCircleArc FrameHighArc FrameCoreArc
open FrameCoreHighGeometry

theorem pair_angle_lower (s t : FramePair.State) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) : -(203/250:ℝ)<x := by
  have hs := s.offset_range
  have ht := t.offset_range
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem positive_target_angle (s t : FramePair.State) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (ht : t.positive=true) : -(13/500:ℝ)<x := by
  have hs := s.offset_range.2
  have hratio : 0≤t.b/t.a := div_nonneg t.b_nonneg t.a_pos.le
  have hangle : 0≤Real.arctan (t.b/t.a) := by
    simpa using Real.arctan_mono hratio
  have htarget : 0≤t.offset := by simpa [State.offset,ht,sign] using hangle
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem state_core_high_cost (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.high) (x : ℝ) :
    s.cost t x=coreHighCost s.positive t.positive s.a s.b t.b x := by
  rw [State.cost,state_core_label s hs,state_high_label t ht]
  rfl

theorem state_high_core_cost (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch.type=0) (x : ℝ) :
    s.cost t x=highCoreCost s.positive t.positive s.b t.a t.b x := by
  rw [State.cost,state_high_label s hs,state_core_label t ht]
  rfl

theorem state_core_high_secondary (s t : FramePair.State)
    (ht : t.branch=.high) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤coreHighSecondary s.positive t.positive s.a s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,(state_high_chart t ht).1]
  rfl

theorem state_core_high_primary (s t : FramePair.State)
    (ht : t.branch=.high) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤coreHighPrimary t.positive s.a t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_succ,Matrix.cons_val_zero,
    (state_high_chart t ht).1]
  rfl

theorem state_high_core_secondary (s t : FramePair.State) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤highCoreSecondary s.positive t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero]
  rfl

theorem state_high_core_primary (s t : FramePair.State)
    (hs : s.branch=.high) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤highCorePrimary t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_succ,Matrix.cons_val_zero,
    (state_high_chart s hs).1]
  rfl

theorem source_core_secondary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hc := state_core_chart s hs
  have hH := (state_high_chart t ht).2
  rw [state_core_high_cost s t hs ht]
  by_cases hlarge : (5/2:ℝ)≤x
  · exact core_high_tail s.positive t.positive hc hH hlarge
  · exact FrameCoreHighCoreSecondary.core_secondary s.positive t.positive hc hH
      ⟨(pair_angle_lower s t hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_high_secondary s t ht x).mp hm)

theorem source_core_primary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hc := state_core_chart s hs
  have hH := (state_high_chart t ht).2
  rw [state_core_high_cost s t hs ht]
  by_cases hlarge : (5/2:ℝ)≤x
  · exact core_high_tail s.positive t.positive hc hH hlarge
  · exact FrameCoreHighCorePrimary.core_primary s.positive t.positive hc hH
      ⟨(pair_angle_lower s t hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_high_primary s t ht x).mp hm)

theorem source_high_secondary (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch.type=0) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hH := (state_high_chart s hs).2
  have hc := state_core_chart t ht
  rw [state_high_core_cost s t hs ht]
  by_cases hlarge : (5/2:ℝ)≤x
  · exact high_core_tail s.positive t.positive hH hc hlarge
  · exact FrameCoreHighHighSecondary.high_secondary s.positive t.positive hH hc
      ⟨(pair_angle_lower s t hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_high_core_secondary s t x).mp hm)

theorem source_high_primary (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch.type=0) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hH := (state_high_chart s hs).2
  have hc := state_core_chart t ht
  rw [state_high_core_cost s t hs ht]
  by_cases hlarge : (5/2:ℝ)≤x
  · exact high_core_tail s.positive t.positive hH hc hlarge
  · exact FrameCoreHighHighPrimary.high_primary s.positive t.positive hH hc
      ⟨(pair_angle_lower s t hgap).le,(lt_of_not_ge hlarge).le⟩
      (fun hj => (positive_target_angle s t hgap hj).le)
      ((state_high_core_primary s t hs x).mp hm)

/-- Every original weak axis in the core-to-high orientation. -/
theorem core_high_pair (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.high) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(8833/10000:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_core_secondary s t hs ht hgap hm
  · have hh := source_high_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_high_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_core_primary s t hs ht hgap hm

/-- Every original weak axis in the high-to-core orientation. -/
theorem high_core_pair (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch.type=0) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(8833/10000:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_high_secondary s t hs ht hgap hm
  · have hh := source_core_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_core_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_high_primary s t hs ht hgap hm

theorem core_high_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : (branchOf C i).type=0) (hj : branchOf C (next i)=.high)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact core_high_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem high_core_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.high) (hj : (branchOf C (next i)).type=0)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact high_core_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.TableFree.FrameCoreHighPair
