module

public import SquaresInCircles.Eight.Frames.Core.MidPrimary
public import SquaresInCircles.Eight.Frames.Core.MidTransverse

/-!
# Eight squares: the complete original core/middle frame-pair inequality

Both orientations, both signs at each actual point and all four weak
forward witnesses are included.  Reflection reverses an edge without
changing its original cost.  The only angular premise is the already
proved original exterior gap, not a concentrated frame interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreMidPair
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FrameCoreMidGeometry FrameCoreMidTransverse FrameCoreMidPrimary

theorem core_mid_angle (s t : FramePair.State)
    (ht : t.branch=.middle) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(54/125:ℝ)<x := by
  have hs := s.offset_range
  have hh := middle_offset_bounds t ht
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem mid_core_angle (s t : FramePair.State)
    (hs : s.branch=.middle) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(54/125:ℝ)<x := by
  have ht := t.offset_range
  have hh := middle_offset_bounds s hs
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem state_core_mid_cost (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.middle) (x : ℝ) :
    s.cost t x=coreMidCost s.positive t.positive s.a s.b t.b x := by
  rw [State.cost,state_core_label s hs,state_mid_label t ht]
  rfl

theorem state_mid_core_cost (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch.type=0) (x : ℝ) :
    s.cost t x=midCoreCost s.positive t.positive s.b t.a t.b x := by
  rw [State.cost,state_mid_label s hs,state_core_label t ht]
  rfl

theorem state_core_mid_secondary (s t : FramePair.State)
    (ht : t.branch=.middle) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤coreMidSecondary s.positive t.positive s.a s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,(state_mid_chart t ht).1]
  rfl

theorem state_core_mid_primary (s t : FramePair.State)
    (ht : t.branch=.middle) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤coreMidPrimary t.positive s.a t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_mid_chart t ht).1]
  rfl

theorem state_mid_core_secondary (s t : FramePair.State) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤ midCoreSecondary s.positive t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero]
  rfl

theorem state_mid_core_primary (s t : FramePair.State)
    (hs : s.branch=.middle) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤ midCorePrimary t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_mid_chart s hs).1]
  rfl

theorem source_core_secondary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hcore := state_core_chart s hs
  have hmid := (state_mid_chart t ht).2
  rw [state_core_mid_cost s t hs ht]
  by_cases hlarge : (109/50:ℝ)≤x
  · exact core_mid_tail s.positive t.positive hcore hmid hlarge
  · exact core_secondary s.positive t.positive hcore hmid
      ⟨(core_mid_angle s t ht hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_mid_secondary s t ht x).mp hm)

theorem source_core_primary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hcore := state_core_chart s hs
  have hmid := (state_mid_chart t ht).2
  rw [state_core_mid_cost s t hs ht]
  by_cases hlarge : (109/50:ℝ)≤x
  · exact core_mid_tail s.positive t.positive hcore hmid hlarge
  · exact core_primary s.positive t.positive hcore hmid
      ⟨(core_mid_angle s t ht hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_mid_primary s t ht x).mp hm)

theorem source_middle_secondary (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch.type=0) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hmid := (state_mid_chart s hs).2
  have hcore := state_core_chart t ht
  rw [state_mid_core_cost s t hs ht]
  by_cases hlarge : (109/50:ℝ)≤x
  · exact mid_core_tail s.positive t.positive hmid hcore hlarge
  · exact middle_secondary s.positive t.positive hmid hcore
      ⟨(mid_core_angle s t hs hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_mid_core_secondary s t x).mp hm)

theorem source_middle_primary (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch.type=0) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hmid := (state_mid_chart s hs).2
  have hcore := state_core_chart t ht
  rw [state_mid_core_cost s t hs ht]
  by_cases hlarge : (109/50:ℝ)≤x
  · exact mid_core_tail s.positive t.positive hmid hcore hlarge
  · exact middle_primary s.positive t.positive hmid hcore
      ⟨(mid_core_angle s t hs hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_mid_core_primary s t hs x).mp hm)

/-- All original weak witnesses in the core-to-middle orientation. -/
theorem core_mid_pair (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.middle) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(1801/2000:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_core_secondary s t hs ht hgap hm
  · have hh := source_middle_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_middle_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_core_primary s t hs ht hgap hm

/-- All original weak witnesses in the middle-to-core orientation. -/
theorem mid_core_pair (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch.type=0) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(1801/2000:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_middle_secondary s t hs ht hgap hm
  · have hh := source_core_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_core_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_middle_primary s t hs ht hgap hm

theorem core_mid_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : (branchOf C i).type=0) (hj : branchOf C (next i)=.middle)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact core_mid_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem mid_core_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.middle) (hj : (branchOf C (next i)).type=0)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact mid_core_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.FrameCoreMidPair
