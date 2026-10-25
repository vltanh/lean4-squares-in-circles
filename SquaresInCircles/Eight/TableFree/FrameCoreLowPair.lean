module

public import SquaresInCircles.Eight.TableFree.FrameCoreLowLowPrimary

/-!
# The complete original core/low frame-pair inequality

Both orientations, both original signs and all four weak forward axes
are included.  The only angular premise is the original exterior gap.
The proof derives each angle cut from separation and covers target axes
by reflected reversal, preserving their actual cost and all ties.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreLowPair
open FramePair FrameCircleArc FrameLowArc FrameCoreArc
open FrameCoreLowGeometry FrameCoreLowSecondary FrameCoreLowCorePrimary FrameCoreLowLowPrimary

theorem core_low_angle (s t : FramePair.State)
    (ht : t.branch=.low) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(3/10:ℝ)<x := by
  have hs := s.offset_range
  have hh := low_offset_bounds t ht
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem low_core_angle (s t : FramePair.State)
    (hs : s.branch=.low) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    -(3/10:ℝ)<x := by
  have ht := t.offset_range
  have hh := low_offset_bounds s hs
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem state_core_low_cost (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.low) (x : ℝ) :
    s.cost t x=coreLowCost s.positive t.positive s.a s.b t.b x := by
  rw [State.cost,state_core_label s hs,state_low_label t ht]
  rfl

theorem state_low_core_cost (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch.type=0) (x : ℝ) :
    s.cost t x=lowCoreCost s.positive t.positive s.b t.a t.b x := by
  rw [State.cost,state_low_label s hs,state_core_label t ht]
  rfl

theorem state_core_low_secondary (s t : FramePair.State)
    (ht : t.branch=.low) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤coreLowSecondary s.positive t.positive s.a s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,(state_low_chart t ht).1]
  rfl

theorem state_core_low_primary (s t : FramePair.State)
    (ht : t.branch=.low) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤coreLowPrimary t.positive s.a t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_succ,Matrix.cons_val_zero,
    (state_low_chart t ht).1]
  rfl

theorem state_low_core_secondary (s t : FramePair.State) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤lowCoreSecondary s.positive t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero]
  rfl

theorem state_low_core_primary (s t : FramePair.State)
    (hs : s.branch=.low) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤lowCorePrimary t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_succ,Matrix.cons_val_zero,
    (state_low_chart s hs).1]
  rfl

theorem source_core_secondary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (91/100:ℝ)<s.cost t x := by
  have hcore := state_core_chart s hs
  have hlow := (state_low_chart t ht).2
  rw [state_core_low_cost s t hs ht]
  by_cases hlarge : (41/20:ℝ)≤x
  · exact core_low_tail s.positive t.positive hcore hlow hlarge
  · exact core_secondary s.positive t.positive hcore hlow
      ⟨(core_low_angle s t ht hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_low_secondary s t ht x).mp hm)

theorem source_core_primary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (91/100:ℝ)<s.cost t x := by
  have hcore := state_core_chart s hs
  have hlow := (state_low_chart t ht).2
  rw [state_core_low_cost s t hs ht]
  by_cases hlarge : (41/20:ℝ)≤x
  · exact core_low_tail s.positive t.positive hcore hlow hlarge
  · exact core_primary s.positive t.positive hcore hlow
      ⟨(core_low_angle s t ht hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_low_primary s t ht x).mp hm)

theorem source_low_secondary (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch.type=0) {x : ℝ}
    (hm : s.Feasible t 0 x) : False := by
  exact low_secondary_false s.positive t.positive (state_low_chart s hs).2
    (state_core_chart t ht) ((state_low_core_secondary s t x).mp hm)

theorem source_low_primary (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch.type=0) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (91/100:ℝ)<s.cost t x := by
  have hlow := (state_low_chart s hs).2
  have hcore := state_core_chart t ht
  rw [state_low_core_cost s t hs ht]
  by_cases hlarge : (41/20:ℝ)≤x
  · exact low_core_tail s.positive t.positive hlow hcore hlarge
  · exact low_primary s.positive t.positive hlow hcore
      ⟨(low_core_angle s t hs hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_low_core_primary s t hs x).mp hm)

/-- Every original weak forward witness in the core-to-low orientation. -/
theorem core_low_pair (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.low) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(91/100:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_core_secondary s t hs ht hgap hm
  · have hh := source_low_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · exact (source_low_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      ((s.target_secondary_reverse t x).mp hm)).elim
  · exact source_core_primary s t hs ht hgap hm

/-- Every original weak forward witness in the low-to-core orientation. -/
theorem low_core_pair (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch.type=0) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(91/100:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact (source_low_secondary s t hs ht hm).elim
  · have hh := source_core_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_core_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_low_primary s t hs ht hgap hm

theorem core_low_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : (branchOf C i).type=0) (hj : branchOf C (next i)=.low)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact core_low_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem low_core_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.low) (hj : (branchOf C (next i)).type=0)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact low_core_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.TableFree.FrameCoreLowPair
