module

public import SquaresInCircles.Eight.TableFree.FrameLowMidPrimary
public import SquaresInCircles.Eight.TableFree.FrameLowMidTransversePositive
public import SquaresInCircles.Eight.TableFree.FrameLowMidTransverseNegative
public import SquaresInCircles.Eight.TableFree.FrameLowMidSecondaryEndpoints
public import SquaresInCircles.Eight.TableFree.FrameLowMidSecondaryContinuation
public import SquaresInCircles.Eight.TableFree.FrameLowMidReverseTransverse

/-!
# The complete original low/middle frame-pair inequality

Both arc directions, both signed tangents and all four original weak
separating axes are included.  The two target-owned axes are transported
by exact reflected reversal.  The supplied physical witness is never
replaced by a preferred owner, and intrinsic endpoint ties stay in the
closed source and target domains.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidPair
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidGeometry

theorem source_secondary_low_mid (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 0 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hb := (state_low_chart s hs).2
  have hB := (state_mid_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_secondary s t
    (by simp [ht,Branch.type]) x).mp hm
  have hx := low_mid_angle s t hs ht hgap
  rw [state_low_mid_cost s t hs ht]
  cases hss : s.positive <;> cases htt : t.positive
  all_goals rw [hss,htt] at hmargin ⊢
  all_goals simp only [hss,htt,lowMidFloor,ite_true,ite_false] at hx
  · by_cases htail : (19/20:ℝ)≤x
    · exact low_mid_tail false false hb hB (by simpa [lowMidTail] using htail)
    · exact FrameLowMidSecondaryEndpoints.low_mid_negative_target false hb hB
        ⟨by simpa [FrameLowMidEndpointScalars.start] using hx,
          by linarith [FrameLowPair.pi_lower]⟩ hmargin
  · by_cases htail : (171/100:ℝ)≤x
    · exact low_mid_tail false true hb hB (by simpa [lowMidTail] using htail)
    · exact FrameLowMidTransverseNegative.weak_separator hb hB
        ⟨hx,(lt_of_not_ge htail).le⟩ hmargin
  · by_cases htail : (16/25:ℝ)≤x
    · exact low_mid_tail true false hb hB (by simpa [lowMidTail] using htail)
    · exact FrameLowMidSecondaryEndpoints.low_mid_negative_target true hb hB
        ⟨by simpa [FrameLowMidEndpointScalars.start] using hx,
          by linarith [FrameLowPair.pi_lower]⟩ hmargin
  · by_cases htail : (7/5:ℝ)≤x
    · exact low_mid_tail true true hb hB (by simpa [lowMidTail] using htail)
    · exact FrameLowMidTransversePositive.weak_separator hb hB
        ⟨hx,(lt_of_not_ge htail).le⟩ hmargin

theorem source_secondary_mid_low (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 0 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hb := (state_mid_chart s hs).2
  have hB := (state_low_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_secondary s t
    (by simp [ht,Branch.type]) x).mp hm
  have hx := mid_low_angle s t hs ht hgap
  rw [state_mid_low_cost s t hs ht]
  cases hss : s.positive <;> cases htt : t.positive
  all_goals rw [hss,htt] at hmargin ⊢
  all_goals simp only [hss,htt,midLowFloor,ite_true,ite_false] at hx
  · by_cases htail : (7/5:ℝ)≤x
    · exact mid_low_tail false false hb hB (by simpa [midLowTail] using htail)
    · exact FrameLowMidSecondaryContinuation.negative_weak_separator hb hB
        ⟨hx,(lt_of_not_ge htail).le⟩ hmargin
  · by_cases htail : (171/100:ℝ)≤x
    · exact mid_low_tail false true hb hB (by simpa [midLowTail] using htail)
    · exact FrameLowMidReverseTransverse.weak_separator hb hB
        ⟨hx,(lt_of_not_ge htail).le⟩ hmargin
  · by_cases htail : (16/25:ℝ)≤x
    · exact mid_low_tail true false hb hB (by simpa [midLowTail] using htail)
    · exact FrameLowMidSecondaryEndpoints.mid_low_positive_negative hb hB
        ⟨hx,(lt_of_not_ge htail).le⟩ hmargin
  · by_cases htail : (19/20:ℝ)≤x
    · exact mid_low_tail true true hb hB (by simpa [midLowTail] using htail)
    · have hcut := FrameLowMidCuts.mid_low_secondary_cut hb hB
        (by linarith : 0≤x) hmargin
      by_cases hcontact : x≤79/100
      · exact FrameLowMidContact.weak_separator hb hB ⟨hcut.le,hcontact⟩ hmargin
      · exact FrameLowMidSecondaryContinuation.positive_weak_separator hb hB
          ⟨(lt_of_not_ge hcontact).le,(lt_of_not_ge htail).le⟩ hmargin

theorem source_primary_low_mid (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 3 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hb := (state_low_chart s hs).2
  have hB := (state_mid_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_primary s t
    (by simp [hs,Branch.type]) (by simp [ht,Branch.type]) x).mp hm
  have hx := low_mid_angle s t hs ht hgap
  have hlo : 0≤lowMidFloor s.positive t.positive := by
    cases s.positive <;> cases t.positive <;> norm_num [lowMidFloor]
  rw [state_low_mid_cost s t hs ht]
  exact FrameLowMidPrimary.low_mid_primary s.positive t.positive hb hB
    (hlo.trans hx) hmargin

theorem source_primary_mid_low (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch=.low) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t 3 x) :
    (1801/2000:ℝ)<s.cost t x := by
  have hb := (state_mid_chart s hs).2
  have hB := (state_low_chart t ht).2
  have hmargin := (FrameLowMidGeometry.state_primary s t
    (by simp [hs,Branch.type]) (by simp [ht,Branch.type]) x).mp hm
  have hx := mid_low_angle s t hs ht hgap
  have hlo : 0≤midLowFloor s.positive t.positive := by
    cases s.positive <;> cases t.positive <;> norm_num [midLowFloor]
  rw [state_mid_low_cost s t hs ht]
  exact FrameLowMidPrimary.mid_low_primary s.positive t.positive hb hB
    (hlo.trans hx) hmargin

/-- The complete low-to-middle entry before any frame concentration. -/
theorem low_mid_pair (s t : FramePair.State) (hs : s.branch=.low)
    (ht : t.branch=.middle) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(1801/2000:ℝ) := by
    norm_num [hs,ht,Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_secondary_low_mid s t hs ht hgap hm
  · have hh := source_primary_mid_low t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_secondary_mid_low t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_primary_low_mid s t hs ht hgap hm

/-- The reverse entry uses the same original-axis convention. -/
theorem mid_low_pair (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.low) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(1801/2000:ℝ) := by
    norm_num [hs,ht,Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_secondary_mid_low s t hs ht hgap hm
  · have hh := source_primary_low_mid t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_secondary_low_mid t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_primary_mid_low s t hs ht hgap hm

theorem low_mid_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.low) (hj : branchOf C (next i)=.middle)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact low_mid_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem mid_low_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.middle) (hj : branchOf C (next i)=.low)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact mid_low_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.TableFree.FrameLowMidPair
