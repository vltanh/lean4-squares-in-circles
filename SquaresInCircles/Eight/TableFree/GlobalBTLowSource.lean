module

public import SquaresInCircles.Eight.TableFree.GlobalBTZeroExclusion

/-!
# Actual source data under either forbidden low BT owner

Every stored sign, radial fact, owner and projection is derived from
the unchanged physical cycle.  This record introduces no source
hypothesis and retains a feasible original witness for each edge.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open Candidate FramePair GlobalOuterAnchor

theorem frame_zero_projection {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (i : Vertex) (hi : word i=0) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    GlobalOuterAnchor.width (delta F.theta i)≤projection false (stateOf C i) (stateOf C (next i))
      (delta F.theta i) j := by
  have hd : |delta F.theta i|≤frameCap := by simpa only [frameCap] using (F.delta_small i).le
  apply (projection_feasible false _ _ _ hd).1
  simpa [Candidate.phi,hi] using GlobalAllHigh.frame_state_feasible F i j hj

theorem frame_quarter_projection {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (i : Vertex) (hi : word i=1) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    GlobalOuterAnchor.width (delta F.theta i)≤projection true (stateOf C i) (stateOf C (next i))
      (delta F.theta i) j := by
  have hd : |delta F.theta i|≤frameCap := by simpa only [frameCap] using (F.delta_small i).le
  apply (projection_feasible true _ _ _ hd).1
  simpa [Candidate.phi,hi] using GlobalAllHigh.frame_state_feasible F i j hj

structure LowSource (C : BoundaryCycle Q0) (F : Candidate.Frame C) (j : Fin 4) where
  AB : Bool
  TD : Bool
  DE : Fin 4
  A_tangent : 0<C.tangent A
  A_positive : 0≤transverse (stateOf C A)
  T_positive : 0≤transverse (stateOf C T)
  D_negative : transverse (stateOf C D)≤0
  E_negative : transverse (stateOf C E)≤0
  T_outer : (stateOf C T).branch.type≠0
  DE_owner : DE=2 ∨ DE=3
  AB_projection : GlobalOuterAnchor.width (delta F.theta A)≤
    projection false (stateOf C A) (stateOf C B) (delta F.theta A) (leftOwner AB)
  BT_projection : GlobalOuterAnchor.width (delta F.theta B)≤
    projection true (stateOf C B) (stateOf C T) (delta F.theta B) j
  TD_projection : GlobalOuterAnchor.width (delta F.theta T)≤
    projection false (stateOf C T) (stateOf C D) (delta F.theta T) (leftOwner TD)
  DE_projection : GlobalOuterAnchor.width (delta F.theta D)≤
    projection true (stateOf C D) (stateOf C E) (delta F.theta D) DE

theorem lowSource {C : BoundaryCycle Q0} (F : Candidate.Frame C) (hE : C.tangent E≤0)
    (j : Fin 4) (hj : j=0 ∨ j=1)
    (hBT : (forwardAxis j).Feasible (C.square B) (C.square T)) : Nonempty (LowSource C F j) := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hA := GlobalZeroLow.frame_BT_low_A_positive F hq j hj hBT
  have hTOuter := GlobalQuarterOuter.frame_low_outer F hq B (by norm_num [word,B]) j hj
    (by simpa [B,T,next] using hBT)
  have hT : 0<C.tangent T := by
    rcases GlobalQuarterSign.of_frame F hq B (by norm_num [word,B]) j
      (by simpa [B,T,next] using hBT) with ⟨_,hh⟩ | ⟨hh,_⟩
    · simpa [B,T,next] using hh
    · rcases hj with rfl | rfl <;> rcases hh with hh | hh <;> norm_num at hh
  have hD := GlobalQuarterSign.frame_DE F hq hE
  have hex (i : Vertex) :
      ∃ k : Fin 4,(forwardAxis k).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨k,hk⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨k,hk ▸ C.feasible i⟩
  choose owner hf using hex
  have hABowner : owner A=0 ∨ owner A=2 := by
    rcases GlobalZeroSign.of_frame F hq A (by norm_num [word,A]) (owner A) (hf A) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hTDowner : owner T=0 ∨ owner T=2 := by
    rcases GlobalZeroSign.of_frame F hq T (by norm_num [word,T]) (owner T) (hf T) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  obtain ⟨ab,hab⟩ : ∃ab : Bool,leftOwner ab=owner A := by
    rcases hABowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  obtain ⟨td,htd⟩ : ∃td : Bool,leftOwner td=owner T := by
    rcases hTDowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  refine ⟨{
    AB := ab, TD := td, DE := owner D,
    A_tangent := hA,
    A_positive := (GlobalAllHigh.state_positive_of_tangent C A hA).le,
    T_positive := (GlobalAllHigh.state_positive_of_tangent C T hT).le,
    D_negative := (GlobalAllHigh.state_negative_of_tangent C D hD.1).le,
    E_negative := ?_, T_outer := ?_, DE_owner := ?_,
    AB_projection := ?_, BT_projection := ?_, TD_projection := ?_, DE_projection := ?_ }⟩
  · rw [GlobalAllHigh.state_transverse_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (C.a_pos E).le hE
  · exact GlobalAllHigh.state_outer_of_kind C T (by simpa [B,T,next] using hTOuter)
  · exact hD.2 (owner D) (by simpa [D,E,next] using hf D)
  · simpa [A,B,next,hab] using frame_zero_projection F A (by norm_num [word,A]) (owner A) (hf A)
  · simpa [B,T,next] using frame_quarter_projection F B (by norm_num [word,B]) j
      (by simpa [B,T,next] using hBT)
  · simpa [T,D,next,htd] using frame_zero_projection F T (by norm_num [word,T]) (owner T) (hf T)
  · simpa [D,E,next] using frame_quarter_projection F D (by norm_num [word,D]) (owner D) (hf D)

end SquaresInCircles.Eight.TableFree.GlobalBT
