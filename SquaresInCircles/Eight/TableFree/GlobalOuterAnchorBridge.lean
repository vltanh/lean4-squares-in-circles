module

public import SquaresInCircles.Eight.TableFree.GlobalOuterAnchorCycle

/-!
# Four original radial anchors from the actual normal owner family

Only the original feasible quarter axes are used.  The surrounding
zero edges obtain their own original secondary witnesses from the
global zero-edge theorem.  No separate anchor-circle or anchor-sign
premise is needed.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalOuterAnchor

open Candidate

theorem frame_zero_high_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=0) (hj : word (next i)=1)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next i)=.outer := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact zero_high_outer C hq G i hinc hinc' j howner haxis

theorem frame_low_zero_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=1) (hj : word (next i)=0)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind (next i)=.outer := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact low_zero_outer C hq G i hinc hinc' j howner haxis

theorem frame_low_anchor {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=1) (hj : word (next i)=0)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind (next i)=.outer ∧ 0<C.tangent (next i) := by
  refine ⟨frame_low_zero_outer F hq i hi hj j howner haxis,?_⟩
  rcases GlobalQuarterSign.of_frame F hq i hi j haxis with ⟨_,ht⟩ | ⟨hh,_⟩
  · exact ht
  · rcases howner with rfl | rfl <;> rcases hh with hh | hh <;> norm_num at hh

theorem frame_high_anchor {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=0) (hj : word (next i)=1)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next i)=.outer ∧ C.tangent (next i)<0 := by
  refine ⟨frame_zero_high_outer F hq i hi hj j howner haxis,?_⟩
  rcases GlobalQuarterSign.of_frame F hq (next i) hj j haxis with ⟨hh,_⟩ | ⟨_,ht⟩
  · rcases howner with rfl | rfl <;> rcases hh with hh | hh <;> norm_num at hh
  · exact ht

/-- The original normal owner theorem alone supplies every radial and
sign anchor required by the sharp same-radius source record. -/
theorem normal_anchors {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0)
    (howners : Candidate.OwnerRestriction C SignedCycle.normalOwners) :
    (C.kind H=.outer ∧ 0<C.tangent H) ∧
      (C.kind A=.outer ∧ 0<C.tangent A) ∧
      (C.kind B=.outer ∧ C.tangent B<0) ∧
      (C.kind D=.outer ∧ C.tangent D<0) := by
  let w := SignedCycle.retainedWitnesses F howners
  have hf (i : Vertex) : (forwardAxis (w.owner i)).Feasible
      (C.square i) (C.square (next i)) :=
    (SignedCycle.atFrame_feasible F i (w.owner i)).1 (w.feasible i)
  have hG : w.owner G=0 ∨ w.owner G=1 := by
    simpa [SignedCycle.normalOwners,G] using w.allowed G
  have hB : w.owner B=2 ∨ w.owner B=3 := by
    simpa [SignedCycle.normalOwners,B] using w.allowed B
  have hD : w.owner D=2 ∨ w.owner D=3 := by
    simpa [SignedCycle.normalOwners,D] using w.allowed D
  have hE : w.owner E=0 ∨ w.owner E=1 := by
    simpa [SignedCycle.normalOwners,E] using w.allowed E
  have hHanchor := frame_low_anchor F hq E (by norm_num [word,E])
    (by norm_num [word,E,next]) (w.owner E) hE (hf E)
  have hAanchor := frame_low_anchor F hq G (by norm_num [word,G])
    (by norm_num [word,G,next]) (w.owner G) hG (hf G)
  have hBanchor := frame_high_anchor F hq A (by norm_num [word,A])
    (by norm_num [word,A,next]) (w.owner B) hB
    (by simpa [A,B,next] using hf B)
  have hDanchor := frame_high_anchor F hq T (by norm_num [word,T])
    (by norm_num [word,T,next]) (w.owner D) hD
    (by simpa [T,D,next] using hf D)
  exact ⟨by simpa [E,H,next] using hHanchor,
    by simpa [G,A,next] using hAanchor,
    by simpa [A,B,next] using hBanchor,
    by simpa [T,D,next] using hDanchor⟩

theorem normal_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0)
    (howners : Candidate.OwnerRestriction C SignedCycle.normalOwners) :
    ∀i∈({H,A,B,D} : Finset Vertex),C.kind i=.outer := by
  have hh := normal_anchors F hq howners
  intro i hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact hh.1.1
  · exact hh.2.1.1
  · exact hh.2.2.1.1
  · exact hh.2.2.2.1

end SquaresInCircles.Eight.TableFree.GlobalOuterAnchor
