module

public import SquaresInCircles.Eight.Owners.BT.Exclusion
public import SquaresInCircles.Eight.Owners.EH.HighRestriction

/-!
# Eight squares: the quarter owners and the outer anchors

The BT obstruction settles the owners of EH: a high EH witness makes E negative, so a BT witness
would be high, which the all-high obstruction excludes; so every EH witness is low
(`frame_EH_low`). When E is nonpositive every BT and DE witness is high, and every weak axis of an
edge other than GA has a normal owner (`frame_other_owners`). The selected axes then make H, B and
D outer anchors at the radius `q` (`frame_H_anchor`, `frame_B_anchor`, `frame_D_anchor`,
`atFrame_anchors`). The owners of GA are not restricted here.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight

open Candidate

namespace GlobalEH

/-- Every weak EH witness has owner `0` or `1`, whatever the sign of E. -/
theorem frame_EH_low {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (j : Fin 4) (hEH : (forwardAxis j).Feasible (C.square E) (C.square H)) :
    j=0 ∨ j=1 := by
  by_contra hn
  have hhigh : j=2 ∨ j=3 := by fin_cases j <;> simp_all
  have hE := GlobalQuarterOuter.frame_high_anchor F hq E
    (by norm_num [word,E]) j hhigh (by simpa [E,H,next] using hEH)
  let jB := SignedCycle.retainedOwner F B
  have hBT : (forwardAxis jB).Feasible (C.square B) (C.square T) := by
    have hh := (SignedCycle.atFrame_feasible F B jB).1
      (SignedCycle.retainedOwner_feasible F B)
    simpa [B,T,next] using hh
  have hB := GlobalBT.frame_BT_high F hq hE.2.le jB hBT
  exact frame_high_EH_high_BT_false F hq j jB hhigh hB hEH hBT

end GlobalEH

namespace GlobalOriginalOwners

theorem frame_H_anchor {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) :
    C.kind H=.outer ∧ 0<C.tangent H := by
  have hf : (forwardAxis (SignedCycle.retainedOwner F E)).Feasible (C.square E)
      (C.square (next E)) :=
    (SignedCycle.atFrame_feasible F E _).1 (SignedCycle.retainedOwner_feasible F E)
  generalize SignedCycle.retainedOwner F E = j at hf
  have hlow := GlobalEH.frame_EH_low F hq j (by simpa [E,H,next] using hf)
  rcases GlobalQuarterOuter.frame_classify F hq E (by norm_num [word,E]) j hf with
    ⟨_,ho,hs⟩ | ⟨hbad,_⟩
  · simpa [E,H,next] using And.intro ho hs
  · rcases hlow with rfl | rfl <;> rcases hbad with hbad | hbad <;> norm_num at hbad

theorem frame_B_anchor {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0) :
    C.kind B=.outer ∧ C.tangent B<0 := by
  let j := SignedCycle.retainedOwner F B
  have hf : (forwardAxis j).Feasible (C.square B) (C.square (next B)) :=
    (SignedCycle.atFrame_feasible F B j).1 (SignedCycle.retainedOwner_feasible F B)
  have hhigh := GlobalBT.frame_BT_high F hq hE j (by simpa [B,T,next] using hf)
  exact GlobalQuarterOuter.frame_high_anchor F hq B (by norm_num [word,B]) j hhigh hf

theorem frame_D_anchor {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0) :
    C.kind D=.outer ∧ C.tangent D<0 := by
  let j := SignedCycle.retainedOwner F D
  have hf : (forwardAxis j).Feasible (C.square D) (C.square (next D)) :=
    (SignedCycle.atFrame_feasible F D j).1 (SignedCycle.retainedOwner_feasible F D)
  have hhigh := (GlobalQuarterSign.frame_DE F hq hE).2 j
    (by simpa [D,E,next] using hf)
  exact GlobalQuarterOuter.frame_high_anchor F hq D (by norm_num [word,D]) j hhigh hf

/-- When `C.tangent E ≤ 0`, every weak axis on an edge other than GA has a normal owner, each member
of a weak tie included. -/
theorem frame_other_owners {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (i : Vertex) (hi : i≠G) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    j∈SignedCycle.normalOwners i := by
  have hcases : i=H ∨ i=A ∨ i=B ∨ i=T ∨ i=D ∨ i=E := by
    fin_cases i <;> simp_all [H,G,A,B,T,D,E]
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) j hj with hh | hh
    · simp [SignedCycle.normalOwners,H,hh.1]
    · simp [SignedCycle.normalOwners,H,hh.1]
  · rcases GlobalZeroSign.of_frame F hq A (by norm_num [word,A]) j hj with hh | hh
    · simp [SignedCycle.normalOwners,A,hh.1]
    · simp [SignedCycle.normalOwners,A,hh.1]
  · have hh := GlobalBT.frame_BT_high F hq hE j (by simpa [B,T,next] using hj)
    rcases hh with rfl | rfl <;> simp [SignedCycle.normalOwners,B]
  · rcases GlobalZeroSign.of_frame F hq T (by norm_num [word,T]) j hj with hh | hh
    · simp [SignedCycle.normalOwners,T,hh.1]
    · simp [SignedCycle.normalOwners,T,hh.1]
  · have hh := (GlobalQuarterSign.frame_DE F hq hE).2 j
      (by simpa [D,E,next] using hj)
    rcases hh with rfl | rfl <;> simp [SignedCycle.normalOwners,D]
  · have hh := GlobalEH.frame_EH_low F hq j (by simpa [E,H,next] using hj)
    rcases hh with rfl | rfl <;> simp [SignedCycle.normalOwners,E]

/-- In the signed cycle of the frame, H, B and D lie on the circle of `q`, with `0 < H.y`, `B.y < 0`
and `D.y < 0`. -/
theorem atFrame_anchors {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0) :
    ((SignedCycle.atFrame F).point H).Outer q ∧
      0<((SignedCycle.atFrame F).point H).y ∧
    ((SignedCycle.atFrame F).point B).Outer q ∧
      ((SignedCycle.atFrame F).point B).y<0 ∧
    ((SignedCycle.atFrame F).point D).Outer q ∧
      ((SignedCycle.atFrame F).point D).y<0 := by
  have hH := frame_H_anchor F hq
  have hB := frame_B_anchor F hq hE
  have hD := frame_D_anchor F hq hE
  exact ⟨SignedCycle.atFrame_outer_of_kind F H hH.1,
    (SignedCycle.atFrame_y_pos_iff F H).2 hH.2,
    SignedCycle.atFrame_outer_of_kind F B hB.1,
    (SignedCycle.atFrame_y_neg_iff F B).2 hB.2,
    SignedCycle.atFrame_outer_of_kind F D hD.1,
    (SignedCycle.atFrame_y_neg_iff F D).2 hD.2⟩

end GlobalOriginalOwners
end SquaresInCircles.Eight
