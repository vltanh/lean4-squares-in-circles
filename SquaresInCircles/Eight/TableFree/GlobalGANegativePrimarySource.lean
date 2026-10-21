module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativePrimaryExclusion
public import SquaresInCircles.Eight.TableFree.GlobalOriginalOwners

/-!
# Negative-primary high-GA exclusion on the unchanged source cycle

Every sign, circle/core bound, HG owner and variation budget is derived
from the original boundary frame.  The supplied axes are precisely the
owner family being excluded, and their original errors may be weakly
zero.  No radial kind is imposed on A, T or E.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativePrimary

open Candidate

theorem frame_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (ga ab td : Bool)
    (hGA : (forwardAxis (if ga then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if ab then 2 else 0)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis (if td then 2 else 0)).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis 2).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H))
    (hga : ga=true → delta F.theta G≤0)
    (hab : ab=true → delta F.theta A≤0)
    (htd : td=true → delta F.theta T≤0) : False := by
  have hn := SignedCycle.atFrame_necessary F
  have hanchors := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hhigh : (if ga then 3 else 2 : Fin 4)=2 ∨
      (if ga then 3 else 2 : Fin 4)=3 := by cases ga <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G
    (by norm_num [word,G]) _ hhigh (by simpa [G,A,next] using hGA)
  have hHG : (SignedCycle.atFrame F).Feasible H 0 ∨
      (SignedCycle.atFrame F).Feasible H 2 := by
    let j := SignedCycle.retainedOwner F H
    have hf : (SignedCycle.atFrame F).Feasible H j := SignedCycle.retainedOwner_feasible F H
    have ha := (SignedCycle.atFrame_feasible F H j).1 hf
    rcases GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) j ha with hh | hh
    · exact Or.inl (by simpa [hh.1] using hf)
    · exact Or.inr (by simpa [hh.1] using hf)
  apply actual_false ga ab td hn.sorted hn.contained hn.core (show q≤qCap from hq.2)
    hanchors.2.1.le ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
    hanchors.2.2.2.1.le hanchors.2.2.2.2.2.le
    (FramePhysicalTransport.candidate_variations F hq).1.le hHG
  · exact (SignedCycle.atFrame_feasible F G _).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A _).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B _).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T _).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D _).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E _).2 (by simpa [E,H,next] using hEH)
  · exact hga
  · exact hab
  · exact htd

/-- Original-axis statement of the complete fixed-stress family.  The
secondary choices have arbitrary errors; each primary choice has its
actual nonpositive error, independently of the other two choices. -/
theorem frame_nonpositive_primary_row_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (hGA : (forwardAxis 2).Feasible (C.square G) (C.square A) ∨
      ((forwardAxis 3).Feasible (C.square G) (C.square A) ∧ delta F.theta G≤0))
    (hAB : (forwardAxis 0).Feasible (C.square A) (C.square B) ∨
      ((forwardAxis 2).Feasible (C.square A) (C.square B) ∧ delta F.theta A≤0))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 0).Feasible (C.square T) (C.square D) ∨
      ((forwardAxis 2).Feasible (C.square T) (C.square D) ∧ delta F.theta T≤0))
    (hDE : (forwardAxis 2).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H)) : False := by
  have hga : ∃p : Bool,
      (forwardAxis (if p then 3 else 2)).Feasible (C.square G) (C.square A) ∧
        (p=true → delta F.theta G≤0) := by
    rcases hGA with hh | ⟨hh,hd⟩
    · exact ⟨false,hh,by simp⟩
    · exact ⟨true,hh,by intro _; exact hd⟩
  have hab : ∃p : Bool,
      (forwardAxis (if p then 2 else 0)).Feasible (C.square A) (C.square B) ∧
        (p=true → delta F.theta A≤0) := by
    rcases hAB with hh | ⟨hh,hd⟩
    · exact ⟨false,hh,by simp⟩
    · exact ⟨true,hh,by intro _; exact hd⟩
  have htd : ∃p : Bool,
      (forwardAxis (if p then 2 else 0)).Feasible (C.square T) (C.square D) ∧
        (p=true → delta F.theta T≤0) := by
    rcases hTD with hh | ⟨hh,hd⟩
    · exact ⟨false,hh,by simp⟩
    · exact ⟨true,hh,by intro _; exact hd⟩
  obtain ⟨ga,hGA,hga⟩ := hga
  obtain ⟨ab,hAB,hab⟩ := hab
  obtain ⟨td,hTD,htd⟩ := htd
  exact frame_false F hq hE ga ab td hGA hAB hBT hTD hDE hEH hga hab htd

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativePrimary
