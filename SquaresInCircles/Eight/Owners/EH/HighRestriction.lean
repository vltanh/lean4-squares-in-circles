module

public import SquaresInCircles.Eight.Owners.All.HighCycle
public import SquaresInCircles.Eight.Owners.EH.Cycle

/-!
# Eight squares: a high EH axis forces every BT axis low

A weak EH witness of a high owner makes every GA witness high (`frame_GA_high_of_EH_high`); with
the sign implication at DE, a high BT witness would then make all four quarter edges high, which
the all-high cycle obstruction excludes (`frame_high_EH_high_BT_false`). The conclusions quantify
over the weak witnesses of the cycle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalEH

open Candidate

theorem frame_GA_high_of_EH_high {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (jE : Fin 4) (hE : jE=2 ∨ jE=3)
    (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H))
    (jG : Fin 4) (hGA : (forwardAxis jG).Feasible (C.square G) (C.square A)) :
    jG=2 ∨ jG=3 := by
  by_contra hn
  have hG : jG=0 ∨ jG=1 := by fin_cases jG <;> simp_all
  have he := frame_EH_low_of_GA_low F hq jG hG hGA jE hEH
  rcases hE with rfl | rfl <;> rcases he with he | he <;> norm_num at he

theorem frame_high_EH_high_BT_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (jE jB : Fin 4) (hE : jE=2 ∨ jE=3) (hB : jB=2 ∨ jB=3)
    (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H))
    (hBT : (forwardAxis jB).Feasible (C.square B) (C.square T)) : False := by
  have hex (i : Vertex) :
      ∃ k : Fin 4,(forwardAxis k).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨k,hk⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨k,hk ▸ C.feasible i⟩
  choose original horiginal using hex
  let owner : Vertex→Fin 4 := fun i => if i=E then jE else if i=B then jB else original i
  have hf (i : Vertex) :
      (forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)) := by
    by_cases hiE : i=E
    · subst i
      simpa [owner,E,H,next] using hEH
    · by_cases hiB : i=B
      · subst i
        simpa [owner,B,T,E,next] using hBT
      · simpa only [owner,hiE,hiB,↓reduceIte] using horiginal i
  have hGowner : owner G=2 ∨ owner G=3 :=
    frame_GA_high_of_EH_high F hq jE hE hEH (owner G)
      (by simpa [G,A,next] using hf G)
  have hEnegative := GlobalQuarterOuter.frame_high_anchor F hq E
    (by norm_num [word,E]) jE hE (by simpa [E,H,next] using hEH)
  have hDE := GlobalQuarterSign.frame_DE F hq hEnegative.2.le
  have hDowner : owner D=2 ∨ owner D=3 :=
    hDE.2 (owner D) (by simpa [D,E,next] using hf D)
  have hBowner : owner B=2 ∨ owner B=3 := by simpa [owner,B,E] using hB
  have hEowner : owner E=2 ∨ owner E=3 := by simpa [owner] using hE
  apply GlobalAllHigh.frame_all_high_false F hq owner hf
  intro i hi
  have hcases : i=G ∨ i=B ∨ i=D ∨ i=E := by
    revert hi
    fin_cases i <;> decide
  rcases hcases with rfl | rfl | rfl | rfl
  · exact hGowner
  · exact hBowner
  · exact hDowner
  · exact hEowner

end SquaresInCircles.Eight.GlobalEH
