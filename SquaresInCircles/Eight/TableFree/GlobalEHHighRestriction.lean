module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighCycle
public import SquaresInCircles.Eight.TableFree.GlobalEHCycle

/-!
# A high original EH axis forces all original BT axes low

The conditional EH/GA restriction and the actual DE sign implication
force all four quarter edges high whenever the supplied EH and BT axes
are both high.  The complete all-high cycle obstruction excludes that
possibility.  Each conclusion quantifies over original weak witnesses;
no replacement owner is used on either prescribed edge.  Uncompiled
source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalEH

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

/-- A single high EH witness classifies each original BT witness. -/
theorem frame_BT_low_of_EH_high {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (jE : Fin 4) (hE : jE=2 ∨ jE=3)
    (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H))
    (jB : Fin 4) (hBT : (forwardAxis jB).Feasible (C.square B) (C.square T)) :
    jB=0 ∨ jB=1 := by
  by_contra hn
  have hB : jB=2 ∨ jB=3 := by fin_cases jB <;> simp_all
  exact frame_high_EH_high_BT_false F hq jE jB hE hB hEH hBT

/-- A single high BT witness controls every original EH witness. -/
theorem frame_EH_low_of_BT_high {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (jB : Fin 4) (hB : jB=2 ∨ jB=3)
    (hBT : (forwardAxis jB).Feasible (C.square B) (C.square T))
    (jE : Fin 4) (hEH : (forwardAxis jE).Feasible (C.square E) (C.square H)) :
    jE=0 ∨ jE=1 := by
  by_contra hn
  have hE : jE=2 ∨ jE=3 := by fin_cases jE <;> simp_all
  exact frame_high_EH_high_BT_false F hq jE jB hE hB hEH hBT

end SquaresInCircles.Eight.TableFree.GlobalEH
