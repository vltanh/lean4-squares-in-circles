module

public import SquaresInCircles.Eight.TableFree.GlobalQuarterOuterCycle

/-!
# Every original quarter owner selects an outer endpoint

The four local zero/quarter placements cover the surviving original
word.  A low owner selects the positive outer target; a high owner
selects the negative outer source.  The conclusion is applied to each
original weak axis individually and is independent of any restriction
on the other quarter owners.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalQuarterOuter

open Candidate

theorem frame_zero_low_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=0) (hj : word (next i)=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square (next i)) (C.square (next (next i)))) :
    C.kind (next (next i))=.outer := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact zero_low_outer C hq G i hinc hinc' j howner haxis

theorem frame_high_zero_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex)
    (hi : word i=1) (hj : word (next i)=0)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro k; simpa only [mul_div_assoc] using F.canonical_eq k)
  have hinc : integerQuarterIncrement G.quarter i=1 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hi]
  have hinc' : integerQuarterIncrement G.quarter (next i)=0 := by
    rw [hGquarter,GlobalZeroSign.offset_increment,hj]
  exact high_zero_outer C hq G i hinc hinc' j howner haxis

theorem frame_low_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1)
    (j : Fin 4) (howner : j=0 ∨ j=1)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind (next i)=.outer := by
  by_cases hnext : word (next i)=0
  · exact GlobalOuterAnchor.frame_low_zero_outer F hq i hi hnext j howner haxis
  · have hiD : i=D := by fin_cases i <;> simp_all [word,next,D]
    subst i
    simpa [T,D,E,next] using frame_zero_low_outer F hq T
      (by norm_num [word,T]) (by norm_num [word,T,next]) j howner
      (by simpa [T,D,E,next] using haxis)

theorem frame_high_outer {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1)
    (j : Fin 4) (howner : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer := by
  by_cases hiE : i=E
  · subst i
    exact frame_high_zero_outer F hq E (by norm_num [word,E])
      (by norm_num [word,E,next]) j howner haxis
  · have hcases : i=G ∨ i=B ∨ i=D := by
      fin_cases i <;> simp_all [word,G,B,D,E]
    rcases hcases with rfl | rfl | rfl
    · simpa [H,G,next] using GlobalOuterAnchor.frame_zero_high_outer F hq H
        (by norm_num [word,H]) (by norm_num [word,H,next]) j howner
        (by simpa [H,G,next] using haxis)
    · simpa [A,B,next] using GlobalOuterAnchor.frame_zero_high_outer F hq A
        (by norm_num [word,A]) (by norm_num [word,A,next]) j howner
        (by simpa [A,B,next] using haxis)
    · simpa [T,D,next] using GlobalOuterAnchor.frame_zero_high_outer F hq T
        (by norm_num [word,T]) (by norm_num [word,T,next]) j howner
        (by simpa [T,D,next] using haxis)

/-- Complete original sign/radial classification, without choosing an
owner on any other quarter edge. -/
theorem frame_classify {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ((j=0 ∨ j=1) ∧ C.kind (next i)=.outer ∧ 0<C.tangent (next i)) ∨
      ((j=2 ∨ j=3) ∧ C.kind i=.outer ∧ C.tangent i<0) := by
  rcases GlobalQuarterSign.of_frame F hq i hi j haxis with ⟨hj,hs⟩ | ⟨hj,hs⟩
  · exact Or.inl ⟨hj,frame_low_outer F hq i hi j hj haxis,hs⟩
  · exact Or.inr ⟨hj,frame_high_outer F hq i hi j hj haxis,hs⟩

theorem frame_high_anchor {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (hi : word i=1)
    (j : Fin 4) (hj : j=2 ∨ j=3)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer ∧ C.tangent i<0 := by
  rcases frame_classify F hq i hi j haxis with ⟨hbad,_⟩ | ⟨_,hh⟩
  · rcases hj with rfl | rfl <;> rcases hbad with hbad | hbad <;> norm_num at hbad
  · exact hh

/-- This is exactly the radial/sign domain needed by the common
all-high potential: high-quarter sources are negative outer states;
each nonpositive zero source is outer as well. -/
theorem frame_all_high_domain {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) :
    (∀i,word i=1 → C.kind i=.outer ∧ C.tangent i<0) ∧
      (∀i,word i=0 → C.tangent i≤0 → C.kind i=.outer) := by
  refine ⟨?_,?_⟩
  · intro i hi
    exact frame_high_anchor F hq i hi (owner i) (hhigh i hi) (hf i)
  · intro i hi hs
    exact GlobalZeroSourceOuter.frame_nonpositive_source_outer F hq i hi hs

end SquaresInCircles.Eight.TableFree.GlobalQuarterOuter
