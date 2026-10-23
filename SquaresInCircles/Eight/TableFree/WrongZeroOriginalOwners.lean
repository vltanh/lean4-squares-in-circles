module

public import SquaresInCircles.Eight.TableFree.GlobalZeroSignCycle

/-!
# Original zero-edge owners before wrong-word scalar estimates

Uncompiled source draft.  The G1 cycle consequences apply before any
word normalization: every original weak zero owner is secondary, and
its strict sign is fixed.  This module expresses those consequences in
the literal Boolean signs used by the wrong-word labels.  Both signs
at a vanishing transverse coordinate remain represented; an infeasible
owner is excluded by its strict original tangent consequence.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.WrongZeroOriginalOwners
open Arithmetic TableFreeWordGeometry

theorem tangent_nonnegative (C : BoundaryCycle Q0) (i : Vertex)
    (hi : positiveOf C i=true) : 0≤C.tangent i := by
  have he := positiveOf_spec C i
  have hs : C.sigma i=1 := by simpa [hi,WordProblems.sign] using he.symm
  dsimp [BoundaryCycle.tangent]
  rw [hs,one_mul]
  exact div_nonneg (C.b_nonneg i) (C.a_pos i).le

theorem tangent_nonpositive (C : BoundaryCycle Q0) (i : Vertex)
    (hi : positiveOf C i=false) : C.tangent i≤0 := by
  have he := positiveOf_spec C i
  have hs : C.sigma i= -1 := by simpa [hi,WordProblems.sign] using he.symm
  dsimp [BoundaryCycle.tangent]
  rw [hs,neg_one_mul]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (C.b_nonneg i)) (C.a_pos i).le

theorem original (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hi : F.word hgap pi_lt_22_over_7 i=0) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (j=0 ∧ positiveOf C i=true) ∨ (j=2 ∧ positiveOf C (next i)=false) := by
  have hinc : integerQuarterIncrement F.quarter i=0 := by
    have hh := F.word_cast hgap pi_lt_22_over_7 i
    rw [hi] at hh
    norm_num at hh
    omega
  rcases GlobalZeroSign.classify C (by norm_num [Q0]) F i hinc j haxis with
    ⟨hj,hs⟩ | ⟨hj,ht⟩
  · refine Or.inl ⟨hj,?_⟩
    cases hp : positiveOf C i
    · exact (not_lt_of_ge (tangent_nonpositive C i hp) hs).elim
    · rfl
  · refine Or.inr ⟨hj,?_⟩
    cases hp : positiveOf C (next i)
    · rfl
    · exact (not_lt_of_ge (tangent_nonnegative C (next i) hp) ht).elim

theorem target_positive (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hi : F.word hgap pi_lt_22_over_7 i=0)
    (ht : positiveOf C (next i)=true) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    j=0 ∧ positiveOf C i=true := by
  rcases original C F hgap i hi j haxis with hh | ⟨_,hn⟩
  · exact hh
  · simp [ht] at hn

theorem source_negative (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : positiveOf C i=false) (j : Fin 4)
    (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    j=2 ∧ positiveOf C (next i)=false := by
  rcases original C F hgap i hi j haxis with ⟨_,hn⟩ | hh
  · simp [hs] at hn
  · exact hh

end SquaresInCircles.Eight.TableFree.WrongZeroOriginalOwners
