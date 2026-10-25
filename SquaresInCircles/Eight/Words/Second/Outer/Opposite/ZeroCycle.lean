module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAsymmetricCycle
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroSymmetric
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle

/-!
# Eight squares: all original outer zero-quarter edges of the second wrong word

The symmetric edge-four argument (`symmetric_source`, `symmetric_target`) joins the two
asymmetric edges. The separate G1 zero-owner theorem keeps every original weak axis, including
ties. The same-sign and opposite-sign families then give one outer-zero statement for the cyclic
assembly (`actual`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.OppositeZero
open CommonQuarter Arithmetic QuarterWordGeometry

lemma literal_four (a b A B x : ℝ) :
    SecondWord.cost 4 .outer .outer true false a b A B x=
      x+LLabel.eval a b+LLabel.eval A B := by
  norm_num [SecondWord.cost,label,wrongValue,WordProblems.secondCoefficients,
    WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
    next,RoleLabel.eval,LLabel]
  ring

theorem symmetric_source {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    threshold 4<SecondWord.cost 4 .outer .outer true false a b A B x := by
  rw [threshold_value,literal_four]
  exact Symmetric.original hs ht hx hm

theorem symmetric_target {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 (-1) x) :
    threshold 4<SecondWord.cost 4 .outer .outer true false a b A B x := by
  have hrev : 0≤Eight.forwardMargin 0 A B a b 1 (-1) x := by
    simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm
  have hh := Symmetric.original ht hs hx hrev
  rw [threshold_value,literal_four]
  linarith

theorem symmetric_actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (hs : C.kind 4=.outer) (ht : C.kind (next 4)=.outer)
    (hsg : positiveOf C 4≠positiveOf C (next 4)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square 4) (C.square (next 4))) :
    threshold 4<phaseValue F hgap 4+wrongMarker C .second 4-
      wrongMarker C .second (next 4) := by
  have hz : F.word hgap pi_lt_22_over_7 4=0 := by
    rw [hw]
    norm_num [WordProblems.wrongWord]
  have hx : |phaseValue F hgap 4|≤7/10 := by
    simpa [phaseValue,hz] using (difference_small F 4).le
  have hsource : OuterState (C.a 4) (C.b 4) := by
    simpa [State,hs] using actual_state C 4
  have htarget : OuterState (C.a (next 4)) (C.b (next 4)) := by
    simpa [State,ht] using actual_state C (next 4)
  have hm := original_margin C F hgap 4 j howner
  have hh : threshold 4<SecondWord.cost 4 .outer .outer
      (positiveOf C 4) (positiveOf C (next 4)) (C.a 4) (C.b 4)
      (C.a (next 4)) (C.b (next 4)) (phaseValue F hgap 4) := by
    rcases WrongZeroOriginalOwners.original C F hgap 4 hz j howner with
      ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
    · have htargetneg : positiveOf C (next 4)=false := by
        cases h : positiveOf C (next 4) <;> simp_all
      rw [hpos,htargetneg]
      exact symmetric_source hsource htarget hx
        (by simpa [hpos,htargetneg,WordProblems.sign] using hm)
    · have hsourcepos : positiveOf C 4=true := by
        cases h : positiveOf C 4 <;> simp_all
      rw [hsourcepos,hneg]
      exact symmetric_target hsource htarget hx
        (by simpa [hsourcepos,hneg,WordProblems.sign] using hm)
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i≠positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hword : WordProblems.wrongWord .second i=0 := by simpa [hw] using hi
  have hcases : i=0 ∨ i=1 ∨ i=4 := by
    revert hword
    fin_cases i <;> norm_num [WordProblems.wrongWord]
  rcases hcases with hzero | hone | hfour
  · exact Asymmetric.actual_owner C F hgap hw i (Or.inl hzero) hs ht hsg j howner
  · exact Asymmetric.actual_owner C F hgap hw i (Or.inr hone) hs ht hsg j howner
  · subst i
    exact symmetric_actual_owner C F hgap hw hs ht hsg j howner

end SquaresInCircles.Eight.SecondWord.OppositeZero

namespace SquaresInCircles.Eight.SecondWord.OuterZero
open CommonQuarter Arithmetic QuarterWordGeometry

/-- Every zero edge, either sign relation, and every originally feasible axis. -/
theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  by_cases hsign : positiveOf C i=positiveOf C (next i)
  · exact SameZero.actual_owner C F hgap hw i hi hs ht hsign j howner
  · exact OppositeZero.actual_owner C F hgap hw i hi hs ht hsign j howner

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F hgap hw i hi hs ht j (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.SecondWord.OuterZero
