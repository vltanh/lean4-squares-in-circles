module

public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroCycle
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeCycle
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameCycle
public import SquaresInCircles.Eight.Words.Wrong.WordCore

/-!
# Eight squares: every original zero-quarter edge of the short wrong word

All radial assignments and original weak owners are dispatched. The
zero-primary impossibility is derived from the same physical cycle,
before either binary wrong-word exclusion, so the join is noncircular.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ShortWord.Zero
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

lemma threshold_le (i : Vertex) : WordProblems.wrongGamma .short i≤(449/500:ℝ) := by
  by_cases hi : i=2 <;> norm_num [WordProblems.wrongGamma,hi]

theorem actual_outer (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hz : WordProblems.wrongWord .short i=0 := by simpa [hw] using hi
  have ha := actual_allowed C F hgap .short hw i
  rcases ShortMixedZero.zero_signs i hz (positiveOf C i) (positiveOf C (next i)) ha with
    he | ⟨hσ,hτ⟩
  · exact ShortOuterZero.SameCycle.actual C F hgap hw i hi hs ht he
  · exact ShortOuterZero.Opposite.actual C F hgap hw i hi hs ht hσ hτ

theorem actual_mixed (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : (C.kind i=.outer ∧ C.kind (next i)≠.outer) ∨
      (C.kind i≠.outer ∧ C.kind (next i)=.outer)) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  have haxis : j=0 ∨ j=2 := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  exact ShortMixedZero.actual_mixed_zero_secondary C F hgap hw i hi hmixed j haxis howner

/-- Complete original-cycle zero-edge conclusion, without an extra pair-bound premise. -/
theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0) :
    WordProblems.wrongGamma .short i<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  by_cases hs : C.kind i=.outer
  · by_cases ht : C.kind (next i)=.outer
    · exact (threshold_le i).trans_lt (actual_outer C F hgap hw i hi hs ht)
    · exact (threshold_le i).trans_lt (actual_mixed C F hgap hw i hi (Or.inl ⟨hs,ht⟩))
  · by_cases ht : C.kind (next i)=.outer
    · exact (threshold_le i).trans_lt (actual_mixed C F hgap hw i hi (Or.inr ⟨hs,ht⟩))
    · exact WrongWordCore.actual_core_pair C F hgap .short hw i hs ht

end SquaresInCircles.Eight.ShortWord.Zero
