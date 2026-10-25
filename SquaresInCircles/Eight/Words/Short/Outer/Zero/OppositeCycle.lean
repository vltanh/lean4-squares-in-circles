module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeNegative
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositive
public import SquaresInCircles.Eight.Words.Wrong.ZeroOriginalOwners

/-!
# Eight squares: all six original opposite-sign outer zero owners of the short word

The
negative and positive angle halves meet with their actual weak contact.
Reversal swaps the original states and their label coefficients exactly;
it never changes a role label on another edge of the physical cycle.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem original (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (449/500:ℝ)<x+c r+p r*a+q r*b+v r*A+t r*B := by
  by_cases hpos : 0≤x
  · have hh := Positive.original r hs ht ⟨hpos,(abs_le.mp hx).2⟩ hm
    linarith
  · have hx' : -x∈Set.Icc 0 (7/10) :=
      ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have hh := Negative.original r hs ht hx' (by simpa only [neg_neg] using hm)
    simp only [neg_neg] at hh
    linarith

private lemma reverse_target {a b A B x : ℝ}
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 (-1) x) :
    0≤Eight.forwardMargin 0 A B a b 1 (-1) x := by
  simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm

macro "short_opposite_literal" : tactic => `(tactic|
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,next,c,p,q,v,t] at * <;> linarith)

lemma zero_role (i : Vertex) (hi : WordProblems.wrongWord .short i=0) :
    i=0 ∨ i=1 ∨ i=3 := by
  revert hi
  fin_cases i <;> norm_num [WordProblems.wrongWord]

/-- Both original secondary owners at each of the three literal zero roles. -/
theorem original_secondary (i : Vertex) (hi : WordProblems.wrongWord .short i=0)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) x) :
    (449/500:ℝ)<x+wrongValue .short i .outer true a b-
      wrongValue .short (next i) .outer false A B := by
  rcases zero_role i hi with rfl | rfl | rfl
  · rcases hj with rfl | rfl
    · have hh := original 0 hs ht hx hm
      short_opposite_literal
    · have hh := original 1 ht hs hx (reverse_target hm)
      short_opposite_literal
  · rcases hj with rfl | rfl
    · have hh := original 2 hs ht hx hm
      short_opposite_literal
    · have hh := original 3 ht hs hx (reverse_target hm)
      short_opposite_literal
  · rcases hj with rfl | rfl
    · have hh := original 4 hs ht hx hm
      short_opposite_literal
    · have hh := original 5 ht hs hx (reverse_target hm)
      short_opposite_literal

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=true) (hτ : positiveOf C (next i)=false) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hword : WordProblems.wrongWord .short i=0 := by simpa [hw] using hi
  have hx : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have haxis : j=0 ∨ j=2 := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hm := original_margin C F hgap i j howner
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hh := original_secondary i hword hsource htarget hx j haxis (by simpa [hσ,hτ,WordProblems.sign] using hm)
  simpa only [wrongMarker,hs,ht,hσ,hτ] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=true) (hτ : positiveOf C (next i)=false) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F hgap hw i hi hs ht hσ hτ j
    (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.ShortOuterZero.Opposite
