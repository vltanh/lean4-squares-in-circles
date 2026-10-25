module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameMinimum
public import SquaresInCircles.Eight.TableFree.ShortOuterZeroUnfavorable
public import SquaresInCircles.Eight.TableFree.WrongZeroOriginalOwners

/-!
# All eight same-sign outer zero-secondary families of the short word

Uncompiled source draft. The four favorable coupled estimates and four
unfavorable supports are restored to the original role, radial states,
and original weak owner. Reflection/reversal is only an exact algebraic
exchange of the original pair; the literal cycle labels are unchanged.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.SameCycle
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

lemma roles (i : Vertex) (σ : Bool)
    (hi : WordProblems.wrongWord .short i=0)
    (ha : WordProblems.allowed .short i σ σ) :
    (i=0 ∧ σ=true) ∨ (i=1 ∧ σ=false) ∨ (i=3 ∧ σ=true) ∨ (i=3 ∧ σ=false) := by
  revert hi ha
  fin_cases i <;> cases σ <;>
    norm_num [WordProblems.allowed,WordProblems.wrongWord,next]

private lemma reverse_target {a b A B x σ : ℝ}
    (hm : 0≤Eight.forwardMargin 2 a b A B σ σ x) :
    0≤Eight.forwardMargin 0 A B a b (-σ) (-σ) x := by
  simp only [Eight.forwardMargin,Matrix.cons_val] at hm ⊢
  linarith

macro "short_same_literal" : tactic => `(tactic|
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,next,
    Same.c,Same.p,Same.q,Same.P,Same.t,
    Unfavorable.c,Unfavorable.p,Unfavorable.q,Unfavorable.P,Unfavorable.t] at *
  <;> linarith)

/-- Every literal same-sign outer zero-secondary row on its full closed domain. -/
theorem original (i : Vertex) (σ : Bool)
    (hi : WordProblems.wrongWord .short i=0)
    (ha : WordProblems.allowed .short i σ σ)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign σ) x) :
    (449/500:ℝ)<x+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) .outer σ A B := by
  rcases roles i σ hi ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rcases hj with rfl | rfl
    · have hh := Same.original (0:Same.Row) hs ht hx (by simpa [WordProblems.sign] using hm)
      short_same_literal
    · have hrev := reverse_target (by simpa [WordProblems.sign] using hm :
        0≤Eight.forwardMargin 2 a b A B 1 1 x)
      have hh := Unfavorable.original_cost (0:Unfavorable.Row) ht hs hx (by simpa using hrev)
      short_same_literal
  · rcases hj with rfl | rfl
    · have hh := Unfavorable.original_cost (1:Unfavorable.Row) hs ht hx
        (by simpa [WordProblems.sign] using hm)
      short_same_literal
    · have hrev := reverse_target (by simpa [WordProblems.sign] using hm :
        0≤Eight.forwardMargin 2 a b A B (-1) (-1) x)
      have hh := Same.original (1:Same.Row) ht hs hx (by simpa using hrev)
      short_same_literal
  · rcases hj with rfl | rfl
    · have hh := Same.original (2:Same.Row) hs ht hx (by simpa [WordProblems.sign] using hm)
      short_same_literal
    · have hrev := reverse_target (by simpa [WordProblems.sign] using hm :
        0≤Eight.forwardMargin 2 a b A B 1 1 x)
      have hh := Unfavorable.original_cost (2:Unfavorable.Row) ht hs hx (by simpa using hrev)
      short_same_literal
  · rcases hj with rfl | rfl
    · have hh := Unfavorable.original_cost (3:Unfavorable.Row) hs ht hx
        (by simpa [WordProblems.sign] using hm)
      short_same_literal
    · have hrev := reverse_target (by simpa [WordProblems.sign] using hm :
        0≤Eight.forwardMargin 2 a b A B (-1) (-1) x)
      have hh := Same.original (3:Same.Row) ht hs hx (by simpa using hrev)
      short_same_literal

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hword : WordProblems.wrongWord .short i=0 := by simpa [hw] using hi
  have ha := actual_allowed C F hgap .short hw i
  have hx : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have haxis : j=0 ∨ j=2 := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  have hh := original i (positiveOf C i) hword (by simpa [←hsg] using ha)
    hsource htarget hx j haxis (by simpa [←hsg] using hm)
  simpa only [wrongMarker,hs,ht,←hsg] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F hgap hw i hi hs ht hsg j
    (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.TableFree.ShortOuterZero.SameCycle
