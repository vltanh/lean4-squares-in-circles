module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroAsymmetric

/-!
# Both original asymmetric opposite zero edges

Uncompiled source draft.  The original G1 owner theorem retains every
weak owner and reduces it to the appropriate secondary order.  Both
literal role labels, signs, and the original cycle telescope are
restored; reflected reversal covers the target-secondary order.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Asymmetric
open CommonQuarter Arithmetic TableFreeWordGeometry

lemma literal_zero (a b A B x : ℝ) :
    SecondWord.cost 0 .outer .outer true false a b A B x=x+PLabel.eval a b+JLabel.eval A B := by
  norm_num [SecondWord.cost,label,wrongValue,WordProblems.secondCoefficients,
    WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,next,RoleLabel.eval,PLabel,JLabel]
  ring
lemma literal_one (a b A B x : ℝ) :
    SecondWord.cost 1 .outer .outer true false a b A B x=x+JLabel.eval a b+PLabel.eval A B := by
  norm_num [SecondWord.cost,label,wrongValue,WordProblems.secondCoefficients,
    WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,next,RoleLabel.eval,PLabel,JLabel]
  ring

theorem original_source {i : Vertex} (hi : i=0 ∨ i=1)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    threshold i<SecondWord.cost i .outer .outer true false a b A B x := by
  rw [threshold_value]
  rcases hi with rfl | rfl
  · rw [literal_zero]
    have hh := original false hs ht hx hm
    dsimp [F,G] at hh
    linarith
  · rw [literal_one]
    have hh := original true hs ht hx hm
    dsimp [F,G] at hh
    linarith

theorem original_target {i : Vertex} (hi : i=0 ∨ i=1)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 (-1) x) :
    threshold i<SecondWord.cost i .outer .outer true false a b A B x := by
  have hrev : 0≤Eight.forwardMargin 0 A B a b 1 (-1) x := by
    simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm
  have hir : reverseEdge i=0 ∨ reverseEdge i=1 := by
    rcases hi with rfl | rfl <;> norm_num [reverseEdge]
  have hh := original_source hir ht hs hx hrev
  have he := cost_reflection i .outer .outer true false a b A B x
  norm_num at he
  rw [he,threshold_value] at hh
  simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F₀ : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F₀.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : i=0 ∨ i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i≠positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F₀ hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hz : F₀.word hgap pi_lt_22_over_7 i=0 := by
    rw [hw]; rcases hi with rfl | rfl <;> norm_num [WordProblems.wrongWord]
  have hx : |phaseValue F₀ hgap i|≤7/10 := by simpa [phaseValue,hz] using (difference_small F₀ i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hm := original_margin C F₀ hgap i j howner
  have hh : threshold i<SecondWord.cost i .outer .outer
      (positiveOf C i) (positiveOf C (next i)) (C.a i) (C.b i)
      (C.a (next i)) (C.b (next i)) (phaseValue F₀ hgap i) := by
    rcases WrongZeroOriginalOwners.original C F₀ hgap i hz j howner with
      ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
    · have htargetneg : positiveOf C (next i)=false := by
        cases h : positiveOf C (next i) <;> simp_all
      rw [hpos,htargetneg]
      exact original_source hi hsource htarget hx (by simpa [hpos,htargetneg,WordProblems.sign] using hm)
    · have hsourcepos : positiveOf C i=true := by cases h : positiveOf C i <;> simp_all
      rw [hsourcepos,hneg]
      exact original_target hi hsource htarget hx (by simpa [hsourcepos,hneg,WordProblems.sign] using hm)
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual (C : BoundaryCycle Q0) (F₀ : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F₀.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : i=0 ∨ i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i≠positiveOf C (next i)) :
    threshold i<phaseValue F₀ hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F₀ hgap hw i hi hs ht hsg j (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Asymmetric
