module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJMinimum
public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroLKCycle

/-!
# Every original same-sign outer zero-quarter row

Uncompiled source draft.  The P/J and L/K representatives and their
reflected reversals are joined using the original allowed role signs.
All weak owners are retained through the independent G1 owner theorem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero
open CommonQuarter Arithmetic TableFreeWordGeometry

lemma PJ_positive_cost (a b A B x : ℝ) :
    SecondWord.cost 0 .outer .outer true true a b A B x=
      x+PLabel.eval a b-JLabel.eval A B := by
  norm_num [SecondWord.cost,label,wrongValue,WordProblems.secondCoefficients,
    WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
    next,RoleLabel.eval,PLabel,JLabel]
  ring

theorem original_positive {i : Vertex} (hi : i=0 ∨ i=4)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    threshold i<SecondWord.cost i .outer .outer true true a b A B x := by
  rw [threshold_value]
  rcases hi with rfl | rfl
  · rw [PJ_positive_cost]
    linarith [PJ.original_primary hs ht hx hm]
  · linarith [LK.original_positive hs ht hx hm]

theorem original_negative {i : Vertex} (hi : i=1 ∨ i=4)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) x) :
    threshold i<SecondWord.cost i .outer .outer false false a b A B x := by
  have hrev : 0≤Eight.forwardMargin 0 A B a b 1 1 x := by
    simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm
  have hir : reverseEdge i=0 ∨ reverseEdge i=4 := by
    rcases hi with rfl | rfl <;> norm_num [reverseEdge]
  have hh := original_positive hir ht hs hx hrev
  have he := cost_reflection i .outer .outer false false a b A B x
  norm_num at he
  rw [he,threshold_value] at hh
  simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hx : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hword : WordProblems.wrongWord .second i=0 := by simpa [hw] using hi
  have ha := actual_allowed C F hgap .second hw i
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,if_pos rfl] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,if_pos rfl] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  have hh : threshold i<SecondWord.cost i .outer .outer
      (positiveOf C i) (positiveOf C (next i)) (C.a i) (C.b i)
      (C.a (next i)) (C.b (next i)) (phaseValue F hgap i) := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with
      ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
    · have htpos : positiveOf C (next i)=true := hsg.symm.trans hpos
      rw [hpos,htpos] at ha ⊢
      have hir : i=0 ∨ i=4 := by
        fin_cases i <;> norm_num [WordProblems.wrongWord,WordProblems.allowed,next] at hword ha ⊢
      exact original_positive hir hsource htarget hx
        (by simpa [hpos,htpos,WordProblems.sign] using hm)
    · have hsneg : positiveOf C i=false := hsg.trans hneg
      rw [hsneg,hneg] at ha ⊢
      have hir : i=1 ∨ i=4 := by
        fin_cases i <;> norm_num [WordProblems.wrongWord,WordProblems.allowed,next] at hword ha ⊢
      exact original_negative hir hsource htarget hx
        (by simpa [hsneg,hneg,WordProblems.sign] using hm)
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F hgap hw i hi hs ht hsg j
    (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero
