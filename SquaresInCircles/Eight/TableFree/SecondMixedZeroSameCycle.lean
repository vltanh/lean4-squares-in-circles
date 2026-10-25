module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroSameCore
public import SquaresInCircles.Eight.TableFree.SecondMixedZeroSameOuter

/-!
# Every original same-sign mixed zero edge of the second wrong word

Uncompiled source draft.  The independent cyclic owner theorem fixes
the source-secondary owner for positive signs and the target-secondary
owner for negative signs.  The latter is an exact reflected expression
of one of the two positive radial orders.  All original axes are tested
before this reduction, including axes tied at a weak physical contact.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Same
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

def Mixed (source target : RadialKind) : Prop :=
  (source=.outer ∧ target≠.outer) ∨ (source≠.outer ∧ target=.outer)

lemma mixed_swap {source target : RadialKind} (hm : Mixed source target) :
    Mixed target source := by
  rcases hm with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact Or.inr ⟨ht,hs⟩
  · exact Or.inl ⟨ht,hs⟩

lemma positive_roles (i : Vertex) (hi : WordProblems.wrongWord .second i=0)
    (ha : WordProblems.allowed .second i true true) : i=0 ∨ i=4 := by
  revert hi ha
  fin_cases i <;> norm_num [WordProblems.wrongWord,WordProblems.allowed,next]

lemma negative_roles (i : Vertex) (hi : WordProblems.wrongWord .second i=0)
    (ha : WordProblems.allowed .second i false false) : i=1 ∨ i=4 := by
  revert hi ha
  fin_cases i <;> norm_num [WordProblems.wrongWord,WordProblems.allowed,next]

theorem original_row (r : SameRow) {source target : RadialKind}
    (hmixed : Mixed source target) {a b A B x : ℝ}
    (hs : State source a b) (ht : State target A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    (17953/20000:ℝ)<cost (![0,4] r) source target true true a b A B x := by
  rcases hmixed with ⟨rfl,hcore⟩ | ⟨hcore,rfl⟩
  · have ho : OuterState a b := by simpa [State] using hs
    have hc : CoreState A B := by simpa [State,hcore] using ht
    rw [same_outer_literal r target hcore ho]
    exact SameOuter.original r ho hc hx hm
  · have hc : CoreState a b := by simpa [State,hcore] using hs
    have ho : OuterState A B := by simpa [State] using ht
    rw [same_core_literal r source hcore ho]
    exact SameCore.original r hc ho hx hm

theorem original_positive {i : Vertex} (hi : i=0 ∨ i=4)
    {source target : RadialKind} (hmixed : Mixed source target)
    {a b A B x : ℝ} (hs : State source a b) (ht : State target A B)
    (hx : |x|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    threshold i<cost i source target true true a b A B x := by
  rw [threshold_value]
  rcases hi with rfl | rfl
  · simpa using original_row (0:SameRow) hmixed hs ht hx hm
  · simpa using original_row (1:SameRow) hmixed hs ht hx hm

theorem original_negative {i : Vertex} (hi : i=1 ∨ i=4)
    {source target : RadialKind} (hmixed : Mixed source target)
    {a b A B x : ℝ} (hs : State source a b) (ht : State target A B)
    (hx : |x|≤7/10) (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) x) :
    threshold i<cost i source target false false a b A B x := by
  have hrev : 0≤Eight.forwardMargin 0 A B a b 1 1 x := by
    have h2 : Eight.forwardMargin 2 a b A B (-1) (-1) x=
        a*Real.sin x+(-1)*b*Real.cos x-(-1)*B-pairWidth x := rfl
    have h0 : Eight.forwardMargin 0 A B a b 1 1 x=
        1*B+a*Real.sin x-1*b*Real.cos x-pairWidth x := rfl
    rw [h0]
    rw [h2] at hm
    linarith
  have hir : reverseEdge i=0 ∨ reverseEdge i=4 := by
    rcases hi with rfl | rfl <;> norm_num [reverseEdge]
  have hh := original_positive hir (mixed_swap hmixed) ht hs hx hrev
  have he := cost_reflection i source target false false a b A B x
  norm_num at he
  rw [he,threshold_value] at hh
  simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : Mixed (C.kind i) (C.kind (next i)))
    (hsg : positiveOf C i=positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hx : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hword : WordProblems.wrongWord .second i=0 := by simpa [hw] using hi
  have ha := actual_allowed C F hgap .second hw i
  have hm := original_margin C F hgap i j howner
  have hh : threshold i<cost i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (phaseValue F hgap i) := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with
      ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
    · have htpos : positiveOf C (next i)=true := hsg.symm.trans hpos
      rw [hpos,htpos] at ha ⊢
      exact original_positive (positive_roles i hword ha) hmixed
        (actual_state C i) (actual_state C (next i)) hx
        (by simpa [hpos,htpos,WordProblems.sign] using hm)
    · have hsneg : positiveOf C i=false := hsg.trans hneg
      rw [hsneg,hneg] at ha ⊢
      exact original_negative (negative_roles i hword ha) hmixed
        (actual_state C i) (actual_state C (next i)) hx
        (by simpa [hsneg,hneg,WordProblems.sign] using hm)
  simpa only [cost,label,wrongMarker] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : Mixed (C.kind i) (C.kind (next i)))
    (hsg : positiveOf C i=positiveOf C (next i)) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hi hmixed hsg j howner

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Same
