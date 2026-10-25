module

public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroLKMinimum
public import SquaresInCircles.Eight.Words.Wrong.ZeroOriginalOwners

/-!
# Eight squares: both original same-sign L/K zero-quarter rows

The full contact bound is restored to the
literal role-four labels.  Reflected reversal gives the negative row.
The independent G1 zero-owner theorem excludes the other original
axes, including every weak tie, before either scalar estimate is used.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.SameZero.LK
open CommonQuarter Arithmetic QuarterWordGeometry

lemma positive_cost (a b A B x : ℝ) :
    SecondWord.cost 4 .outer .outer true true a b A B x=
      x+LLabel.eval a b-KLabel.eval A B := by
  norm_num [SecondWord.cost,label,wrongValue,WordProblems.secondCoefficients,
    WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
    next,RoleLabel.eval,LLabel,KLabel]

theorem original_positive {a b A B x : ℝ} (hs : OuterState a b)
    (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    (89777/100000:ℝ)<SecondWord.cost 4 .outer .outer true true a b A B x := by
  rw [positive_cost]
  exact original_primary hs ht hx hm

theorem original_negative {a b A B x : ℝ} (hs : OuterState a b)
    (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) x) :
    (89777/100000:ℝ)<SecondWord.cost 4 .outer .outer false false a b A B x := by
  have hrev : 0≤Eight.forwardMargin 0 A B a b 1 1 x := by
    simp [Eight.forwardMargin] at hm ⊢
    linarith
  have hh := original_positive ht hs hx hrev
  have he := cost_reflection (4:Vertex) .outer .outer true true A B a b x
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (hs : C.kind 4=.outer) (ht : C.kind (next 4)=.outer)
    (hsg : positiveOf C 4=positiveOf C (next 4)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square 4) (C.square (next 4))) :
    threshold 4<phaseValue F hgap 4+wrongMarker C .second 4-
      wrongMarker C .second (next 4) := by
  have hz : F.word hgap pi_lt_22_over_7 4=0 := by
    rw [hw]
    norm_num [WordProblems.wrongWord]
  have hx : |phaseValue F hgap 4|≤7/10 := by
    simpa [phaseValue,hz] using (difference_small F 4).le
  have hsource : OuterState (C.a 4) (C.b 4) := by
    simpa only [State,hs,↓reduceIte] using actual_state C 4
  have htarget : OuterState (C.a (next 4)) (C.b (next 4)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next 4)
  have hm := original_margin C F hgap 4 j howner
  have hh : (89777/100000:ℝ)<SecondWord.cost 4 .outer .outer
      (positiveOf C 4) (positiveOf C (next 4))
      (C.a 4) (C.b 4) (C.a (next 4)) (C.b (next 4)) (phaseValue F hgap 4) := by
    rcases WrongZeroOriginalOwners.original C F hgap 4 hz j howner with
      ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
    · have htpos : positiveOf C (next 4)=true := hsg.symm.trans hpos
      rw [hpos,htpos]
      exact original_positive hsource htarget hx
        (by simpa [hpos,htpos,WordProblems.sign] using hm)
    · have hsneg : positiveOf C 4=false := hsg.trans hneg
      rw [hsneg,hneg]
      exact original_negative hsource htarget hx
        (by simpa [hsneg,hneg,WordProblems.sign] using hm)
  rw [threshold_value]
  have he : SecondWord.cost 4 .outer .outer (positiveOf C 4)
      (positiveOf C (next 4)) (C.a 4) (C.b 4) (C.a (next 4)) (C.b (next 4))
      (phaseValue F hgap 4)=phaseValue F hgap 4+wrongMarker C .second 4-
        wrongMarker C .second (next 4) := by
    simp only [SecondWord.cost,label,wrongMarker,hs,ht]
  rw [he] at hh
  linarith

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (hs : C.kind 4=.outer) (ht : C.kind (next 4)=.outer)
    (hsg : positiveOf C 4=positiveOf C (next 4)) :
    threshold 4<phaseValue F hgap 4+wrongMarker C .second 4-
      wrongMarker C .second (next 4) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl 4 (C.selected 4) (C.feasible 4)
  have howner : (forwardAxis j).Feasible (C.square 4) (C.square (next 4)) := by
    simpa only [←hj] using C.feasible 4
  exact actual_owner C F hgap hw hs ht hsg j howner

end SquaresInCircles.Eight.SecondWord.SameZero.LK
