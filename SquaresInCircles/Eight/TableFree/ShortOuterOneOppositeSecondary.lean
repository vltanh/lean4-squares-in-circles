module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeSecondaryNegative

/-!
# All six original opposite-sign secondary owners

Uncompiled assembly of
`HAND_SHORT_WORD_OPPOSITE_SECONDARY_FAMILIES_WITHOUT_TABLES.md`.
The original axes one and three are retained independently. Reflection
and reversal restore the latter using their literal adjacent labels.
Both full angle halves, all state endpoints, and every weak owner tie
are included, with the distinct edge-two threshold unchanged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeSecondary
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

lemma margin (high : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Unit.angle high x)) :
    (1+Real.cos x+Real.sin x)/2≤ -b+A*Real.cos x+Unit.direction high*B*Real.sin x := by
  have hw := quarter_width (x:=Unit.direction high*x)
    (by cases high <;> simpa [Unit.direction,abs_of_nonneg hx.1,abs_neg] using hx.2)
  have hs := (positive_trig hx).2.2.1
  cases high <;>
    norm_num [Unit.angle,Unit.direction,Eight.forwardMargin,Real.sin_add,Real.cos_add,
      Real.sin_neg,Real.cos_neg,abs_of_nonneg hs,abs_neg] at hm hw ⊢ <;> linarith

theorem normalized (r : Row) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 φ) :
    threshold r<φ+c r+p r*a-q r*b-P r*A-t r*B := by
  obtain ⟨high,x,hx,rfl⟩ := Unit.angle_cover hφ
  have hm' := margin high hx hm
  have hv : threshold r<value r high x := by
    cases high
    · exact Negative.value_lower r hx
    · exact (Endpoint.initial_threshold r true).trans_le
        (Positive.value_monotone r (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx hx.1)
  exact hv.trans_le (original_support r high hs ht hm')

def OriginalOwner (i : Vertex) (j : Fin 4) : Prop := (i=2 ∨ i=4 ∨ i=6) ∧ (j=0 ∨ j=2)

theorem original_owner (i : Vertex) (j : Fin 4) (hrole : OriginalOwner i j)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (WordProblems.wrongGamma .short i:ℝ)<φ+wrongValue .short i .outer false a b-
      wrongValue .short (next i) .outer true A B := by
  rcases hrole with ⟨hi,hj⟩
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl
  · have hh := normalized 0 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 1 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 2 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 3 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 4 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 5 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true) (j : Fin 4)
    (hrole : OriginalOwner i j)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    WordProblems.wrongGamma .short i<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hm := original_margin C F hgap i j howner
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hh := original_owner i j hrole hsource htarget
    hφ (by simpa [hσ,hτ,WordProblems.sign] using hm)
  simpa only [wrongMarker,hs,ht,hσ,hτ] using hh

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeSecondary
