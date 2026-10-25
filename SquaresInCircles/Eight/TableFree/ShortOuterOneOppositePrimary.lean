module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryNegative
public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpper

/-!
# All six stipulated opposite-primary owners of the short word

Uncompiled assembly of the negative-primary and both upper-primary hand
notes. Each original primary axis is retained, including simultaneous
owners. Reflection and reversal restore axes two with the exact label
rule (p,q,P,t) ↦ (-P,t,-p,q). Both full angle halves and the distinct
edge-two threshold are preserved.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

theorem normalized (r : Row) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 φ) :
    threshold r<φ+c r+p r*a-q r*b-P r*A-t r*B := by
  obtain ⟨high,x,hx,rfl⟩ := Unit.angle_cover hφ
  have hm' := normalized_margin high hx hm
  cases high
  · have hh := Negative.original r hs ht hx (by
      simp only [Unit.direction,Bool.false_eq_true,ite_false] at hm'
      linarith)
    simpa [cost] using hh
  · have hh := Upper.original r hs ht hx (by simpa [Unit.direction] using hm')
    simpa [cost] using hh

def OriginalOwner (i : Vertex) (j : Fin 4) : Prop :=
  (i=2∨i=4∨i=6) ∧ (j=1∨j=3)

theorem original_owner (i : Vertex) (j : Fin 4) (hrole : OriginalOwner i j)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (WordProblems.wrongGamma .short i:ℝ)<φ+wrongValue .short i .outer false a b-
      wrongValue .short (next i) .outer true A B := by
  rcases hrole with ⟨hi,hj⟩
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl
  · have hh := normalized 0 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 1 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 2 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 3 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 4 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 5 hs ht hφ hm
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
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hi]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  simp only [hσ,hτ,WordProblems.sign,Bool.false_eq_true,ite_false,ite_true,
    Rat.cast_neg,Rat.cast_one] at hm
  have hh := original_owner i j hrole hsource htarget hφ hm
  simpa only [wrongMarker,hs,ht,hσ,hτ] using hh

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary
