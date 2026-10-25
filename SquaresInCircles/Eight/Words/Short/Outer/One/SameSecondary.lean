module

public import SquaresInCircles.Eight.Words.Short.Outer.One.RoleFour
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryNegativeFirst
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryNegativeLater
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryPositive

/-!
# Eight squares: both complete halves of the three same-sign secondary owners

The first two original owners are restored by the literal reflection
and reversal of the adjacent states. The third is already in the
normalized orientation. All original weak owner ties remain included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem negative_original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (449/500:ℝ)<Real.pi/2-x+c r-P r*a+t r*b+p r*A-q r*B := by
  by_cases hr : r=0
  · subst r
    exact Negative.FirstStrip.original hs ht hx hm
  · have hrows : r=1 ∨ r=2 := by fin_cases r <;> simp_all
    linarith [Negative.Later.original r hrows hs ht hx hm]

theorem normalized (r : Row) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (449/500:ℝ)<φ+c r-P r*a+t r*b+p r*A-q r*B := by
  obtain ⟨high,x,hx,rfl⟩ := Unit.angle_cover hφ
  have hh := RoleFour.primary_margin high hx hm
  cases high
  · have hh' : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x := by
      simp only [Unit.direction,Bool.false_eq_true,↓reduceIte] at hh
      linarith
    have hv := negative_original r hs ht hx hh'
    simp only [Unit.angle,Unit.direction,Bool.false_eq_true,↓reduceIte]
    linarith
  · have hh' : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+B*Real.sin x := by
      simp only [Unit.direction,↓reduceIte] at hh
      linarith
    have hv := Positive.original r hs ht hx hh'
    simp only [Unit.angle,Unit.direction,↓reduceIte]
    linarith

def OriginalOwner (i : Vertex) (σ : Bool) (j : Fin 4) : Prop :=
  ((i=2 ∨ i=4) ∧ σ=false ∧ j=2) ∨ (i=6 ∧ σ=true ∧ j=0)

theorem original_owner (i : Vertex) (σ : Bool) (j : Fin 4) (hrole : OriginalOwner i σ j)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) .outer σ A B := by
  rcases hrole with ⟨hi,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hm' : 0≤Eight.forwardMargin 0 A B a b 1 1 φ := by
      simp [WordProblems.sign,Eight.forwardMargin] at hm ⊢
      linarith
    rcases hi with rfl | rfl
    · have hh := normalized 0 ht hs hφ hm'
      norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
        WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t] at *
      linarith
    · have hh := normalized 1 ht hs hφ hm'
      norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
        WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t] at *
      linarith
  · have hh := normalized 2 hs ht hφ (by simpa [WordProblems.sign] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t] at *
    linarith

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (_hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) (j : Fin 4)
    (hrole : OriginalOwner i (positiveOf C i) j)
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
  have hh := original_owner i (positiveOf C i) j hrole
    hsource htarget hφ (by simpa [←hsg] using hm)
  have hh' : (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by simpa only [wrongMarker,hs,ht,←hsg] using hh
  exact (ShortWord.Zero.threshold_le i).trans_lt hh'

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary
