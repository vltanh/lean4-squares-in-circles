module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneUnitScalars

/-!
# The eight original unit-support quarter-one owners

Uncompiled transcription of Sections 2--4 of
`HAND_SHORT_WORD_SAME_SIGN_UNIT_SUPPORTS_WITHOUT_TABLES.md`.
Each original weak owner is multiplied by one on both complete angle
halves. Exact circle endpoint supports give the scalar estimates already
proved, and reversal restores the literal adjacent role labels.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Unit
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry WrongWordCircleSupport

lemma source_V (r : Row) {a b : ℝ} (hs : OuterState a b) :
    vp r*outerAxial≤vp r*a+(1-vq r)*b := by
  apply outer_concave_lower hs (coefficient_bounds r).1 le_rfl
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  fin_cases r <;> norm_num [vp,vq] <;> linarith

lemma target_V_signs (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    -vP r-Real.cos x<0 ∧ 0<vt r+direction high*Real.sin x := by
  have ht := positive_trig hx
  fin_cases r <;> cases high <;> norm_num [vP,vt,direction] <;>
    constructor <;> linarith [ht.1,ht.2.2.1,ht.2.2.2.1]

lemma target_V (r : Row) (high : Bool) {A B x : ℝ}
    (ht : OuterState A B) (hx : x∈Icc 0 (7/10)) :
    (-vP r-Real.cos x)*outerAxial≤
      (-vP r-Real.cos x)*A+(vt r+direction high*Real.sin x)*B := by
  have hh := target_V_signs r high hx
  apply outer_axial_lower ht hh.1.le
  have hp := mul_nonneg
    (show 0≤outerAxial+1/2 by linarith [outer_endpoint_bounds.1]) hh.2.le
  linarith

theorem V_original_half (r : Row) (high : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤
      -b+A*Real.cos x-direction high*B*Real.sin x) :
    (949/1000:ℝ)<angle high x+c r+vp r*a-vq r*b-vP r*A+vt r*B := by
  have hsrc := source_V r hs
  have htar := target_V r high ht hx
  have hvalue := V_lower r high hx
  dsimp [V] at hvalue
  nlinarith only [hsrc,htar,hm,hvalue]

lemma source_U (r : Row) {a b : ℝ} (hs : OuterState a b) :
    (up r-1)*outerAxial≤(up r-1)*a+uq r*b := by
  have hrow := coefficient_bounds r
  have hp : up r<1 ∧ 0<uq r := by fin_cases r <;> norm_num [up,uq,vP,vt]
  apply outer_axial_lower hs (by linarith)
  have hh := mul_nonneg
    (show 0≤outerAxial+1/2 by linarith [outer_endpoint_bounds.1]) hp.2.le
  linarith

theorem U_low_half (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤a-A*Real.sin x-B*Real.cos x) :
    (949/1000:ℝ)<angle false x+c r+up r*a+uq r*b-uP r*A-ut r*B := by
  have hsrc := source_U r hs
  have hX : 0≤-uP r+Real.sin x := by
    have hP : uP r≤0 := by fin_cases r <;> norm_num [uP,vp]
    linarith [(positive_trig hx).2.2.1]
  by_cases hmin : (-uP r+Real.sin x)*outerAxial≤
      (-uP r+Real.sin x+(Real.cos x-ut r))*outerDiagonal
  · have htar := outer_concave_lower ht hX le_rfl hmin
    have hscalar := axial_lower r hx
    simp only [axial,angle,direction,Bool.false_eq_true,↓reduceIte] at hscalar ⊢
    linarith only [hsrc,htar,hm,hscalar]
  · have htar := outer_concave_lower ht hX (le_of_not_ge hmin) le_rfl
    have hscalar := diagonal_lower r hx
    simp only [diagonal,angle,direction,Bool.false_eq_true,↓reduceIte] at hscalar ⊢
    linarith only [hsrc,htar,hm,hscalar]

lemma target_U_high (r : Row) {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) :
    -uP r*outerDiagonal-outerAxial*Real.sin x-(ut r-191/250)*outerDiagonal≤
      (-uP r-Real.sin x)*A+(Real.cos x-ut r)*B := by
  have hs := outer_bounds ht
  have htr := positive_trig hx
  have hP : uP r≤0 ∧ (191/250:ℝ)<ut r := by
    fin_cases r <;> norm_num [uP,ut,vp,vq]
  have hp := mul_le_mul_of_nonneg_left hs.1 (neg_nonneg.mpr hP.1)
  have hsin := mul_le_mul_of_nonneg_right hs.2.1 htr.2.2.1
  have hcos := mul_le_mul_of_nonneg_right
    (show (191/250:ℝ)≤Real.cos x by linarith [htr.1]) ht.1
  have htarget := mul_le_mul_of_nonpos_left hs.2.2.2.1
    (show (191/250:ℝ)-ut r≤0 by linarith)
  nlinarith only [hp,hsin,hcos,htarget]

theorem U_high_half (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x-B*Real.cos x) :
    (949/1000:ℝ)<angle true x+c r+up r*a+uq r*b-uP r*A-ut r*B := by
  have hsrc := source_U r hs
  have htar := target_U_high r ht hx
  have htr := positive_trig hx
  have hp := mul_nonneg
    (show 0≤3/2-outerAxial by linarith [outer_endpoint_bounds.2.1]) htr.2.2.1
  have hangle : 0≤x+(1/2-outerAxial)*Real.sin x := by
    nlinarith [htr.2.2.2.2.1]
  have hf := positive_floor r
  dsimp [positiveFloor,angle,direction] at *
  nlinarith only [hsrc,htar,hangle,hm,hf,htr.1]

lemma V_margin (high : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (angle high x)) :
    (1+Real.cos x+Real.sin x)/2≤-b+A*Real.cos x-direction high*B*Real.sin x := by
  have hw := quarter_width (x := direction high*x)
    (by cases high <;> simpa [direction,abs_of_nonneg hx.1,abs_neg] using hx.2)
  have hs := (positive_trig hx).2.2.1
  cases high <;>
    norm_num [angle,direction,Eight.forwardMargin,Real.sin_add,Real.cos_add,
      Real.sin_neg,Real.cos_neg,abs_of_nonneg hs,abs_neg] at hm hw ⊢ <;> linarith

lemma U_margin (high : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 (angle high x)) :
    (1+Real.cos x+Real.sin x)/2≤a+direction high*A*Real.sin x-B*Real.cos x := by
  have hw := quarter_width (x := direction high*x)
    (by cases high <;> simpa [direction,abs_of_nonneg hx.1,abs_neg] using hx.2)
  have hs := (positive_trig hx).2.2.1
  cases high <;>
    norm_num [angle,direction,Eight.forwardMargin,Real.sin_add,Real.cos_add,
      Real.sin_neg,Real.cos_neg,abs_of_nonneg hs,abs_neg] at hm hw ⊢ <;> linarith

lemma angle_cover {φ : ℝ} (hφ : |φ-Real.pi/2|≤7/10) :
    ∃high x, x∈Icc 0 (7/10) ∧ angle high x=φ := by
  by_cases h : Real.pi/2≤φ
  · exact ⟨true,φ-Real.pi/2,⟨by linarith,(abs_le.mp hφ).2⟩,by simp [angle,direction]⟩
  · refine ⟨false,Real.pi/2-φ,⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩,?_⟩
    dsimp [angle,direction]
    ring

theorem V_original (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) φ) :
    (949/1000:ℝ)<φ+c r+vp r*a-vq r*b-vP r*A+vt r*B := by
  obtain ⟨high,x,hx,he⟩ := angle_cover hφ
  subst φ
  exact V_original_half r high hs ht hx (V_margin high hx hm)

theorem U_original (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 φ) :
    (949/1000:ℝ)<φ+c r+up r*a+uq r*b-uP r*A-ut r*B := by
  obtain ⟨high,x,hx,he⟩ := angle_cover hφ
  subst φ
  have hmargin := U_margin high hx hm
  cases high
  · exact U_low_half r hs ht hx (by
      simp only [direction,Bool.false_eq_true,↓reduceIte] at hmargin; linarith)
  · exact U_high_half r hs ht hx (by simp only [direction,↓reduceIte] at hmargin; linarith)

def OriginalOwner (i : Vertex) (σ : Bool) (j : Fin 4) : Prop :=
  ((i=2 ∨ i=4) ∧ σ=false ∧ (j=0 ∨ j=1)) ∨
  ((i=4 ∨ i=6) ∧ σ=true ∧ (j=2 ∨ j=3))

macro "short_unit_literal" : tactic => `(tactic|
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,next,c,vp,vq,vP,vt,up,uq,uP,ut] at * <;> linarith)

/-- All eight original owners and both angle halves, with literal source labels. -/
theorem original_owner (i : Vertex) (σ : Bool) (j : Fin 4) (hrole : OriginalOwner i σ j)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign σ) φ) :
    (949/1000:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) .outer σ A B := by
  rcases hrole with ⟨hi,rfl,hj⟩ | ⟨hi,rfl,hj⟩
  · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · have hh := V_original 0 hs ht hφ (by simpa [WordProblems.sign] using hm)
      short_unit_literal
    · have hh := U_original 0 ht hs hφ (by
        simp [WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_unit_literal
    · have hh := V_original 1 hs ht hφ (by simpa [WordProblems.sign] using hm)
      short_unit_literal
    · have hh := U_original 1 ht hs hφ (by
        simp [WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_unit_literal
  · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · have hh := V_original 2 ht hs hφ (by
        simp [WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_unit_literal
    · have hh := U_original 2 hs ht hφ (by simpa [WordProblems.sign] using hm)
      short_unit_literal
    · have hh := V_original 3 ht hs hφ (by
        simp [WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_unit_literal
    · have hh := U_original 3 hs ht hφ (by simpa [WordProblems.sign] using hm)
      short_unit_literal

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
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
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hh := original_owner i (positiveOf C i) j hrole
    hsource htarget hφ (by simpa [←hsg] using hm)
  have hΓ := ShortWord.Zero.threshold_le i
  have hh' : (949/1000:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by simpa only [wrongMarker,hs,ht,←hsg] using hh
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Unit
