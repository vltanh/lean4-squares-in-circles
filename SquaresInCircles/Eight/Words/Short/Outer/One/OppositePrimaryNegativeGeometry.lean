module

public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial
public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Stationary.System
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroLReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAsymmetric
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperAxialData
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveUpperPrimary
public import SquaresInCircles.Eight.Words.Short.Outer.One.UnitScalars
public import SquaresInCircles.Eight.Words.Short.WordZero

/-!
# Eight squares: the original lower primary separator forces the whole angle cap

The separator makes the whole angle region beyond the cap impossible (`forced_cap`). The proof
takes the two outer-arc endpoints (`target_support`) and the strictly decreasing original
feasibility expression (`feasibility_decreases`, `cap_infeasible`).
-/

section
/-!
## The eight original unit-support quarter-one owners

Each original weak owner is multiplied by one on both complete angle
halves. Exact circle endpoint supports give the scalar estimates already
proved, and reversal restores the literal adjacent role labels.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Unit
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry WrongWordCircleSupport

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
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hh := original_owner i (positiveOf C i) j hrole
    hsource htarget hφ (by simpa [←hsg] using hm)
  have hΓ := ShortWord.Zero.threshold_le i
  have hh' : (949/1000:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by simpa only [wrongMarker,hs,ht,←hsg] using hh
  linarith

end SquaresInCircles.Eight.ShortOuterOne.Unit
end
end
end

section
/-!
## All role-four positive-sign original quarter owners

The first two original owners use their exact weak separator with
multiplier .71553. Reflection restores the second original owner. The
other two original owners are the previously proved unit supports.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.RoleFour
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry WrongWordCircleSupport

lemma primaryHigh_support {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) :
    (-weight*Real.cos x+(-target-weight*Real.sin x))*outerDiagonal≤
      -weight*Real.cos x*A+(-target-weight*Real.sin x)*B := by
  apply outer_diagonal_lower ht
  · have hc := (positive_trig hx).1
    dsimp [weight]
    linarith
  · have hh := positive_trig hx
    dsimp [weight,target]
    linarith [hh.2.1,hh.2.2.1]

theorem primary_high {a b A B x : ℝ} (_hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+B*Real.sin x) :
    (89809/100000:ℝ)<Real.pi/2+x+constant+weight*b-target*B := by
  have htar := primaryHigh_support ht hx
  have hmargin := mul_le_mul_of_nonneg_left hm (show 0≤weight by norm_num [weight])
  have hscalar := primaryHigh_lower hx
  dsimp [primaryHigh] at hscalar
  nlinarith only [htar,hmargin,hscalar]

lemma primaryLow_diagonal_support {e A B x : ℝ} (he : IsEvent e)
    (ht : OuterState A B) (hx : x∈Icc 0 e) :
    (-weight*Real.cos x+(-target+weight*Real.sin x))*outerDiagonal≤
      -weight*Real.cos x*A+(-target+weight*Real.sin x)*B := by
  apply outer_diagonal_lower ht
  · have hc := (positive_trig
      (show x∈Icc 0 (7/10) from ⟨hx.1,hx.2.trans (event_angle he).2⟩)).1
    dsimp [weight]
    linarith
  · nlinarith only [before_event he hx]

lemma norm_coefficients (x : ℝ) :
    Real.sqrt ((-weight*Real.cos x)^2+(-target+weight*Real.sin x)^2)=N x := by
  unfold N CircularNorm.norm
  congr 1
  dsimp [CircularNorm.energy,normA,normC]
  linear_combination weight^2*(Real.sin_sq_add_cos_sq x)

theorem primary_low {a b A B x : ℝ} (_hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (89809/100000:ℝ)<Real.pi/2-x+constant+weight*b-target*B := by
  obtain ⟨e,he⟩ := exists_event
  have hmargin := mul_le_mul_of_nonneg_left hm (show 0≤weight by norm_num [weight])
  rcases le_total x e with hxe | hex
  · have htar := primaryLow_diagonal_support he ht ⟨hx.1,hxe⟩
    have hdiagonal := diagonal_increasing (show (0:ℝ)∈Icc 0 (3/10) by norm_num)
      (show x∈Icc 0 (3/10) from ⟨hx.1,hxe.trans he.1.2.le⟩) hx.1
    have hscalar : (90009/100000:ℝ)<diagonal x := diagonal_initial.trans_le hdiagonal
    dsimp [diagonal] at hscalar
    nlinarith only [htar,hmargin,hscalar]
  · have htar := ShortOuterZero.Opposite.Positive.Cap.full_circle_lower
      (X := -weight*Real.cos x) (Y := -target+weight*Real.sin x) ht
    rw [norm_coefficients] at htar
    have hscalar := normValue_lower he ⟨hex,hx.2⟩
    dsimp [normValue] at hscalar
    nlinarith only [htar,hmargin,hscalar]

lemma secondary_source {a b : ℝ} (hs : OuterState a b) :
    -(weight+target)*outerDiagonal≤-weight*a-target*b := by
  have hh := outer_diagonal_lower (X := -weight) (Y := -target) hs
    (by norm_num [weight]) (by norm_num [weight,target])
  nlinarith only [hh]

lemma secondaryHigh_target {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) :
    -weight*Real.sin x*outerAxial≤
      -weight*Real.sin x*A+weight*(1-Real.cos x)*B := by
  have hh := positive_trig hx
  have hX : -weight*Real.sin x≤0 := by dsimp [weight]; linarith [hh.2.2.1]
  apply outer_axial_lower ht hX
  have hY := mul_nonneg
    (show 0≤outerAxial+1/2 by linarith [outer_endpoint_bounds.1])
    (show 0≤weight*(1-Real.cos x) by dsimp [weight]; linarith [hh.2.1])
  linarith

theorem secondary_high {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x+B*Real.cos x) :
    (90009/100000:ℝ)<Real.pi/2+x+constant-target*b+weight*B := by
  have hsrc := secondary_source hs
  have htar := secondaryHigh_target ht hx
  have hmargin := mul_le_mul_of_nonneg_left hm (show 0≤weight by norm_num [weight])
  have hscalar := secondaryHigh_lower hx
  dsimp [secondaryHigh] at hscalar
  nlinarith only [hsrc,htar,hmargin,hscalar]

theorem secondary_low {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤a-A*Real.sin x+B*Real.cos x) :
    (90009/100000:ℝ)<Real.pi/2-x+constant-target*b+weight*B := by
  have hsrc := secondary_source hs
  have hmargin := mul_le_mul_of_nonneg_left hm (show 0≤weight by norm_num [weight])
  have hX : 0≤weight*Real.sin x := by
    dsimp [weight]
    linarith [(positive_trig hx).2.2.1]
  by_cases hmin : weight*Real.sin x*outerAxial≤
      (weight*Real.sin x+weight*(1-Real.cos x))*outerDiagonal
  · have htar := outer_concave_lower ht hX le_rfl hmin
    have hscalar := secondaryLow_lower hx
    dsimp [secondaryLow] at hscalar
    nlinarith only [hsrc,htar,hmargin,hscalar]
  · have htar := outer_concave_lower ht hX (le_of_not_ge hmin) le_rfl
    have hscalar := diagonal_lower hx
    dsimp [diagonal] at hscalar
    nlinarith only [hsrc,htar,hmargin,hscalar]

lemma primary_margin (high : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 (Unit.angle high x)) :
    (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+Unit.direction high*B*Real.sin x := by
  have hw := quarter_width (x := Unit.direction high*x)
    (by cases high <;> simpa [Unit.direction,abs_of_nonneg hx.1,abs_neg] using hx.2)
  have hs := (positive_trig hx).2.2.1
  cases high <;>
    norm_num [Unit.angle,Unit.direction,Eight.forwardMargin,Real.sin_add,Real.cos_add,
      Real.sin_neg,Real.cos_neg,abs_of_nonneg hs,abs_neg] at hm hw ⊢ <;> linarith

lemma secondary_margin (high : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Unit.angle high x)) :
    (1+Real.cos x+Real.sin x)/2≤a+Unit.direction high*A*Real.sin x+B*Real.cos x := by
  have hw := quarter_width (x := Unit.direction high*x)
    (by cases high <;> simpa [Unit.direction,abs_of_nonneg hx.1,abs_neg] using hx.2)
  have hs := (positive_trig hx).2.2.1
  cases high <;>
    norm_num [Unit.angle,Unit.direction,Eight.forwardMargin,Real.sin_add,Real.cos_add,
      Real.sin_neg,Real.cos_neg,abs_of_nonneg hs,abs_neg] at hm hw ⊢ <;> linarith

theorem primary_original {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (89809/100000:ℝ)<φ+constant+weight*b-target*B := by
  obtain ⟨high,x,hx,rfl⟩ := Unit.angle_cover hφ
  have hh := primary_margin high hx hm
  cases high
  · have hm' : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x := by
      simp [Unit.direction] at hh
      linarith
    have h := primary_low hs ht hx hm'
    simp only [Unit.angle,Unit.direction,Bool.false_eq_true,↓reduceIte]
    linarith
  · have hm' : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+B*Real.sin x := by
      simp [Unit.direction] at hh
      linarith
    have h := primary_high hs ht hx hm'
    simp only [Unit.angle,Unit.direction,↓reduceIte]
    linarith

theorem secondary_original {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) φ) :
    (90009/100000:ℝ)<φ+constant-target*b+weight*B := by
  obtain ⟨high,x,hx,rfl⟩ := Unit.angle_cover hφ
  have hh := secondary_margin high hx hm
  cases high
  · have hm' : (1+Real.cos x+Real.sin x)/2≤a-A*Real.sin x+B*Real.cos x := by
      simp [Unit.direction] at hh
      linarith
    have h := secondary_low hs ht hx hm'
    simp only [Unit.angle,Unit.direction,Bool.false_eq_true,↓reduceIte]
    linarith
  · have hm' : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x+B*Real.cos x := by
      simp [Unit.direction] at hh
      linarith
    have h := secondary_high hs ht hx hm'
    simp only [Unit.angle,Unit.direction,↓reduceIte]
    linarith

/-- All four original weak owners, including simultaneous owners. -/
theorem original_owner (j : Fin 4) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    (17953/20000:ℝ)<φ+wrongValue .short 4 .outer true a b-
      wrongValue .short (next 4) .outer true A B := by
  fin_cases j
  · have hh := primary_original hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,next,weight,target,constant] at *
    linarith
  · have hh := secondary_original ht hs hφ (by simpa [Eight.forwardMargin,
      add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,next,weight,target,constant] at *
    linarith
  · have hh := Unit.original_owner 4 true 2
      (by norm_num [Unit.OriginalOwner]) hs ht hφ (by simpa [WordProblems.sign] using hm)
    linarith
  · have hh := Unit.original_owner 4 true 3
      (by norm_num [Unit.OriginalOwner]) hs ht hφ (by simpa [WordProblems.sign] using hm)
    linarith

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (hs : C.kind 4=.outer) (ht : C.kind (next 4)=.outer)
    (hσ : positiveOf C 4=true) (hτ : positiveOf C (next 4)=true) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square 4) (C.square (next 4))) :
    WordProblems.wrongGamma .short 4<phaseValue F hgap 4+wrongMarker C .short 4-
      wrongMarker C .short (next 4) := by
  have hk : F.word hgap pi_lt_22_over_7 4=1 := by rw [hw]; norm_num [WordProblems.wrongWord]
  have hφ : |phaseValue F hgap 4-Real.pi/2|≤7/10 := by
    simpa [phaseValue,hk] using (difference_small F 4).le
  have hm := original_margin C F hgap 4 j howner
  have hsource : OuterState (C.a 4) (C.b 4) := by
    simpa only [State,hs,↓reduceIte] using actual_state C 4
  have htarget : OuterState (C.a (next 4)) (C.b (next 4)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next 4)
  have hh := original_owner j hsource htarget hφ
    (by simpa [hσ,hτ,WordProblems.sign] using hm)
  simpa [WordProblems.wrongGamma,wrongMarker,hs,ht,hσ,hτ] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (hs : C.kind 4=.outer) (ht : C.kind (next 4)=.outer)
    (hσ : positiveOf C 4=true) (hτ : positiveOf C (next 4)=true) :
    WordProblems.wrongGamma .short 4<phaseValue F hgap 4+wrongMarker C .short 4-
      wrongMarker C .short (next 4) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl 4 (C.selected 4) (C.feasible 4)
  exact actual_owner C F hgap hw hs ht hσ hτ j (by simpa [← hj] using C.feasible 4)

end SquaresInCircles.Eight.ShortOuterOne.RoleFour
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Negative
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def cap : ℝ := 113/500
def feasibility (x : ℝ) : ℝ := outerAxial*(1-Real.sin x)-width x
def feasibilityD (x : ℝ) : ℝ := -(outerAxial+1/2)*Real.cos x+Real.sin x/2

theorem target_support {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 (7/10)) :
    outerAxial*Real.sin x≤A*Real.sin x+B*Real.cos x := by
  have tr := positive_trig hx
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hdk := mul_lt_mul'' hd.1 tr.1 (by norm_num) (by norm_num)
  have hds := mul_le_mul
    (show outerAxial-outerDiagonal≤176821959/125000000-449607/500000 by linarith)
    tr.2.2.2.1.le tr.2.2.1 (by norm_num)
  have hdiag : outerAxial*Real.sin x≤(Real.sin x+Real.cos x)*outerDiagonal := by
    linarith
  have hh := outer_concave_lower ht tr.2.2.1 (le_of_eq (mul_comm _ _)) hdiag
  linarith only [hh]

theorem feasibility_hasDerivAt (x : ℝ) : HasDerivAt feasibility (feasibilityD x) x := by
  have hw := ((((Real.hasDerivAt_cos x).const_add 1).fun_add (Real.hasDerivAt_sin x)).div_const 2)
  have hh := (((Real.hasDerivAt_sin x).const_sub 1).const_mul outerAxial).fun_sub hw
  exact hh.congr_deriv (by simp only [feasibilityD]; ring)

theorem feasibility_decreases : AntitoneOn feasibility (Icc 0 (7/10)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (feasibility_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => feasibility_hasDerivAt x)
  intro x hx
  have tr := positive_trig (Ioo_subset_Icc_self hx)
  have hp := mul_lt_mul''
    (show (191/100:ℝ)<outerAxial+1/2 by linarith [outer_endpoint_bounds.1]) tr.1
    (by norm_num) (by norm_num)
  dsimp [feasibilityD]
  linarith [tr.2.2.2.1]

theorem cap_infeasible : feasibility cap< -(17/10000:ℝ) := by
  let Z := (axial.mul ((Interval.point 1).sub (sine (by norm_num [cap] : 0≤cap)))).sub
    ((((Interval.point 1).add (cosine (by norm_num [cap] : 0≤cap))).add
      (sine (by norm_num [cap] : 0≤cap))).mul (Interval.point (1/2)))
  have hh : Z.hi< -(17/10000:ℝ) := by dsimp [Z,cap]; mixed_fixed
  have hz : feasibility cap≤Z.hi := by simpa [feasibility,width,div_eq_mul_inv] using Z.mem.2
  exact hz.trans_lt hh

theorem forced_cap {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : width x≤a-A*Real.sin x-B*Real.cos x) : x<cap := by
  have htarg := target_support ht hx
  have hsrc := (outer_bounds hs).2.1
  have hf : 0≤feasibility x := by dsimp [feasibility]; linarith
  by_contra! hcap
  have hh := feasibility_decreases (by norm_num [cap] : cap∈Icc 0 (7/10)) hx hcap
  linarith [cap_infeasible]

theorem cap_trig : (6091/6250:ℝ)<Real.cos cap ∧ Real.sin cap<22409/100000 := by
  have hc : (6091/6250:ℝ)<(ShortWord.MixedQuarter.Reference.cosine
      (by norm_num [cap] : (0:ℝ)≤cap)).lo := by
    dsimp [cap]; mixed_fixed
  have hs : (ShortWord.MixedQuarter.Reference.sine
      (by norm_num [cap] : (0:ℝ)≤cap)).hi<(22409/100000:ℝ) := by
    dsimp [cap]; mixed_fixed
  exact ⟨hc.trans_le (ShortWord.MixedQuarter.Reference.cosine (by norm_num [cap])).mem.1,
    (ShortWord.MixedQuarter.Reference.sine (by norm_num [cap])).mem.2.trans_lt hs⟩

theorem small_angle {x : ℝ} (hx : x∈Icc 0 cap) : x∈Icc 0 (7/10) :=
  ⟨hx.1,hx.2.trans (by norm_num [cap])⟩
theorem small_trig {x : ℝ} (hx : x∈Icc 0 cap) :
    (6091/6250:ℝ)<Real.cos x ∧ 0≤Real.sin x ∧ Real.sin x<22409/100000 := by
  have hc := cos_anti (small_angle hx) (by norm_num [cap] : cap∈Icc 0 (7/10)) hx.2
  have hs := sin_mono (small_angle hx) (by norm_num [cap] : cap∈Icc 0 (7/10)) hx.2
  exact ⟨cap_trig.1.trans_le hc,(positive_trig (small_angle hx)).2.2.1,hs.trans_lt cap_trig.2⟩

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Negative
end
end
end
