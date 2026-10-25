module

public import SquaresInCircles.Eight.Words.Short.Outer.One.RoleFourNorm
public import SquaresInCircles.Eight.Words.Short.Outer.One.Unit

/-!
# Eight squares: all role-four positive-sign original quarter owners

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
