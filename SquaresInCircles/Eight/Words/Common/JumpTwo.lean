module

public import SquaresInCircles.Eight.Words.Common.JumpTwoScalar

/-!
# Eight squares: complete common-label bound for a quarter increment of two

Label ranges dispose of all but the short opposite-sign regime. The
secondary owner then forces a small source coordinate. The primary owner
is treated on each actual core/outer pair by a circle support or a direct
coordinate inequality. Reflection and reversal cover the other two owners
without changing the cost or choosing a preferred separator.

Every state, weak contact, frame error and radial join is included.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open WordProblems

def cost (source target : RadialKind) (σ τ : Bool)
    (a b A B φ : ℝ) : ℝ :=
  φ+(sign σ:ℝ)*label source a b-(sign τ:ℝ)*label target A B

lemma cost_reverse (source target : RadialKind) (σ τ : Bool)
    (a b A B φ : ℝ) :
    cost target source (!τ) (!σ) A B a b φ=cost source target σ τ a b A B φ := by
  cases σ <;> cases τ <;> simp [cost,sign] <;> ring

lemma margin_reverse (j : Fin 4) (σ τ : Bool) (a b A B φ : ℝ) :
    forwardMargin (![2,3,0,1] j) A B a b (sign (!τ)) (sign (!σ)) φ=
      forwardMargin j a b A B (sign σ) (sign τ) φ := by
  fin_cases j <;> cases σ <;> cases τ <;> simp [forwardMargin,sign] <;> ring

lemma width_ge_one (φ : ℝ) : 1≤pairWidth φ := by
  have h := one_le_abs_cos_add_abs_sin φ
  dsimp [pairWidth]
  linarith

lemma jump_two_nonopposite {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hnot : ¬(σ=false ∧ τ=true)) (hφ : Real.pi-7/10≤φ) :
    (163/200:ℝ)<cost source target σ τ a b A B φ := by
  have hl := state_label_bounds hs
  have hr := state_label_bounds ht
  have hpi := Real.pi_gt_d2
  cases σ <;> cases τ
  · norm_num [cost,sign]
    linarith
  · exact absurd ⟨rfl,rfl⟩ hnot
  · norm_num [cost,sign]
    linarith
  · norm_num [cost,sign]
    linarith

lemma jump_two_large {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (hφ : (13/5:ℝ)≤φ) :
    (163/200:ℝ)<φ-label source a b-label target A B := by
  have hl := state_label_bounds hs
  have hr := state_label_bounds ht
  linarith

lemma small_source_label {source : RadialKind} {a b : ℝ}
    (hs : State source a b) (hb : b<7/100) : label source a b<41/500 := by
  by_cases hk : source=.outer
  · have h := state_bounds hs
    simp only [label,ite_eq_left hk,outerLabel]
    linarith [h.2.1]
  · have hc : CorePairGeometry.CoreState a b := by simpa [State,hk] using hs
    have he := (core_small_side hc (by linarith)).2
    simp only [label,ite_eq_right hk]
    rw [he]
    linarith

/-- A core target cannot support a source-secondary jump-two contact in
this sign regime, by its original center radius. -/
lemma jump_two_secondary_core_false {a b A B φ : ℝ}
    (hb : 0≤b) (ht : CorePairGeometry.CoreState A B)
    (hm : 0≤forwardMargin 0 a b A B (-1) 1 φ) : False := by
  have hcore := CorePairGeometry.core_radius_sq ht
  have hw := width_ge_one φ
  have hproj : 1≤A*Real.sin φ-B*Real.cos φ := by
    norm_num [forwardMargin] at hm
    linarith
  have hid : (A*Real.sin φ-B*Real.cos φ)^2+
      (A*Real.cos φ+B*Real.sin φ)^2=A^2+B^2 := by
    linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
  nlinarith [sq_nonneg (A*Real.cos φ+B*Real.sin φ),
    sq_nonneg (A*Real.sin φ-B*Real.cos φ-1)]

/-- An outer target forces the source coordinate below `.07`, uniformly
on the entire short jump-two interval. -/
lemma jump_two_secondary_small {a b A B φ : ℝ}
    (ht : OuterState A B) (hφ : φ∈Icc (Real.pi-7/10) (13/5))
    (hm : 0≤forwardMargin 0 a b A B (-1) 1 φ) : b<7/100 := by
  have htφ := JumpTwo.short_trig hφ
  have hs0 : 0≤Real.sin φ := by linarith [htφ.1]
  have hd0 : 0≤ -Real.cos φ := by linarith [htφ.2.2.1]
  have hsd : Real.sin φ≤ -Real.cos φ := by linarith [htφ.2.1,htφ.2.2.1]
  have hu := outer_diagonal_upper (X := Real.sin φ) (Y := -Real.cos φ) ht hs0 hsd
  have hsum : Real.sin φ-Real.cos φ<(57/40:ℝ) := by
    have hsq := sq_nonneg (Real.sin φ+Real.cos φ)
    have hid := Real.sin_sq_add_cos_sq φ
    nlinarith
  have hcap := mul_lt_mul_of_pos_right outer_endpoint_bounds.2.2.2
    (show 0<Real.sin φ-Real.cos φ by linarith [htφ.1,htφ.2.2.1])
  have hw := JumpTwo.short_width hφ
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  nlinarith

lemma jump_two_secondary_opposite {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B)
    (hφ : φ∈Icc (Real.pi-7/10) (13/5))
    (hm : 0≤forwardMargin 0 a b A B (-1) 1 φ) :
    (163/200:ℝ)<φ-label source a b-label target A B := by
  by_cases hk : target=.outer
  · have hto : OuterState A B := by simpa [State,hk] using ht
    have hb := jump_two_secondary_small hto hφ hm
    have hls := small_source_label hs hb
    have hlt := (state_label_bounds ht).2
    linarith [hφ.1,Arithmetic.pi_hand_enclosure.1]
  · have htc : CorePairGeometry.CoreState A B := by simpa [State,hk] using ht
    exact (jump_two_secondary_core_false (state_bounds hs).2.2.1 htc hm).elim

lemma jump_two_primary_core_core_false {a b A B φ : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : CorePairGeometry.CoreState A B)
    (hφ : φ∈Icc (Real.pi-7/10) (13/5))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 φ) : False := by
  have hsa := CoreAngleEndpoint.state_bounds hs
  have hta := CoreAngleEndpoint.state_bounds ht
  have hx := JumpTwo.short_trig hφ
  have hw := JumpTwo.short_width hφ
  have hAc := mul_le_mul_of_nonneg_right hta.2.1
    (show 0≤ -Real.cos φ by linarith [hx.2.2.1])
  have hBs := mul_nonneg hta.2.2.1 (show 0≤Real.sin φ by linarith [hx.1])
  have hc := Real.neg_one_le_cos φ
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  nlinarith [hsa.2.1]

lemma jump_two_primary_core_outer_target_cut {a b A B φ : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : OuterState A B)
    (hφ : φ∈Icc (Real.pi-7/10) (13/5))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 φ) :
    B<39/50 ∧ outerLabel A B<96/125 := by
  have hsa := CoreAngleEndpoint.state_bounds hs
  have hta := outer_bounds ht
  have hx := JumpTwo.short_trig hφ
  have hw := JumpTwo.short_width hφ
  have hsum : A+B<9/5 := by linarith [hta.2.2.2.2,outer_endpoint_bounds.2.2.2]
  have hdpos : 0< -Real.cos φ := by linarith [hx.2.2.1]
  have hAsum := mul_lt_mul_of_pos_right hsum hdpos
  have hB0 : 0≤B := ht.1
  have hcoef : (5/4:ℝ)<Real.sin φ-Real.cos φ := by
    linarith [hx.1,hx.2.2.1]
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  have hprod : B*(Real.sin φ-Real.cos φ)<233/240 := by
    nlinarith [hsa.2.1,hx.2.2.2,hx.1]
  have hB : B<39/50 := by
    have hl := mul_le_mul_of_nonneg_left hcoef.le hB0
    nlinarith
  refine ⟨hB,?_⟩
  dsimp [outerLabel]
  linarith

lemma jump_two_primary_core_outer {a b A B φ : ℝ}
    (hs : CorePairGeometry.CoreState a b) (ht : OuterState A B)
    (hφ : φ∈Icc (Real.pi-7/10) (13/5))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 φ) :
    (163/200:ℝ)<φ-coreLabel a b-outerLabel A B := by
  have hlt := (jump_two_primary_core_outer_target_cut hs ht hφ hm).2
  have hls := (core_label_bounds hs).2
  linarith [hφ.1,Arithmetic.pi_hand_enclosure.1]

/-- The original outer circle and the complete core diagonal support give
an actual lower bound by the monotone mixed envelope. -/
lemma jump_two_primary_outer_core_support {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B)
    (hφ : φ∈Icc (Real.pi-7/10) (13/5))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 φ) :
    JumpTwo.mixedEnvelope φ≤φ-outerLabel a b-coreLabel A B := by
  have hx := JumpTwo.short_trig hφ
  have hw := JumpTwo.short_width hφ
  have hsource := outer_circle_lower (X := -(213/200:ℝ)) (Y := -(203/200:ℝ)) hs
  have htarget := core_diagonal_lower (X := (73/10)+Real.cos φ)
    (Y := Real.sin φ-(291/250)) ht
    (by linarith [Real.neg_one_le_cos φ]) (by linarith [hx.2.1])
  have e : (-(213/200:ℝ))^2+(-(203/200:ℝ))^2=(213/200:ℝ)^2+(203/200)^2 := by norm_num
  rw [e] at hsource
  norm_num [forwardMargin] at hm
  rw [hw] at hm
  dsimp only [JumpTwo.mixedEnvelope,JumpTwo.mixedNorm,outerLabel,coreLabel]
  linarith

lemma jump_two_primary_outer_core {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CorePairGeometry.CoreState A B)
    (hφ : φ∈Icc (Real.pi-7/10) (13/5))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 φ) :
    (163/200:ℝ)<φ-outerLabel a b-coreLabel A B := by
  have h := jump_two_primary_outer_core_support hs ht hφ hm
  have hg := JumpTwo.mixedEnvelope_gt hφ
  linarith

/-- Fixed `3/4` separation multiplier, diagonal source support, and a
full-circle target support. The target need not lie at its support minimizer. -/
lemma jump_two_primary_outer_outer_support {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : φ∈Icc (Real.pi-7/10) (13/5))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 φ) :
    JumpTwo.envelope φ≤φ-outerLabel a b-outerLabel A B := by
  have hw := JumpTwo.short_width hφ
  have hsource := outer_diagonal_upper (X := (163/200:ℝ))
    (Y := (203/200:ℝ)) hs (by norm_num) (by norm_num)
  have htarget := outer_circle_lower (X := (3/4)*Real.cos φ-(13/200))
    (Y := (3/4)*Real.sin φ-(203/200)) ht
  have hrad : ((3/4)*Real.cos φ-(13/200))^2+
      ((3/4)*Real.sin φ-(203/200))^2=
        CircularNorm.energy JumpTwo.mass JumpTwo.cosCoeff JumpTwo.sinCoeff φ := by
    dsimp [CircularNorm.energy,JumpTwo.mass,JumpTwo.cosCoeff,JumpTwo.sinCoeff]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  rw [hrad] at htarget
  change -(((3/4)*Real.cos φ-(13/200))+((3/4)*Real.sin φ-(203/200)))/2-
    radius*JumpTwo.N φ≤((3/4)*Real.cos φ-(13/200))*A+
      ((3/4)*Real.sin φ-(203/200))*B at htarget
  have hmul := mul_nonneg (show (0:ℝ)≤3/4 by norm_num) hm
  norm_num [forwardMargin] at hmul
  rw [hw] at hmul
  dsimp [JumpTwo.envelope,outerLabel]
  nlinarith

lemma jump_two_primary_outer_outer {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : φ∈Icc (Real.pi-7/10) (13/5))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 φ) :
    (163/200:ℝ)<φ-outerLabel a b-outerLabel A B := by
  have h := jump_two_primary_outer_outer_support hs ht hφ hm
  have hg := JumpTwo.envelope_gt hφ
  linarith

lemma jump_two_primary_opposite {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B)
    (hφ : φ∈Icc (Real.pi-7/10) (13/5))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 φ) :
    (163/200:ℝ)<φ-label source a b-label target A B := by
  by_cases hso : source=.outer <;> by_cases hto : target=.outer
  · have hs' : OuterState a b := by simpa [State,hso] using hs
    have ht' : OuterState A B := by simpa [State,hto] using ht
    simpa [label,hso,hto] using jump_two_primary_outer_outer hs' ht' hφ hm
  · have hs' : OuterState a b := by simpa [State,hso] using hs
    have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
    simpa [label,hso,hto] using jump_two_primary_outer_core hs' ht' hφ hm
  · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
    have ht' : OuterState A B := by simpa [State,hto] using ht
    simpa [label,hso,hto] using jump_two_primary_core_outer hs' ht' hφ hm
  · have hs' : CorePairGeometry.CoreState a b := by simpa [State,hso] using hs
    have ht' : CorePairGeometry.CoreState A B := by simpa [State,hto] using ht
    exact (jump_two_primary_core_core_false hs' ht' hφ hm).elim

lemma jump_two_secondary {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hφ : Real.pi-7/10≤φ ∧ φ≤Real.pi+7/10)
    (hm : 0≤forwardMargin 0 a b A B (sign σ) (sign τ) φ) :
    (163/200:ℝ)<cost source target σ τ a b A B φ := by
  by_cases ho : σ=false ∧ τ=true
  · rcases ho with ⟨rfl,rfl⟩
    simp only [cost,sign,Bool.false_eq_true,ite_false,ite_true,Rat.cast_neg,
      Rat.cast_one,neg_one_mul,one_mul] at hm ⊢
    by_cases hlarge : (13/5:ℝ)≤φ
    · simpa [sub_eq_add_neg] using jump_two_large hs ht hlarge
    · simpa [sub_eq_add_neg] using jump_two_secondary_opposite hs ht
        ⟨hφ.1,(le_of_not_ge hlarge)⟩ hm
  · exact jump_two_nonopposite hs ht σ τ ho hφ.1

lemma jump_two_primary {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hφ : Real.pi-7/10≤φ ∧ φ≤Real.pi+7/10)
    (hm : 0≤forwardMargin 3 a b A B (sign σ) (sign τ) φ) :
    (163/200:ℝ)<cost source target σ τ a b A B φ := by
  by_cases ho : σ=false ∧ τ=true
  · rcases ho with ⟨rfl,rfl⟩
    simp only [cost,sign,Bool.false_eq_true,ite_false,ite_true,Rat.cast_neg,
      Rat.cast_one,neg_one_mul,one_mul] at hm ⊢
    by_cases hlarge : (13/5:ℝ)≤φ
    · simpa [sub_eq_add_neg] using jump_two_large hs ht hlarge
    · simpa [sub_eq_add_neg] using jump_two_primary_opposite hs ht
        ⟨hφ.1,(le_of_not_ge hlarge)⟩ hm
  · exact jump_two_nonopposite hs ht σ τ ho hφ.1

/-- Full common jump-two inequality, for each original feasible axis. -/
theorem jump_two_cost {source target : RadialKind} {a b A B φ : ℝ}
    (hs : State source a b) (ht : State target A B) (σ τ : Bool)
    (hφ : |φ-Real.pi|≤7/10) (j : Fin 4)
    (hm : 0≤forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (163/200:ℝ)<cost source target σ τ a b A B φ := by
  have hp : Real.pi-7/10≤φ ∧ φ≤Real.pi+7/10 := by
    constructor <;> linarith [(abs_le.mp hφ).1,(abs_le.mp hφ).2]
  fin_cases j
  · exact jump_two_secondary hs ht σ τ hp hm
  · have hr : 0≤forwardMargin 3 A B a b (sign (!τ)) (sign (!σ)) φ := by
      simpa using (margin_reverse 1 σ τ a b A B φ).symm ▸ hm
    simpa [cost_reverse] using jump_two_primary ht hs (!τ) (!σ) hp hr
  · have hr : 0≤forwardMargin 0 A B a b (sign (!τ)) (sign (!σ)) φ := by
      simpa using (margin_reverse 2 σ τ a b A B φ).symm ▸ hm
    simpa [cost_reverse] using jump_two_secondary ht hs (!τ) (!σ) hp hr
  · exact jump_two_primary hs ht σ τ hp hm

/-- The actual physical jump-two edge, using its original radial states,
chosen signed representation, quarter lift, and weak owner witness. -/
theorem actual_jump_two (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=2) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (163/200:ℝ)<QuarterWordGeometry.phaseValue F hgap i+
      QuarterWordGeometry.commonMarker C i-QuarterWordGeometry.commonMarker C (next i) := by
  have hm := QuarterWordGeometry.original_margin C F hgap i j hj
  have hp : |QuarterWordGeometry.phaseValue F hgap i-Real.pi|≤7/10 := by
    simpa [QuarterWordGeometry.phaseValue,hk] using
      (QuarterWordGeometry.difference_small F i).le
  have h := jump_two_cost (actual_state C i) (actual_state C (next i))
    (QuarterWordGeometry.positiveOf C i) (QuarterWordGeometry.positiveOf C (next i)) hp j hm
  simpa [cost,QuarterWordGeometry.commonMarker,commonValue_eq] using h

end SquaresInCircles.Eight.CommonQuarter
