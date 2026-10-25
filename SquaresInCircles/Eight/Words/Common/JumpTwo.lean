module

public import SquaresInCircles.Eight.Arithmetic.HighOrderTaylor
public import SquaresInCircles.Eight.Owners.CircularNorm
public import SquaresInCircles.Eight.Words.Common.QuarterState

/-!
# Eight squares: complete common-label bound for a quarter increment of two

Label ranges dispose of all but the short opposite-sign regime. The
secondary owner then forces a small source coordinate. The primary owner
is treated on each actual core/outer pair by a circle support or a direct
coordinate inequality. Reflection and reversal cover the other two owners
without changing the cost or choosing a preferred separator.

Every state, weak contact, frame error and radial join is included.
-/

section
/-!
## The entire jump-two outer/outer support envelope

A fixed multiplier `3/4` gives a positive sinusoidal norm. Its exact
curvature identity makes the envelope strictly concave on the whole
remaining angle interval. Only the two geometric endpoint values require
Taylor substitutions. No angular mesh or supplied envelope premise enters.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter.JumpTwo

open Arithmetic

def mass : ℝ := (13/200)^2+(203/200)^2+(3/4)^2
def cosCoeff : ℝ := -2*(3/4)*(13/200)
def sinCoeff : ℝ := -2*(3/4)*(203/200)
def N (φ : ℝ) : ℝ := CircularNorm.norm mass cosCoeff sinCoeff φ

def envelope (φ : ℝ) : ℝ :=
  φ+219/200-(183/100)*outerDiagonal-(3/4)*Real.cos φ-radius*N φ

def envelopeD (φ : ℝ) : ℝ :=
  1+(3/4)*Real.sin φ-radius*CircularNorm.d1 mass cosCoeff sinCoeff φ

def envelopeDD (φ : ℝ) : ℝ :=
  (3/4)*Real.cos φ-radius*CircularNorm.d2 mass cosCoeff sinCoeff φ

/-- The entire remaining angle domain stays in one closed second-quadrant
regime. The estimates are deliberately uniform. -/
theorem short_trig {φ : ℝ} (hφ : φ∈Icc (Real.pi-7/10) (13/5)) :
    1/2≤Real.sin φ ∧ Real.sin φ<13/20 ∧
      3/4< -Real.cos φ ∧ -Real.cos φ<7/8 := by
  let t : ℝ := Real.pi-φ
  have ht : 27/50≤t ∧ t≤7/10 := by
    dsimp [t]
    constructor <;> linarith [hφ.1,hφ.2,Real.pi_gt_d2]
  have ht0 : 0≤t := by linarith [ht.1]
  have hst : Real.sin (27/50:ℝ)≤Real.sin t :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos])
      (by linarith [ht.2,Real.pi_gt_three]) ht.1
  have hsu : Real.sin t≤Real.sin (7/10:ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [ht0,Real.pi_pos])
      (by linarith [Real.pi_gt_three]) ht.2
  have hcu : Real.cos t≤Real.cos (27/50:ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num)
      (by linarith [ht.2,Real.pi_gt_three]) ht.1
  have hsl := Real.sin_ge_sub_cube (show (0:ℝ)≤27/50 by norm_num)
  have hsh := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hcl := Real.one_sub_sq_div_two_le_cos (x := t)
  have hch := cos_upper_four (show (0:ℝ)≤27/50 by norm_num)
  have ht2 := pow_le_pow_left₀ ht0 ht.2 2
  have heS : Real.sin φ=Real.sin t := by simp [t,Real.sin_sub]
  have heC : -Real.cos φ=Real.cos t := by simp [t,Real.cos_sub]
  rw [heS,heC]
  norm_num at hsl hsh hch
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem short_width {φ : ℝ} (hφ : φ∈Icc (Real.pi-7/10) (13/5)) :
    pairWidth φ=(1-Real.cos φ+Real.sin φ)/2 := by
  have h := short_trig hφ
  simp [pairWidth,abs_of_pos (show 0<Real.sin φ by linarith [h.1]),
    abs_of_neg (show Real.cos φ<0 by linarith [h.2.2.1])]
  ring

theorem energy_pos (φ : ℝ) : 0<CircularNorm.energy mass cosCoeff sinCoeff φ := by
  have hsin := Real.sin_le_one φ
  have hbase : 0<(203/200:ℝ)-(3/4)*Real.sin φ := by linarith
  have hsq := sq_pos_of_pos hbase
  have hid : CircularNorm.energy mass cosCoeff sinCoeff φ=
      ((13/200)-(3/4)*Real.cos φ)^2+((203/200)-(3/4)*Real.sin φ)^2 := by
    dsimp [CircularNorm.energy,mass,cosCoeff,sinCoeff]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  rw [hid]
  nlinarith [sq_nonneg ((13/200:ℝ)-(3/4)*Real.cos φ)]

theorem N_pos (φ : ℝ) : 0<N φ := CircularNorm.norm_pos (energy_pos φ)

theorem N_sq (φ : ℝ) :
    (N φ)^2=(13/200:ℝ)^2+(203/200)^2+(3/4)^2-
      2*(3/4)*((13/200)*Real.cos φ+(203/200)*Real.sin φ) := by
  have h := CircularNorm.norm_sq (energy_pos φ).le
  rw [N,h]
  simp only [CircularNorm.energy,mass,cosCoeff,sinCoeff]
  ring

theorem N_lt_one {φ : ℝ} (hφ : φ∈Icc (Real.pi-7/10) (13/5)) : N φ<1 := by
  have ht := short_trig hφ
  have hc := Real.neg_one_le_cos φ
  have hs := N_sq φ
  nlinarith [N_pos φ]

theorem envelope_hasDerivAt (φ : ℝ) : HasDerivAt envelope (envelopeD φ) φ := by
  have hn := CircularNorm.norm_hasDerivAt (energy_pos φ)
  have h := ((((hasDerivAt_id φ).add_const (219/200)).sub_const
    ((183/100)*outerDiagonal)).sub ((Real.hasDerivAt_cos φ).const_mul (3/4))).sub
      (hn.const_mul radius)
  convert h using 1
  · funext y
    simp only [envelope,N,Pi.sub_apply,id]
  · simp only [envelopeD]
    ring

theorem envelopeD_hasDerivAt (φ : ℝ) : HasDerivAt envelopeD (envelopeDD φ) φ := by
  have hn := CircularNorm.d1_hasDerivAt (energy_pos φ)
  have h := (((Real.hasDerivAt_sin φ).const_mul (3/4)).const_add 1).sub
    (hn.const_mul radius)
  convert h using 1
  · funext y
    simp only [envelopeD,Pi.sub_apply]
  · simp only [envelopeDD]

/-- The norm curvature identity gives the uniform reserve `F''<-1/16`. -/
theorem envelopeDD_negative {φ : ℝ} (hφ : φ∈Icc (Real.pi-7/10) (13/5)) :
    envelopeDD φ< -(1/16:ℝ) := by
  have ht := short_trig hφ
  have hN := N_lt_one hφ
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hn := CircularNorm.curvature_lower (energy_pos φ)
    (show cosCoeff^2+sinCoeff^2≤ mass^2 by norm_num [mass,cosCoeff,sinCoeff])
  have hm := mul_le_mul_of_nonneg_left hn hR.le
  have hRN := mul_lt_mul_of_pos_left hN hR
  dsimp only [envelopeDD]
  change -(N φ)/4≤CircularNorm.d2 mass cosCoeff sinCoeff φ at hn
  change radius*(-(N φ)/4)≤radius*CircularNorm.d2 mass cosCoeff sinCoeff φ at hm
  nlinarith [radius_bounds.2]

theorem envelope_concave :
    ConcaveOn ℝ (Icc (Real.pi-7/10) (13/5)) envelope := by
  apply concave_of_deriv2
    (fun φ _ => envelope_hasDerivAt φ)
    (fun φ _ => envelopeD_hasDerivAt φ)
  intro φ hφ
  exact (envelopeDD_negative hφ).le.trans (by norm_num)

/-- Fixed Taylor bounds at the left endpoint. -/
theorem left_trig :
    644/1000<Real.sin (Real.pi-7/10) ∧
      -(765/1000:ℝ)<Real.cos (Real.pi-7/10) ∧
      Real.cos (Real.pi-7/10)< -(764/1000:ℝ) := by
  have hs := sin_lower_seven (show (0:ℝ)≤7/10 by norm_num)
  have hcl := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hcu := cos_le_cos8 (show (0:ℝ)≤7/10 by norm_num)
  norm_num [cos8] at hs hcl hcu
  simp only [Real.sin_sub,Real.cos_sub,Real.sin_pi,Real.cos_pi,zero_mul,
    neg_one_mul,zero_sub]
  refine ⟨?_,?_,?_⟩ <;> linarith

/-- Fixed Taylor bounds at the right endpoint. -/
theorem right_trig :
    515/1000<Real.sin (13/5:ℝ) ∧
      -(857/1000:ℝ)<Real.cos (13/5:ℝ) ∧
      Real.cos (13/5:ℝ)< -(856/1000:ℝ) := by
  have hs := Eight.HighOrderTaylor.S11_le_sin (show (0:ℝ)≤13/5 by norm_num)
  have hcl := Eight.HighOrderTaylor.C14_le_cos (show (0:ℝ)≤13/5 by norm_num)
  have hcu := Eight.HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤13/5 by norm_num)
  norm_num [Eight.HighOrderTaylor.S11,Eight.HighOrderTaylor.C14,
    Eight.HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hcl hcu
  exact ⟨by linarith,by linarith,by linarith⟩

theorem left_norm : N (Real.pi-7/10)<832/1000 := by
  have h := N_sq (Real.pi-7/10)
  have ht := left_trig
  nlinarith [N_pos (Real.pi-7/10)]

theorem right_norm : N (13/5:ℝ)<947/1000 := by
  have h := N_sq (13/5:ℝ)
  have ht := right_trig
  nlinarith [N_pos (13/5:ℝ)]

theorem envelope_left : (203993/250000:ℝ)<envelope (Real.pi-7/10) := by
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hRN := mul_lt_mul_of_pos_left left_norm hR
  have hcap := mul_lt_mul_of_pos_right radius_bounds.2
    (show (0:ℝ)<832/1000 by norm_num)
  have hc := left_trig.2.2
  dsimp [envelope]
  linarith [outer_endpoint_bounds.2.2.2,pi_hand_enclosure.1]

theorem envelope_right : (815887/1000000:ℝ)<envelope (13/5:ℝ) := by
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hRN := mul_lt_mul_of_pos_left right_norm hR
  have hcap := mul_lt_mul_of_pos_right radius_bounds.2
    (show (0:ℝ)<947/1000 by norm_num)
  have hc := right_trig.2.2
  dsimp [envelope]
  linarith [outer_endpoint_bounds.2.2.2]

/-- Complete closed-interval scalar result, with no additional analytic
or Taylor-bound hypotheses on the caller. -/
theorem envelope_gt {φ : ℝ} (hφ : φ∈Icc (Real.pi-7/10) (13/5)) :
    (815887/1000000:ℝ)<envelope φ := by
  have hlo : (815887/1000000:ℝ)<envelope (Real.pi-7/10) := by
    linarith [envelope_left]
  have hhi := envelope_right
  have hl : Real.pi-7/10≤(13/5:ℝ) := by linarith [pi_lt_22_over_7]
  exact (lt_min hlo hhi).trans_le
    (envelope_concave.min_le_of_mem_Icc ⟨le_rfl,hl⟩ ⟨hl,le_rfl⟩ hφ)

/-- The outer/core primary support has only a fixed circle norm. -/
def mixedNorm : ℝ := radius*Real.sqrt ((213/200:ℝ)^2+(203/200)^2)

def mixedEnvelope (φ : ℝ) : ℝ :=
  φ+163/100-coreLabel CoreAngleEndpoint.diagonal CoreAngleEndpoint.diagonal-
    mixedNorm+(CoreAngleEndpoint.diagonal-1/2)*Real.cos φ+
      (CoreAngleEndpoint.diagonal+1/2)*Real.sin φ

theorem mixedNorm_lt : mixedNorm<73/25 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤(213/200)^2+(203/200)^2 by norm_num)
  have hn := Real.sqrt_nonneg ((213/200:ℝ)^2+(203/200)^2)
  have hR : 0≤radius := by linarith [radius_bounds.1]
  have hsq : mixedNorm^2=Q0*((213/200:ℝ)^2+(203/200)^2) := by
    rw [mixedNorm,mul_pow,radius_sq,hs]
  norm_num [Q0] at hsq
  have hnon : 0≤ mixedNorm := mul_nonneg hR hn
  nlinarith

theorem diagonal_core : CorePairGeometry.CoreState
    CoreAngleEndpoint.diagonal CoreAngleEndpoint.diagonal := by
  apply Or.inr
  exact ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl,
    by nlinarith [CoreAngleEndpoint.diagonal_sq]⟩

theorem mixedEnvelope_hasDerivAt (φ : ℝ) :
    HasDerivAt mixedEnvelope
      (1-(CoreAngleEndpoint.diagonal-1/2)*Real.sin φ+
        (CoreAngleEndpoint.diagonal+1/2)*Real.cos φ) φ := by
  have h := (((((hasDerivAt_id φ).add_const (163/100)).sub_const
    (coreLabel CoreAngleEndpoint.diagonal CoreAngleEndpoint.diagonal)).sub_const
    mixedNorm).add ((Real.hasDerivAt_cos φ).const_mul
    (CoreAngleEndpoint.diagonal-1/2))).add
    ((Real.hasDerivAt_sin φ).const_mul (CoreAngleEndpoint.diagonal+1/2))
  convert h using 1
  · funext y
    simp only [mixedEnvelope,Pi.add_apply,id]
  · ring

theorem mixedEnvelope_monotone :
    MonotoneOn mixedEnvelope (Icc (Real.pi-7/10) (13/5)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun φ _ => (mixedEnvelope_hasDerivAt φ).continuousAt.continuousWithinAt)
    (fun φ _ => mixedEnvelope_hasDerivAt φ)
  intro φ hφ
  have ht := short_trig (Ioo_subset_Icc_self hφ)
  have hd := CoreAngleEndpoint.diagonal_bounds
  have h₁ := mul_le_mul_of_nonneg_left ht.2.1.le
    (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith [hd.1])
  have h₂ := mul_le_mul_of_nonneg_left ht.2.2.2.le
    (show 0≤CoreAngleEndpoint.diagonal+1/2 by linarith [hd.1])
  nlinarith

theorem mixedEnvelope_left : (4759/5000:ℝ)< mixedEnvelope (Real.pi-7/10) := by
  have ht := left_trig
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hlabel := (core_label_bounds diagonal_core).2
  have hcos := mul_lt_mul_of_pos_left ht.2.1
    (show 0<CoreAngleEndpoint.diagonal-1/2 by linarith [hd.1])
  have hsin := mul_lt_mul_of_pos_left ht.1
    (show 0<CoreAngleEndpoint.diagonal+1/2 by linarith [hd.1])
  dsimp [mixedEnvelope]
  nlinarith [mixedNorm_lt,pi_hand_enclosure.1]

theorem mixedEnvelope_gt {φ : ℝ} (hφ : φ∈Icc (Real.pi-7/10) (13/5)) :
    (4759/5000:ℝ)< mixedEnvelope φ :=
  mixedEnvelope_left.trans_le
    (mixedEnvelope_monotone ⟨le_rfl,hφ.1.trans hφ.2⟩ hφ hφ.1)

end SquaresInCircles.Eight.CommonQuarter.JumpTwo
end
end
end

section
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
end
end
end
