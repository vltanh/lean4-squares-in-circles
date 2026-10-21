module

public import SquaresInCircles.Eight.TableFree.CommonQuarterState
public import SquaresInCircles.Eight.TableFree.CircularNorm
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# The entire jump-two outer/outer support envelope

A fixed multiplier `3/4` gives a positive sinusoidal norm. Its exact
curvature identity makes the envelope strictly concave on the whole
remaining angle interval. Only the two geometric endpoint values require
Taylor substitutions. No angular mesh or supplied envelope premise enters.
Uncompiled source draft.
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
  have hcl := cos_lower_two ht0
  have hch := cos_upper_four (show (0:ℝ)≤27/50 by norm_num)
  have ht2 := pow_le_pow_left₀ ht0 ht.2 2
  have heS : Real.sin φ=Real.sin t := by simp [t,Real.sin_sub]
  have heC : -Real.cos φ=Real.cos t := by simp [t,Real.cos_sub]
  rw [heS,heC]
  norm_num at hsl hsh hch
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

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
  simpa [N,CircularNorm.energy,mass,cosCoeff,sinCoeff] using h

theorem N_lt_one {φ : ℝ} (hφ : φ∈Icc (Real.pi-7/10) (13/5)) : N φ<1 := by
  have ht := short_trig hφ
  have hc := Real.neg_one_le_cos φ
  have hs := N_sq φ
  nlinarith [N_pos φ]

theorem envelope_hasDerivAt (φ : ℝ) : HasDerivAt envelope (envelopeD φ) φ := by
  have hn := CircularNorm.norm_hasDerivAt (energy_pos φ)
  convert ((((hasDerivAt_id φ).add_const (219/200)).sub_const
    ((183/100)*outerDiagonal)).sub ((Real.hasDerivAt_cos φ).const_mul (3/4))).sub
      (hn.const_mul radius) using 1 <;> dsimp [envelope,envelopeD,N] <;> ring

theorem envelopeD_hasDerivAt (φ : ℝ) : HasDerivAt envelopeD (envelopeDD φ) φ := by
  have hn := CircularNorm.d1_hasDerivAt (energy_pos φ)
  convert (((Real.hasDerivAt_sin φ).const_mul (3/4)).const_add 1).sub
    (hn.const_mul radius) using 1 <;> dsimp [envelopeD,envelopeDD] <;> ring

/-- The norm curvature identity gives the uniform reserve `F''<-1/16`. -/
theorem envelopeDD_negative {φ : ℝ} (hφ : φ∈Icc (Real.pi-7/10) (13/5)) :
    envelopeDD φ< -(1/16:ℝ) := by
  have ht := short_trig hφ
  have hN := N_lt_one hφ
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hn := CircularNorm.curvature_lower (energy_pos φ)
    (show cosCoeff^2+sinCoeff^2≤mass^2 by norm_num [mass,cosCoeff,sinCoeff])
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
    neg_one_mul,zero_sub,one_mul,mul_zero,sub_zero]
  refine ⟨?_,?_,?_⟩ <;> linarith

/-- Fixed Taylor bounds at the right endpoint. -/
theorem right_trig :
    515/1000<Real.sin (13/5:ℝ) ∧
      -(857/1000:ℝ)<Real.cos (13/5:ℝ) ∧
      Real.cos (13/5:ℝ)< -(856/1000:ℝ) := by
  have hs := TableFree.HighOrderTaylor.S11_le_sin (show (0:ℝ)≤13/5 by norm_num)
  have hcl := TableFree.HighOrderTaylor.C14_le_cos (show (0:ℝ)≤13/5 by norm_num)
  have hcu := TableFree.HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤13/5 by norm_num)
  norm_num [TableFree.HighOrderTaylor.S11,TableFree.HighOrderTaylor.C14,
    TableFree.HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hcl hcu
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
  have hnon : 0≤mixedNorm := mul_nonneg hR hn
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
  convert (((((hasDerivAt_id φ).add_const (163/100)).sub_const
    (coreLabel CoreAngleEndpoint.diagonal CoreAngleEndpoint.diagonal)).sub_const
      mixedNorm).add ((Real.hasDerivAt_cos φ).const_mul
        (CoreAngleEndpoint.diagonal-1/2))).add
          ((Real.hasDerivAt_sin φ).const_mul (CoreAngleEndpoint.diagonal+1/2))
      using 1 <;> dsimp [mixedEnvelope] <;> ring

theorem mixedEnvelope_monotone :
    MonotoneOn mixedEnvelope (Icc (Real.pi-7/10) (13/5)) := by
  apply monoOn_of_hasDeriv_nonneg (by fun_prop)
    (fun φ _ => mixedEnvelope_hasDerivAt φ)
  intro φ hφ
  have ht := short_trig (Ioo_subset_Icc_self hφ)
  have hd := CoreAngleEndpoint.diagonal_bounds
  have h₁ := mul_le_mul_of_nonneg_left ht.2.1.le
    (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith [hd.1])
  have h₂ := mul_le_mul_of_nonneg_left ht.2.2.2.le
    (show 0≤CoreAngleEndpoint.diagonal+1/2 by linarith [hd.1])
  nlinarith

theorem mixedEnvelope_left : (4759/5000:ℝ)<mixedEnvelope (Real.pi-7/10) := by
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
    (4759/5000:ℝ)<mixedEnvelope φ :=
  mixedEnvelope_left.trans_le
    (mixedEnvelope_monotone ⟨le_rfl,hφ.1.trans hφ.2⟩ hφ hφ.1)

end SquaresInCircles.Eight.CommonQuarter.JumpTwo
