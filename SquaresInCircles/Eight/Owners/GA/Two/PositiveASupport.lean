module

public import SquaresInCircles.Eight.Owners.GA.Sorted.Support

/-!
# Eight squares: the A support in the two-positive-angle argument

The only transition is the one between the tangent-zero and the full-circle branches
(`transition_value`, `transition_derivative`). Both signs of the tangent of A are allowed, and the
support bound uses the circle inequality of A at its radius (`actual_charge`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalGA.TwoPositive.ASupport
open Candidate Secondary PositiveAngularEnvelope

def beta : ℝ := Real.arctan ((1/2)/(axial+1/2))
def alpha : ℝ := 2*beta

def axialCharge (a : ℝ) : ℝ :=
  (Real.cos a-1)/2+(1/2-axial)*Real.sin a

def circleCharge (a : ℝ) : ℝ := Real.sin a-2*R*Real.sin (a/2)

def charge (a : ℝ) : ℝ :=
  if a≤alpha then axialCharge a else circleCharge a

def axialD (a : ℝ) : ℝ :=
  -Real.sin a/2+(1/2-axial)*Real.cos a

def circleD (a : ℝ) : ℝ := Real.cos a-R*Real.cos (a/2)

def axialDD (a : ℝ) : ℝ :=
  -Real.cos a/2+(axial-1/2)*Real.sin a

def circleDD (a : ℝ) : ℝ := -Real.sin a+(R/2)*Real.sin (a/2)

theorem beta_mem : beta∈Ioo 0 (Real.pi/2) := by
  have hb : 0<axial+1/2 := by linarith [axial_bounds.1]
  exact ⟨Real.arctan_pos.mpr (div_pos (by norm_num) hb),
    Real.arctan_lt_pi_div_two _⟩

theorem beta_tangent : (axial+1/2)*Real.sin beta=Real.cos beta/2 := by
  have hc : 0<Real.cos beta := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [beta_mem.1,Real.pi_pos],beta_mem.2⟩
  have hb : 0<axial+1/2 := by linarith [axial_bounds.1]
  have hh : Real.sin beta/Real.cos beta=(1/2)/(axial+1/2) := by
    rw [← Real.tan_eq_sin_div_cos]
    exact Real.tan_arctan _
  have hcross := (div_eq_div_iff hc.ne' hb.ne').mp hh
  nlinarith only [hcross]

theorem beta_frame : R*Real.cos beta=axial+1/2 ∧ R*Real.sin beta=1/2 := by
  have hc : 0<Real.cos beta := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [beta_mem.1,Real.pi_pos],beta_mem.2⟩
  have hR : 0<R := by linarith [radius_bounds.1]
  have hb : 0<axial+1/2 := by linarith [axial_bounds.1]
  have ht := beta_tangent
  have hR2 : R^2=(axial+1/2)^2+1/4 := by rw [radius_sq,← axial_circle]; ring
  have hsq : (R*Real.cos beta)^2=(axial+1/2)^2 := by
    linear_combination (Real.cos beta)^2*hR2-((axial+1/2)*Real.sin beta+Real.cos beta/2)*ht+
      (axial+1/2)^2*Real.sin_sq_add_cos_sq beta
  have hcos : R*Real.cos beta=axial+1/2 :=
    (sq_eq_sq₀ (mul_pos hR hc).le hb.le).mp hsq
  refine ⟨hcos,?_⟩
  have hm := congrArg (fun v : ℝ => R*v) ht
  have hm2 : (axial+1/2)*(R*Real.sin beta)=(axial+1/2)*(1/2) := by
    linear_combination hm+(1/2)*hcos
  exact mul_left_cancel₀ hb.ne' hm2

theorem alpha_bounds : (1/2:ℝ)<alpha ∧ alpha<frameCap := by
  have hb : 0<axial+1/2 := by linarith [axial_bounds.1]
  have hr : (13/50:ℝ)<(1/2)/(axial+1/2) := by
    apply (lt_div_iff₀ hb).mpr
    linarith [axial_bounds.2]
  have hquarter : (1/4:ℝ)∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_gt_three]
  have hc : 0<Real.cos (1/4:ℝ) := Real.cos_pos_of_mem_Ioo hquarter
  have htan : Real.tan (1/4:ℝ)≤8/31 := by
    rw [Real.tan_eq_sin_div_cos,div_le_iff₀ hc]
    have hs := Real.sin_le (show (0:ℝ)≤1/4 by norm_num)
    have hl := Real.one_sub_sq_div_two_le_cos (x:=(1/4:ℝ))
    norm_num at hs hl ⊢
    linarith
  have hbetal : (1/4:ℝ)<beta := by
    by_contra! hh
    have hm := Real.strictMonoOn_tan.monotoneOn
      (show beta∈Ioo (-(Real.pi/2)) (Real.pi/2) from
        ⟨by linarith [beta_mem.1,Real.pi_pos],beta_mem.2⟩) hquarter hh
    rw [show Real.tan beta=(1/2)/(axial+1/2) by
      exact Real.tan_arctan _] at hm
    linarith
  have hbetau : beta≤(1/2)/(axial+1/2) :=
    Real.arctan_le_self (div_nonneg (show (0:ℝ)≤1/2 by norm_num) hb.le)
  have hratio : (1/2)/(axial+1/2)<7/20 := by
    apply (div_lt_iff₀ hb).mpr
    linarith [axial_bounds.1]
  dsimp only [alpha,frameCap]
  exact ⟨by linarith,by linarith⟩

theorem half_trig {a : ℝ} (ha : a∈Icc 0 frameCap) :
    0≤Real.sin (a/2) ∧ 0<Real.cos (a/2) := by
  have hhalf : a/2∈Icc 0 frameCap := by
    constructor <;> dsimp [frameCap] at ha ⊢ <;> linarith [ha.1,ha.2]
  exact ⟨(transport_trig hhalf).2.2.1,
    transport_cos_pos (by rw [abs_of_nonneg hhalf.1]; exact hhalf.2)⟩

theorem double_angle (a : ℝ) :
    Real.sin a=2*Real.sin (a/2)*Real.cos (a/2) ∧
      1-Real.cos a=2*(Real.sin (a/2))^2 := by
  have hs := Real.sin_add (a/2) (a/2)
  have hc := Real.cos_add (a/2) (a/2)
  rw [show a/2+a/2=a by ring] at hs hc
  exact ⟨by nlinarith,by nlinarith [Real.sin_sq_add_cos_sq (a/2)]⟩

theorem axial_force_condition {a : ℝ} (ha : a∈Icc 0 frameCap) (hcut : a≤alpha) :
    (axial+1/2)*(1-Real.cos a)≤Real.sin a/2 := by
  have hb : 0<axial+1/2 := by linarith [axial_bounds.1]
  have hc := (half_trig ha).2
  have hhalf : a/2∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> dsimp [frameCap] at ha <;> linarith [ha.1,ha.2,Real.pi_gt_three]
  have hm := Real.strictMonoOn_tan.monotoneOn hhalf
    (show beta∈Ioo (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [beta_mem.1,Real.pi_pos],beta_mem.2⟩)
    (show a/2≤beta by dsimp [alpha] at hcut; linarith)
  rw [show Real.tan beta=(1/2)/(axial+1/2) by exact Real.tan_arctan _,
    Real.tan_eq_sin_div_cos] at hm
  have hcross := (div_le_div_iff₀ hc hb).mp hm
  have hprod := mul_le_mul_of_nonneg_left hcross
    (show 0≤2*Real.sin (a/2) by linarith [(half_trig ha).1])
  have hh := double_angle a
  rw [hh.2,hh.1]
  linarith only [hprod]

theorem force_norm {a : ℝ} (ha : a∈Icc 0 frameCap) :
    Real.sqrt ((Real.sin a)^2+(1-Real.cos a)^2)=2*Real.sin (a/2) := by
  have hs := (half_trig ha).1
  have hh := double_angle a
  have he : (Real.sin a)^2+(1-Real.cos a)^2=(2*Real.sin (a/2))^2 := by
    nlinarith [Real.sin_sq_add_cos_sq a]
  rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg (by linarith)]

theorem axial_demand {a : ℝ} (ha : a∈Icc 0 frameCap) :
    edgeWidth a-1-axial*Real.sin a=axialCharge a := by
  have ht := transport_trig ha
  have hc := transport_cos_pos (by rw [abs_of_nonneg ha.1]; exact ha.2)
  simp only [edgeWidth,pairWidth,abs_of_pos hc,abs_of_nonneg ht.2.2.1,axialCharge]
  ring

theorem full_demand {a : ℝ} (ha : a∈Icc 0 frameCap) :
    edgeWidth a-1-fullSupport (Real.sin a) (1-Real.cos a)=circleCharge a := by
  have ht := transport_trig ha
  have hc := transport_cos_pos (by rw [abs_of_nonneg ha.1]; exact ha.2)
  simp only [fullSupport,force_norm ha,edgeWidth,pairWidth,
    abs_of_pos hc,abs_of_nonneg ht.2.2.1,circleCharge]
  ring

/-- The A support bound allows either sign of the tangent and either radial kind. -/
theorem actual_charge {q a : ℝ} {P : SignedPoint}
    (_hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap)
    (ha : a∈Icc 0 frameCap) (atG : Bool) :
    charge a≤edgeWidth a-1-
      (P.a*Real.sin a+P.y*(if atG then 1-Real.cos a else Real.cos a-1)) := by
  let A : SignedPoint := ⟨P.a,|P.y|⟩
  have hA : A.Contained q := by simpa [A,SignedPoint.Contained,SignedPoint.circle] using hc
  have ht := transport_trig ha
  have hg : 0≤1-Real.cos a := sub_nonneg.mpr (Real.cos_le_one a)
  have hsign : P.y*(if atG then 1-Real.cos a else Real.cos a-1)≤
      |P.y| *(1-Real.cos a) := by
    cases atG
    · have hh := mul_le_mul_of_nonneg_right (neg_le_abs P.y) hg
      simp only [Bool.false_eq_true,ite_false]
      nlinarith only [hh]
    · simpa only [ite_true] using mul_le_mul_of_nonneg_right (le_abs_self P.y) hg
  by_cases hcut : a≤alpha
  · have hsup := actual_axial_support (P:=A) (by exact abs_nonneg _)
      hA hq ht.2.2.1 (axial_force_condition ha hcut)
    have hid := axial_demand ha
    simp only [charge,ite_eq_left hcut]
    dsimp [A] at hsup
    nlinarith only [hsup,hsign,hid]
  · have hsup := actual_full_support (P:=A) (by exact abs_nonneg _) hA hq
      (f:=Real.sin a) (g:=1-Real.cos a)
    have hid := full_demand ha
    simp only [charge,ite_eq_right hcut]
    dsimp [A] at hsup
    nlinarith only [hsup,hsign,hid]

@[simp] theorem charge_zero : charge 0=0 := by
  have hh : (0:ℝ)≤alpha := by linarith [alpha_bounds.1]
  simp [charge,hh,axialCharge]

theorem charge_low {a : ℝ} (ha : a≤1/6) : charge a=axialCharge a := by
  rw [charge,ite_eq_left (show a≤alpha by linarith [alpha_bounds.1])]

theorem axial_derivative (a : ℝ) : HasDerivAt axialCharge (axialD a) a := by
  have h := (((Real.hasDerivAt_cos a).sub_const 1).div_const 2).fun_add
    ((Real.hasDerivAt_sin a).const_mul (1/2-axial))
  unfold axialCharge
  exact h.congr_deriv (by simp only [axialD])

theorem circle_derivative (a : ℝ) : HasDerivAt circleCharge (circleD a) a := by
  have hh : HasDerivAt (fun x : ℝ => x/2) (1/2) a := (hasDerivAt_id' a).div_const 2
  have h := (Real.hasDerivAt_sin a).fun_sub (hh.sin.const_mul (2*R))
  unfold circleCharge
  exact h.congr_deriv (by simp only [circleD]; ring)

theorem axial_second (a : ℝ) : HasDerivAt axialD (axialDD a) a := by
  have h := ((Real.hasDerivAt_sin a).fun_neg.div_const 2).fun_add
    ((Real.hasDerivAt_cos a).const_mul (1/2-axial))
  unfold axialD
  exact h.congr_deriv (by simp only [axialDD]; ring)

theorem circle_second (a : ℝ) : HasDerivAt circleD (circleDD a) a := by
  have hh : HasDerivAt (fun x : ℝ => x/2) (1/2) a := (hasDerivAt_id' a).div_const 2
  have h := (Real.hasDerivAt_cos a).fun_sub (hh.cos.const_mul R)
  unfold circleD
  exact h.congr_deriv (by simp only [circleDD]; ring)

theorem charge_difference (a : ℝ) :
    axialCharge a-circleCharge a=
      2*R*Real.sin (a/2)*(1-Real.cos ((a-alpha)/2)) := by
  have hh := double_angle a
  have hr : R*Real.cos ((a-alpha)/2)=
      (axial+1/2)*Real.cos (a/2)+(1/2)*Real.sin (a/2) := by
    rw [show (a-alpha)/2=a/2-beta by dsimp only [alpha]; ring,Real.cos_sub]
    linear_combination Real.cos (a/2)*beta_frame.1+Real.sin (a/2)*beta_frame.2
  dsimp only [axialCharge,circleCharge]
  linear_combination (-1/2)*hh.2-(axial+1/2)*hh.1+2*Real.sin (a/2)*hr

theorem transition_value : axialCharge alpha=circleCharge alpha := by
  have hh := charge_difference alpha
  simp only [sub_self,zero_div,Real.cos_zero,sub_self,mul_zero] at hh
  linarith

theorem transition_derivative : axialD alpha=circleD alpha := by
  have hdouble := double_angle alpha
  have hh : alpha/2=beta := by dsimp only [alpha]; ring
  rw [hh] at hdouble
  dsimp only [axialD,circleD]
  rw [hh]
  linear_combination (-1/2)*hdouble.1+(axial+1/2)*hdouble.2+beta_frame.1+
    2*Real.sin beta*beta_tangent

theorem axial_curvature {a : ℝ} (ha : a∈Icc 0 frameCap) :
    axialDD a≤-Real.cos a/2+(183/200)*Real.sin a := by
  have hp := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2])
    (transport_trig ha).2.2.1
  dsimp [axialDD]
  linarith

theorem circle_curvature {a : ℝ} (ha : a∈Icc 0 frameCap) : circleDD a≤0 := by
  have hh := double_angle a
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=a/2)
  have ha2 : (a/2)^2≤(7/20:ℝ)^2 := by
    apply pow_le_pow_left₀ (by linarith [ha.1])
    dsimp [frameCap] at ha
    linarith [ha.2]
  have hcoef : R/2-2*Real.cos (a/2)≤0 := by
    linarith [radius_bounds.2]
  have hp := mul_nonpos_of_nonneg_of_nonpos (half_trig ha).1 hcoef
  dsimp [circleDD]
  nlinarith only [hp,hh.1]

theorem high_curvature_majorant {a : ℝ} (ha : a∈Icc (1/2:ℝ) frameCap) :
    0≤-Real.cos a/2+(23/25)*Real.sin a := by
  let f : ℝ→ℝ := fun x => -Real.cos x/2+(23/25)*Real.sin x
  have hm : MonotoneOn f (Icc (1/2:ℝ) frameCap) := by
    apply monoOn_of_hasDeriv_nonneg (by dsimp [f]; fun_prop)
    · intro x _
      convert (((Real.hasDerivAt_cos x).neg).div_const 2).add
        ((Real.hasDerivAt_sin x).const_mul (23/25)) using 1
    · intro x hx
      have ht := transport_trig (show x∈Icc 0 frameCap from
        ⟨by linarith [hx.1],hx.2.le⟩)
      have hcos := ht.1
      have hsin := ht.2.2.1
      linarith
  have hleft : 0≤f (1/2) := by
    have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤1/2 by norm_num)
    have hc := cos_upper_four (show (0:ℝ)≤1/2 by norm_num)
    norm_num [f] at hs hc ⊢
    linarith
  exact hleft.trans (hm (by norm_num [frameCap]) ha ha.1)

end SquaresInCircles.Eight.GlobalGA.TwoPositive.ASupport
