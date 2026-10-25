module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Owners.GA.DMinorantCalculus
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2SignedCurvature

/-!
# Eight squares: the fixed-coefficient tangents in the low separated alternatives

The larger coefficient varies over its
whole interval. The rational center is exactly 5/4, and the intercept
buffers pay the stated two-sided derivative-rounding errors.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryCurvatureBounds OrdinaryNegativeSlope

abbrev p0 : ℝ := 757/1000
abbrev q0 : ℝ := 5/4
abbrev qMax : ℝ := 169/125

def root (q : ℝ) : ℝ := Real.sqrt (p0^2+q^2)
def D0 (q : ℝ) : ℝ := R*p0*q/root q
def D1 (q : ℝ) : ℝ := R*p0^3/(root q)^3
def D2 (q : ℝ) : ℝ := -3*R*p0^3*q/(root q)^5
def D3 (q : ℝ) : ℝ := 3*R*p0^3*(4*q^2-p0^2)/(root q)^7
def C0 (q : ℝ) : ℝ := R*p0^2*q^2/(root q)^3
def C1 (q : ℝ) : ℝ := R*p0^2*q*(2*p0^2-q^2)/(root q)^5
def C2 (q : ℝ) : ℝ := R*p0^2*(2*p0^4-11*p0^2*q^2+2*q^4)/(root q)^7

theorem root_pos (q : ℝ) : 0<root q := Real.sqrt_pos.mpr (by dsimp [p0]; positivity)
theorem root_sq (q : ℝ) : (root q)^2=p0^2+q^2 := Real.sq_sqrt (by positivity)
theorem root_derivative (q : ℝ) : HasDerivAt root (q/root q) q := by
  convert (((hasDerivAt_id q).pow 2).const_add (p0^2)).sqrt
    (by dsimp [p0]; positivity : p0^2+q^2≠0) using 1
  · rfl
  · dsimp [root]
    ring

theorem D0_derivative (q : ℝ) : HasDerivAt D0 (D1 q) q := by
  have hr := root_pos q
  have hs := root_sq q
  have hh := ((hasDerivAt_id q).const_mul (R*p0)).div (root_derivative q) hr.ne'
  convert hh using 1
  · rfl
  dsimp [D1]
  field_simp
  linear_combination (-1000000:ℝ)*hs

theorem D1_derivative (q : ℝ) : HasDerivAt D1 (D2 q) q := by
  have hh := (hasDerivAt_const q (R*p0^3)).div
    ((root_derivative q).pow 3) (pow_ne_zero 3 (root_pos q).ne')
  convert hh using 1
  · rfl
  · dsimp [D2]
    field_simp [(root_pos q).ne']
    ring

theorem D2_derivative (q : ℝ) : HasDerivAt D2 (D3 q) q := by
  have hr := root_pos q
  have hs := root_sq q
  have hh := ((hasDerivAt_id q).const_mul (-3*R*p0^3)).div
    ((root_derivative q).pow 5) (pow_ne_zero 5 hr.ne')
  convert hh using 1
  · rfl
  dsimp [D3]
  field_simp
  linear_combination (1000000:ℝ)*hs

theorem C0_derivative (q : ℝ) : HasDerivAt C0 (C1 q) q := by
  have hr := root_pos q
  have hs := root_sq q
  have hh := (((hasDerivAt_id q).pow 2).const_mul (R*p0^2)).div
    ((root_derivative q).pow 3) (pow_ne_zero 3 hr.ne')
  convert hh using 1
  · rfl
  dsimp [C1]
  field_simp
  linear_combination (-2000000*q)*hs

theorem C1_derivative (q : ℝ) : HasDerivAt C1 (C2 q) q := by
  have hr := root_pos q
  have hs := root_sq q
  have hh := (((hasDerivAt_id q).const_mul (R*p0^2)).mul
    ((hasDerivAt_pow 2 q).const_sub (2*p0^2))).div
    ((root_derivative q).pow 5) (pow_ne_zero 5 hr.ne')
  convert hh using 1
  · rfl
  dsimp [C2]
  field_simp
  linear_combination (3000000000000*q^2-1146098000000)*hs

theorem lower_quotient {x y c : ℝ} (hx : 0<x) (hy : 0<y) (hc : 0≤c)
    (hsq : c^2*y^2<x^2) : c<x/y := by
  apply (lt_div_iff₀ hy).2
  have hp : 0≤c*y := mul_nonneg hc hy.le
  nlinarith

theorem endpoint_bounds :
    D0 q0<12813/10000 ∧ D1 q0∈Ioo (5501/20000:ℝ) (27507/100000) ∧
    C0 q0<28387/50000 ∧ C1 q0∈Ioo (-(8857/100000):ℝ) (-(1771/20000)) ∧
    D2 qMax< -(389/1000:ℝ) := by
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hpow (q : ℝ) (n : ℕ) : ((root q)^n)^2=(p0^2+q^2)^n := by
    rw [←pow_mul,mul_comm,pow_mul,root_sq]
  have hD0 : D0 q0<12813/10000 := by
    unfold D0
    apply quotient_lt_of_square (root_pos _) (by norm_num)
    rw [mul_pow,mul_pow,hR2,root_sq]
    norm_num [qCap]
  have hD1lo : (5501/20000:ℝ)<D1 q0 := by
    unfold D1
    apply lower_quotient (mul_pos hR (by norm_num)) (pow_pos (root_pos _) 3) (by norm_num)
    rw [hpow,mul_pow,hR2]
    norm_num [qCap]
  have hD1hi : D1 q0<27507/100000 := by
    unfold D1
    apply quotient_lt_of_square (pow_pos (root_pos _) 3) (by norm_num)
    rw [hpow,mul_pow,hR2]
    norm_num [qCap]
  have hC0 : C0 q0<28387/50000 := by
    unfold C0
    apply quotient_lt_of_square (pow_pos (root_pos _) 3) (by norm_num)
    rw [hpow,mul_pow,mul_pow,hR2]
    norm_num [qCap]
  have he : -C1 q0=R*p0^2*q0*(q0^2-2*p0^2)/(root q0)^5 := by dsimp [C1]; ring
  have hC1lo : (1771/20000:ℝ)< -C1 q0 := by
    rw [he]
    apply lower_quotient (mul_pos (mul_pos (mul_pos hR (by norm_num)) (by norm_num))
      (by norm_num)) (pow_pos (root_pos _) 5) (by norm_num)
    rw [hpow,mul_pow,mul_pow,mul_pow,hR2]
    norm_num [qCap]
  have hC1hi : -C1 q0<8857/100000 := by
    rw [he]
    apply quotient_lt_of_square (pow_pos (root_pos _) 5) (by norm_num)
    rw [hpow,mul_pow,mul_pow,mul_pow,hR2]
    norm_num [qCap]
  have hD2 : (389/1000:ℝ)< -D2 qMax := by
    have he2 : -D2 qMax=3*R*p0^3*qMax/(root qMax)^5 := by dsimp [D2]; ring
    rw [he2]
    apply lower_quotient (mul_pos (mul_pos (mul_pos (by norm_num) hR) (by norm_num))
      (by norm_num)) (pow_pos (root_pos _) 5) (by norm_num)
    rw [hpow,mul_pow,mul_pow,mul_pow,hR2]
    norm_num [qCap]
  exact ⟨hD0,⟨hD1lo,hD1hi⟩,hC0,⟨by linarith,by linarith⟩,by linarith⟩

theorem D2_upper {q : ℝ} (hq : q∈Icc 1 qMax) : D2 q< -(389/1000:ℝ) := by
  have hm : MonotoneOn D2 (Icc (1:ℝ) qMax) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun q _ => (D2_derivative q).continuousAt.continuousWithinAt)
      (fun q _ => D2_derivative q)
    intro q hq
    have hnum : 0≤4*q^2-p0^2 := by norm_num [p0]; nlinarith [hq.1]
    exact div_nonneg (mul_nonneg (by positivity : 0≤3*R*p0^3) hnum)
      (pow_nonneg (root_pos _).le 7)
  exact (hm hq (by norm_num [qMax]) hq.2).trans_lt endpoint_bounds.2.2.2.2

theorem C2_nonpositive {q : ℝ} (hq : q∈Icc 1 qMax) : C2 q≤0 := by
  have hq0 : 0≤q := by linarith [hq.1]
  have hq2lo : (1:ℝ)≤q^2 := by nlinarith [hq.1]
  have hq2hi := pow_le_pow_left₀ hq0 hq.2 2
  have hprod := mul_nonneg (sub_nonneg.mpr hq2lo) (sub_nonneg.mpr hq2hi)
  have hpoly : 2*p0^4-11*p0^2*q^2+2*q^4≤0 := by
    norm_num [p0,qMax] at *
    nlinarith
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity : 0≤R*p0^2) hpoly)
    (pow_nonneg (root_pos _).le 7)

/-- The derivative form of the two-sided concave tangent inequality. -/
theorem tangent_upper {f df : ℝ→ℝ} {a b c x : ℝ}
    (hc : c∈Icc a b) (hx : x∈Icc a b)
    (hd : ∀y∈Icc a b,HasDerivAt f (df y) y)
    (hm : AntitoneOn df (Icc a b)) : f x≤f c+df c*(x-c) := by
  by_cases hxc : x≤c
  · have hh := derivative_reserve
      (f:=f) (df:=df) (k:=df c)
      (fun y hy => (hd y ⟨hy.1,hy.2.trans hc.2⟩).continuousAt.continuousWithinAt)
      (fun y hy => hd y ⟨hy.1.le,hy.2.le.trans hc.2⟩)
      (fun y hy => hm ⟨hy.1.le,hy.2.le.trans hc.2⟩ hc hy.2.le)
      (show x∈Icc a c from ⟨hx.1,hxc⟩) (show c∈Icc a c from ⟨hc.1,le_rfl⟩) hxc
    linarith
  · have hcx : c≤x := (lt_of_not_ge hxc).le
    have hh := derivative_reserve
      (f:=fun y => -f y) (df:=fun y => -df y) (k:=-df c)
      (fun y hy => (hd y ⟨hc.1.trans hy.1,hy.2⟩).neg.continuousAt.continuousWithinAt)
      (fun y hy => (hd y ⟨hc.1.trans hy.1.le,hy.2.le⟩).neg)
      (fun y hy => neg_le_neg (hm hc ⟨hc.1.trans hy.1.le,hy.2.le⟩ hy.1.le))
      (show c∈Icc c b from ⟨le_rfl,hc.2⟩) (show x∈Icc c b from ⟨hcx,hx.2⟩) hcx
    linarith

theorem exact_tangents {q : ℝ} (hq : q∈Icc 1 qMax) :
    D0 q≤D0 q0+D1 q0*(q-q0)-(389/2000)*(q-q0)^2 ∧
    C0 q≤C0 q0+C1 q0*(q-q0) := by
  have hcenter : q0∈Icc (1:ℝ) qMax := by norm_num [q0,qMax]
  have hD (q : ℝ) : HasDerivAt
      (fun q => D0 q+(389/2000)*(q-q0)^2)
      (D1 q+(389/1000)*(q-q0)) q := by
    have h1 := (D0_derivative q).add
      ((((hasDerivAt_id q).sub_const q0).pow 2).const_mul (389/2000:ℝ))
    convert h1 using 1
    · rfl
    · simp only [id,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one]
      ring
  have hD1 (q : ℝ) : HasDerivAt (fun q => D1 q+(389/1000)*(q-q0)) (D2 q+389/1000) q := by
    have h1 := (D1_derivative q).add (((hasDerivAt_id q).sub_const q0).const_mul (389/1000:ℝ))
    convert h1 using 1
    · rfl
    · ring
  have hDm : AntitoneOn (fun q => D1 q+(389/1000)*(q-q0)) (Icc (1:ℝ) qMax) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun q _ => (hD1 q).continuousAt.continuousWithinAt) (fun q _ => hD1 q)
    intro q hq
    linarith [D2_upper (Ioo_subset_Icc_self hq)]
  have hCm : AntitoneOn C1 (Icc (1:ℝ) qMax) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun q _ => (C1_derivative q).continuousAt.continuousWithinAt)
      (fun q _ => C1_derivative q)
    intro q hq
    exact C2_nonpositive (Ioo_subset_Icc_self hq)
  have hd := tangent_upper hcenter hq (fun q _ => hD q) hDm
  have hc := tangent_upper hcenter hq (fun q _ => C0_derivative q) hCm
  simp only [sub_self,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero,
    add_zero] at hd
  exact ⟨by linarith,hc⟩

theorem rounded_tangents {q : ℝ} (hq : q∈Icc 1 qMax) :
    D0 q<32033/25000+(13753/50000)*(q-q0)-(389/2000)*(q-q0)^2 ∧
    C0 q<2271/4000-(1107/12500)*(q-q0) := by
  have hqabs : |q-q0|≤1/4 := by
    rw [abs_le]
    norm_num [q0,qMax] at *
    exact ⟨by linarith [hq.1],by linarith [hq.2]⟩
  have hDabs : |D1 q0-13753/50000|≤1/100000 := by
    rw [abs_le]
    constructor <;> linarith [endpoint_bounds.2.1.1,endpoint_bounds.2.1.2]
  have hCabs : |C1 q0+1107/12500|≤1/100000 := by
    rw [abs_le]
    constructor <;> linarith [endpoint_bounds.2.2.2.1.1,endpoint_bounds.2.2.2.1.2]
  have hDerr := mul_le_mul hDabs hqabs (abs_nonneg (q-q0)) (by norm_num : (0:ℝ)≤1/100000)
  have hCerr := mul_le_mul hCabs hqabs (abs_nonneg (q-q0)) (by norm_num : (0:ℝ)≤1/100000)
  rw [←abs_mul] at hDerr hCerr
  have hd := (abs_le.mp hDerr).2
  have hc := (abs_le.mp hCerr).2
  have ht := exact_tangents hq
  have hb := endpoint_bounds
  have e1 : D1 q0*(q-q0)=(D1 q0-13753/50000)*(q-q0)+13753/50000*(q-q0) := by ring
  have e2 : C1 q0*(q-q0)=(C1 q0+1107/12500)*(q-q0)-1107/12500*(q-q0) := by ring
  constructor
  · linarith [hb.1,ht.1]
  · have h3 := hb.2.2.1
    have h4 := ht.2
    rw [e2] at h4
    norm_num at h3 h4 hc ⊢
    linarith

@[simp] theorem D0_original (q : ℝ) : D0 q=NegativeAPositiveTD.Curvature.slopeZero p0 q := by
  simp only [D0,NegativeAPositiveTD.Curvature.slopeZero,pairProduct,pairNorm,root,Real.sin_zero,
    mul_zero,add_zero,mul_assoc]
@[simp] theorem C0_original (q : ℝ) : C0 q=curvatureZero R p0 q := by
  simp only [C0,curvatureZero,pairProduct,pairNorm,root,Real.sin_zero,mul_zero,add_zero,mul_pow,
    mul_assoc]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
