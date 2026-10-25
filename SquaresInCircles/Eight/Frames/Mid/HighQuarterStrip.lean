module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Core.HighHighSecondaryScalars
public import SquaresInCircles.Eight.Frames.Diagonal.Tails
public import SquaresInCircles.Eight.Frames.Mid.MidScalars

/-!
# Eight squares: both actual middle/high orders on the complete quarter strip

The source and target contact paths are applied to the original circle
points and original weak central inequality.  Both sides include the
quarter turn and the endpoints of the strip.
-/

section
/-!
## The actual quarter-turn middle/high contact

The contact sum is evaluated on the original two circle points.  Its
one-variable expression is strictly concave on the entire middle arc.
The two endpoint comparisons use positive square comparisons against
the exact remaining radical.  No contact value is an input hypothesis.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighAlignedContact
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport

def d1 : ℝ := a1-b1
def d2 : ℝ := a2-b2
def domain : Set ℝ := Icc d2 d1
def T1 (d : ℝ) : ℝ := Real.sqrt (4*Q0-(d+1)^2)
def T2 (d : ℝ) : ℝ := Real.sqrt (4*Q0-(3-d)^2)
def T1d (d : ℝ) : ℝ := -(d+1)/T1 d
def T2d (d : ℝ) : ℝ := (3-d)/T2 d
def J (d : ℝ) : ℝ :=
  Real.pi/4-4424499/2000000+u*FrameDiagonalArc.a0+(1189333/2000000)*d+
    (1489593/2000000)*T1 d-(4449/15625)*T2 d
def Jd (d : ℝ) : ℝ :=
  1189333/2000000-(1489593/2000000)*(d+1)/T1 d-
    (4449/15625)*(3-d)/T2 d
def Jdd (d : ℝ) : ℝ :=
  -(4*Q0)*(1489593/2000000)/(T1 d)^3+
    (4*Q0)*(4449/15625)/(T2 d)^3

theorem endpoint_order : d2<d1 := by
  dsimp [d1,d2]
  rw [b1_eq,b2_eq]
  linarith [a1_precise.1,a2_precise.2]

theorem domain_bounds {d : ℝ} (hd : d∈domain) :
    (649/1000:ℝ)<d ∧ d<(257/250:ℝ) := by
  have h1 := a1_precise
  have h2 := a2_precise
  dsimp [domain,d1,d2] at hd
  rw [b1_eq,b2_eq] at hd
  constructor <;> linarith [hd.1,hd.2,h1.1,h1.2,h2.1,h2.2]

theorem radicands_positive {d : ℝ} (hd : d∈domain) :
    0<4*Q0-(d+1)^2 ∧ 0<4*Q0-(3-d)^2 := by
  have hb := domain_bounds hd
  have hsq1 := pow_le_pow_left₀ (show 0≤d+1 by linarith)
    (show d+1≤507/250 by linarith) 2
  have hsq2 := pow_le_pow_left₀ (show 0≤3-d by linarith)
    (show 3-d≤2351/1000 by linarith) 2
  norm_num [Q0] at *
  constructor <;> nlinarith

theorem T1_pos {d : ℝ} (hd : d∈domain) : 0<T1 d :=
  Real.sqrt_pos.mpr (radicands_positive hd).1
theorem T2_pos {d : ℝ} (hd : d∈domain) : 0<T2 d :=
  Real.sqrt_pos.mpr (radicands_positive hd).2
theorem T1_sq {d : ℝ} (hd : d∈domain) : (T1 d)^2=4*Q0-(d+1)^2 :=
  Real.sq_sqrt (radicands_positive hd).1.le
theorem T2_sq {d : ℝ} (hd : d∈domain) : (T2 d)^2=4*Q0-(3-d)^2 :=
  Real.sq_sqrt (radicands_positive hd).2.le

theorem T_bounds {d : ℝ} (hd : d∈domain) :
    T1 d<(18/5:ℝ) ∧ (159/50:ℝ)<T2 d := by
  have hb := domain_bounds hd
  have h1 := T1_sq hd
  have h2 := T2_sq hd
  have hp1 := T1_pos hd
  have hp2 := T2_pos hd
  have hsq1 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1649/1000)
    (show (1649/1000:ℝ)≤d+1 by linarith) 2
  have hsq2 := pow_le_pow_left₀ (show 0≤3-d by linarith)
    (show 3-d≤2351/1000 by linarith) 2
  norm_num [Q0] at h1 h2
  constructor <;> nlinarith

theorem T1_deriv {d : ℝ} (hd : d∈domain) : HasDerivAt T1 (T1d d) d := by
  have hh := ((hasDerivAt_const d (4*Q0)).sub
    (((hasDerivAt_id d).add_const 1).pow 2)).sqrt (radicands_positive hd).1.ne'
  convert hh using 1
  · rfl
  · dsimp [T1d,T1]
    ring

theorem T2_deriv {d : ℝ} (hd : d∈domain) : HasDerivAt T2 (T2d d) d := by
  have hh := ((hasDerivAt_const d (4*Q0)).sub
    (((hasDerivAt_const d 3).sub (hasDerivAt_id d)).pow 2)).sqrt
      (radicands_positive hd).2.ne'
  convert hh using 1
  · rfl
  · dsimp [T2d,T2]
    ring

theorem T1d_deriv {d : ℝ} (hd : d∈domain) :
    HasDerivAt T1d (-(4*Q0)/(T1 d)^3) d := by
  have hp := (T1_pos hd).ne'
  have hs := T1_sq hd
  have hh := (((hasDerivAt_id d).add_const 1).neg).div (T1_deriv hd) hp
  convert hh using 1
  · rfl
  · dsimp [T1d]
    field_simp [hp]
    nlinarith only [hs]

theorem T2d_deriv {d : ℝ} (hd : d∈domain) :
    HasDerivAt T2d (-(4*Q0)/(T2 d)^3) d := by
  have hp := (T2_pos hd).ne'
  have hs := T2_sq hd
  have hh := ((hasDerivAt_const d 3).sub (hasDerivAt_id d)).div (T2_deriv hd) hp
  convert hh using 1
  · rfl
  · dsimp [T2d]
    field_simp [hp]
    nlinarith only [hs]

theorem J_deriv {d : ℝ} (hd : d∈domain) : HasDerivAt J (Jd d) d := by
  have hh := ((((hasDerivAt_id d).const_mul (1189333/2000000:ℝ)).const_add
    (Real.pi/4-4424499/2000000+u*FrameDiagonalArc.a0)).fun_add
      ((T1_deriv hd).const_mul (1489593/2000000:ℝ))).fun_sub
        ((T2_deriv hd).const_mul (4449/15625:ℝ))
  convert hh using 1
  · funext y
    simp only [J,id]
  · simp only [Jd,T1d,T2d]
    ring

theorem Jd_deriv {d : ℝ} (hd : d∈domain) : HasDerivAt Jd (Jdd d) d := by
  have hh := (((T1d_deriv hd).const_mul (1489593/2000000:ℝ)).const_add
    (1189333/2000000:ℝ)).fun_sub ((T2d_deriv hd).const_mul (4449/15625:ℝ))
  convert hh using 1
  · funext y
    simp only [Jd,T1d,T2d]
    ring
  · simp only [Jdd]
    ring

theorem Jdd_negative {d : ℝ} (hd : d∈domain) : Jdd d<0 := by
  have h1 := T1_pos hd
  have h2 := T2_pos hd
  have hb := T_bounds hd
  have hpow1 := pow_lt_pow_left₀ hb.1 h1.le (by norm_num : (3:ℕ)≠0)
  have hpow2 := pow_lt_pow_left₀ hb.2 (by norm_num : (0:ℝ)≤159/50)
    (by norm_num : (3:ℕ)≠0)
  have hratio : (4449/15625:ℝ)/(T2 d)^3<
      (1489593/2000000:ℝ)/(T1 d)^3 := by
    apply (div_lt_div_iff₀ (pow_pos h2 3) (pow_pos h1 3)).2
    linarith
  have he : Jdd d=4*Q0*((4449/15625:ℝ)/(T2 d)^3-(1489593/2000000:ℝ)/(T1 d)^3) := by
    dsimp [Jdd]
    ring
  rw [he]
  exact mul_neg_of_pos_of_neg (by norm_num [Q0]) (by linarith)

theorem J_concave : ConcaveOn ℝ domain J :=
  concave_of_deriv2 (fun _ hd => J_deriv hd) (fun _ hd => Jd_deriv hd)
    (fun _ hd => (Jdd_negative hd).le)

theorem middle_difference {b : ℝ} (hb : b∈Icc b1 b2) : A b-b∈domain := by
  have hl := minus_antitone (mid_subset hb)
    ⟨by linarith [b2_bounds.1],le_rfl⟩ hb.2
  have hu := minus_antitone ⟨by linarith [b1_bounds.1],b1_lt_b2.le⟩
    (mid_subset hb) hb.1
  simpa only [A_b1,A_b2,domain,d1,d2,Set.mem_Icc] using And.intro hl hu

theorem root_of_difference {b : ℝ} (hb : b∈Icc 0 b2) :
    Real.sqrt (4*Q0-(A b-b+1)^2)=A b+b+1 := by
  have hc := A_circle hb
  have hp : 0≤A b+b+1 := by linarith [(A_bounds hb).1,a2_precise.1,hb.1]
  rw [show 4*Q0-(A b-b+1)^2=(A b+b+1)^2 by nlinarith only [hc],
    Real.sqrt_sq hp]

theorem aligned_identity {b B : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b2)
    (hc : (A b-b)+(A B-B)=2) :
    Real.pi/2-M b-H B=J (A b-b) := by
  have h1 := root_of_difference (mid_subset hb)
  have h2 := root_of_difference hB
  have he : 3-(A b-b)=A B-B+1 := by linarith
  dsimp [J,T1,T2]
  rw [he,h1,h2]
  dsimp [M,H,cM,k,q,u,v]
  linear_combination (195443/1000000)*hc

def endpointA (first : Bool) : ℝ := if first then a1 else a2
def endpointRatio (first : Bool) : ℝ := if first then 2/5 else 3/5
def lowerA (first : Bool) : ℝ :=
  if first then 85661147/50000000 else 32468681/20000000
def upperA (first : Bool) : ℝ :=
  if first then 34264459/20000000 else 162343407/100000000
def endpointD (first : Bool) : ℝ := (1-endpointRatio first)*endpointA first
def endpointCoefficient (first : Bool) : ℝ :=
  1339463/1000000+(15013/100000)*endpointRatio first
def lowerLinear (first : Bool) : ℝ :=
  314159/400000-1467453/1000000+u*(179842813/100000000)+
    endpointCoefficient first*lowerA first-4463/5000
def upperRadicand (first : Bool) : ℝ :=
  4*Q0-(3-(1-endpointRatio first)*upperA first)^2

theorem endpointD_mem (first : Bool) : endpointD first∈domain := by
  have ho := endpoint_order.le
  cases first <;> dsimp [endpointD,endpointRatio,endpointA,domain]
  · have he : (1-(3/5:ℝ))*a2=d2 := by dsimp [d2]; rw [b2_eq]; ring
    rw [he]
    exact ⟨le_rfl,ho⟩
  · have he : (1-(2/5:ℝ))*a1=d1 := by dsimp [d1]; rw [b1_eq]; ring
    rw [he]
    exact ⟨ho,le_rfl⟩

theorem endpoint_formula (first : Bool) :
    J (endpointD first)=Real.pi/4-1467453/1000000+u*FrameDiagonalArc.a0+
      endpointCoefficient first*endpointA first-(4449/15625)*T2 (endpointD first) := by
  have hroot : T1 (endpointD first)=
      (1+endpointRatio first)*endpointA first+1 := by
    cases first
    · have hh := root_of_difference ⟨by linarith [b2_bounds.1],le_rfl⟩
      have hD : endpointD false=A b2-b2 := by
        rw [A_b2,b2_eq]
        simp only [endpointD,endpointRatio,endpointA,Bool.false_eq_true,↓reduceIte]
        ring
      have hR : (1+endpointRatio false)*endpointA false+1=A b2+b2+1 := by
        rw [A_b2,b2_eq]
        simp only [endpointRatio,endpointA,Bool.false_eq_true,↓reduceIte]
        ring
      rw [T1,hD,hR]
      exact hh
    · have hh := root_of_difference ⟨by linarith [b1_bounds.1],b1_lt_b2.le⟩
      have hD : endpointD true=A b1-b1 := by
        rw [A_b1,b1_eq]
        simp only [endpointD,endpointRatio,endpointA,↓reduceIte]
        ring
      have hR : (1+endpointRatio true)*endpointA true+1=A b1+b1+1 := by
        rw [A_b1,b1_eq]
        simp only [endpointRatio,endpointA,↓reduceIte]
        ring
      rw [T1,hD,hR]
      exact hh
  rw [J,hroot]
  dsimp [endpointD,endpointCoefficient]
  ring

theorem endpoint_arithmetic (first : Bool) :
    0<lowerLinear first ∧
      (4449/15625:ℝ)^2*upperRadicand first<(lowerLinear first)^2 := by
  cases first <;> norm_num [lowerLinear,upperRadicand,endpointCoefficient,
    endpointRatio,lowerA,upperA,u,Q0]

theorem endpoint_lower (first : Bool) : (4463/5000:ℝ)<J (endpointD first) := by
  have hA : lowerA first<endpointA first ∧ endpointA first<upperA first := by
    cases first
    · exact a2_precise
    · exact a1_precise
  have hc : 0<endpointCoefficient first := by
    cases first <;> norm_num [endpointCoefficient,endpointRatio]
  have hp := Arithmetic.pi_hand_enclosure.1
  have hlin : lowerLinear first≤Real.pi/4-1467453/1000000+u*FrameDiagonalArc.a0+
      endpointCoefficient first*endpointA first-4463/5000 := by
    have hmul := mul_le_mul_of_nonneg_left hA.1.le hc.le
    dsimp [lowerLinear,u]
    linarith [a0_precise.1]
  have hrad : (T2 (endpointD first))^2≤upperRadicand first := by
    rw [T2_sq (endpointD_mem first)]
    have he : 0<1-endpointRatio first := by cases first <;> norm_num [endpointRatio]
    have ha := mul_le_mul_of_nonneg_left hA.2.le he.le
    have hpos : 0≤3-(1-endpointRatio first)*upperA first := by
      cases first <;> norm_num [endpointRatio,upperA]
    have hs := pow_le_pow_left₀ hpos
      (show 3-(1-endpointRatio first)*upperA first≤3-endpointD first by
        dsimp [endpointD]; linarith) 2
    dsimp [upperRadicand]
    linarith
  have hn := T2_pos (endpointD_mem first)
  have hnum := endpoint_arithmetic first
  have hscaled := mul_le_mul_of_nonneg_left hrad
    (by positivity : (0:ℝ)≤(4449/15625)^2)
  have hroot : (4449/15625)*T2 (endpointD first)<lowerLinear first := by
    nlinarith
  rw [endpoint_formula]
  linarith

theorem J_lower {d : ℝ} (hd : d∈domain) : (4463/5000:ℝ)<J d := by
  have hl := endpoint_lower false
  have hu := endpoint_lower true
  have heL : endpointD false=d2 := by
    dsimp [endpointD,endpointRatio,endpointA,d2]
    rw [b2_eq]
    ring
  have heU : endpointD true=d1 := by
    dsimp [endpointD,endpointRatio,endpointA,d1]
    rw [b1_eq]
    ring
  rw [heL] at hl
  rw [heU] at hu
  exact concave_gt_of_endpoints J_concave hd hl hu

theorem actual_aligned_lower {b B : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc 0 b2) (hc : (A b-b)+(A B-B)=2) :
    (4463/5000:ℝ)<Real.pi/2-M b-H B := by
  rw [aligned_identity hb hB hc]
  exact J_lower (middle_difference hb)

end SquaresInCircles.Eight.FrameMidHighAlignedContact
end
end
end

section
/-!
## The enlarged high arc and the complete quarter-turn strip

The enlargement to transverse coordinate `.8` is used only for a lower
support.  It is still the same exact circle.  All trigonometric bounds
and one-sided widths hold on the complete closed strip.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighContactArc
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport

def extended : Set ℝ := Icc 0 (4/5)
def strip : Set ℝ := Icc (-(1/50:ℝ)) (1/50)
def side (before : Bool) : Set ℝ :=
  if before then Icc (-(1/50:ℝ)) 0 else Icc 0 (1/50)
def C (e : ℝ) : ℝ := Real.cos e-Real.sin e
def D (e : ℝ) : ℝ := Real.cos e+Real.sin e
def W (before : Bool) (e : ℝ) : ℝ := if before then 1+C e else 1+D e
def Wd (before : Bool) (e : ℝ) : ℝ := if before then -D e else C e
def angular (before : Bool) (e : ℝ) : ℝ :=
  Real.pi/2+e-(9/100)*(W before e-2)

theorem side_subset {before : Bool} {e : ℝ} (he : e∈side before) : e∈strip := by
  cases before <;> dsimp [side,strip] at * <;> constructor <;> linarith [he.1,he.2]

theorem zero_side (before : Bool) : (0:ℝ)∈side before := by cases before <;> norm_num [side]

theorem extended_subset {B : ℝ} (hB : B∈extended) : B∈Icc 0 b2 :=
  ⟨hB.1,by linarith [hB.2,b2_bounds.1]⟩

theorem high_extended {B : ℝ} (hB : B∈Icc 0 b1) : B∈extended :=
  ⟨hB.1,by linarith [hB.2,b1_bounds.2]⟩

theorem extended_radial {B : ℝ} (hB : B∈extended) :
    (67/25:ℝ)<A B+1 ∧ A B≤FrameDiagonalArc.a0 := by
  have hc := A_circle (extended_subset hB)
  have hp := A_shift_pos (extended_subset hB)
  have hsq := pow_le_pow_left₀ hB.1 hB.2 2
  have hu := (A_bounds (extended_subset hB)).2
  norm_num [Q0] at hc
  exact ⟨by nlinarith,hu⟩

theorem extended_slope {B : ℝ} (hB : B∈extended) : 0≤ slope B ∧ slope B<3/10 := by
  have hp := (extended_radial hB).1
  constructor
  · exact div_nonneg hB.1 (by linarith)
  · apply (div_lt_iff₀ (show 0<A B+1 by linarith)).2
    linarith [hB.2]

theorem H_deriv_extended {B : ℝ} (hB : B∈extended) : HasDerivAt H (Hd B) B := by
  have hh := (((A_hasDerivAt (extended_subset hB)).sub_const FrameDiagonalArc.a0).const_mul
    u).fun_add ((hasDerivAt_id B).const_mul v)
  rw [show H=fun y => u*(A y-FrameDiagonalArc.a0)+v*id y from rfl]
  exact hh.congr_deriv (by simp only [Hd,Ad,FrameDiagonalArc.slope]; ring)

theorem Hd_extended {B : ℝ} (hB : B∈extended) :
    v-(3/10)*u<Hd B ∧ Hd B≤v := by
  have hr := extended_slope hB
  dsimp [Hd,u,v]
  constructor <;> linarith

theorem H_monotone_extended : MonotoneOn H extended := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun B hB => (H_deriv_extended hB).continuousAt.continuousWithinAt
  · exact fun B hB => H_deriv_extended (Ioo_subset_Icc_self hB)
  · intro B hB
    have hh := (Hd_extended (Ioo_subset_Icc_self hB)).1
    dsimp [u,v] at hh
    linarith

theorem C_deriv (e : ℝ) : HasDerivAt C (-D e) e := by
  have h := (Real.hasDerivAt_cos e).fun_sub (Real.hasDerivAt_sin e)
  rw [show C=fun x => Real.cos x-Real.sin x from rfl]
  exact h.congr_deriv (by simp only [D]; ring)

theorem D_deriv (e : ℝ) : HasDerivAt D (C e) e := by
  have h := (Real.hasDerivAt_cos e).fun_add (Real.hasDerivAt_sin e)
  rw [show D=fun x => Real.cos x+Real.sin x from rfl]
  exact h.congr_deriv (by simp only [C]; ring)

theorem W_deriv (before : Bool) (e : ℝ) : HasDerivAt (W before) (Wd before e) e := by
  cases before
  · exact (D_deriv e).const_add 1
  · exact (C_deriv e).const_add 1

theorem angular_deriv (before : Bool) (e : ℝ) :
    HasDerivAt (angular before) (1-(9/100)*Wd before e) e := by
  have h := ((hasDerivAt_id e).const_add (Real.pi/2)).fun_sub
    (((W_deriv before e).sub_const 2).const_mul (9/100:ℝ))
  rw [show angular before=fun y => Real.pi/2+id y-9/100*(W before y-2) from rfl]
  exact h.congr_deriv (by ring)

theorem unit (e : ℝ) : (C e)^2+(D e)^2=2 := by
  dsimp [C,D]
  nlinarith [Real.sin_sq_add_cos_sq e]

theorem strip_trig {e : ℝ} (he : e∈strip) :
    -(1/50:ℝ)≤Real.sin e ∧ Real.sin e≤1/50 ∧
      (4999/5000:ℝ)≤Real.cos e ∧ Real.cos e≤1 := by
  have hab : |e|≤(1/50:ℝ) := abs_le.mpr he
  have hs := (Real.abs_sin_le_abs (x := e)).trans hab
  have hsq := pow_le_pow_left₀ (abs_nonneg e) hab 2
  rw [sq_abs] at hsq
  have hc := Real.one_sub_sq_div_two_le_cos (x := e)
  exact ⟨(abs_le.mp hs).1,(abs_le.mp hs).2,by nlinarith,Real.cos_le_one e⟩

theorem CD_bounds {e : ℝ} (he : e∈strip) :
    C e∈Icc (4899/5000:ℝ) (51/50) ∧ D e∈Icc (4899/5000:ℝ) (51/50) := by
  have ht := strip_trig he
  dsimp [C,D]
  constructor <;> constructor <;> linarith

theorem side_signs {before : Bool} {e : ℝ} (he : e∈side before) :
    (if before then Real.sin e≤0 ∧ 1≤C e ∧ D e≤1
      else 0≤Real.sin e ∧ C e≤1 ∧ 1≤D e) := by
  have ht := strip_trig (side_subset he)
  have hp := one_le_abs_cos_add_abs_sin e
  cases before with
  | false =>
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi he.1
        (by linarith [he.2,Arithmetic.pi_hand_enclosure.1])
      simp only [abs_of_nonneg hs,
        abs_of_nonneg (by linarith [ht.2.2.1] : 0≤Real.cos e)] at hp
      simp only [Bool.false_eq_true,↓reduceIte]
      dsimp [C,D]
      exact ⟨hs,by linarith,by linarith⟩
  | true =>
      have hs : Real.sin e≤0 := by
        have hh := Real.sin_nonneg_of_nonneg_of_le_pi
          (show 0≤-e by linarith [he.2])
          (show -e≤Real.pi by linarith [he.1,Arithmetic.pi_hand_enclosure.1])
        simpa only [Real.sin_neg,neg_nonneg] using hh
      simp only [abs_of_nonpos hs,
        abs_of_nonneg (by linarith [ht.2.2.1] : 0≤Real.cos e)] at hp
      simp only [↓reduceIte]
      dsimp [C,D]
      exact ⟨hs,by linarith,by linarith⟩

theorem W_bounds {before : Bool} {e : ℝ} (he : e∈side before) :
    (2:ℝ)≤W before e ∧ W before e≤101/50 := by
  have ht := CD_bounds (side_subset he)
  have hs := side_signs he
  cases before <;> dsimp [W] at * <;> constructor <;>
    linarith [ht.1.1,ht.1.2,ht.2.1,ht.2.2,hs.1,hs.2.1,hs.2.2]

theorem angular_derivative_bounds {before : Bool} {e : ℝ} (he : e∈side before) :
    (if before then 1-(9/100)*Wd before e≤109/100
      else (91/100:ℝ)≤1-(9/100)*Wd before e) := by
  have hs := side_signs he
  cases before <;> dsimp [Wd] at * <;> linarith

theorem angle_trig (e : ℝ) :
    Real.sin (Real.pi/2+e)=Real.cos e ∧ Real.cos (Real.pi/2+e)= -Real.sin e := by
  simp [Real.sin_add,Real.cos_add]

theorem W_actual {before : Bool} {e : ℝ} (he : e∈side before) :
    W before e=2*pairWidth (Real.pi/2+e) := by
  have ht := strip_trig (side_subset he)
  have hs := side_signs he
  rw [pairWidth,(angle_trig e).1,(angle_trig e).2,abs_neg,
    abs_of_nonneg (by linarith [ht.2.2.1] : 0≤Real.cos e)]
  cases before
  · rw [abs_of_nonneg hs.1]
    dsimp [W,D]
    ring
  · rw [abs_of_nonpos hs.1]
    dsimp [W,C]
    ring

theorem angular_actual {before : Bool} {e : ℝ} (he : e∈side before) :
    angular before e=Real.pi/2+e-(9/50)*periodicFrameCost (Real.pi/2+e) := by
  rw [angular,W_actual he]
  dsimp [pairWidth,periodicFrameCost]
  ring

@[simp] theorem C_zero : C 0=1 := by norm_num [C]
@[simp] theorem D_zero : D 0=1 := by norm_num [D]
@[simp] theorem W_zero (before : Bool) : W before 0=2 := by cases before <;> norm_num [W]
@[simp] theorem angular_zero (before : Bool) : angular before 0=Real.pi/2 := by simp [angular]

theorem middle_sum_lower {b : ℝ} (hb : b∈Icc b1 b2) :
    (1199/500:ℝ)<A b+b := by
  have hh := plus_monotone ⟨by linarith [b1_bounds.1],b1_lt_b2.le⟩ (mid_subset hb) hb.1
  simp only [A_b1] at hh
  rw [b1_eq] at hh
  linarith [a1_precise.1]

end SquaresInCircles.Eight.FrameMidHighContactArc
end
end
end

section
/-!
## The actual high-target contact through the quarter turn

For each fixed original middle point, the explicit circle root retains
the central contact.  Its charged cost decreases up to the quarter turn
and increases afterwards.  Every originally feasible high target is
compared with that root on the same circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighTargetContact
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameMidHighContactArc

def L (before : Bool) (b e : ℝ) : ℝ := W before e-(A b-b)+D e
def Ld (before : Bool) (e : ℝ) : ℝ := Wd before e+C e
def Y (before : Bool) (b e : ℝ) : ℝ :=
  FrameDiagonalContactRoot.Y (C e) (D e) (L before b e)
def Yd (before : Bool) (b e : ℝ) : ℝ :=
  FrameDiagonalContactRoot.YD (C e) (D e) (L before b e) (-D e) (C e) (Ld before e)
def denominator (before : Bool) (b e : ℝ) : ℝ := C e+D e*slope (Y before b e)
def F (before : Bool) (b e : ℝ) : ℝ := angular before e-M b-H (Y before b e)
def Fd (before : Bool) (b e : ℝ) : ℝ :=
  1-(9/100)*Wd before e-Hd (Y before b e)*Yd before b e

theorem L_bounds {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    L before b e∈Icc (197/100:ℝ) (12/5) := by
  have hd := FrameMidHighAlignedContact.domain_bounds
    (FrameMidHighAlignedContact.middle_difference hb)
  have ht := strip_trig (side_subset he)
  have hCD := CD_bounds (side_subset he)
  have hsg := side_signs he
  cases before
  · have h1 : 1≤D e := hsg.2.2
    dsimp [L,W]
    constructor <;> linarith [hCD.2.2]
  · dsimp [L,W,C,D]
    constructor <;> linarith

theorem root_data {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    0<4*Q0-(L before b e)^2 ∧ 0<Y before b e ∧ Y before b e<4/5 ∧
      0<FrameDiagonalContactRoot.X (C e) (D e) (L before b e)+1 := by
  exact FrameDiagonalContactRoot.target_root_bounds
    (CD_bounds (side_subset he)).1 (CD_bounds (side_subset he)).2 (L_bounds hb he)

theorem Y_mem {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    Y before b e∈extended :=
  ⟨(root_data hb he).2.1.le,(root_data hb he).2.2.1.le⟩

theorem radial {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    FrameDiagonalContactRoot.X (C e) (D e) (L before b e)=A (Y before b e) :=
  FrameDiagonalContactRoot.X_eq_chart (unit e) (root_data hb he).1.le
    (root_data hb he).2.2.2.le

theorem contact {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    (A b-b)+D e*A (Y before b e)-C e*Y before b e=W before e := by
  have hh := FrameDiagonalContactRoot.contact (l := L before b e) (unit e)
  rw [radial hb he] at hh
  change D e*(A (Y before b e)+1)-C e*Y before b e=L before b e at hh
  dsimp [L] at hh
  linarith

theorem L_deriv (before : Bool) (b e : ℝ) : HasDerivAt (L before b) (Ld before e) e := by
  exact ((W_deriv before e).sub_const (A b-b)).fun_add (D_deriv e)

theorem Y_deriv {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    HasDerivAt (Y before b) (Yd before b e) e :=
  FrameDiagonalContactRoot.Y_deriv (C_deriv e) (D_deriv e) (L_deriv before b e)
    (root_data hb he).1

theorem denominator_lower {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) :
    (4899/5000:ℝ)≤denominator before b e := by
  have ht := CD_bounds (side_subset he)
  have hr := extended_slope (Y_mem hb he)
  have hp := mul_nonneg (by linarith [ht.2.1] : 0≤D e) hr.1
  dsimp [denominator]
  linarith [ht.1.1]

theorem speed_identity {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) :
    Yd before b e*denominator before b e=
      C e*A (Y before b e)+D e*Y before b e-Wd before e := by
  have hh := FrameDiagonalContactRoot.YD_contact (cp := -D e) (dp := C e)
    (lp := Ld before e) (unit e) (by ring) (root_data hb he).1
    (root_data hb he).2.2.2.ne'
  rw [radial hb he] at hh
  change Yd before b e*(C e+D e*(Y before b e/(A (Y before b e)+1)))=
    C e*(A (Y before b e)+1)- -D e*Y before b e-Ld before e at hh
  dsimp only [Ld] at hh
  dsimp [denominator,FrameDiagonalArc.slope]
  linarith

theorem before_speed {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side true) :
    (66/25:ℝ)<Yd true b e := by
  have hid := speed_identity hb he
  have ht := strip_trig (side_subset he)
  have hs := side_signs he
  have hr := extended_slope (Y_mem hb he)
  have hrad := (extended_radial (Y_mem hb he)).1
  have hC := (CD_bounds (side_subset he)).1.1
  have hD := (CD_bounds (side_subset he)).2.1
  have hden : 1≤denominator true b e := by
    have hp := mul_nonneg (show 0≤D e by linarith) hr.1
    dsimp [denominator]
    linarith [hs.2.1]
  have hden0 : 0<denominator true b e := by linarith
  have hcancel : Yd true b e*denominator true b e=
      (A (Y true b e)+1)*denominator true b e+2*Real.sin e := by
    have hp := (A_shift_pos (extended_subset (Y_mem hb he))).ne'
    have hr : slope (Y true b e)*(A (Y true b e)+1)=Y true b e := by
      dsimp [FrameDiagonalArc.slope]
      field_simp [hp]
    have hcd : D e-C e=2*Real.sin e := by dsimp [C,D]; ring
    rw [hid]
    dsimp [Wd,denominator]
    linear_combination -(D e)*hr+hcd
  have hmul := mul_lt_mul_of_pos_right hrad hden0
  apply lt_of_mul_lt_mul_right _ hden0.le
  linarith [ht.1]

theorem after_speed {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side false) :
    0<Yd false b e ∧ Yd false b e<(8080/4899:ℝ) := by
  have hid := speed_identity hb he
  have hs := side_signs he
  have ht := CD_bounds (side_subset he)
  have hy := root_data hb he
  have ha := extended_radial (Y_mem hb he)
  have hden := denominator_lower hb he
  have hden0 : 0<denominator false b e := by linarith
  have hnum0 : 0<C e*(A (Y false b e)-1)+D e*Y false b e := by
    have hp := mul_pos (show 0<C e by linarith [ht.1.1])
      (show 0<A (Y false b e)-1 by linarith [ha.1])
    have hq := mul_nonneg (show 0≤D e by linarith [ht.2.1]) hy.2.1.le
    linarith
  have hnumU : C e*(A (Y false b e)-1)+D e*Y false b e<(202/125:ℝ) := by
    have hp := mul_le_mul_of_nonneg_right hs.2.1
      (show 0≤A (Y false b e)-1 by linarith [ha.1])
    have hq := mul_le_mul ht.2.2 hy.2.2.1.le hy.2.1.le (by norm_num : (0:ℝ)≤51/50)
    nlinarith [ha.2,a0_precise.2]
  have hid' : Yd false b e*denominator false b e=
      C e*(A (Y false b e)-1)+D e*Y false b e := by
    dsimp [Wd] at hid
    linarith
  have hypos : 0<Yd false b e :=
    (mul_pos_iff_of_pos_right hden0).mp (by rw [hid']; exact hnum0)
  have hmul := mul_le_mul_of_nonneg_left hden hypos.le
  exact ⟨hypos,by nlinarith⟩

theorem F_deriv {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    HasDerivAt (F before b) (Fd before b e) e := by
  have hh := ((angular_deriv before e).sub_const (M b)).sub
    ((H_deriv_extended (Y_mem hb he)).comp e (Y_deriv hb he))
  convert hh using 1
  · funext y
    simp only [F,Pi.sub_apply,Function.comp_apply]
  · simp only [Fd]

theorem before_Fd_negative {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side true) :
    Fd true b e<0 := by
  have hy := before_speed hb he
  have hH := (Hd_extended (Y_mem hb he)).1
  have hHp : 0<Hd (Y true b e) := by dsimp [u,v] at hH; linarith
  have hprod := mul_lt_mul_of_pos_left hy hHp
  have ha := angular_derivative_bounds he
  dsimp [Fd,u,v] at *
  nlinarith

theorem after_Fd_positive {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side false) :
    0<Fd false b e := by
  have hy := after_speed hb he
  have hH := (Hd_extended (Y_mem hb he)).2
  have hprod := mul_le_mul_of_nonneg_right hH hy.1.le
  have ha := angular_derivative_bounds he
  dsimp [Fd,v] at *
  nlinarith

theorem before_antitone {b : ℝ} (hb : b∈Icc b1 b2) : AntitoneOn (F true b) (side true) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun e he => (F_deriv hb he).continuousAt.continuousWithinAt
  · exact fun e he => F_deriv hb (Ioo_subset_Icc_self he)
  · exact fun e he => (before_Fd_negative hb (Ioo_subset_Icc_self he)).le

theorem after_monotone {b : ℝ} (hb : b∈Icc b1 b2) : MonotoneOn (F false b) (side false) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun e he => (F_deriv hb he).continuousAt.continuousWithinAt
  · exact fun e he => F_deriv hb (Ioo_subset_Icc_self he)
  · exact fun e he => (after_Fd_positive hb (Ioo_subset_Icc_self he)).le

theorem quarter_minimum {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) : F before b 0≤F before b e := by
  cases before
  · exact after_monotone hb (zero_side false) he he.1
  · exact before_antitone hb he (zero_side true) he.2

theorem F_zero_lower (before : Bool) {b : ℝ} (hb : b∈Icc b1 b2) :
    (4463/5000:ℝ)<F before b 0 := by
  have hc := contact hb (zero_side before)
  simp only [C_zero,D_zero,W_zero,one_mul] at hc
  have hh := FrameMidHighAlignedContact.actual_aligned_lower hb
    (extended_subset (Y_mem hb (zero_side before))) (by linarith :
      (A b-b)+(A (Y before b 0)-Y before b 0)=2)
  simpa only [F,angular_zero] using hh

theorem F_lower {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    (4463/5000:ℝ)<F before b e :=
  (F_zero_lower before hb).trans_le (quarter_minimum hb he)

theorem actual_target_le {before : Bool} {b B e : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (he : e∈side before)
    (hm : 0≤central false true (A b) b (A B) B (Real.pi/2+e)) : B≤Y before b e := by
  have hactual : W before e≤(A b-b)+D e*A B-C e*B := by
    dsimp [central,sign] at hm
    rw [(angle_trig e).1,(angle_trig e).2,← W_actual he] at hm
    dsimp [C,D]
    linarith
  have hc := contact hb he
  have ht := CD_bounds (side_subset he)
  by_contra! hbad
  have hA := A_antitone (extended_subset (Y_mem hb he)) (high_subset hB) hbad.le
  have hp := mul_le_mul_of_nonneg_left hA (show 0≤D e by linarith [ht.2.1])
  have hq := mul_lt_mul_of_pos_left hbad (show 0<C e by linarith [ht.1.1])
  nlinarith

theorem actual_lower {before : Bool} {b B e : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (he : e∈side before)
    (hm : 0≤central false true (A b) b (A B) B (Real.pi/2+e)) :
    (4463/5000:ℝ)<cost true false false true b B (Real.pi/2+e) := by
  have hy := actual_target_le hb hB he hm
  have hH := H_monotone_extended (high_extended hB) (Y_mem hb he) hy
  have hF := F_lower hb he
  rw [F,angular_actual he] at hF
  dsimp [cost,marker,sign]
  linarith

end SquaresInCircles.Eight.FrameMidHighTargetContact
end
end
end

section
/-!
## The actual high-source contact through the quarter turn

The middle target remains fixed.  The high point moves on its actual
circle along the explicit primary-minus-transverse level.  Both one-sided
charged derivatives have strict signs on the complete strip, and every
original weakly feasible high source lies below this contact parameter.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighSourceContact
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameMidHighContactArc

def L (before : Bool) (b e : ℝ) : ℝ := W before e-D e*A b+C e*b+1
def Ld (before : Bool) (b e : ℝ) : ℝ := Wd before e-C e*A b-D e*b
def Y (before : Bool) (b e : ℝ) : ℝ := FrameDiagonalContactRoot.Y 1 1 (L before b e)
def Yd (before : Bool) (b e : ℝ) : ℝ :=
  FrameDiagonalContactRoot.YD 1 1 (L before b e) 0 0 (Ld before b e)
def denominator (before : Bool) (b e : ℝ) : ℝ := 1+slope (Y before b e)
def F (before : Bool) (b e : ℝ) : ℝ := angular before e-M b-H (Y before b e)
def Fd (before : Bool) (b e : ℝ) : ℝ :=
  1-(9/100)*Wd before e-Hd (Y before b e)*Yd before b e

theorem L_bounds {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    L before b e∈Icc (19/10:ℝ) (243/100) := by
  have ha := A_mid_bounds hb
  have ht := CD_bounds (side_subset he)
  have hw := W_bounds he
  have hA0 : 0≤A b := by linarith [ha.1,a2_precise.1]
  have hb0 : 0≤b := (mid_subset hb).1
  have hDAU := mul_le_mul ht.2.2
    (show A b≤857/500 by linarith [ha.2,a1_precise.2]) hA0 (by norm_num)
  have hDAL := mul_le_mul ht.2.1
    (show (1623/1000:ℝ)≤A b by linarith [ha.1,a2_precise.1])
    (by norm_num) (by linarith [ht.2.1] : 0≤D e)
  have hCbU := mul_le_mul ht.1.2
    (show b≤39/40 by linarith [hb.2,b2_bounds.2]) hb0 (by norm_num)
  have hCbL := mul_le_mul ht.1.1
    (show (137/200:ℝ)≤b by linarith [hb.1,b1_bounds.1])
    (by norm_num) (by linarith [ht.1.1] : 0≤C e)
  dsimp [L]
  constructor <;> nlinarith

theorem root_data {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    0<4*Q0-(L before b e)^2 ∧ 0<Y before b e ∧ Y before b e<4/5 ∧
      0<FrameDiagonalContactRoot.X 1 1 (L before b e)+1 :=
  FrameDiagonalContactRoot.source_root_bounds (L_bounds hb he)

theorem Y_mem {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    Y before b e∈extended :=
  ⟨(root_data hb he).2.1.le,(root_data hb he).2.2.1.le⟩

theorem radial {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    FrameDiagonalContactRoot.X 1 1 (L before b e)=A (Y before b e) :=
  FrameDiagonalContactRoot.X_eq_chart (by norm_num) (root_data hb he).1.le
    (root_data hb he).2.2.2.le

theorem contact {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    A (Y before b e)-Y before b e+D e*A b-C e*b=W before e := by
  have hh := FrameDiagonalContactRoot.contact (c := (1:ℝ)) (d := (1:ℝ))
    (l := L before b e) (by norm_num)
  rw [radial hb he] at hh
  change 1*(A (Y before b e)+1)-1*Y before b e=L before b e at hh
  dsimp [L] at hh
  linarith

theorem L_deriv (before : Bool) (b e : ℝ) : HasDerivAt (L before b) (Ld before b e) e := by
  have hh := (((W_deriv before e).fun_sub ((D_deriv e).mul_const (A b))).fun_add
    ((C_deriv e).mul_const b)).add_const 1
  rw [show L before b=fun x => W before x-D x*A b+C x*b+1 from rfl]
  exact hh.congr_deriv (by simp only [Ld]; ring)

theorem Y_deriv {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    HasDerivAt (Y before b) (Yd before b e) e :=
  FrameDiagonalContactRoot.Y_deriv (hasDerivAt_const e 1) (hasDerivAt_const e 1)
    (L_deriv before b e) (root_data hb he).1

theorem denominator_bounds {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) :
    1≤denominator before b e ∧ denominator before b e<13/10 := by
  have hr := extended_slope (Y_mem hb he)
  dsimp [denominator]
  constructor <;> linarith

theorem speed_identity {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) :
    Yd before b e*denominator before b e=C e*A b+D e*b-Wd before e := by
  have hh := FrameDiagonalContactRoot.YD_contact (c := (1:ℝ)) (d := (1:ℝ))
    (cp := (0:ℝ)) (dp := (0:ℝ)) (lp := Ld before b e)
    (by norm_num) (by norm_num) (root_data hb he).1 (root_data hb he).2.2.2.ne'
  rw [radial hb he] at hh
  change Yd before b e*(1+1*(Y before b e/(A (Y before b e)+1)))=
    0*(A (Y before b e)+1)-0*Y before b e-Ld before b e at hh
  dsimp [denominator,FrameDiagonalArc.slope]
  dsimp [Ld] at hh
  linarith

theorem before_speed {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side true) :
    (64/25:ℝ)<Yd true b e := by
  have hid := speed_identity hb he
  have ht := CD_bounds (side_subset he)
  have ha := A_mid_bounds hb
  have hsum := middle_sum_lower hb
  have hden := denominator_bounds hb he
  have hden0 : 0<denominator true b e := by linarith
  have hCA := mul_le_mul_of_nonneg_right ht.1.1
    (show 0≤A b by linarith [ha.1,a2_precise.1])
  have hDB := mul_le_mul_of_nonneg_right ht.2.1
    (show 0≤b+1 by linarith [(mid_subset hb).1])
  dsimp [Wd] at hid
  apply lt_of_mul_lt_mul_right _ hden0.le
  linarith

theorem after_speed {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side false) :
    0<Yd false b e ∧ Yd false b e<(3417/2000:ℝ) := by
  have hid := speed_identity hb he
  have ht := CD_bounds (side_subset he)
  have hs := side_signs he
  have ha := A_mid_bounds hb
  have hden := denominator_bounds hb he
  have hden0 : 0<denominator false b e := by linarith
  have hb0 := (mid_subset hb).1
  have hnum0 : 0<C e*(A b-1)+D e*b := by
    have hp := mul_pos (show 0<C e by linarith [ht.1.1])
      (show 0<A b-1 by linarith [ha.1,a2_precise.1])
    have hq := mul_nonneg (show 0≤D e by linarith [ht.2.1]) hb0
    linarith
  have hnumU : C e*(A b-1)+D e*b<(3417/2000:ℝ) := by
    have hp := mul_le_mul_of_nonneg_right hs.2.1
      (show 0≤A b-1 by linarith [ha.1,a2_precise.1])
    have hq := mul_le_mul ht.2.2
      (show b≤39/40 by linarith [hb.2,b2_bounds.2]) hb0 (by norm_num)
    nlinarith [ha.2,a1_precise.2]
  have hid' : Yd false b e*denominator false b e=C e*(A b-1)+D e*b := by
    dsimp [Wd] at hid
    linarith
  have hypos : 0<Yd false b e :=
    (mul_pos_iff_of_pos_right hden0).mp (by rw [hid']; exact hnum0)
  have hmul := mul_le_mul_of_nonneg_left hden.1 hypos.le
  exact ⟨hypos,by nlinarith⟩

theorem F_deriv {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    HasDerivAt (F before b) (Fd before b e) e := by
  have hh := ((angular_deriv before e).sub_const (M b)).fun_sub
    ((H_deriv_extended (Y_mem hb he)).comp e (Y_deriv hb he))
  rw [show F before b=fun x => angular before x-M b-(H ∘ Y before b) x from rfl]
  exact hh.congr_deriv (by simp only [Fd])

theorem before_Fd_negative {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side true) :
    Fd true b e<0 := by
  have hy := before_speed hb he
  have hH := (Hd_extended (Y_mem hb he)).1
  have hHp : 0<Hd (Y true b e) := by dsimp [u,v] at hH; linarith
  have hprod := mul_lt_mul_of_pos_left hy hHp
  have ha := angular_derivative_bounds he
  dsimp [Fd,u,v] at *
  nlinarith

theorem after_Fd_positive {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side false) :
    0<Fd false b e := by
  have hy := after_speed hb he
  have hH := (Hd_extended (Y_mem hb he)).2
  have hprod := mul_le_mul_of_nonneg_right hH hy.1.le
  have ha := angular_derivative_bounds he
  dsimp [Fd,v] at *
  nlinarith

theorem before_antitone {b : ℝ} (hb : b∈Icc b1 b2) : AntitoneOn (F true b) (side true) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun e he => (F_deriv hb he).continuousAt.continuousWithinAt
  · exact fun e he => F_deriv hb (Ioo_subset_Icc_self he)
  · exact fun e he => (before_Fd_negative hb (Ioo_subset_Icc_self he)).le

theorem after_monotone {b : ℝ} (hb : b∈Icc b1 b2) : MonotoneOn (F false b) (side false) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun e he => (F_deriv hb he).continuousAt.continuousWithinAt
  · exact fun e he => F_deriv hb (Ioo_subset_Icc_self he)
  · exact fun e he => (after_Fd_positive hb (Ioo_subset_Icc_self he)).le

theorem quarter_minimum {before : Bool} {b e : ℝ}
    (hb : b∈Icc b1 b2) (he : e∈side before) : F before b 0≤F before b e := by
  cases before
  · exact after_monotone hb (zero_side false) he he.1
  · exact before_antitone hb he (zero_side true) he.2

theorem F_zero_lower (before : Bool) {b : ℝ} (hb : b∈Icc b1 b2) :
    (4463/5000:ℝ)<F before b 0 := by
  have hc := contact hb (zero_side before)
  simp only [C_zero,D_zero,W_zero,one_mul] at hc
  have hh := FrameMidHighAlignedContact.actual_aligned_lower hb
    (extended_subset (Y_mem hb (zero_side before))) (by linarith :
      (A b-b)+(A (Y before b 0)-Y before b 0)=2)
  simpa only [F,angular_zero] using hh

theorem F_lower {before : Bool} {b e : ℝ} (hb : b∈Icc b1 b2) (he : e∈side before) :
    (4463/5000:ℝ)<F before b e :=
  (F_zero_lower before hb).trans_le (quarter_minimum hb he)

theorem actual_source_le {before : Bool} {b B e : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (he : e∈side before)
    (hm : 0≤central false true (A B) B (A b) b (Real.pi/2+e)) : B≤Y before b e := by
  have hactual : W before e≤A B-B+D e*A b-C e*b := by
    dsimp [central,sign] at hm
    rw [(angle_trig e).1,(angle_trig e).2,← W_actual he] at hm
    dsimp [C,D]
    linarith
  have hc := contact hb he
  by_contra! hbad
  have hA := A_antitone (extended_subset (Y_mem hb he)) (high_subset hB) hbad.le
  linarith

theorem actual_lower {before : Bool} {b B e : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (he : e∈side before)
    (hm : 0≤central false true (A B) B (A b) b (Real.pi/2+e)) :
    (4463/5000:ℝ)<cost false true false true B b (Real.pi/2+e) := by
  have hy := actual_source_le hb hB he hm
  have hH := H_monotone_extended (high_extended hB) (Y_mem hb he) hy
  have hF := F_lower hb he
  rw [F,angular_actual he] at hF
  dsimp [cost,marker,sign]
  linarith

end SquaresInCircles.Eight.FrameMidHighSourceContact
end
end
end

section
/-!
## The primary axis of the middle/middle pairs

Two middle states separated along the primary axis of the source, at a frame angle `x ≥ -1/20`,
have the cost of the pair above `557/625` for all signs of the source, which enters through its
floor on the whole arc (`primary_negative`, `primary_positive`). The weak margin forces `x > 0`
(`primary_angle_pos`). For a negative target it forces `x > 21/20` (`primary_negative_cut`), and
the cost is at least the smaller of the values at the two ends of the arc (`lowEndpoint`,
`highEndpoint`, `primary_negative_short`). A positive target is impossible in the first quadrant
(`primary_positive_quadrant_false`), and beyond it the cost is at least the support `primaryF x`
of the circle on the second quadrant (`primary_circle_support`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidMidPrimary
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidGeometry FrameMidMidGeometry FrameMidMidScalars

theorem primary_angle_pos (k : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : -(1/20:ℝ)≤x) (hm : 0≤primary k b B x) : 0<x := by
  by_contra! hneg
  have hs := middle_bounds hb
  have ht := middle_bounds hB
  have hsign := negative_signed_sin_le k (x := x) (show 0≤B by linarith [ht.1])
  have habs : |x|≤1/20 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hsin := (Real.abs_sin_le_abs (x := x)).trans habs
  have hsquare := pow_le_pow_left₀ (abs_nonneg x) habs 2
  rw [sq_abs] at hsquare
  have hcos : (799/800:ℝ)≤Real.cos x := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hco0 : 0≤Real.cos x := by linarith
  have hA := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [ht.2.2.1]) hco0
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤7/500 by linarith [ht.2.1]) (abs_nonneg (Real.sin x))
  dsimp [primary,pairWidth] at hm
  rw [abs_of_nonneg hco0] at hm
  linarith

theorem primary_negative_cut {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : -(1/20:ℝ)≤x) (hm : 0≤primary false b B x) :
    (21/20:ℝ)<x := by
  have hx0 := primary_angle_pos false hb hB hx hm
  by_contra! hsmall
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx0.le,by linarith [hsmall,FrameLowPair.pi_lower]⟩
  have hq := FrameLowPair.quadrant hxq
  have hs := middle_bounds hb
  have ht := middle_bounds hB
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx0.le
    (by linarith [FrameLowPair.pi_lower] : (21/20:ℝ)≤Real.pi) hsmall
  have hcos := cos_lower_six (show (0:ℝ)≤21/20 by norm_num)
  norm_num at hcos
  have hco : (49/100:ℝ)<Real.cos x := by linarith
  have hA := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [ht.2.2.1]) hq.2.2.1
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤7/500 by linarith [ht.2.1]) hq.1
  dsimp [primary,sign] at hm
  rw [(first_width hxq).1] at hm
  nlinarith [hq.2.1]

theorem primary_positive_quadrant_false {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤primary true b B x) : False := by
  have hs := middle_bounds hb
  have ht := middle_bounds hB
  have hq := FrameLowPair.quadrant hx
  have hw := (first_width hx).1
  have hsc : 1≤Real.sin x+Real.cos x := by linarith [width_one_le x]
  have hA := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [ht.2.2.1]) hq.2.2.1
  have hB' := mul_le_mul_of_nonneg_right
    (show (4123/5000:ℝ)≤B+1/2 by linarith [ht.1]) hq.1
  dsimp [primary,sign] at hm
  rw [hw] at hm
  nlinarith

def lowEndpoint (x : ℝ) : ℝ :=
  x+59/100+mP+M1+(41/100-b1)*Real.sin x+(41/100+a1)*Real.cos x
def highEndpoint (x : ℝ) : ℝ :=
  x+59/100+mP+M2+(41/100-b2)*Real.sin x+(41/100+a2)*Real.cos x

theorem endpoint_trig {x : ℝ} (hx : x∈Icc (21/20:ℝ) (109/100)) :
    0≤Real.sin x ∧ Real.sin x≤1 ∧ (23/50:ℝ)<Real.cos x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hxq.1
    (by linarith [FrameLowPair.pi_lower] : (109/100:ℝ)≤Real.pi) hx.2
  have hcos := cos_lower_six (show (0:ℝ)≤109/100 by norm_num)
  norm_num at hcos
  exact ⟨ht.1,ht.2.1,by linarith⟩

theorem lowEndpoint_lower {x : ℝ} (hx : x∈Icc (21/20:ℝ) (109/100)) :
    (107/100:ℝ)<lowEndpoint x := by
  have ht := endpoint_trig hx
  have hsin := mul_nonneg (show 0≤41/100-b1 by linarith [b1_bounds.2]) ht.1
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.le
    (show 0≤41/100+a1 by linarith [a1_precise.1])
  dsimp [lowEndpoint,mP]
  nlinarith [hx.1,M_endpoints.1,a1_precise.1]

theorem highEndpoint_lower {x : ℝ} (hx : x∈Icc (21/20:ℝ) (109/100)) :
    (107/100:ℝ)<highEndpoint x := by
  have ht := endpoint_trig hx
  have hsin := mul_le_mul_of_nonpos_left ht.2.1
    (show 41/100-b2≤0 by linarith [b2_bounds.1])
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.le
    (show 0≤41/100+a2 by linarith [a2_bounds.1])
  dsimp [highEndpoint,mP]
  nlinarith [hx.1,M_endpoints.2.2.1,a2_bounds.1,b2_bounds.2]

theorem primary_negative_short (i : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (21/20:ℝ) (109/100)) (hm : 0≤primary false b B x) :
    (557/625:ℝ)<cost i false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := primary_source_lower i hb
  have ht := linear_endpoint_lower (p := p+Real.cos x) (q := q-Real.sin x)
    (by dsimp [p]; linarith [(FrameLowPair.quadrant hxq).2.2.1])
    b1_mem.1 b2_mem.2 hB
  dsimp [linear] at ht
  rw [A_b1,A_b2] at ht
  have hh : min (lowEndpoint x) (highEndpoint x)≤cost i false b B x := by
    rcases le_total ((p+Real.cos x)*a1+(q-Real.sin x)*b1)
      ((p+Real.cos x)*a2+(q-Real.sin x)*b2) with h | h
    · rw [min_eq_left h] at ht
      apply (min_le_left _ _).trans
      have hw := first_width hxq
      simp only [lowEndpoint,cost,primary,M,M1,sign,Bool.false_eq_true,↓reduceIte,hw.1,hw.2]
        at hm hs ⊢
      linarith
    · rw [min_eq_right h] at ht
      apply (min_le_right _ _).trans
      have hw := first_width hxq
      simp only [highEndpoint,cost,primary,M,M2,sign,Bool.false_eq_true,↓reduceIte,hw.1,hw.2]
        at hm hs ⊢
      linarith
  have hlow := (lt_min (lowEndpoint_lower hx) (highEndpoint_lower hx)).trans_le hh
  linarith

theorem primary_negative (i : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : -(1/20:ℝ)≤x) (hm : 0≤primary false b B x) :
    (557/625:ℝ)<cost i false b B x := by
  by_cases htail : (109/100:ℝ)≤x
  · exact (same_tail false hb hB htail).trans_le (weaken_source i false hb)
  · exact primary_negative_short i hb hB
      ⟨(primary_negative_cut hb hB hx hm).le,(lt_of_not_ge htail).le⟩ hm

theorem primary_circle_support (i : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (Real.pi/2) (37/20:ℝ)) (hm : 0≤primary true b B x) :
    primaryF x≤cost i true b B x := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := primary_source_lower i hb
  have ht := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩)
    (-p+Real.cos x) (-q+Real.sin x)
  have hn : Real.sqrt ((-p+Real.cos x)^2+(-q+Real.sin x)^2)=NP x := by
    dsimp [NP,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination Real.sin_sq_add_cos_sq x
  rw [hn] at ht
  dsimp [primaryF,cost,primary,KP,M] at *
  simp only [sign,ite_true,one_mul] at *
  rw [(second_width hxq).1] at hm
  rw [(second_width hxq).2]
  nlinarith

theorem primary_positive (i : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : -(1/20:ℝ)≤x) (hm : 0≤primary true b B x) :
    (557/625:ℝ)<cost i true b B x := by
  by_cases htail : (37/20:ℝ)≤x
  · exact (negative_positive_tail hb hB htail).trans_le (weaken_source i true hb)
  · have hx0 := primary_angle_pos true hb hB hx hm
    have hxq : Real.pi/2<x := by
      by_contra! hfirst
      exact primary_positive_quadrant_false hb hB ⟨hx0.le,hfirst⟩ hm
    have hdom : x∈Icc (Real.pi/2) (37/20:ℝ) := ⟨hxq.le,(lt_of_not_ge htail).le⟩
    exact (primary_lower hdom).trans_le (primary_circle_support i hb hB hdom hm)

end SquaresInCircles.Eight.FrameMidMidPrimary
end
end
end

section
/-!
## The complete middle/middle opposite-sign transverse contact region

The exact parallel minimum is extended to the entire square of middle
coordinates by the two actual marker slopes.  The original separating
margin then controls the distance from the parallel line.  This avoids
an implicit contact curve, minimizer switches, and any angular partition.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidParallel
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidGeometry

def parallelValue : ℝ := M b2+M (1-b2)
def parallelSum (b : ℝ) : ℝ := M b+M (1-b)
def cost (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+M b+M B
def margin (b B x : ℝ) : ℝ :=
  b+A B*Real.sin x+B*Real.cos x-pairWidth x

theorem complement_bounds : b1<1-b2 ∧ 1-b2<b2 := by
  constructor <;> linarith [b1_bounds.2,b2_bounds.1,b2_bounds.2]

theorem complement_mem : 1-b2∈Icc b1 b2 :=
  ⟨complement_bounds.1.le,complement_bounds.2.le⟩

theorem reflected_mem {b : ℝ} (hb : b∈Icc (1-b2) b2) :
    b∈Icc b1 b2 ∧ 1-b∈Icc b1 b2 := by
  refine ⟨⟨complement_bounds.1.le.trans hb.1,hb.2⟩,?_,?_⟩
  · linarith [hb.2,complement_bounds.1]
  · linarith [hb.1]

theorem Md_lower {b : ℝ} (hb : b∈Icc b1 b2) : (69/100:ℝ)<Md b := by
  have hh := slope_mid_bounds hb
  dsimp [Md,p,q]
  linarith

theorem Md_deriv {b : ℝ} (hb : b∈Icc b1 b2) :
    HasDerivAt Md (p*FrameCircleArc.Add b) b := by
  have hh := ((Ad_hasDerivAt ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩
    ).const_mul p).const_add q
  convert hh using 1
  funext y
  simp only [Md,Ad,FrameLowArc.slope]
  ring

theorem marker_growth_lower {b B : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (horder : b≤B) :
    (69/100)*(B-b)≤M B-M b := by
  have hm : MonotoneOn (fun z => M z-(69/100)*z) (Icc b1 b2) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact ((M_deriv hz).sub ((hasDerivAt_id z).const_mul (69/100))).continuousAt.continuousWithinAt
    · intro z hz
      exact (M_deriv (Ioo_subset_Icc_self hz)).sub
        ((hasDerivAt_id z).const_mul (69/100))
    · intro z hz
      linarith [Md_lower (Ioo_subset_Icc_self hz)]
  have hh := hm hb hB horder
  linarith

theorem marker_growth_upper {b B : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (horder : b≤B) :
    M B-M b≤(449/500)*(B-b) := by
  have hm : MonotoneOn (fun z => (449/500)*z-M z) (Icc b1 b2) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact (((hasDerivAt_id z).const_mul (449/500)).sub (M_deriv hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact ((hasDerivAt_id z).const_mul (449/500)).sub
        (M_deriv (Ioo_subset_Icc_self hz))
    · intro z hz
      linarith [(Md_bounds (Ioo_subset_Icc_self hz)).2]
  have hh := hm hb hB horder
  linarith

theorem parallelSum_deriv {b : ℝ} (hb : b∈Icc (1-b2) b2) :
    HasDerivAt parallelSum (Md b-Md (1-b)) b := by
  have hh := reflected_mem hb
  have hr : HasDerivAt (fun z : ℝ => 1-z) (-1) b := by
    simpa using (hasDerivAt_id b).const_sub 1
  have h := (M_deriv hh.1).fun_add ((M_deriv hh.2).comp b hr)
  convert h using 1
  · funext y
    simp only [parallelSum,Function.comp_apply]
  · ring

theorem parallelSum_second {b : ℝ} (hb : b∈Icc (1-b2) b2) :
    HasDerivAt (fun z => Md z-Md (1-z)) (p*FrameCircleArc.Add b+p*FrameCircleArc.Add (1-b)) b := by
  have hh := reflected_mem hb
  have hr : HasDerivAt (fun z : ℝ => 1-z) (-1) b := by
    simpa using (hasDerivAt_id b).const_sub 1
  have h := (Md_deriv hh.1).fun_sub ((Md_deriv hh.2).comp b hr)
  convert h using 1
  · funext y
    simp only [Function.comp_apply]
  · ring

theorem parallelSum_concave : ConcaveOn ℝ (Icc (1-b2) b2) parallelSum := by
  apply concave_of_deriv2 (fun b hb => parallelSum_deriv hb)
    (fun b hb => parallelSum_second hb)
  intro b hb
  have hh := reflected_mem hb
  have h1 := Add_negative ⟨b1_mem.1.trans hh.1.1,hh.1.2.trans b2_mem.2⟩
  have h2 := Add_negative ⟨b1_mem.1.trans hh.2.1,hh.2.2.trans b2_mem.2⟩
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by norm_num [p]) h1.le)
    (mul_nonpos_of_nonneg_of_nonpos (by norm_num [p]) h2.le)

theorem parallel_minimum {b : ℝ} (hb : b∈Icc (1-b2) b2) :
    parallelValue≤M b+M (1-b) := by
  have hh := parallelSum_concave.min_le_of_mem_Icc
    ⟨le_rfl,complement_bounds.2.le⟩ ⟨complement_bounds.2.le,le_rfl⟩ hb
  have hleft : parallelSum (1-b2)=parallelValue := by
    simp [parallelSum,parallelValue,add_comm]
  have hright : parallelSum b2=parallelValue := rfl
  rw [hleft,hright,min_self] at hh
  exact hh

theorem complement_primary_lower : (303904031/250000000:ℝ)<A (1-b2) := by
  have hc := A_circle
    ⟨b1_mem.1.trans complement_mem.1,complement_mem.2.trans b2_mem.2⟩
  have ha := A_mid_bounds complement_mem
  have hb : 0≤(1-b2)+1/2 := by linarith [b2_bounds.2]
  have hbU : (1-b2)+1/2≤3/2-(3/7)*(59962803/50000000:ℝ) := by
    dsimp [b2]
    linarith [a2_bounds.1]
  have hsB := pow_le_pow_left₀ hb hbU 2
  by_contra! hbad
  have hsA := pow_le_pow_left₀ (show 0≤A (1-b2)+1/2 by linarith [ha.1,a2_bounds.1])
    (show A (1-b2)+1/2≤(303904031/250000000:ℝ)+1/2 by linarith) 2
  norm_num [Q0] at hc
  nlinarith

theorem parallelValue_lower : (22281/25000:ℝ)<parallelValue := by
  have ha := complement_primary_lower
  have he : parallelValue=2*cM+q+p*(a2+A (1-b2)) := by
    dsimp [parallelValue,M]
    rw [A_b2]
    ring
  rw [he]
  dsimp [cM,p,q]
  linarith [a2_bounds.1]

/-- A global lower support below the parallel contact line. -/
theorem sum_below_parallel {b B : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (hsum : b+B≤1) :
    parallelValue-(449/500)*(1-b-B)≤M b+M B := by
  by_cases hB0 : 1-b2≤B
  · have hB' : B∈Icc (1-b2) b2 := ⟨hB0,hB.2⟩
    have href := (reflected_mem hB').2
    have hg := marker_growth_upper hb href (by linarith)
    have he := parallel_minimum hB'
    linarith
  · have hg1 := marker_growth_upper hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
    have hg2 := marker_growth_upper hB complement_mem (lt_of_not_ge hB0).le
    dsimp [parallelValue]
    linarith

/-- A global lower support above the parallel contact line. -/
theorem sum_above_parallel {b B : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (hsum : 1≤b+B) :
    parallelValue+(69/100)*(b+B-1)≤M b+M B := by
  have hB' : B∈Icc (1-b2) b2 := ⟨by linarith [hb.2],hB.2⟩
  have href := (reflected_mem hB').2
  have hg := marker_growth_lower href hb (by linarith)
  have he := parallel_minimum hB'
  linarith

theorem positive_deficit {b B x : ℝ} (hB : B∈Icc b1 b2)
    (hx : x∈Icc (0:ℝ) (8/25)) (hm : 0≤ margin b B x) :
    1-b-B≤(20679/25000)*x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hb := middle_bounds hB
  have hs := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hA := mul_le_mul_of_nonneg_right
    (show A B-1/2≤799/1000 by linarith [hb.2.2.2]) ht.1
  have hB' := mul_le_mul_of_nonneg_right
    (show 1/2-B≤22/125 by linarith [hb.1])
    (show 0≤1-Real.cos x by linarith [ht.2.2.2])
  have hx2 := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  dsimp [margin] at hm
  rw [(first_width hxq).1] at hm
  linarith

theorem positive_region {b B x : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (0:ℝ) (8/25)) (hm : 0≤ margin b B x) :
    parallelValue≤cost b B x := by
  have hd := positive_deficit hB hx hm
  have hsum : parallelValue-(449/500)*(20679/25000)*x≤M b+M B := by
    by_cases hs : b+B≤1
    · have hh := sum_below_parallel hb hB hs
      linarith
    · have hh := sum_above_parallel hb hB (lt_of_not_ge hs).le
      linarith [hx.1]
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hcharge : (9/50)*periodicFrameCost x≤(9/100)*x := by
    rw [(first_width hxq).2]
    linarith [Real.sin_le hx.1,Real.cos_le_one x]
  dsimp [cost]
  linarith [hx.1]

theorem negative_surplus {b B z : ℝ} (hB : B∈Icc b1 b2)
    (hz : z∈Icc (0:ℝ) (1/20)) (hm : 0≤ margin b B (-z)) :
    (169/100)*z≤b+B-1 := by
  have hzq : z∈Icc 0 (Real.pi/2) :=
    ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hzq
  have hb := middle_bounds hB
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have hA := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [hb.2.2.1]) ht.1
  have hB' := mul_le_mul_of_nonneg_right
    (show -(22/125:ℝ)≤B-1/2 by linarith [hb.1])
    (show 0≤1-Real.cos z by linarith [ht.2.2.2])
  have hz2 := mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
  have hzsq := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hzsq hz.1
  dsimp [margin,pairWidth] at hm
  simp only [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg ht.1,
    abs_of_nonneg ht.2.2.1] at hm
  nlinarith

theorem negative_region {b B z : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hz : z∈Icc (0:ℝ) (1/20)) (hm : 0≤ margin b B (-z)) :
    parallelValue≤cost b B (-z) := by
  have hd := negative_surplus hB hz hm
  have hsum : 1≤b+B := by linarith [hz.1]
  have hs := sum_above_parallel hb hB hsum
  have hzq : z∈Icc 0 (Real.pi/2) :=
    ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hzq
  have hcharge : (9/50)*periodicFrameCost (-z)≤(9/100)*z := by
    dsimp [periodicFrameCost]
    simp only [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg ht.1,
      abs_of_nonneg ht.2.2.1]
    linarith [Real.sin_le hz.1,Real.cos_le_one z]
  dsimp [cost]
  linarith [hz.1]

/-- The full original contact strip, including both signs of its angle. -/
theorem contact_strip {b B x : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(1/20:ℝ)) (8/25)) (hm : 0≤ margin b B x) :
    (557/625:ℝ)<cost b B x := by
  have hh : parallelValue≤cost b B x := by
    by_cases hp : 0≤x
    · exact positive_region hb hB ⟨hp,hx.2⟩ hm
    · have hz : -x∈Icc (0:ℝ) (1/20) := ⟨by linarith,by linarith [hx.1]⟩
      simpa only [neg_neg] using negative_region hb hB hz (by simpa using hm)
  exact (lt_trans (by norm_num) parallelValue_lower).trans_le hh

end SquaresInCircles.Eight.FrameMidParallel
end
end
end

section
/-!
## The middle/middle pairs

Two states of the closed middle arc, with any signs, separated along any forward axis at a gap of
at least `19/25`, have the cost of the pair above `557/625` (`middle_pair`; `middle_cycle_pair` on
the edges of a boundary cycle at `Q0`). On the secondary axis with two positive ends, the cost is
at least the circle support `F x` for `3/5 ≤ x ≤ 109/100` (`transverse_circle_support`,
`transverse_positive`); with opposite signs, the support of the parallel line bounds it for
`-1/20 ≤ x ≤ 8/25` (`transverse_opposite`); the other cases use the supports of the whole circle
and of the ends of the arc from `FrameMidMidScalars` and `FrameMidMidPrimary`
(`source_secondary`, `source_primary`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidMidPair
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidGeometry FrameMidMidGeometry
open FrameMidMidScalars FrameMidMidPrimary

theorem transverse_circle_support {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (3/5:ℝ) (109/100)) (hm : 0≤ secondary true true b B x) :
    F x≤cost true true b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := transverse_source_lower hb
  have hscaled := mul_nonneg (show (0:ℝ)≤lambda by norm_num [lambda]) hm
  have ht := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩)
    (-p-lambda*Real.sin x) (-q+lambda*Real.cos x)
  have hn : Real.sqrt ((-p-lambda*Real.sin x)^2+(-q+lambda*Real.cos x)^2)=NF x := by
    dsimp [NF,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination lambda^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  dsimp [F,cost,secondary,KF,M] at *
  simp only [sign,ite_true,one_mul] at *
  rw [(first_width hxq).1] at hscaled
  rw [(first_width hxq).2]
  nlinarith

theorem transverse_positive {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (3/5:ℝ) (109/100)) (hm : 0≤ secondary true true b B x) :
    (557/625:ℝ)<cost true true b B x :=
  (transverse_lower hx).trans_le (transverse_circle_support hb hB hx hm)

theorem transverse_opposite {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(1/20:ℝ)) (8/25)) (hm : 0≤ secondary true false b B x) :
    (557/625:ℝ)<cost true false b B x := by
  have hh := FrameMidParallel.contact_strip hb hB hx
    (by simpa [FrameMidParallel.margin,secondary,sign] using hm)
  simpa [FrameMidParallel.cost,cost,sign] using hh

theorem state_cost (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) (x : ℝ) :
    s.cost t x=cost s.positive t.positive s.b t.b x := by
  rw [State.cost,state_mid_label s hs,state_mid_label t ht]
  rfl

theorem state_secondary (s t : FramePair.State) (ht : t.branch=.middle) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤ secondary s.positive t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,(state_mid_chart t ht).1]
  rfl

theorem state_primary (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤primary t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_mid_chart s hs).1,(state_mid_chart t ht).1]
  rfl

theorem source_secondary (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (557/625:ℝ)<s.cost t x := by
  have hb := (state_mid_chart s hs).2
  have hB := (state_mid_chart t ht).2
  have hmargin := (state_secondary s t ht x).mp hm
  have hx := angle_floor s t hs ht hgap
  rw [state_cost s t hs ht]
  revert hmargin
  cases hss : s.positive <;> cases htt : t.positive <;> intro hmargin
  · by_cases htail : (109/100:ℝ)≤x
    · exact same_tail false hb hB htail
    · have hlo := same_sign_angle s t hs ht (by rw [hss,htt]) hgap
      exact False.elim (negative_secondary_false false hb hB
        ⟨by linarith,by linarith [FrameLowPair.pi_lower]⟩ hmargin)
  · by_cases htail : (37/20:ℝ)≤x
    · exact negative_positive_tail hb hB htail
    · have hlo := negative_positive_angle s t hs ht hss htt hgap
      exact False.elim (negative_secondary_false true hb hB
        ⟨by linarith,by linarith [FrameLowPair.pi_lower]⟩ hmargin)
  · by_cases htail : (8/25:ℝ)≤x
    · exact positive_negative_tail hb hB htail
    · exact transverse_opposite hb hB ⟨hx.le,(lt_of_not_ge htail).le⟩ hmargin
  · by_cases htail : (109/100:ℝ)≤x
    · exact same_tail true hb hB htail
    · have hlo := same_sign_angle s t hs ht (by rw [hss,htt]) hgap
      exact transverse_positive hb hB ⟨hlo.le,(lt_of_not_ge htail).le⟩ hmargin

theorem source_primary (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (557/625:ℝ)<s.cost t x := by
  have hb := (state_mid_chart s hs).2
  have hB := (state_mid_chart t ht).2
  have hmargin := (state_primary s t hs ht x).mp hm
  have hx := angle_floor s t hs ht hgap
  rw [state_cost s t hs ht]
  revert hmargin
  cases htt : t.positive with
  | false =>
      intro hmargin
      exact primary_negative s.positive hb hB hx.le hmargin
  | true =>
      intro hmargin
      exact primary_positive s.positive hb hB hx.le hmargin

/-- The middle/middle pair inequality, on every forward axis. -/
theorem middle_pair (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.middle) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(557/625:ℝ) := by
    norm_num [hs,ht,Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_secondary s t hs ht hgap hm
  · have hh := source_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_primary s t hs ht hgap hm

theorem middle_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.middle) (hj : branchOf C (next i)=.middle)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact middle_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.FrameMidMidPair
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighQuarterStrip
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameMidHighContactArc

theorem middle_high {b B x : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (Real.pi/2-1/50) (Real.pi/2+1/50))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost true false false true b B x := by
  let e : ℝ := x-Real.pi/2
  have he : e∈strip := by dsimp [e,strip]; constructor <;> linarith [hx.1,hx.2]
  have hid : Real.pi/2+e=x := by dsimp [e]; ring
  by_cases hn : e≤0
  · have hs : e∈side true := ⟨he.1,hn⟩
    have hh := FrameMidHighTargetContact.actual_lower hb hB hs (by simpa only [hid] using hm)
    simpa only [hid] using hh
  · have hs : e∈side false := ⟨(lt_of_not_ge hn).le,he.2⟩
    have hh := FrameMidHighTargetContact.actual_lower hb hB hs (by simpa only [hid] using hm)
    simpa only [hid] using hh

theorem high_middle {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (Real.pi/2-1/50) (Real.pi/2+1/50))
    (hm : 0≤central false true (A b) b (A B) B x) :
    (4463/5000:ℝ)<cost false true false true b B x := by
  let e : ℝ := x-Real.pi/2
  have he : e∈strip := by dsimp [e,strip]; constructor <;> linarith [hx.1,hx.2]
  have hid : Real.pi/2+e=x := by dsimp [e]; ring
  by_cases hn : e≤0
  · have hs : e∈side true := ⟨he.1,hn⟩
    have hh := FrameMidHighSourceContact.actual_lower hB hb hs (by simpa only [hid] using hm)
    simpa only [hid] using hh
  · have hs : e∈side false := ⟨(lt_of_not_ge hn).le,he.2⟩
    have hh := FrameMidHighSourceContact.actual_lower hB hb hs (by simpa only [hid] using hm)
    simpa only [hid] using hh

end SquaresInCircles.Eight.FrameMidHighQuarterStrip
end
end
end
