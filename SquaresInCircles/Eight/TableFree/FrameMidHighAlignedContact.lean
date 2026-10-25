module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalCuts

/-!
# The actual quarter-turn middle/high contact

The contact sum is evaluated on the original two circle points.  Its
one-variable expression is strictly concave on the entire middle arc.
The two endpoint comparisons use positive square comparisons against
the exact remaining radical.  No contact value is an input hypothesis.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighAlignedContact
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
  concave_of_deriv2 (fun d hd => J_deriv hd) (fun d hd => Jd_deriv hd)
    (fun d hd => (Jdd_negative hd).le)

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

end SquaresInCircles.Eight.TableFree.FrameMidHighAlignedContact
