module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein
public import SquaresInCircles.Eight.Owners.Endpoint.BudgetScalars
public import SquaresInCircles.Eight.Owners.PowerTailBounds
public import SquaresInCircles.Eight.Owners.Stronger.EndpointBudget

/-!
# Eight squares: exterior slopes for the original one-negative middle stress

The two coefficient families (`Weights`) are continuous stresses on their whole domains. All
exterior slope comparisons are proved at the common angle `7/10`, after derivative monotonicity
on the whole angle interval (`negativeSlope_mono`, `positiveSlope_mono`). The varying-weight
reciprocal norm comparison uses one quartic identity on the whole coefficient interval, with
positive Bernstein coefficients. The resulting caps are `lower_exterior_cap` and
`upper_exterior_cap`.
-/

section
/-!
## The strict positive HG charge at the remaining negative-BT endpoint

The two support formulas use the original exact circle radius.  Their
strict lower bounds follow from concavity on each complete analytic
branch and rational Taylor bounds at its endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OneNegativeAnchorCharge
open PositiveAngularEnvelope CorrelatedSameBlock

abbrev R : ℝ := EndpointRotationPenalty.R
abbrev k0 : ℝ := EndpointBudgetScalars.k0
def p : ℝ := 41/40

def short (v : ℝ) : ℝ :=
  p*v-k0*Real.sin v-(1-Real.cos v)/2

def long (v : ℝ) : ℝ :=
  p*v-2*R*Real.sin (v/2)+Real.sin v

def f (v : ℝ) : ℝ := if v≤1/2 then short v else long v

theorem radius_upper : R<(197878751/100000000 : ℝ) := by
  have hs := EndpointRotationPenalty.R_sq
  have hn := EndpointRotationPenalty.R_nonneg
  dsimp [qCap] at hs
  nlinarith

theorem k0_bounds : 0≤k0 ∧ k0<(914576/1000000 : ℝ) := by
  have hh := EndpointBudgetScalars.radical_bounds
  exact ⟨by linarith [hh.1],hh.2.1⟩

@[simp] theorem short_zero : short 0=0 := by simp [short]

theorem short_taylor_lower {v : ℝ} (hv : v∈Icc 0 frameCap) :
    p*v-(914576/1000000)*(v-v^3/6+v^5/120)-
      (1-(1-v^2/2+v^4/24-v^6/720))/2≤ short v := by
  have hm := mul_le_mul k0_bounds.2.le (sin_upper_five hv.1)
    (transport_trig hv).2.2.1 (by norm_num : (0:ℝ)≤914576/1000000)
  have hc := cos_lower_six hv.1
  dsimp [short]
  linarith

theorem short_endpoints :
    (1/250 : ℝ)<short (1/25) ∧ (1/250 : ℝ)<short (1/2) := by
  have hleft := short_taylor_lower
    (show (1/25 : ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hright := short_taylor_lower
    (show (1/2 : ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  norm_num [p] at hleft hright
  constructor <;> linarith

theorem short_concave : ConcaveOn ℝ (Icc 0 (1/2 : ℝ)) short := by
  apply concave_of_deriv2
    (f' := fun v => p-k0*Real.cos v-Real.sin v/2)
    (f'' := fun v => k0*Real.sin v-Real.cos v/2)
  · intro v _
    have hraw := (((hasDerivAt_id v).const_mul p).sub
      ((Real.hasDerivAt_sin v).const_mul k0)).sub
        (((Real.hasDerivAt_cos v).const_sub 1).div_const 2)
    convert hraw using 1
    · rfl
    · ring
  · intro v _
    convert (((hasDerivAt_const v p).sub
      ((Real.hasDerivAt_cos v).const_mul k0)).sub
        ((Real.hasDerivAt_sin v).div_const 2)) using 1
    ring
  · intro v hv
    have hv' : v∈Icc 0 frameCap := ⟨hv.1,by dsimp [frameCap]; linarith [hv.2]⟩
    have hh : (1/2 : ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
    have hs := (sin_mono hv' hh hv.2).trans (sin_upper_five (by norm_num : (0:ℝ)≤1/2))
    have hc := (cos_lower_six (by norm_num : (0:ℝ)≤1/2)).trans (cos_anti hv' hh hv.2)
    have hm := mul_le_mul k0_bounds.2.le hs (transport_trig hv').2.2.1
      (by norm_num : (0:ℝ)≤914576/1000000)
    norm_num at hm hc
    linarith

theorem short_positive {v : ℝ} (hv : v∈Ioc 0 (1/2 : ℝ)) : 0<short v :=
  concave_pos_of_zero_left short_concave hv short_zero (by linarith [short_endpoints.2])

theorem short_reserve {v : ℝ} (hv : v∈Icc (1/25 : ℝ) (1/2)) :
    (1/250 : ℝ)<short v := by
  have hm := short_concave.min_le_of_mem_Icc
    (show (1/25 : ℝ)∈Icc 0 (1/2) by norm_num)
    (show (1/2 : ℝ)∈Icc 0 (1/2) by norm_num) hv
  exact (lt_min short_endpoints.1 short_endpoints.2).trans_le hm

theorem long_taylor_lower {v : ℝ} (hv : v∈Icc 0 frameCap) :
    p*v-2*(197878751/100000000)*
      (v/2-(v/2)^3/6+(v/2)^5/120)+
      (v-v^3/6+v^5/120-v^7/5040)≤long v := by
  have hh : v/2∈Icc 0 frameCap := by
    constructor <;> dsimp [frameCap] at * <;> linarith [hv.1,hv.2]
  have hm := mul_le_mul radius_upper.le (sin_upper_five hh.1)
    (transport_trig hh).2.2.1 (by norm_num : (0:ℝ)≤197878751/100000000)
  have hs := sin_lower_seven hv.1
  dsimp [long]
  linarith

theorem long_endpoints :
    (1/250 : ℝ)<long (1/2) ∧ (1/250 : ℝ)<long frameCap := by
  have hleft := long_taylor_lower
    (show (1/2 : ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hright := long_taylor_lower
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  norm_num [p,frameCap] at hleft hright
  constructor <;> linarith

theorem long_concave : ConcaveOn ℝ (Icc (1/2 : ℝ) frameCap) long := by
  apply concave_of_deriv2
    (f' := fun v => p-R*Real.cos (v/2)+Real.cos v)
    (f'' := fun v => (R/2)*Real.sin (v/2)-Real.sin v)
  · intro v _
    have hh : HasDerivAt (fun x : ℝ => x/2) (1/2) v := (hasDerivAt_id' v).div_const 2
    have hraw : HasDerivAt long (p*1-2*R*(Real.cos (v/2)*(1/2))+Real.cos v) v :=
      (((hasDerivAt_id' v).const_mul p).fun_sub
        (hh.sin.const_mul (2*R))).fun_add (Real.hasDerivAt_sin v)
    convert hraw using 1
    ring
  · intro v _
    have hh : HasDerivAt (fun x : ℝ => x/2) (1/2) v := (hasDerivAt_id' v).div_const 2
    have hraw : HasDerivAt (fun v => p-R*Real.cos (v/2)+Real.cos v)
        (0-R*(-Real.sin (v/2)*(1/2))+-Real.sin v) v :=
      (((hasDerivAt_const v p).fun_sub (hh.cos.const_mul R))).fun_add (Real.hasDerivAt_cos v)
    convert hraw using 1
    ring
  · intro v hv
    have hh : v/2∈Icc 0 frameCap := by
      constructor <;> dsimp [frameCap] at * <;> linarith [hv.1,hv.2]
    obtain ⟨hc,_,hs,_,_⟩ := transport_trig hh
    have hr : R<2 := by linarith [radius_upper]
    have hm := mul_nonneg hs (show 0≤2*Real.cos (v/2)-R/2 by linarith)
    have hid : Real.sin v=2*Real.sin (v/2)*Real.cos (v/2) := by
      calc
        Real.sin v=Real.sin (v/2+v/2) := by congr 1; ring
        _=2*Real.sin (v/2)*Real.cos (v/2) := by rw [Real.sin_add]; ring
    show (R/2)*Real.sin (v/2)-Real.sin v ≤ 0
    rw [hid]
    linarith

theorem long_reserve {v : ℝ} (hv : v∈Icc (1/2 : ℝ) frameCap) :
    (1/250 : ℝ)<long v :=
  (lt_min long_endpoints.1 long_endpoints.2).trans_le
    (long_concave.min_le_of_mem_Icc
      (show (1/2 : ℝ)∈Icc (1/2) frameCap by norm_num [frameCap])
      (show frameCap∈Icc (1/2 : ℝ) frameCap by norm_num [frameCap]) hv)

theorem f_of_short {v : ℝ} (hv : v≤1/2) : f v=short v := by
  simp only [f,ite_eq_left hv]

theorem f_of_long {v : ℝ} (hv : 1/2<v) : f v=long v := by
  simp only [f,ite_eq_right (not_le.mpr hv)]

/-- Positive at every original strictly positive HG error. -/
theorem f_pos {v : ℝ} (hv : v∈Ioc 0 frameCap) : 0<f v := by
  by_cases hshort : v≤1/2
  · rw [f_of_short hshort]
    exact short_positive ⟨hv.1,hshort⟩
  · rw [f_of_long (lt_of_not_ge hshort)]
    have hh := long_reserve ⟨(lt_of_not_ge hshort).le,hv.2⟩
    linarith

/-- The strict reserve needed by the varying-weight middle endpoint. -/
theorem f_reserve {v : ℝ} (hv : v∈Icc (1/25 : ℝ) frameCap) :
    (1/250 : ℝ)<f v := by
  by_cases hshort : v≤1/2
  · rw [f_of_short hshort]
    exact short_reserve ⟨hv.1,hshort⟩
  · rw [f_of_long (lt_of_not_ge hshort)]
    exact long_reserve ⟨(lt_of_not_ge hshort).le,hv.2⟩

end SquaresInCircles.Eight.OneNegativeAnchorCharge
end
end
end

section
/-!
## The whole-interval middle endpoint for one negative BT contact

The certificate is the displayed degree-ten rational polynomial, with
one coefficient norm on the whole centered interval `|x|≤41/100`.
Its positive quadratic lower bound is proved by completing a square.
Positive scalar tangents then transfer the certificate directly to the
two original trigonometric norms, retaining their exact common radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.OneNegativeAnchorPolynomial
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open Polynomial PowerTailBounds

abbrev R : ℝ := EndpointRotationPenalty.R
abbrev p : ℝ := OneNegativeAnchorCharge.p
abbrev S0 : ℝ := EndpointBudgetScalars.S0

def MB (l mu L : ℝ) : ℝ :=
  R*(pairNorm 1 l (-L)+pairNorm mu l 0)-1/2-3*mu/2-2*l-Real.cos L+
    (1-mu)*(39/250)+p*L-S0

def MG (l mu L : ℝ) : ℝ :=
  R*(pairNorm 1 l 0+pairNorm mu l (-L))-3/2-3*mu/2-l-l*Real.cos L+
    (1-mu)*(39/250)+p*L-S0

def Rplus : ℚ := 197878751/100000000
def Sminus : ℚ := 41502562/100000000
def center : ℚ := 29/100
def span : ℚ := 41/100

def z : ℚ[X] := C center+X
def weight : ℚ[X] := C (59/100)+C (1/2)*z
def r0 : ℚ[X] := C (1241058016/1000000000)+
  C (296118308/1000000000)*X+C (65393376/1000000000)*X^2
def r1 : ℚ[X] := C (1058241574/1000000000)-
  C (453379807/1000000000)*X-C (332448780/1000000000)*X^2

def S7 : ℚ[X] := z-C (1/6)*z^3+C (1/120)*z^5-C (1/5040)*z^7
def C6 : ℚ[X] := 1-C (1/2)*z^2+C (1/24)*z^4-C (1/720)*z^6
def radicandNegative : ℚ[X] := 1+weight^2-C 2*weight*S7
def radicandZero : ℚ[X] := 1+weight^2
def target : ℚ[X] :=
  C 2+C 2*weight+C6+C (Sminus+1/250)-C (41/40)*z
def certificate : ℚ[X] :=
  C 2*r0*r1*target-C Rplus*
    (r1*(radicandZero+r0^2)+r0*(radicandNegative+r1^2))

def sine7 (t : ℝ) : ℝ := t-t^3/6+t^5/120-t^7/5040
def cosine6 (t : ℝ) : ℝ := 1-t^2/2+t^4/24-t^6/720

theorem radius_reserves : R<(Rplus:ℝ) ∧ (Sminus:ℝ)<S0 := by
  constructor
  · simpa only [Rplus,Rat.cast_div,Rat.cast_ofNat] using OneNegativeAnchorCharge.radius_upper
  · have hs := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
    have hn := Real.sqrt_nonneg (qCap-1)
    dsimp [Sminus,S0,EndpointBudgetScalars.S0,qCap] at *
    nlinarith

/-- The eleven coefficients of the certificate, by evaluation. -/
private lemma r28_cert_eq : certificate=
    C (11476260499286278890699450261167/22500000000000000000000000000000000)+
    C (52000018626414935921894995528781/100000000000000000000000000000000000)*X+
    C (2423520721149005874853655522318203/18750000000000000000000000000000000)*X^2-
    C (446747893503226327402945712059841/75000000000000000000000000000000000)*X^3-
    C (536156806252004849727279466093177/4687500000000000000000000000000000)*X^4-
    C (131388114650132076250405430869347/1562500000000000000000000000000000)*X^5-
    C (3495706604173550739450136664731/117187500000000000000000000000000)*X^6-
    C (902753809673662971167/250000000000000000000000)*X^7+
    C (2044549171344678359/7500000000000000000000)*X^8+
    C (114644842028341799/450000000000000000000)*X^9+
    C (26035666269703/750000000000000000)*X^10 := by
  apply Polynomial.funext
  intro r
  simp only [certificate,target,radicandZero,radicandNegative,r0,r1,weight,z,S7,C6,
    Rplus,Sminus,center,eval_sub,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one]
  ring

private lemma r28_c0 : certificate.coeff 0=(11476260499286278890699450261167/22500000000000000000000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c1 : certificate.coeff 1=(52000018626414935921894995528781/100000000000000000000000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c2 : certificate.coeff 2=(2423520721149005874853655522318203/18750000000000000000000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c3 : certificate.coeff 3=(-446747893503226327402945712059841/75000000000000000000000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c4 : certificate.coeff 4=(-536156806252004849727279466093177/4687500000000000000000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c5 : certificate.coeff 5=(-131388114650132076250405430869347/1562500000000000000000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c6 : certificate.coeff 6=(-3495706604173550739450136664731/117187500000000000000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c7 : certificate.coeff 7=(-902753809673662971167/250000000000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c8 : certificate.coeff 8=(2044549171344678359/7500000000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c9 : certificate.coeff 9=(114644842028341799/450000000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

private lemma r28_c10 : certificate.coeff 10=(26035666269703/750000000000000000:ℚ) := by
  rw [r28_cert_eq]
  simp only [coeff_add,coeff_sub,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X]
  norm_num

theorem expansion_identity :
    certificate=C (certificate.coeff 0)+C (certificate.coeff 1)*X+
      C (certificate.coeff 2)*X^2+tail certificate 3 8 := by
  simp only [tail,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,Nat.reduceAdd,
    zero_add,r28_c0,r28_c1,r28_c2,r28_c3,r28_c4,r28_c5,r28_c6,r28_c7,r28_c8,r28_c9,r28_c10]
  conv_lhs => rw [r28_cert_eq]
  simp only [neg_div,map_neg]
  ring

theorem coefficient_reserves :
    (51/100000 : ℚ)<certificate.coeff 0 ∧
      |certificate.coeff 1|<521/1000000 ∧
      (1009/10000 : ℚ)<certificate.coeff 2-
        PowerTailBounds.norm certificate 3 8 span := by
  simp only [PowerTailBounds.norm,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,
    Nat.reduceAdd,zero_add,r28_c0,r28_c1,r28_c2,r28_c3,r28_c4,r28_c5,r28_c6,r28_c7,r28_c8,r28_c9,r28_c10,span]
  norm_num [abs_of_pos,abs_of_neg]

/-- One completed square proves the strict degree-ten reserve for every
real point of the centered interval. -/
theorem polynomial_positive {x : ℝ} (hx : |x|≤(span:ℝ)) :
    (509/1000000 : ℝ)<aeval x certificate := by
  have hbound := quadratic_lower expansion_identity
    (show (0:ℚ) ≤ span by norm_num [span]) hx
  have hc0 : (51/100000 : ℝ)<(certificate.coeff 0:ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr coefficient_reserves.1
    push_cast at h; exact h
  have hc1 : |(certificate.coeff 1:ℝ)|<521/1000000 := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr coefficient_reserves.2.1
    push_cast at h; exact h
  have hc2 : (1009/10000 : ℝ)<(certificate.coeff 2:ℝ)-
      (PowerTailBounds.norm certificate 3 8 span:ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr coefficient_reserves.2.2
    push_cast at h; exact h
  have hlinear : -(521/1000000)*|x|≤(certificate.coeff 1:ℝ)*x := by
    have hm := mul_le_mul_of_nonneg_right hc1.le (abs_nonneg x)
    rw [← abs_mul] at hm
    linarith [(abs_le.mp hm).1]
  have hquadratic := mul_le_mul_of_nonneg_right hc2.le (sq_nonneg x)
  nlinarith [sq_nonneg (|x|-(521/201800 : ℝ)),sq_abs x]

theorem auxiliary_positive {x : ℝ} (hx : |x|≤(span:ℝ)) :
    (102/125 : ℝ)<aeval x r0 ∧ (102/125 : ℝ)<aeval x r1 := by
  have hx' : -(41/100 : ℝ)≤x ∧ x≤41/100 := by
    simpa only [span,Rat.cast_div,Rat.cast_ofNat] using abs_le.mp hx
  have hx2 : x^2≤(41/100 : ℝ)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg x) hx 2
    simpa only [sq_abs,span,Rat.cast_div,Rat.cast_ofNat] using hh
  simp only [r0,r1,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X]
  norm_num
  constructor <;> nlinarith [sq_nonneg x,hx'.1,hx'.2]

@[simp] theorem S7_eval (x : ℝ) : aeval x S7=sine7 (aeval x z) := by
  simp [S7,sine7]
  ring

@[simp] theorem C6_eval (x : ℝ) : aeval x C6=cosine6 (aeval x z) := by
  simp [C6,cosine6]
  ring

theorem certificate_eval (x : ℝ) : aeval x certificate=
    2*aeval x r0*aeval x r1*
      (2+2*aeval x weight+cosine6 (aeval x z)+(Sminus:ℝ)+1/250-p*aeval x z)-
    (Rplus:ℝ)*(aeval x r1*(1+(aeval x weight)^2+(aeval x r0)^2)+
      aeval x r0*(1+(aeval x weight)^2-
        2*aeval x weight*sine7 (aeval x z)+(aeval x r1)^2)) := by
  simp only [certificate,target,radicandZero,radicandNegative,map_add,map_sub,map_mul,
    map_pow,map_one,aeval_C,C6_eval,S7_eval,eq_ratCast]
  push_cast
  simp only [p,OneNegativeAnchorCharge.p]
  ring

/-- The two positive tangent masses are used algebraically; they need not
approximate either original norm. -/
theorem two_norms {n0 n1 A0 A1 e m0 m1 : ℝ}
    (hn0 : 0≤n0) (hn1 : 0≤n1) (hA0 : n0^2≤A0) (hA1 : n1^2≤A1)
    (hm0 : 0< m0) (hm1 : 0< m1)
    (hcertificate : 0<2*m0*m1*e-(Rplus:ℝ)*
      (m1*(A0+m0^2)+m0*(A1+m1^2))) :
    R*(n0+n1)<e := by
  have hRplus : 0≤(Rplus:ℝ) := by norm_num [Rplus]
  have h0 : 2*m0*n0≤A0+m0^2 := by nlinarith [sq_nonneg (n0-m0)]
  have h1 : 2*m1*n1≤A1+m1^2 := by nlinarith [sq_nonneg (n1-m1)]
  have h0w := mul_le_mul_of_nonneg_left h0 (mul_nonneg hRplus hm1.le)
  have h1w := mul_le_mul_of_nonneg_left h1 (mul_nonneg hRplus hm0.le)
  have hR := mul_le_mul_of_nonneg_right radius_reserves.1.le (add_nonneg hn0 hn1)
  have hscale : 0<2*m0*m1 := by positivity
  have hRw := mul_le_mul_of_nonneg_left hR hscale.le
  have hkey : 2*m0*m1*(R*(n0+n1))<2*m0*m1*e := by linarith
  exact lt_of_mul_lt_mul_left hkey hscale.le

theorem negative_norm_upper {l L : ℝ} (hl : 0<l) (hL : L∈Icc 0 frameCap) :
    (pairNorm 1 l (-L))^2≤1+l^2-2*l*sine7 L := by
  have hN := pairNorm_sq (show (0:ℝ)<1 by norm_num) hl
    (show |-L|≤frameCap by rw [abs_neg,abs_of_nonneg hL.1]; exact hL.2)
  have hm := mul_le_mul_of_nonneg_left (sin_lower_seven hL.1)
    (show 0≤2*l by positivity)
  simp only [pairEnergy,pairProduct,Real.sin_neg,one_pow,one_mul] at hN
  dsimp [sine7]
  nlinarith

/-- The exact varying-weight endpoint is below `.004` on the complete
large interval; all Taylor directions and radical comparisons are
proved inside this theorem. -/
theorem large_MB {L : ℝ} (hL : L∈Icc (1/25 : ℝ) frameCap) :
    MB (59/100+L/2) 1 L<(1/250 : ℝ) := by
  let x : ℝ := L-29/100
  let l : ℝ := 59/100+L/2
  have hx : |x|≤(span:ℝ) := by
    rw [abs_le]
    dsimp [x,span,frameCap] at *
    constructor <;> linarith [hL.1,hL.2]
  have hz : aeval x z=L := by simp [z,center,x]
  have hw : aeval x weight=l := by
    simp [weight,hz,l]
    ring
  have hL' : L∈Icc 0 frameCap := ⟨by linarith [hL.1],hL.2⟩
  have hl : 0<l := by dsimp [l]; linarith [hL.1]
  have hP : 0<aeval x certificate := by linarith [polynomial_positive hx]
  rw [certificate_eval,hz,hw] at hP
  obtain ⟨h0,h1⟩ := auxiliary_positive hx
  have hNZ : (pairNorm 1 l 0)^2=1+l^2 := by
    simpa [pairEnergy,pairProduct] using pairNorm_sq (show (0:ℝ)<1 by norm_num) hl
      (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hNN := negative_norm_upper hl hL'
  have hnorm := two_norms (n0 := pairNorm 1 l 0) (n1 := pairNorm 1 l (-L))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hNZ.le hNN (by linarith : 0<aeval x r0) (by linarith : 0<aeval x r1) hP
  have hcos := cos_lower_six hL'.1
  have hS := radius_reserves.2
  change MB l 1 L<(1/250 : ℝ)
  dsimp only [MB]
  dsimp only [cosine6] at hnorm
  linarith

theorem MG_le_MB {l L : ℝ} (hl : l≤1) : MG l 1 L≤MB l 1 L := by
  have hm := mul_nonneg (sub_nonneg.mpr hl)
    (show 0≤1-Real.cos L by linarith [Real.cos_le_one L])
  dsimp [MG,MB]
  norm_num
  nlinarith

theorem large_endpoints {L : ℝ} (hL : L∈Icc (1/25 : ℝ) frameCap) :
    MB (59/100+L/2) 1 L<(1/250 : ℝ) ∧
      MG (59/100+L/2) 1 L<(1/250 : ℝ) := by
  have hB := large_MB hL
  exact ⟨hB,(MG_le_MB (by dsimp [frameCap] at hL; linarith [hL.2])).trans_lt hB⟩

def negativeSupport (a b c t : ℝ) : ℝ :=
  R*pairNorm a b (-t)-c*Real.cos t

/-- Negative-angle convexity remains valid when the cosine coefficient
is only the smaller norm coefficient.  The strict gap is `.7648-.762`.
This is also the convexity used by the original A-frame concentration. -/
theorem negativeSupport_convex {a b c : ℝ} (ha : 0<a) (hb : 0<b) (hbc : b≤c) :
    ConvexOn ℝ (Icc 0 frameCap) (negativeSupport a b c) := by
  let d (t : ℝ) := -R*normD1 a b (-t)+c*Real.sin t
  let dd (t : ℝ) := R*normD2 a b (-t)+c*Real.cos t
  have hd (t : ℝ) (ht : t∈Icc 0 frameCap) :
      HasDerivAt (negativeSupport a b c) (d t) t := by
    have hn := (pairNorm_hasDerivAt ha hb
      (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)).comp t
        (hasDerivAt_id t).neg
    convert (hn.const_mul R).sub ((Real.hasDerivAt_cos t).const_mul c) using 1
    · rfl
    · dsimp [d]
      ring
  have hdd (t : ℝ) (ht : t∈Icc 0 frameCap) : HasDerivAt d (dd t) t := by
    have hn := (normD1_hasDerivAt ha hb
      (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)).comp t
        (hasDerivAt_id t).neg
    convert (hn.const_mul (-R)).add ((Real.hasDerivAt_sin t).const_mul c) using 1
    · rfl
    · dsimp [dd]
      ring
  have hswap : curvatureZero R a b=curvatureZero R b a := by
    dsimp [curvatureZero,pairProduct]
    rw [pairNorm_symm a b 0]
    ring
  have hzero : curvatureZero R a b<(381/500)*b := by
    rw [hswap,(curvature_constants_normalize (R := R) hb ha).1]
    rw [mul_comm (381/500:ℝ) b]
    exact mul_lt_mul_of_pos_left
      (shapeC0p_lt EndpointRotationPenalty.R_sq.le) hb
  have hnonneg (t : ℝ) (ht : t∈Icc 0 frameCap) : 0≤dd t := by
    have hcurv := curvature_negative_upper EndpointRotationPenalty.R_nonneg ha hb
      (show -t∈Icc (-frameCap) 0 by constructor <;> linarith [ht.1,ht.2])
    have hc := (transport_trig ht).1
    have hcos := mul_lt_mul_of_pos_left hc hb
    have hcoefficient := mul_le_mul_of_nonneg_right hbc (show 0≤Real.cos t by linarith)
    dsimp [dd,curvature] at hcurv ⊢
    nlinarith
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 frameCap)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => (hdd t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => hnonneg t (interior_subset ht))

theorem add_affine_convex {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Icc 0 frameCap) g) (a b : ℝ) :
    ConvexOn ℝ (Icc 0 frameCap) (fun t => g t+a*t+b) := by
  have ha := (affine_concave (-a) (-b) 0 frameCap).neg
  convert hg.add ha using 1
  funext t
  simp only [Pi.add_apply,Pi.neg_apply]
  ring

theorem MB_convex {l mu : ℝ} (hl : 0<l) (_hmu : 0< mu) (hl1 : l≤1) :
    ConvexOn ℝ (Icc 0 frameCap) (MB l mu) := by
  have hc := negativeSupport_convex (show (0:ℝ)<1 by norm_num) hl hl1
  convert add_affine_convex hc p
    (R*pairNorm mu l 0-1/2-3*mu/2-2*l+(1-mu)*(39/250)-S0) using 1
  funext L
  dsimp [MB,negativeSupport]
  ring

theorem MG_convex {l mu : ℝ} (hl : 0<l) (hmu : 0< mu) :
    ConvexOn ℝ (Icc 0 frameCap) (MG l mu) := by
  have hc := negativeSupport_convex hmu hl (show l≤l from le_rfl)
  convert add_affine_convex hc p
    (R*pairNorm 1 l 0-3/2-3*mu/2-l+(1-mu)*(39/250)-S0) using 1
  funext L
  dsimp [MG,negativeSupport]
  ring

theorem small_norm_bounds :
    pairNorm 1 (121/200) 0<(1168770722/1000000000 : ℝ) ∧
      pairNorm (47/50) (121/200) 0<(1117866272/1000000000 : ℝ) ∧
      pairNorm 1 (121/200) (-(1/25))<(1147884100/1000000000 : ℝ) ∧
      pairNorm (47/50) (121/200) (-(1/25))<(1097333647/1000000000 : ℝ) := by
  have key : ∀ {a b t c : ℝ},0<a → 0<b → |t|≤frameCap → 0≤c →
      pairEnergy a b+2*pairProduct a b*Real.sin t<c^2 → pairNorm a b t<c := by
    intro a b t c ha hb ht hc h
    rw [← pairNorm_sq ha hb ht] at h
    exact lt_of_pow_lt_pow_left₀ 2 hc h
  have hz : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have he : |-(1/25 : ℝ)|≤frameCap := by norm_num [frameCap]
  have hs := sin_lower_seven (show (0:ℝ)≤1/25 by norm_num)
  norm_num at hs
  refine ⟨key (by norm_num) (by norm_num) hz (by norm_num) ?_,
    key (by norm_num) (by norm_num) hz (by norm_num) ?_,
    key (by norm_num) (by norm_num) he (by norm_num) ?_,
    key (by norm_num) (by norm_num) he (by norm_num) ?_⟩
  · simp only [pairEnergy,pairProduct,Real.sin_zero]; norm_num
  · simp only [pairEnergy,pairProduct,Real.sin_zero]; norm_num
  · simp only [pairEnergy,pairProduct,Real.sin_neg]; linarith
  · simp only [pairEnergy,pairProduct,Real.sin_neg]; linarith

theorem small_zero :
    MB (121/200) (47/50) 0< -(8968/10000000 : ℝ) ∧
      MG (121/200) (47/50) 0< -(8968/10000000 : ℝ) := by
  have hnorm : pairNorm 1 (121/200) 0+pairNorm (47/50) (121/200) 0≤
      (1168770722/1000000000 : ℝ)+1117866272/1000000000 := by
    linarith [small_norm_bounds.1,small_norm_bounds.2.1]
  have hm := mul_le_mul_of_nonneg_left hnorm EndpointRotationPenalty.R_nonneg
  have hr := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<1168770722/1000000000+1117866272/1000000000 by norm_num)
  have hs := radius_reserves.2
  simp only [MB,MG,neg_zero,Real.cos_zero,mul_zero,add_zero,mul_one]
  norm_num [Rplus,Sminus,p,OneNegativeAnchorCharge.p] at hr hs
  constructor <;> linarith

theorem small_cap :
    MB (121/200) (47/50) (1/25)< -(4271/10000000 : ℝ) ∧
      MG (121/200) (47/50) (1/25)< -(426/10000000 : ℝ) := by
  have hnormB : pairNorm 1 (121/200) (-(1/25))+pairNorm (47/50) (121/200) 0≤
      (1147884100/1000000000 : ℝ)+1117866272/1000000000 := by
    linarith [small_norm_bounds.2.2.1,small_norm_bounds.2.1]
  have hnormG : pairNorm 1 (121/200) 0+pairNorm (47/50) (121/200) (-(1/25))≤
      (1168770722/1000000000 : ℝ)+1097333647/1000000000 := by
    linarith [small_norm_bounds.1,small_norm_bounds.2.2.2]
  have hmB := mul_le_mul_of_nonneg_left hnormB EndpointRotationPenalty.R_nonneg
  have hmG := mul_le_mul_of_nonneg_left hnormG EndpointRotationPenalty.R_nonneg
  have hrB := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<1147884100/1000000000+1117866272/1000000000 by norm_num)
  have hrG := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<1168770722/1000000000+1097333647/1000000000 by norm_num)
  have hs := radius_reserves.2
  have hc := cos_lower_six (show (0:ℝ)≤1/25 by norm_num)
  dsimp only [MB,MG]
  norm_num [Rplus,Sminus,p,OneNegativeAnchorCharge.p] at hrB hrG hs hc
  simp only [p,OneNegativeAnchorCharge.p]
  constructor <;> linarith

/-- Both constant-family endpoints are strictly negative throughout the
whole short interval, including both weak interval endpoints. -/
theorem small_endpoints {L : ℝ} (hL : L∈Icc 0 (1/25 : ℝ)) :
    MB (121/200) (47/50) L<0 ∧ MG (121/200) (47/50) L<0 := by
  have hB := (MB_convex (show (0:ℝ)<121/200 by norm_num)
    (show (0:ℝ)<47/50 by norm_num) (show (121/200:ℝ)≤1 by norm_num)).neg
  have hG := (MG_convex (show (0:ℝ)<121/200 by norm_num)
    (show (0:ℝ)<47/50 by norm_num)).neg
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hcap : (1/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hminB := hB.min_le_of_mem_Icc hzero hcap hL
  have hminG := hG.min_le_of_mem_Icc hzero hcap hL
  simp only [Pi.neg_apply] at hminB hminG
  have hpB : 0 < min (-MB (121/200) (47/50) 0) (-MB (121/200) (47/50) (1/25)) := by
    exact lt_min (by linarith [small_zero.1]) (by linarith [small_cap.1])
  have hpG : 0 < min (-MG (121/200) (47/50) 0) (-MG (121/200) (47/50) (1/25)) := by
    exact lt_min (by linarith [small_zero.2]) (by linarith [small_cap.2])
  exact ⟨by linarith [hpB.trans_le hminB],by linarith [hpG.trans_le hminG]⟩

end SquaresInCircles.Eight.OneNegativeAnchorPolynomial
end
end
end

section
/-!
## The sharper HG charge at the original signed source

Both weak HG owners are handled with the original endpoint circles, and the signed G tangent is
kept (`positive_zero`, `positive_HG_charge`). The short span uses the transverse corner floor and
the long span the full-circle support, which gives exactly the positive function
`OneNegativeAnchorCharge.f`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace OneNegativeHGCharge
open PositiveAngularEnvelope EndpointECharge EndpointBudgetScalars OneNegativeAnchorCharge

theorem point_remainder {P : SignedPoint} {v : ℝ}
    (hP : P.Sorted) (hc : P.circle≤qCap) (hv : v∈Icc 0 frameCap) :
    (P.a-1/2)*Real.sin v+(|P.y|+1/2)*(1-Real.cos v)≤p*v-OneNegativeAnchorCharge.f v := by
  by_cases hvh : v≤1/2
  · have hs := restricted_support
      (show 0≤P.a+1/2 by linarith [hP.1])
      (show 1/2≤|P.y|+1/2 by linarith [abs_nonneg P.y]) hc ⟨hv.1,hvh⟩
    rw [f_of_short hvh]
    dsimp only [short,positiveGain,OneNegativeAnchorCharge.k0] at hs ⊢
    linarith
  · have hs := circle_chord_support hc hv
    rw [f_of_long (lt_of_not_ge hvh)]
    dsimp only [long,OneNegativeAnchorCharge.R] at hs ⊢
    linarith

/-- A positive HG error yields the strict-excess charge for either original transverse owner,
for either sign of G. -/
theorem positive_zero {H G : SignedPoint} {v : ℝ}
    (hH : H.Sorted) (hG : G.Sorted)
    (hcH : H.circle≤qCap) (hcG : G.circle≤qCap)
    (hv : v∈Icc 0 frameCap)
    (hHG : zeroFeasible H G v 0 ∨ zeroFeasible H G v 2) :
    1+OneNegativeAnchorCharge.f v-p*v≤H.y-G.y := by
  have hw := edgeWidth_positive_formula hv
  have hcos : 0≤1-Real.cos v := by linarith [Real.cos_le_one v]
  rcases hHG with hHG | hHG
  · have hf : edgeWidth v≤H.y+G.a*Real.sin v-G.y*Real.cos v := by
      simpa [zeroFeasible,zeroProjection] using hHG
    have hsupport := point_remainder hG hcG hv
    have hsigned := mul_le_mul_of_nonneg_right (le_abs_self G.y) hcos
    rw [hw] at hf
    nlinarith
  · have hf : edgeWidth v≤H.a*Real.sin v+H.y*Real.cos v-G.y := by
      simpa [zeroFeasible,zeroProjection] using hHG
    have hsupport := point_remainder hH hcH hv
    have hsigned := mul_le_mul_of_nonneg_right (neg_le_abs H.y) hcos
    rw [hw] at hf
    nlinarith

end OneNegativeHGCharge

namespace SignedCycle
open Candidate EndpointBudgetScalars OneNegativeAnchorCharge

private theorem r60_feasible_zero {C : SignedCycle} {i : Vertex} (hw : Candidate.word i=0)
    (j : Fin 4) : C.Feasible i j ↔
      zeroFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,zeroFeasible,delta,sub_nonneg]

theorem positive_HG_charge {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (w : C.Witnesses)
    (hv : C.theta H≤C.theta G) :
    1+OneNegativeAnchorCharge.f (C.theta G-C.theta H)-p*(C.theta G-C.theta H)≤
      (C.point H).y-(C.point G).y := by
  have ho : w.owner H=0 ∨ w.owner H=2 := by
    simpa [normalOwners,H] using w.allowed H
  have hf : zeroFeasible (C.point H) (C.point G) (C.theta G-C.theta H) 0 ∨
      zeroFeasible (C.point H) (C.point G) (C.theta G-C.theta H) 2 := by
    have hw := (r60_feasible_zero (C := C) (i := H) (by decide) _).1 (w.feasible H)
    rw [show next H=G by decide] at hw
    rcases ho with ho | ho
    · left
      rwa [ho] at hw
    · right
      rwa [ho] at hw
  exact OneNegativeHGCharge.positive_zero (hC.sorted H) (hC.sorted G)
    ((hC.contained H).trans hq) ((hC.contained G).trans hq)
    ⟨sub_nonneg.mpr hv,(le_abs_self _).trans (hC.spread G H)⟩ hf

/-- The original H/D/E budget plus the original positive HG charge and aligned TD. The
nonnegative H--D deficit cancels exactly. -/
theorem positive_one_negative_excess {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (ha : C.NormalAnchors)
    (hyE : (C.point E).y≤0) (w : C.Witnesses)
    (halign : C.theta T=C.theta D) (hHG : C.theta H≤C.theta G) :
    S0+OneNegativeAnchorCharge.f (C.theta G-C.theta H)+(27/160000 : ℝ)<
      -(C.point G).y+(C.point T).y+p*(C.theta G-C.theta D) := by
  have hHGcharge := positive_HG_charge hq hC w hHG
  have hbudget := stronger_endpoint_budget hq hC ha hyE w
  have ho : w.owner T=0 ∨ w.owner T=2 := by
    simpa [normalOwners,T] using w.allowed T
  have hTD : 1≤(C.point T).y-(C.point D).y := by
    have hw := (r60_feasible_zero (C := C) (i := T) (by decide) _).1 (w.feasible T)
    rw [show next T=D by decide,halign,sub_self] at hw
    simp only [zeroFeasible,zeroProjection_aligned,edgeWidth_zero] at hw
    rcases ho with ho | ho <;> rw [ho] at hw <;> simpa using hw
  dsimp [StrongerEndpointScalars.charge,StrongerEndpointScalars.epsilon,p] at *
  linarith

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OneNegativeAnchorConcentration
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope

abbrev R : ℝ := EndpointRotationPenalty.R
abbrev negativeSupport := OneNegativeAnchorPolynomial.negativeSupport

/-- The exact two stresses used in the anchor-order argument. -/
def Weights (l mu L : ℝ) : Prop :=
  (L∈Icc 0 (1/25 : ℝ) ∧ l=121/200 ∧ mu=47/50) ∨
  (L∈Icc (1/25 : ℝ) frameCap ∧ l=59/100+L/2 ∧ mu=1)

theorem Weights.bounds {l mu L : ℝ} (hw : Weights l mu L) :
    L∈Icc 0 frameCap ∧ (121/200 : ℝ)≤l ∧ l≤ mu ∧
      mu≤1 ∧ (47/50 : ℝ)≤ mu ∧ l/mu∈Icc (61/100 : ℝ) (47/50) ∧
      PositiveStressCoefficients.ratio L≤l := by
  rcases hw with ⟨hL,rfl,rfl⟩ | ⟨hL,rfl,rfl⟩
  · exact ⟨⟨hL.1,by dsimp [frameCap]; linarith [hL.2]⟩,
      by norm_num,by norm_num,by norm_num,le_rfl,by norm_num,
      by dsimp [PositiveStressCoefficients.ratio]; linarith [hL.2]⟩
  · simp only [div_one]
    dsimp [PositiveStressCoefficients.ratio]
    dsimp [frameCap] at hL ⊢
    exact ⟨⟨by linarith [hL.1],hL.2⟩,by linarith [hL.1],
      by linarith [hL.2],le_rfl,by norm_num,
      ⟨by linarith [hL.1],by linarith [hL.2]⟩,by linarith [hL.1]⟩

def positiveSupport (a b c t : ℝ) : ℝ := R*pairNorm a b t-c*PositiveAngularEnvelope.phi t
def negativeSlope (a b c t : ℝ) : ℝ := -R*normD1 a b (-t)+c*Real.sin t
def positiveSlope (a b c t : ℝ) : ℝ :=
  R*normD1 a b t-c*(Real.cos t-Real.sin t)

theorem negativeSupport_hasDerivAt {a b c t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (negativeSupport a b c) (negativeSlope a b c t) t := by
  have hn := (pairNorm_hasDerivAt ha hb
    (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)).comp t
      (hasDerivAt_id t).neg
  convert (hn.const_mul R).sub ((Real.hasDerivAt_cos t).const_mul c) using 1
  · rfl
  · dsimp [negativeSlope]
    ring

theorem positiveSupport_hasDerivAt {a b c t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (positiveSupport a b c) (positiveSlope a b c t) t := by
  have hn := pairNorm_hasDerivAt ha hb
    (show |t|≤frameCap by rw [abs_of_nonneg ht.1]; exact ht.2)
  convert (hn.const_mul R).sub
    (((Real.hasDerivAt_cos t).add (Real.hasDerivAt_sin t)).const_mul c) using 1
  · rfl
  · dsimp [positiveSlope]
    ring

theorem negativeSlope_hasDerivAt {a b c t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (negativeSlope a b c)
      (R*normD2 a b (-t)+c*Real.cos t) t := by
  have hn := (normD1_hasDerivAt ha hb
    (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)).comp t
      (hasDerivAt_id t).neg
  convert (hn.const_mul (-R)).add ((Real.hasDerivAt_sin t).const_mul c) using 1
  · rfl
  · ring

theorem positiveSlope_hasDerivAt {a b c t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (positiveSlope a b c)
      (R*normD2 a b t+c*PositiveAngularEnvelope.phi t) t := by
  have hn := normD1_hasDerivAt ha hb
    (show |t|≤frameCap by rw [abs_of_nonneg ht.1]; exact ht.2)
  convert (hn.const_mul R).sub
    (((Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t)).const_mul c) using 1
  · rfl
  · dsimp [PositiveAngularEnvelope.phi]
    ring

private theorem r47_abs_cap : |frameCap|≤frameCap := by
  rw [abs_of_nonneg (by norm_num [frameCap])]

private theorem r47_abs_neg_cap : |-frameCap|≤frameCap := by
  rw [abs_neg]; exact r47_abs_cap

theorem negativeSlope_mono {a b c : ℝ} (ha : 0<a) (hb : 0<b) (hbc : b≤c) :
    MonotoneOn (negativeSlope a b c) (Icc 0 frameCap) := by
  have hswap : curvatureZero R a b=curvatureZero R b a := by
    dsimp [curvatureZero,pairProduct]
    rw [pairNorm_symm a b 0]
    ring
  have hzero : curvatureZero R a b<(381/500)*b := by
    rw [hswap,(curvature_constants_normalize (R := R) hb ha).1]
    rw [mul_comm (381/500 : ℝ) b]
    exact mul_lt_mul_of_pos_left
      (shapeC0p_lt EndpointRotationPenalty.R_sq.le) hb
  apply monoOn_of_hasDeriv_nonneg
  · exact fun t ht => (negativeSlope_hasDerivAt ha hb ht).continuousAt.continuousWithinAt
  · exact fun t ht => negativeSlope_hasDerivAt ha hb (Ioo_subset_Icc_self ht)
  · intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have hcurv := curvature_negative_upper EndpointRotationPenalty.R_nonneg ha hb
      (show -t∈Icc (-frameCap) 0 by constructor <;> linarith [ht'.1,ht'.2])
    have hc := (transport_trig ht').1
    have hcos := mul_lt_mul_of_pos_left hc hb
    have hmore := mul_le_mul_of_nonneg_right hbc (show 0≤Real.cos t by linarith)
    dsimp [curvature] at hcurv
    nlinarith


theorem positiveSlope_mono {a b c : ℝ}
    (hb : 0<b) (hba : b≤a) (hab : a≤2*b) (hbc : b≤c) :
    MonotoneOn (positiveSlope a b c) (Icc 0 frameCap) := by
  have ha : 0<a := hb.trans_le hba
  have hswap (t : ℝ) : curvature R a b t=curvature R b a t := by
    dsimp [curvature,normD2,pairProduct,pairEnergy]
    rw [pairNorm_symm a b t]
    ring
  apply monoOn_of_hasDeriv_nonneg
  · exact fun t ht => (positiveSlope_hasDerivAt ha hb ht).continuousAt.continuousWithinAt
  · exact fun t ht => positiveSlope_hasDerivAt ha hb (Ioo_subset_Icc_self ht)
  · intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have hc := mixedP_second_lt EndpointRotationPenalty.R_nonneg
      EndpointRotationPenalty.R_sq.le hb hba hab ht'
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    simp only [sub_zero] at hc
    rw [← hswap] at hc
    have hphi : 0≤PositiveAngularEnvelope.phi t := (by norm_num : (0:ℝ)≤1).trans
      (CorrelatedSameBlock.one_le_phi ht')
    have hmore := mul_le_mul_of_nonneg_right hbc hphi
    dsimp [curvature] at hc
    nlinarith

theorem cap_reserves :
    (3221/5000 : ℝ)<Real.sin frameCap ∧ Real.sin frameCap<(6443/10000 : ℝ) ∧
    (478/625 : ℝ)<Real.cos frameCap ∧ Real.cos frameCap<(153001/200000 : ℝ) ∧
    (241/2000 : ℝ)<Real.cos frameCap-Real.sin frameCap ∧
    (19787/10000 : ℝ)<R ∧ R<(4947/2500 : ℝ) := by
  have hslo := sin_lower_seven (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hshi := sin_upper_five (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hclo := cos_lower_six (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hchi := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hRlo := sqrt_cap_lower
  have hRhi := OneNegativeAnchorPolynomial.radius_reserves.1
  norm_num [frameCap] at hslo hshi hclo hchi
  dsimp [OneNegativeAnchorPolynomial.Rplus] at hRhi
  refine ⟨by linarith,by linarith,by linarith,by linarith,
    by linarith,hRlo,?_⟩
  norm_num at hRhi
  linarith

theorem radius_cos_reserves :
    (19787/10000 : ℝ)*(478/625)<R*Real.cos frameCap ∧
      R*Real.cos frameCap<(4947/2500 : ℝ)*(153001/200000) := by
  obtain ⟨_,_,hc,hc',_,hR,hR'⟩ := cap_reserves
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hR) (sub_pos.mpr hc)]
  · have hp := mul_pos (sub_pos.mpr hR') (show 0<Real.cos frameCap by linarith)
    linarith

theorem pairNorm_normalize {a : ℝ} (ha : 0<a) (b t : ℝ) :
    pairNorm a b t=a*pairNorm 1 (b/a) t := by
  have he : a*(b/a)=b := by field_simp [ha.ne']
  calc
    pairNorm a b t=pairNorm (a*1) (a*(b/a)) t := by rw [he,mul_one]
    _=a*pairNorm 1 (b/a) t := pairNorm_homogeneous ha.le 1 (b/a) t

/-- The positive exterior A term has slope below `.72` on its whole
domain; the only endpoint comparison is by positive squaring. -/
theorem positive_one_cap {l : ℝ} (hl : 0<l) (hl1 : l≤1) :
    positiveSlope 1 l 1 frameCap<(18/25 : ℝ) := by
  have hh : |frameCap|≤frameCap := by rw [abs_of_nonneg]; norm_num [frameCap]
  have hN := pairNorm_pos (show (0:ℝ)<1 by norm_num) hl hh
  have hN2 := pairNorm_sq (show (0:ℝ)<1 by norm_num) hl hh
  obtain ⟨hs,_,_,_,hd,_,_⟩ := cap_reserves
  have hp := mul_nonneg (show 0≤1-l by linarith)
    (show 0≤1+l+2*l*Real.sin frameCap by positivity)
  have hNsq : ((1813/1000)*l)^2<(pairNorm 1 l frameCap)^2 := by
    have hs' := mul_lt_mul_of_pos_left hs (show 0<2*l^2 by positivity)
    dsimp [pairEnergy,pairProduct] at hN2
    nlinarith [sq_pos_of_pos hl]
  have hNl : (1813/1000)*l<pairNorm 1 l frameCap := by
    nlinarith [mul_pos (show (0:ℝ)<1813/1000 by norm_num) hl]
  have hupper := radius_cos_reserves.2
  have hnum : R*l*Real.cos frameCap<(21/25)*pairNorm 1 l frameCap := by
    have hm := mul_lt_mul_of_pos_right hupper hl
    nlinarith
  have hdiv : R*normD1 1 l frameCap<(21/25 : ℝ) := by
    calc
      R*normD1 1 l frameCap=(R*l*Real.cos frameCap)/pairNorm 1 l frameCap := by
        dsimp [normD1,pairProduct]
        ring
      _<(21/25 : ℝ) := (div_lt_iff₀ hN).2 hnum
  dsimp [positiveSlope]
  nlinarith

theorem negative_norm_cap {r : ℝ} (hr : r∈Icc (61/100 : ℝ) (47/50)) :
    pairNorm 1 r (-frameCap)<(4101/5000 : ℝ) := by
  have hr0 : 0<r := by linarith [hr.1]
  have hh : |-frameCap|≤frameCap := r47_abs_neg_cap
  have hN := pairNorm_sq (show (0:ℝ)<1 by norm_num) hr0 hh
  have hs := mul_lt_mul_of_pos_left cap_reserves.1 (show 0<2*r by positivity)
  have hp := mul_nonpos_of_nonneg_of_nonpos (show 0≤r-61/100 by linarith [hr.1])
    (show r-47/50≤0 by linarith [hr.2])
  dsimp [pairEnergy,pairProduct] at hN
  simp only [Real.sin_neg,one_pow,one_mul] at hN
  have hN0 := Real.sqrt_nonneg (1^2+r^2+2*1*r*Real.sin (-frameCap))
  change 0≤pairNorm 1 r (-frameCap) at hN0
  have hsq : (pairNorm 1 r (-frameCap))^2<(4101/5000)^2 := by
    have hr2 := hr.2
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq


theorem negative_mu_cap {l mu : ℝ} (hmu : 0< mu) (hl : 0<l)
    (hr : l/mu∈Icc (61/100 : ℝ) (47/50)) :
    negativeSlope mu l l frameCap< -(6/5)*l := by
  have hr0 : 0<l/mu := div_pos hl hmu
  have hh : |-frameCap|≤frameCap := r47_abs_neg_cap
  have hN := pairNorm_pos (show (0:ℝ)<1 by norm_num) hr0 hh
  have hNu := negative_norm_cap hr
  have hlow := radius_cos_reserves.1
  have hdiv : (18443/10000 : ℝ)<R*Real.cos frameCap/pairNorm 1 (l/mu) (-frameCap) := by
    apply (lt_div_iff₀ hN).2
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hdiv hl
  have hsin := mul_lt_mul_of_pos_left cap_reserves.2.1 hl
  have he : negativeSlope mu l l frameCap=
      l*(Real.sin frameCap-R*Real.cos frameCap/pairNorm 1 (l/mu) (-frameCap)) := by
    dsimp [negativeSlope,normD1,pairProduct]
    rw [pairNorm_normalize hmu,Real.cos_neg]
    field_simp [hmu.ne',hN.ne']
    ring
  rw [he]
  nlinarith


def exteriorC (r : ℝ) : ℝ :=
  R*Real.cos frameCap/pairNorm 1 r frameCap-Real.cos frameCap+Real.sin frameCap
def exteriorG (l : ℝ) : ℝ :=
  R*Real.cos frameCap/pairNorm 1 l (-frameCap)-Real.sin frameCap/l

theorem positive_norm_lower {r : ℝ} (hr : (61/100 : ℝ)≤r) :
    (1469/1000 : ℝ)<pairNorm 1 r frameCap := by
  have hr0 : 0<r := by linarith
  have hN := pairNorm_sq (show (0:ℝ)<1 by norm_num) hr0
    r47_abs_cap
  have hsq := mul_nonneg (show 0≤r-61/100 by linarith)
    (show 0≤r+61/100 by linarith)
  have hs := mul_lt_mul_of_pos_left cap_reserves.1 (show 0<2*r by positivity)
  have hN0 := pairNorm_pos (show (0:ℝ)<1 by norm_num) hr0
    r47_abs_cap
  dsimp [pairEnergy,pairProduct] at hN
  nlinarith


theorem positive_norm_lower_small {r : ℝ} (hr : (16/25 : ℝ)≤r) :
    (747/500 : ℝ)<pairNorm 1 r frameCap := by
  have hr0 : 0<r := by linarith
  have hN := pairNorm_sq (show (0:ℝ)<1 by norm_num) hr0
    r47_abs_cap
  have hsq := mul_nonneg (show 0≤r-16/25 by linarith)
    (show 0≤r+16/25 by linarith)
  have hs := mul_lt_mul_of_pos_left cap_reserves.1 (show 0<2*r by positivity)
  have hN0 := pairNorm_pos (show (0:ℝ)<1 by norm_num) hr0
    r47_abs_cap
  dsimp [pairEnergy,pairProduct] at hN
  nlinarith


theorem exteriorC_large {r : ℝ} (hr : (61/100 : ℝ)≤r) :
    exteriorC r<(91/100 : ℝ) := by
  have hN := positive_norm_lower hr
  have hdiv : R*Real.cos frameCap/pairNorm 1 r frameCap<(2061/2000 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0<pairNorm 1 r frameCap)).2
    nlinarith [radius_cos_reserves.2]
  dsimp [exteriorC]
  linarith [cap_reserves.2.2.2.2.1]

theorem exteriorC_small {r : ℝ} (hr : (16/25 : ℝ)≤r) :
    exteriorC r<(893/1000 : ℝ) := by
  have hN := positive_norm_lower_small hr
  have hdiv : R*Real.cos frameCap/pairNorm 1 r frameCap<(2027/2000 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0<pairNorm 1 r frameCap)).2
    nlinarith [radius_cos_reserves.2]
  dsimp [exteriorC]
  linarith [cap_reserves.2.2.2.2.1]

private def lowerProduct : ℝ := (19787/10000)*(478/625)
private def quartic (l : ℝ) : ℝ :=
  (lowerProduct*l)^2-((23/25)*l+6443/10000)^2*(1+l^2-2*(3221/5000)*l)

/-- A single positive-coefficient identity on the whole interval `.61≤l≤1`. -/
private theorem quartic_positive {l : ℝ} (hl : l∈Icc (61/100 : ℝ) 1) :
    0<quartic l := by
  let z : ℝ := (l-61/100)/(39/100)
  have hz : z∈Icc 0 1 := by dsimp [z]; constructor <;> linarith [hl.1,hl.2]
  have he : l=61/100+(39/100)*z := by dsimp [z]; ring
  let b0 : ℝ := 29287839019429/97656250000000000
  let b1 : ℝ := 243170797943379757/1562500000000000000
  let b2 : ℝ := 126344718400862311/390625000000000000
  let b3 : ℝ := 29481487353515773/62500000000000000
  let b4 : ℝ := 85749482285509/156250000000000
  have hid : quartic l=1/5000+
      (b0-1/5000)*(1-z)^4+4*(b1-1/5000)*z*(1-z)^3+
      6*(b2-1/5000)*z^2*(1-z)^2+4*(b3-1/5000)*z^3*(1-z)+
      (b4-1/5000)*z^4 := by
    rw [he]
    dsimp [quartic,lowerProduct,b0,b1,b2,b3,b4]
    ring
  have h0 : 0≤(b0-1/5000)*(1-z)^4 := mul_nonneg (by norm_num [b0]) (by positivity)
  have h1 : 0≤4*(b1-1/5000)*z*(1-z)^3 := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num [b1]) hz.1
    · exact pow_nonneg (by linarith [hz.2]) _
  have h2 : 0≤6*(b2-1/5000)*z^2*(1-z)^2 :=
    mul_nonneg (mul_nonneg (by norm_num [b2]) (sq_nonneg z)) (sq_nonneg (1-z))
  have h3 : 0≤4*(b3-1/5000)*z^3*(1-z) := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num [b3]) (pow_nonneg hz.1 _)
    · linarith [hz.2]
  have h4 : 0≤(b4-1/5000)*z^4 := mul_nonneg (by norm_num [b4]) (by positivity)
  linarith

theorem exteriorG_large {l : ℝ} (hl : l∈Icc (61/100 : ℝ) 1) :
    (23/25 : ℝ)<exteriorG l := by
  have hl0 : 0<l := by linarith [hl.1]
  have hh : |-frameCap|≤frameCap := r47_abs_neg_cap
  have hN := pairNorm_pos (show (0:ℝ)<1 by norm_num) hl0 hh
  have hN2 := pairNorm_sq (show (0:ℝ)<1 by norm_num) hl0 hh
  dsimp [pairEnergy,pairProduct] at hN2
  simp only [one_pow,one_mul,Real.sin_neg] at hN2
  have hslo := mul_lt_mul_of_pos_left cap_reserves.1 (show 0<2*l by positivity)
  have hNup : (pairNorm 1 l (-frameCap))^2≤1+l^2-2*(3221/5000)*l := by
    nlinarith
  have hw := mul_le_mul_of_nonneg_left hNup
    (sq_nonneg ((23/25)*l+6443/10000))
  have hpoly := quartic_positive hl
  have hprod : ((23/25)*l+6443/10000)*pairNorm 1 l (-frameCap)<lowerProduct*l := by
    have hright : 0<lowerProduct*l := by dsimp [lowerProduct]; positivity
    have hleft : 0≤((23/25)*l+6443/10000)*pairNorm 1 l (-frameCap) := by positivity
    dsimp [quartic] at hpoly
    nlinarith
  have hR := mul_lt_mul_of_pos_right radius_cos_reserves.1 hl0
  change lowerProduct*l<R*Real.cos frameCap*l at hR
  have hsin := mul_lt_mul_of_pos_right cap_reserves.2.1 hN
  have hactual : ((23/25)*l+Real.sin frameCap)*pairNorm 1 l (-frameCap)<
      R*Real.cos frameCap*l := by nlinarith
  have he : ((23/25)+Real.sin frameCap/l)*pairNorm 1 l (-frameCap)*l=
      ((23/25)*l+Real.sin frameCap)*pairNorm 1 l (-frameCap) := by
    field_simp [hl0.ne']
  have hdiv : (23/25)+Real.sin frameCap/l<
      R*Real.cos frameCap/pairNorm 1 l (-frameCap) := by
    apply (lt_div_iff₀ hN).2
    refine lt_of_mul_lt_mul_right ?_ hl0.le
    rw [he]
    exact hactual
  dsimp [exteriorG]
  linarith


theorem exteriorG_small : (9/10 : ℝ)<exteriorG (121/200) := by
  suffices h : ∀ l : ℝ, l=121/200 → (9/10 : ℝ)<exteriorG l from h _ rfl
  intro l hl
  have hl0 : 0<l := by rw [hl]; norm_num
  have hh : |-frameCap|≤frameCap := r47_abs_neg_cap
  have hN := pairNorm_pos (show (0:ℝ)<1 by norm_num) hl0 hh
  have hN2 := pairNorm_sq (show (0:ℝ)<1 by norm_num) hl0 hh
  dsimp [pairEnergy,pairProduct] at hN2
  simp only [one_pow,one_mul,Real.sin_neg] at hN2
  have hslo := mul_lt_mul_of_pos_left cap_reserves.1 (show 0<2*l by positivity)
  have hNup : (pairNorm 1 l (-frameCap))^2≤1+l^2-2*(3221/5000)*l := by nlinarith
  have hw := mul_le_mul_of_nonneg_left hNup (sq_nonneg ((9/10)*l+6443/10000))
  have hpoly : 0<(lowerProduct*l)^2-
      ((9/10)*l+6443/10000)^2*(1+l^2-2*(3221/5000)*l) := by
    rw [hl]; norm_num [lowerProduct]
  have hprod : ((9/10)*l+6443/10000)*pairNorm 1 l (-frameCap)<lowerProduct*l := by
    have hright : 0<lowerProduct*l := by dsimp [lowerProduct]; positivity
    have hleft : 0≤((9/10)*l+6443/10000)*pairNorm 1 l (-frameCap) := by positivity
    nlinarith
  have hR := mul_lt_mul_of_pos_right radius_cos_reserves.1 hl0
  change lowerProduct*l<R*Real.cos frameCap*l at hR
  have hsin := mul_lt_mul_of_pos_right cap_reserves.2.1 hN
  have hactual : ((9/10)*l+Real.sin frameCap)*pairNorm 1 l (-frameCap)<
      R*Real.cos frameCap*l := by nlinarith
  have he : ((9/10)+Real.sin frameCap/l)*pairNorm 1 l (-frameCap)*l=
      ((9/10)*l+Real.sin frameCap)*pairNorm 1 l (-frameCap) := by
    field_simp [hl0.ne']
  have hdiv : (9/10)+Real.sin frameCap/l<
      R*Real.cos frameCap/pairNorm 1 l (-frameCap) := by
    apply (lt_div_iff₀ hN).2
    refine lt_of_mul_lt_mul_right ?_ hl0.le
    rw [he]
    exact hactual
  dsimp [exteriorG]
  linarith


theorem lower_exterior_cap {l mu L : ℝ} (hw : Weights l mu L) :
    negativeSlope 1 l 1 frameCap+positiveSlope mu l l frameCap<0 := by
  obtain ⟨hL,hl,hlu,hmu1,hmu,hr,_⟩ := hw.bounds
  have hl0 : 0<l := by linarith
  have hmu0 : 0< mu := by linarith
  have hN := pairNorm_pos (show (0:ℝ)<1 by norm_num) (div_pos hl0 hmu0)
    r47_abs_cap
  have hNm := pairNorm_pos (show (0:ℝ)<1 by norm_num) hl0
    r47_abs_neg_cap
  have he : negativeSlope 1 l 1 frameCap+positiveSlope mu l l frameCap=
      l*(exteriorC (l/mu)-exteriorG l) := by
    dsimp [negativeSlope,positiveSlope,exteriorC,exteriorG,normD1,pairProduct]
    rw [pairNorm_normalize hmu0,Real.cos_neg]
    field_simp [hmu0.ne',hl0.ne',hN.ne',hNm.ne']
    ring
  have hCG : exteriorC (l/mu)<exteriorG l := by
    rcases hw with ⟨_,rfl,rfl⟩ | ⟨hL,rfl,rfl⟩
    · have hc := exteriorC_small (r := (121/200)/(47/50)) (by norm_num)
      linarith [exteriorG_small]
    · have hc := exteriorC_large (r := 59/100+L/2)
        (by linarith [hL.1])
      have hg := exteriorG_large (l := 59/100+L/2)
        ⟨by linarith [hL.1],by dsimp [frameCap] at hL; linarith [hL.2]⟩
      simp only [div_one]
      linarith
  rw [he]
  exact mul_neg_of_pos_of_neg hl0 (sub_neg.mpr hCG)


theorem upper_exterior_cap {l mu L : ℝ} (hw : Weights l mu L) :
    positiveSlope 1 l 1 frameCap+negativeSlope mu l l frameCap<0 := by
  obtain ⟨_,hl,hlu,hmu1,hmu,hr,_⟩ := hw.bounds
  have hl0 : 0<l := by linarith
  have hp := positive_one_cap hl0 (hlu.trans hmu1)
  have hn := negative_mu_cap (by linarith : 0< mu) hl0 hr
  linarith

end SquaresInCircles.Eight.OneNegativeAnchorConcentration
end
end
end
