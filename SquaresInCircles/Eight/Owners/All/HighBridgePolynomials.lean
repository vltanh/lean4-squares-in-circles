module

public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.All.HighZeroPositive
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds

/-!
# Eight squares: four polynomials of the outer bridge

The endpoint polynomials `lowLow` and `lowNonlow`, built from `endpointPoly`, have degree eight;
the two circle envelopes `midLow` and `midNonlow` have degree twelve. Each is positive on
`[0, 7/10]` (`lowLow_positive`, `lowNonlow_positive`, `midLow_positive`, `midNonlow_positive`),
where its Bernstein coefficients are positive.
-/

section
/-!
## Two fixed whole-interval polynomials for the nonpositive zero source

The norm remainder, the high-target curvature, and the lower-target
slope each have one exact coefficient bound on the entire interval.
There is no angle subdivision or state inventory.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.ZeroPolynomial

open Polynomial PowerTailBounds DirectedPowerBounds

def mu : ℚ[X] := 1-C (1/5)*X
def S7 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7
def p1 : ℚ[X] := 1-C (5/52)*X-C (725/16224)*X^2+
  C (1045/281216)*X^3+C (365515/526436352)*X^4
def p2 : ℚ[X] := 1-C (1/10)*X+C (1/200)*X^2+C (1/2000)*X^3+C (1/20000)*X^4
def X1 : ℚ[X] := C (26/25)-C (1/5)*X-C (1/12)*X^2+
  C (1/60)*X^3+C (1/360)*X^4-C (1/1800)*X^5
def remainder : ℚ[X] := C (26/25)*p1^2-X1
def remainderQuotient : ℚ[X] := remainder.divX.divX.divX.divX.divX
def H : ℚ[X] := X+C (103/100)*(mu*(1+S7)-1-C (1009/500)*X*p1-
  C (139921/50000)*(p2-1))
def L : ℚ[X] := C (3/50)+X+C (103/100)*(mu*S7+C (1/250)*X-C (1009/500)*X*p1)
def highCurvature : ℚ[X] := shift (7/20) (-H.derivative.derivative)
def lowSlope : ℚ[X] := shift (7/20) (-L.derivative)

@[simp] theorem mu_eval (z : ℝ) : aeval z mu=1-z/5 := by simp [mu]; ring
@[simp] theorem S7_eval (z : ℝ) : aeval z S7=Arithmetic.sin7 z := by
  simp [S7,Arithmetic.sin7]
  ring
@[simp] theorem p1_eval (z : ℝ) : aeval z p1=
    1-(5/52)*z-(725/16224)*z^2+(1045/281216)*z^3+(365515/526436352)*z^4 := by
  simp [p1]
@[simp] theorem p2_eval (z : ℝ) : aeval z p2=
    1-z/10+z^2/200+z^3/2000+z^4/20000 := by
  simp [p2]
  ring
@[simp] theorem X1_eval (z : ℝ) : aeval z X1=
    (26/25)-z/5-z^2/12+z^3/60+z^4/360-z^5/1800 := by
  simp [X1]
  ring
theorem H_eval (z : ℝ) : aeval z H=z+kappa*((1-z/5)*(1+Arithmetic.sin7 z)-1-
    (1009/500)*z*aeval z p1-(139921/50000)*(aeval z p2-1)) := by
  simp [H,kappa]
theorem L_eval (z : ℝ) : aeval z L=zeroGap+z+kappa*((1-z/5)*Arithmetic.sin7 z+
    z/250-(1009/500)*z*aeval z p1) := by
  simp [L,kappa,zeroGap]
  ring

theorem rational_aeval (p : ℚ[X]) (r : ℚ) : aeval (r:ℝ) p=((p.eval r:ℚ):ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp

/-! Closed forms of the certified polynomials. -/

private def r59_RQ : ℚ[X] := C (938291/13160908800)+
    C (-8241161/164248141824)*X+
    C (15278527/2846967791616)*X^2+
    C (5344048609/10659047411810304)*X^3

private def r59_H : ℚ[X] := C (1684863/50000000)*X+
    C (-267179219/13000000000)*X^2+
    C (-135579198597/1690000000000)*X^3+
    C (8721656135171/329550000000000)*X^4+
    C (37588411399/5264363520000)*X^5+
    C (-103/60000)*X^6+
    C (-103/504000)*X^7+
    C (103/2520000)*X^8

private def r59_L : ℚ[X] := C (3/50)+
    C (-2221/50000)*X+
    C (-3193/520000)*X^2+
    C (-852119/10816000)*X^3+
    C (224490251/8436480000)*X^4+
    C (37588411399/5264363520000)*X^5+
    C (-103/60000)*X^6+
    C (-103/504000)*X^7+
    C (103/2520000)*X^8

private def r59_HC : ℚ[X] := C (27204031190429246771/164511360000000000000)+
    C (592134702175235077/2741856000000000000)*X+
    C (-58471481123931757/137092800000000000)*X^2+
    C (-681640651097/10967424000000)*X^3+
    C (12463/200000)*X^4+
    C (1133/300000)*X^5+
    C (-103/45000)*X^6

private def r59_LS : ℚ[X] := C (2548946901698092579/35095756800000000000)+
    C (175435649475577903/1316090880000000000)*X+
    C (4520850152779433/43869696000000000)*X^2+
    C (-93933716227453/658045440000000)*X^3+
    C (-681640651097/43869696000000)*X^4+
    C (12463/1000000)*X^5+
    C (1133/1800000)*X^6+
    C (-103/315000)*X^7

private theorem r59_divX_X_mul (q : ℚ[X]) : (X*q).divX=q := by
  have h := X_mul_divX_add (X*q)
  rw [coeff_X_mul_zero,map_zero,add_zero] at h
  exact mul_left_cancel₀ X_ne_zero h

private theorem r59_remainder_eq : remainder=X^5*r59_RQ := by
  apply Polynomial.funext
  intro x
  simp only [remainder,p1,X1,r59_RQ,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow,eval_one]
  ring

private theorem r59_RQ_eq : remainderQuotient=r59_RQ := by
  rw [remainderQuotient,r59_remainder_eq,
    show (X^5*r59_RQ : ℚ[X])=X*(X*(X*(X*(X*r59_RQ)))) by ring]
  simp only [r59_divX_X_mul]

private theorem r59_H_eq : H=r59_H := by
  apply Polynomial.funext
  intro x
  simp only [H,mu,S7,p1,p2,r59_H,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow,eval_one]
  ring

private theorem r59_L_eq : L=r59_L := by
  apply Polynomial.funext
  intro x
  simp only [L,mu,S7,p1,r59_L,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow,eval_one]
  ring

private theorem r59_HC_eq : highCurvature=r59_HC := by
  rw [highCurvature,r59_H_eq]
  apply Polynomial.funext
  intro x
  simp only [shift,r59_H,r59_HC,eval_comp,eval_neg,derivative_add,
    derivative_C_mul_X_pow,derivative_C_mul_X,derivative_C,eval_add,eval_mul,eval_C,
    eval_X,eval_pow,zero_add]
  norm_num
  ring

private theorem r59_LS_eq : lowSlope=r59_LS := by
  rw [lowSlope,r59_L_eq]
  apply Polynomial.funext
  intro x
  simp only [shift,r59_L,r59_LS,eval_comp,eval_neg,derivative_add,
    derivative_C_mul_X_pow,derivative_C_mul_X,derivative_C,eval_add,eval_mul,eval_C,
    eval_X,eval_pow,zero_add]
  norm_num
  ring

theorem remainder_factor : remainder=X^5*remainderQuotient := by
  rw [r59_RQ_eq]
  exact r59_remainder_eq

theorem remainder_identity : remainderQuotient=C (remainderQuotient.coeff 0)+
    tail remainderQuotient 1 3 := by
  rw [r59_RQ_eq]
  apply Polynomial.funext
  intro x
  simp only [r59_RQ,PowerTailBounds.tail,Fin.sum_univ_succ,Fin.sum_univ_zero,coeff_add,
    coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,eval_add,eval_mul,eval_C,eval_X,eval_pow,
    Fin.val_zero,Fin.val_succ]
  norm_num
  ring

theorem remainder_reserve : (0:ℚ)<remainderQuotient.coeff 0-
    PowerTailBounds.norm remainderQuotient 1 3 (7/10) := by
  rw [r59_RQ_eq]
  simp only [r59_RQ,PowerTailBounds.norm,Fin.sum_univ_succ,Fin.sum_univ_zero,coeff_add,
    coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,Fin.val_zero,Fin.val_succ]
  norm_num

theorem highCurvature_identity : highCurvature=C (highCurvature.coeff 0)+
    tail highCurvature 1 6 := by
  rw [r59_HC_eq]
  apply Polynomial.funext
  intro x
  simp only [r59_HC,PowerTailBounds.tail,Fin.sum_univ_succ,Fin.sum_univ_zero,coeff_add,
    coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,eval_add,eval_mul,eval_C,eval_X,eval_pow,
    Fin.val_zero,Fin.val_succ]
  norm_num
  ring

theorem highCurvature_reserve : (1/100:ℚ)<highCurvature.coeff 0-
    PowerTailBounds.norm highCurvature 1 6 (7/20) := by
  rw [r59_HC_eq]
  simp only [r59_HC,PowerTailBounds.norm,Fin.sum_univ_succ,Fin.sum_univ_zero,coeff_add,
    coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,Fin.val_zero,Fin.val_succ]
  norm_num

theorem lowSlope_identity : lowSlope=C (lowSlope.coeff 0)+tail lowSlope 1 7 := by
  rw [r59_LS_eq]
  apply Polynomial.funext
  intro x
  simp only [r59_LS,PowerTailBounds.tail,Fin.sum_univ_succ,Fin.sum_univ_zero,coeff_add,
    coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,eval_add,eval_mul,eval_C,eval_X,eval_pow,
    Fin.val_zero,Fin.val_succ]
  norm_num
  ring

theorem lowSlope_reserve : (1/1000:ℚ)<lowSlope.coeff 0-
    PowerTailBounds.norm lowSlope 1 7 (7/20) := by
  rw [r59_LS_eq]
  simp only [r59_LS,PowerTailBounds.norm,Fin.sum_univ_succ,Fin.sum_univ_zero,coeff_add,
    coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,Fin.val_zero,Fin.val_succ]
  norm_num

theorem endpoint_reserves : H.eval 0=0 ∧ (0:ℚ)<H.eval (7/20) ∧
    -(7/1000:ℚ)<H.eval (7/10) ∧ (0:ℚ)<L.eval (7/10) := by
  rw [r59_H_eq,r59_L_eq]
  simp only [r59_H,r59_L,eval_add,eval_mul,eval_C,eval_X,eval_pow]
  norm_num

theorem remainder_nonnegative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤aeval z remainder := by
  have ha : |z|≤((7/10:ℚ):ℝ) := by
    rw [abs_of_nonneg hz.1]
    have := hz.2
    dsimp [frameCap] at this
    push_cast
    exact this
  have hl := DirectedPowerBounds.constant_lower remainder_identity ha
  have hr := Rat.cast_lt (K := ℝ) |>.mpr remainder_reserve
  push_cast at hr
  have hq : 0≤aeval z remainderQuotient := by linarith
  have hh := mul_nonneg (pow_nonneg hz.1 5) hq
  have hi := congrArg (fun p : ℚ[X] => aeval z p) remainder_factor
  simp only [map_mul,map_pow,aeval_X] at hi
  simpa only [hi] using hh

theorem centered_domain {z : ℝ} (hz : z∈Icc 0 frameCap) :
    |z-7/20|≤(7/20:ℝ) := by
  apply abs_le.mpr
  dsimp [frameCap] at hz
  constructor <;> linarith [hz.1,hz.2]

theorem H_second_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z H.derivative.derivative<0 := by
  have hw : |z-7/20|≤((7/20:ℚ):ℝ) := by
    have := centered_domain hz
    push_cast
    exact this
  have hl := DirectedPowerBounds.constant_lower highCurvature_identity hw
  have hr := Rat.cast_lt (K := ℝ) |>.mpr highCurvature_reserve
  push_cast at hr
  have hi : aeval (z-7/20) highCurvature= -aeval z H.derivative.derivative := by
    have hz' : ((7/20:ℚ):ℝ)+(z-7/20)=z := by push_cast; ring
    rw [highCurvature,shift_eval,hz',map_neg]
  rw [hi] at hl
  linarith

theorem H_concave {r : ℝ} (hr : r≤frameCap) :
    ConcaveOn ℝ (Icc 0 r) (fun z : ℝ => aeval z H) := by
  apply concave_of_deriv2
    (fun z _ => CenteredMonomialBounds.aeval_hasDerivAt H z)
    (fun z _ => CenteredMonomialBounds.aeval_hasDerivAt H.derivative z)
  intro z hz
  exact (H_second_negative ⟨hz.1,hz.2.trans hr⟩).le

theorem H_zero : aeval (0:ℝ) H=0 := by simp [H,p1,p2,S7,mu]

theorem H_half_positive : 0<aeval (7/20:ℝ) H := by
  rw [show (7/20:ℝ)=((7/20:ℚ):ℝ) by norm_num,rational_aeval]
  exact_mod_cast endpoint_reserves.2.1

theorem H_right_lower : -(7/1000:ℝ)<aeval (7/10:ℝ) H := by
  rw [show (7/10:ℝ)=((7/10:ℚ):ℝ) by norm_num,rational_aeval]
  have h := Rat.cast_lt (K := ℝ) |>.mpr endpoint_reserves.2.2.1
  push_cast at h ⊢
  exact h

theorem H_short_nonnegative {z : ℝ} (hz : z∈Icc 0 (7/20:ℝ)) :
    0≤aeval z H := by
  have hconc := H_concave (by norm_num [frameCap] : (7/20:ℝ)≤frameCap)
  have hl : 0≤ min (aeval (0:ℝ) H) (aeval (7/20:ℝ) H) := by
    apply le_min
    · rw [H_zero]
    · exact H_half_positive.le
  exact hl.trans (hconc.min_le_of_mem_Icc (by norm_num) (by norm_num) hz)

theorem H_lower {z : ℝ} (hz : z∈Icc 0 frameCap) : -(7/1000:ℝ)<aeval z H := by
  apply concave_gt_of_endpoints (H_concave le_rfl) hz
  · rw [H_zero]; norm_num
  · exact H_right_lower

theorem L_derivative_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z L.derivative<0 := by
  have hw : |z-7/20|≤((7/20:ℚ):ℝ) := by
    have := centered_domain hz
    push_cast
    exact this
  have hl := DirectedPowerBounds.constant_lower lowSlope_identity hw
  have hr := Rat.cast_lt (K := ℝ) |>.mpr lowSlope_reserve
  push_cast at hr
  have hi : aeval (z-7/20) lowSlope= -aeval z L.derivative := by
    have hz' : ((7/20:ℚ):ℝ)+(z-7/20)=z := by push_cast; ring
    rw [lowSlope,shift_eval,hz',map_neg]
  rw [hi] at hl
  linarith

theorem L_antitone : AntitoneOn (fun z : ℝ => aeval z L) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt L z).continuousAt.continuousWithinAt
  · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt L z
  · exact fun z hz => (L_derivative_negative (Ioo_subset_Icc_self hz)).le

theorem L_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z L := by
  have hm := L_antitone hz (by norm_num [frameCap]) hz.2
  have he : 0<aeval (7/10:ℝ) L := by
    rw [show (7/10:ℝ)=((7/10:ℚ):ℝ) by norm_num,rational_aeval]
    exact_mod_cast endpoint_reserves.2.2.2
  exact he.trans_le hm

end SquaresInCircles.Eight.GlobalAllHigh.ZeroPolynomial
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge.DualPolynomial

open Polynomial PowerTailBounds DirectedPowerBounds

def S7 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7
def C8 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+C (1/40320)*X^8
def C10 : ℚ[X] := C8-C (1/3628800)*X^10
def capQ : ℚ := 710/113-6*(8833/10000)
def piLow : ℚ := 314159/100000
def eta : ℚ := 957/1000
def radiusUpper : ℚ := 494697/250000
def a1Upper : ℚ := 3246869/2500000
def b1Lower : ℚ := 811717/2500000
def Am (mu : ℚ) : ℚ := -103/100+(11/10)*(8898/15625)+(11/10+mu)*(1489593/1000000)
def Bm (mu : ℚ) : ℚ := -(11/10)*(195443/500000)+(11/10+mu)*(1580219/1000000)
def endpointPoly (mu lambda K g bonus : ℚ) : ℚ[X] :=
  C ((1+mu)*piLow/2-mu*(capQ-bonus)+K+g+lambda/2-mu*(9/100))-
    C (1+mu)*X+C (lambda*(1/2-a1Upper)+mu*(9/100))*C8+
    C (lambda*(1/2+b1Lower)+mu*(9/100))*S7
def normSqPoly (mu lambda : ℚ) : ℚ[X] :=
  C (Am mu^2+Bm mu^2+lambda^2)+C (2*lambda)*(C (Am mu)*C8-C (Bm mu)*S7)
def distancePoly (mu lambda K g bonus : ℚ) : ℚ[X] :=
  C ((1+mu)*piLow/2-mu*(capQ-bonus)+K+g+lambda/2-mu*(9/100)-eta)-
    C (1+mu)*X+C (lambda+mu*(9/100))*C10+C (mu*(9/100))*S7
def pLow : ℚ[X] := C (1463/200)-C (129/100)*X-C (18/25)*X^2
def pNonlow : ℚ[X] := C (3241/200)-C (2643/1000)*X-C (731/500)*X^2
def lowLow : ℚ[X] := endpointPoly (17/10) (59/25) (2113/2500) (-4029/2500) 0-
  C eta-C (1/625)
def lowNonlow : ℚ[X] := endpointPoly 5 (93/20) (-1673/10000) (-1357/1000) (93/10000)-C eta
def midLow : ℚ[X] := C 2*pLow*
    distancePoly (17/10) (59/25) (109221/10000) (-4029/2500) (93/10000)-
  C radiusUpper*(pLow^2+normSqPoly (17/10) (59/25))
def midNonlow : ℚ[X] := C 2*pNonlow*
    distancePoly 5 (93/20) (115297/5000) (-1357/1000) (43/2500)-
  C radiusUpper*(pNonlow^2+normSqPoly 5 (93/20))

@[simp] theorem S7_eval (z : ℝ) : aeval z S7=Arithmetic.sin7 z := by
  simp [S7,Arithmetic.sin7]
  ring
@[simp] theorem C8_eval (z : ℝ) : aeval z C8=Arithmetic.cos8 z := by
  simp [C8,Arithmetic.cos8]
  ring
@[simp] theorem C10_eval (z : ℝ) : aeval z C10=Arithmetic.cos10 z := by
  simp [C10,Arithmetic.cos10,Arithmetic.cos8]
  ring
@[simp] theorem pLow_eval (z : ℝ) : aeval z pLow=1463/200-(129/100)*z-(18/25)*z^2 := by
  simp [pLow]
@[simp] theorem pNonlow_eval (z : ℝ) : aeval z pNonlow=3241/200-(2643/1000)*z-(731/500)*z^2 := by
  simp [pNonlow]

theorem centered_domain {z : ℝ} (hz : z∈Icc 0 frameCap) :
    |z-(7/20:ℝ)|≤7/20 := by
  apply abs_le.mpr
  dsimp [frameCap] at hz
  constructor <;> linarith [hz.1,hz.2]

/-- Each of the four polynomials has positive Bernstein coefficients of its degree on `[0, 7/10]`:
it is a positive combination of the products `z^i (7/10 - z)^(n-i)`, which `linarith` finds. -/
theorem lowLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z lowLow := by
  have h1 : 0≤7/10-z := sub_nonneg.2 hz.2
  have hb (i j : ℕ) : 0≤z^i*(7/10-z)^j := mul_nonneg (pow_nonneg hz.1 i) (pow_nonneg h1 j)
  simp only [lowLow,endpointPoly,capQ,piLow,eta,a1Upper,b1Lower,S7,C8,map_add,map_sub,map_mul,
    map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 8 0,hb 7 1,hb 6 2,hb 5 3,hb 4 4,hb 3 5,hb 2 6,hb 1 7,hb 0 8]

theorem midLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z midLow := by
  have h1 : 0≤7/10-z := sub_nonneg.2 hz.2
  have hb (i j : ℕ) : 0≤z^i*(7/10-z)^j := mul_nonneg (pow_nonneg hz.1 i) (pow_nonneg h1 j)
  simp only [midLow,distancePoly,normSqPoly,pLow,Am,Bm,capQ,piLow,eta,radiusUpper,C10,S7,C8,
    map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 12 0,hb 11 1,hb 10 2,hb 9 3,hb 8 4,hb 7 5,hb 6 6,hb 5 7,hb 4 8,hb 3 9,hb 2 10,
    hb 1 11,hb 0 12]

theorem lowNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z lowNonlow := by
  have h1 : 0≤7/10-z := sub_nonneg.2 hz.2
  have hb (i j : ℕ) : 0≤z^i*(7/10-z)^j := mul_nonneg (pow_nonneg hz.1 i) (pow_nonneg h1 j)
  simp only [lowNonlow,endpointPoly,capQ,piLow,eta,a1Upper,b1Lower,S7,C8,map_add,map_sub,map_mul,
    map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 8 0,hb 7 1,hb 6 2,hb 5 3,hb 4 4,hb 3 5,hb 2 6,hb 1 7,hb 0 8]

theorem midNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z midNonlow := by
  have h1 : 0≤7/10-z := sub_nonneg.2 hz.2
  have hb (i j : ℕ) : 0≤z^i*(7/10-z)^j := mul_nonneg (pow_nonneg hz.1 i) (pow_nonneg h1 j)
  simp only [midNonlow,distancePoly,normSqPoly,pNonlow,Am,Bm,capQ,piLow,eta,radiusUpper,C10,S7,C8,
    map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 12 0,hb 11 1,hb 10 2,hb 9 3,hb 8 4,hb 7 5,hb 6 6,hb 5 7,hb 4 8,hb 3 9,hb 2 10,
    hb 1 11,hb 0 12]

theorem pLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z pLow := by
  rw [pLow_eval]
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  dsimp [frameCap] at *
  nlinarith

theorem pNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z pNonlow := by
  rw [pNonlow_eval]
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  dsimp [frameCap] at *
  nlinarith

end SquaresInCircles.Eight.GlobalAllHigh.Bridge.DualPolynomial
end
end
end
