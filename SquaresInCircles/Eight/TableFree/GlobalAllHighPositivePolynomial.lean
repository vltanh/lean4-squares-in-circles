module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighSecondary
public import SquaresInCircles.Eight.TableFree.DirectedPowerBounds
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# The complete positive-primary scalar for the all-high potential

One degree-eleven polynomial bounds the scalar on the complete angle
interval.  Dividing its known zero constant term gives one degree-ten
polynomial whose derivative is negative by a single centered coefficient
norm.  The scalar transfer is algebraic in the original diagonal
constant.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

def positiveRadius : ℝ := 1979/1000
def etaLower : ℝ := 39921/100000
def etaError : ℝ := 1/100000
def sineCoefficient : ℝ := positiveRadius-(3/4+etaLower^2)/(2*positiveRadius)

def positivePrimaryScalar (z e : ℝ) : ℝ := z+kappa*(e+
  Real.cos z*(Real.sin z-e)-positiveRadius*Real.sin z+
  Real.sin z*(Real.sin z-e)^2/(2*positiveRadius))

namespace PositivePolynomial
open Polynomial PowerTailBounds

def S9 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7+C (1/362880)*X^9
def S11 : ℚ[X] := S9-C (1/39916800)*X^11
def C8 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+C (1/40320)*X^8
def C10 : ℚ[X] := C8-C (1/3628800)*X^10
def B : ℚ := (1979/1000)-((3/4)+(39921/100000)^2)/(2*(1979/1000))

def H : ℚ[X] := C (1-(103/100)*(1/100000))*X+C (103/100)*
  (C (39921/100000)*(1-C8)+C (1/2)*(S11.comp (C 2*X))-C B*S9-
    C (1/(8*(1979/1000)))*(S9.comp (C 3*X))-
    C ((39921/100000)/(2*(1979/1000)))*(1-C10.comp (C 2*X)))
def P : ℚ[X] := H.divX
def negDerivative : ℚ[X] := DirectedPowerBounds.shift (7/20) (-P.derivative)

@[simp] theorem S9_eval (z : ℝ) : aeval z S9=Arithmetic.sin9 z := by
  simp [S9,Arithmetic.sin9,Arithmetic.sin7]
  ring
@[simp] theorem S11_eval (z : ℝ) : aeval z S11=HighOrderTaylor.S11 z := by
  simp [S11,HighOrderTaylor.S11]
  ring
@[simp] theorem C8_eval (z : ℝ) : aeval z C8=Arithmetic.cos8 z := by
  simp [C8,Arithmetic.cos8]
  ring
@[simp] theorem C10_eval (z : ℝ) : aeval z C10=Arithmetic.cos10 z := by
  simp [C10,Arithmetic.cos10]
  ring

theorem H_eval (z : ℝ) : aeval z H=(1-kappa*etaError)*z+kappa*
    (etaLower*(1-Arithmetic.cos8 z)+(1/2)*HighOrderTaylor.S11 (2*z)-
      sineCoefficient*Arithmetic.sin9 z-Arithmetic.sin9 (3*z)/(8*positiveRadius)-
      etaLower/(2*positiveRadius)*(1-Arithmetic.cos10 (2*z))) := by
  simp [H,aeval_comp,B,kappa,etaError,etaLower,sineCoefficient,positiveRadius]
  ring

/-- `P` in closed form: the coefficients of `H/X`. -/
private def r59_P : ℚ[X] := C (130980455423/3958000000000)+
    C (-86349123/39580000000)*X+
    C (-2223241222823/23748000000000)*X^2+
    C (8252509041/158320000000)*X^3+
    C (-4475878777177/474960000000000)*X^4+
    C (-13715804347/1583200000000)*X^5+
    C (309372358777177/19948320000000000)*X^6+
    C (8225096621/12665600000000)*X^7+
    C (-4031858278777177/1436279040000000000)*X^8+
    C (-195803/6679125000)*X^9+
    C (-103/3898125)*X^10

/-- `negDerivative` in closed form. -/
private def r59_N : ℚ[X] := C (18179501021475297728077903/361121587200000000000000000)+
    C (1665131271580472521376603/18056079360000000000000000)*X+
    C (-37129888110956042190271/300934656000000000000000)*X^2+
    C (-68932579828309747453/9028039680000000000000)*X^3+
    C (-42307927320328579879/451401984000000000000)*X^4+
    C (-11505424702701754579/263317824000000000000)*X^5+
    C (295279021179782129/5642524800000000000)*X^6+
    C (48110634043956947/1974883680000000000)*X^7+
    C (26845199/24490125000)*X^8+
    C (206/779625)*X^9

private theorem r59_H_eq : H=X*r59_P := by
  apply Polynomial.funext
  intro x
  simp only [H,S11,S9,C10,C8,B,r59_P,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow,
    eval_comp,eval_one]
  ring

private theorem r59_P_eq : P=r59_P := by
  have h := X_mul_divX_add H
  have h0 : H.coeff 0=0 := by rw [r59_H_eq,coeff_X_mul_zero]
  rw [h0,map_zero,add_zero] at h
  exact mul_left_cancel₀ X_ne_zero (h.trans r59_H_eq)

private theorem r59_N_eq : negDerivative=r59_N := by
  rw [negDerivative,r59_P_eq]
  apply Polynomial.funext
  intro x
  simp only [DirectedPowerBounds.shift,r59_P,r59_N,eval_comp,eval_neg,derivative_add,
    derivative_C_mul_X_pow,derivative_C_mul_X,derivative_C,eval_add,eval_mul,eval_C,
    eval_X,eval_pow,zero_add]
  norm_num
  ring

theorem factor_identity : H=X*P := by
  rw [r59_P_eq]
  exact r59_H_eq

theorem derivative_identity : negDerivative=C (negDerivative.coeff 0)+tail negDerivative 1 9 := by
  rw [r59_N_eq]
  apply Polynomial.funext
  intro x
  simp only [r59_N,PowerTailBounds.tail,Fin.sum_univ_succ,Fin.sum_univ_zero,coeff_add,
    coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,eval_add,eval_mul,eval_C,eval_X,eval_pow,
    Fin.val_zero,Fin.val_succ]
  norm_num
  ring

theorem derivative_reserve :
    (1/1250:ℚ)<negDerivative.coeff 0-PowerTailBounds.norm negDerivative 1 9 (7/20) := by
  rw [r59_N_eq]
  simp only [r59_N,PowerTailBounds.norm,Fin.sum_univ_succ,Fin.sum_univ_zero,coeff_add,
    coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,Fin.val_zero,Fin.val_succ]
  norm_num

theorem endpoint_reserve : (3/2000:ℚ)<P.eval (7/10) := by
  rw [r59_P_eq]
  simp only [r59_P,eval_add,eval_mul,eval_C,eval_X,eval_pow]
  norm_num

theorem P_derivative_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z P.derivative<0 := by
  have hw : |z-7/20|≤((7/20:ℚ):ℝ) := by
    apply abs_le.mpr
    dsimp [frameCap] at hz
    push_cast
    constructor <;> linarith [hz.1,hz.2]
  have hh := DirectedPowerBounds.constant_lower derivative_identity hw
  have hr := Rat.cast_lt (K := ℝ) |>.mpr derivative_reserve
  push_cast at hr
  have he : aeval (z-7/20) negDerivative= -aeval z P.derivative := by
    have hz' : ((7/20:ℚ):ℝ)+(z-7/20)=z := by push_cast; ring
    rw [negDerivative,DirectedPowerBounds.shift_eval,hz',map_neg]
  rw [he] at hh
  linarith

theorem P_antitone : AntitoneOn (fun z : ℝ => aeval z P) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro z _
    exact (CenteredMonomialBounds.aeval_hasDerivAt P z).continuousAt.continuousWithinAt
  · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt P z
  · exact fun z hz => (P_derivative_negative (Ioo_subset_Icc_self hz)).le

theorem P_lower {z : ℝ} (hz : z∈Icc 0 frameCap) : (3/2000:ℝ)<aeval z P := by
  have hh := P_antitone hz (by norm_num [frameCap]) hz.2
  have he : (3/2000:ℝ)<aeval (7/10:ℝ) P := by
    have h1 : ((3/2000:ℚ):ℝ)<((P.eval (7/10):ℚ):ℝ) := Rat.cast_lt.mpr endpoint_reserve
    have h2 := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℝ) (7/10:ℚ) P
    simp only [eq_ratCast] at h2
    have h3 : ((7/10:ℚ):ℝ)=7/10 := by norm_num
    have h4 : ((3/2000:ℚ):ℝ)=3/2000 := by norm_num
    rw [h3] at h2
    rw [h2,← h4]
    exact h1
  simpa only [frameCap] using he.trans_le hh

theorem H_lower {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (3/2000)*z≤aeval z H ∧ (0<z → (3/2000)*z<aeval z H) := by
  have hid := congrArg (fun p : ℚ[X] => aeval z p) factor_identity
  simp only [map_mul,aeval_X] at hid
  have hP := P_lower hz
  rw [hid]
  refine ⟨by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hP.le)],?_⟩
  intro hzpos
  nlinarith [mul_pos hzpos (sub_pos.mpr hP)]

end PositivePolynomial

theorem positive_harmonic_identity (z : ℝ) :
    positivePrimaryScalar z etaLower-kappa*etaError*z=
      (1-kappa*etaError)*z+kappa*
        (etaLower*(1-Real.cos z)+(1/2)*Real.sin (2*z)-sineCoefficient*Real.sin z-
          Real.sin (3*z)/(8*positiveRadius)-
          etaLower/(2*positiveRadius)*(1-Real.cos (2*z))) := by
  dsimp [positivePrimaryScalar,sineCoefficient,kappa,etaLower,etaError,positiveRadius]
  rw [Real.sin_two_mul,Real.sin_three_mul,Real.cos_two_mul]
  linear_combination (-(103/100)*(39921/100000)/(1979/1000):ℝ)*Real.sin_sq_add_cos_sq z

theorem positive_polynomial_transfer {z : ℝ} (hz : 0≤z) :
    Polynomial.aeval z PositivePolynomial.H≤
      positivePrimaryScalar z etaLower-kappa*etaError*z := by
  rw [PositivePolynomial.H_eval,positive_harmonic_identity]
  have hc := Arithmetic.cos_le_cos8 hz
  have hs2 := HighOrderTaylor.S11_le_sin (show 0≤2*z by linarith)
  have hs := Arithmetic.sin_le_sin9 hz
  have hs3 := Arithmetic.sin_le_sin9 (show 0≤3*z by linarith)
  have hc2 := Arithmetic.cos10_le_cos (show 0≤2*z by linarith)
  dsimp [kappa,etaLower,etaError,sineCoefficient,positiveRadius]
  norm_num
  linarith only [hc,hs2,hs,hs3,hc2]

theorem positive_eta_transfer {z e : ℝ} (hz : z∈Icc 0 frameCap)
    (he : e∈Icc etaLower (etaLower+etaError)) :
    positivePrimaryScalar z etaLower-kappa*etaError*z≤positivePrimaryScalar z e := by
  obtain ⟨δ,hδdef⟩ : ∃ δ,δ=e-etaLower := ⟨_,rfl⟩
  have hδ : 0≤δ := by rw [hδdef]; linarith [he.1]
  have hδu : δ≤etaError := by rw [hδdef]; linarith [he.2]
  have tr := transport_trig hz
  have hsin := Real.sin_le hz.1
  have hc := Real.cos_le_one z
  have hs1 := Real.sin_le_one z
  have hsquare : (Real.sin z)^2≤z := by
    nlinarith [mul_nonneg tr.2.2.1 (sub_nonneg.mpr hs1)]
  have hfirst := mul_nonneg hδ (sub_nonneg.mpr hc)
  have hsecond := mul_nonneg (mul_nonneg hδ tr.2.2.1)
    (show 0≤e+etaLower by dsimp [etaLower] at he ⊢; linarith [he.1])
  have hthird := mul_le_mul_of_nonneg_left hsquare hδ
  have hfourth := mul_le_mul_of_nonneg_right hδu hz.1
  have hid : positivePrimaryScalar z e-positivePrimaryScalar z etaLower=
      kappa*δ*((1-Real.cos z)+Real.sin z*(e+etaLower-2*Real.sin z)/(2*positiveRadius)) := by
    dsimp [positivePrimaryScalar]
    rw [hδdef]
    ring
  dsimp [kappa,positiveRadius,etaError] at *
  norm_num at hid
  linarith only [hid,hfirst,hsecond,hthird,hfourth,hz.1]

/-- The scalar is strictly positive away from zero on the complete
frame interval, for the actual original diagonal constant. -/
theorem positive_primary_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (3/2000)*z≤positivePrimaryScalar z (FramePair.c0-1/2) ∧
      (0<z → (3/2000)*z<positivePrimaryScalar z (FramePair.c0-1/2)) := by
  have he : FramePair.c0-1/2∈Icc etaLower (etaLower+etaError) := by
    dsimp [etaLower,etaError]
    exact ⟨by linarith [diagonal_bounds.1],by linarith [diagonal_bounds.2]⟩
  have hpoly := PositivePolynomial.H_lower hz
  have htr := (positive_polynomial_transfer hz.1).trans (positive_eta_transfer hz he)
  exact ⟨hpoly.1.trans htr,fun hpos => (hpoly.2 hpos).trans_le htr⟩

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
