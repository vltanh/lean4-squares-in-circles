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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem factor_identity : H=X*P := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem derivative_identity : negDerivative=C (negDerivative.coeff 0)+tail negDerivative 1 9 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem derivative_reserve :
    (1/1250:ℚ)<negDerivative.coeff 0-PowerTailBounds.norm negDerivative 1 9 (7/20) := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem endpoint_reserve : (3/2000:ℚ)<P.eval (7/10) := by decide

theorem P_derivative_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z P.derivative<0 := by
  have hw : |z-7/20|≤(7/20:ℝ) := by
    apply abs_le.mpr
    dsimp [frameCap] at hz
    constructor <;> linarith [hz.1,hz.2]
  have hh := DirectedPowerBounds.constant_lower derivative_identity hw
  have hr : (1/1250:ℝ)<(negDerivative.coeff 0:ℝ)-
      (PowerTailBounds.norm negDerivative 1 9 (7/20):ℝ) := by
    exact_mod_cast derivative_reserve
  have he : aeval (z-7/20) negDerivative= -aeval z P.derivative := by
    simp [negDerivative,DirectedPowerBounds.shift_eval]
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
  have he : (3/2000:ℝ)<aeval (7/10:ℝ) P := by exact_mod_cast endpoint_reserve
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
  nlinarith [Real.sin_sq_add_cos_sq z]

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
  linarith

theorem positive_eta_transfer {z e : ℝ} (hz : z∈Icc 0 frameCap)
    (he : e∈Icc etaLower (etaLower+etaError)) :
    positivePrimaryScalar z etaLower-kappa*etaError*z≤positivePrimaryScalar z e := by
  let δ := e-etaLower
  have hδ : 0≤δ := by dsimp [δ]; linarith [he.1]
  have hδu : δ≤etaError := by dsimp [δ]; linarith [he.2]
  have tr := transport_trig hz
  have hsin := Real.sin_le_self hz.1
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
    dsimp [positivePrimaryScalar,δ]
    ring
  dsimp [kappa,positiveRadius,etaError] at *
  nlinarith only [hid,hfirst,hsecond,hthird,hfourth,hz.1]

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
