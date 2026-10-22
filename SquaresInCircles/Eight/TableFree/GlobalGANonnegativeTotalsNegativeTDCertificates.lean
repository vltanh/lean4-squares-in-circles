module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDPolynomialData

/-!
# Exact finite coefficients for the negative-TD2 endpoints

Uncompiled transcription of equations (21) and (37)--(42). Each
trapezoid is transformed once. The two top-edge H/G bounds retain
their prescribed center 7/20 and full radius 7/20; the remaining seven
boundary polynomials use their complete original intervals.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_certificate (f : Kind) (j : Fin 3) :
    transform (mass f j)=expansion 3 (transform (mass f j)) ∧
      (18/25:ℚ)<lowerOn 3 (mass f j) := by
  cases f with
  | negative i => fin_cases i <;> fin_cases j <;> decide
  | equal => fin_cases j <;> decide
  | positive i => fin_cases i <;> fin_cases j <;> decide
  | diagonal => fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem whole_certificate (f : Kind) (hf : Whole f) :
    transform (numerator f)=expansion (degree f) (transform (numerator f)) ∧
      wholeReserve f<lowerOn (degree f) (numerator f) := by
  cases f with
  | negative i => exact hf.elim
  | equal => decide
  | positive i => fin_cases i <;> decide
  | diagonal => decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem boundary_certificate (b : Boundary) (i : Fin 3) (hdirect : b≠.high ∨ i=2) :
    WholeIntervalPolynomial.centered 0 (boundaryLength b) (boundary b (numerator (.negative i)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength b) (boundary b (numerator (.negative i)))) ∧
    boundaryReserve b i<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength b)
      (boundary b (numerator (.negative i))) := by
  cases b <;> fin_cases i <;> norm_num at hdirect <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_certificate (i : Fin 2) :
    highCentered i.castSucc=C (highCoefficient i.castSucc 0)+C (highCoefficient i.castSucc 1)*X+
      C (highCoefficient i.castSucc 2)*X^2+
        ∑j : Fin 18,C (highCoefficient i.castSucc (j.val+3))*X^(j.val+3) ∧
    0<highCurvature i.castSucc ∧
    boundaryReserve .high i.castSucc<highCoefficient i.castSucc 0-
      (highCoefficient i.castSucc 1)^2/(4*highCurvature i.castSucc) := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem slope_certificate :
    slopePolynomial=C (slopePolynomial.coeff 0)+C (slopePolynomial.coeff 1)*X+
      C (slopePolynomial.coeff 2)*X^2+C (slopePolynomial.coeff 3)*X^3+
        C (slopePolynomial.coeff 4)*X^4 ∧
    (361/5000:ℚ)<slopePolynomial.coeff 0 ∧ (173/1000:ℚ)<slopePolynomial.coeff 1 ∧
    (101/10000:ℚ)<slopePolynomial.coeff 2 ∧ -(91/5000:ℚ)<slopePolynomial.coeff 3 ∧
    -(7/2500:ℚ)<slopePolynomial.coeff 4 := by decide

theorem mass_positive (f : Kind) (j : Fin 3) {t E : ℝ} (hd : Domain t E) :
    (18/25:ℝ)<evaluate t E (mass f j) :=
  positive_on_domain (mass_certificate f j).1 (mass_certificate f j).2 hd

theorem whole_positive (f : Kind) (hf : Whole f) {t E : ℝ} (hd : Domain t E) :
    0<evaluate t E (numerator f) := by
  have hh := positive_on_domain (whole_certificate f hf).1 (whole_certificate f hf).2 hd
  have hv : (0:ℝ)<(wholeReserve f:ℝ) := by
    cases f with
    | negative i => exact hf.elim
    | equal => norm_num [wholeReserve]
    | positive i => fin_cases i <;> norm_num [wholeReserve]
    | diagonal => norm_num [wholeReserve]
  exact hv.trans hh

theorem direct_boundary_positive (b : Boundary) (i : Fin 3) (hdirect : b≠.high ∨ i=2)
    {x : ℝ} (hx : x∈Icc 0 (boundaryLength b:ℝ)) :
    (boundaryReserve b i:ℝ)<aeval x (boundary b (numerator (.negative i))) :=
  WholeIntervalPolynomial.positive_on_interval
    (by cases b <;> norm_num [boundaryLength,L,h,d])
    (boundary_certificate b i hdirect).1 (boundary_certificate b i hdirect).2 hx

theorem high_tail_lower (i : Fin 2) {u : ℝ} (hu : |u|≤7/20) (j : Fin 18) :
    -(|(highCoefficient i.castSucc (j.val+3):ℝ)|*(7/20)^(j.val+1))*u^2≤
      (highCoefficient i.castSucc (j.val+3):ℝ)*u^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg u) hu (j.val+1)
  have hh := mul_le_mul_of_nonneg_left hp (abs_nonneg (highCoefficient i.castSucc (j.val+3):ℝ))
  have hb : |(highCoefficient i.castSucc (j.val+3):ℝ)*u^(j.val+1)|≤
      |(highCoefficient i.castSucc (j.val+3):ℝ)|*(7/20)^(j.val+1) := by
    simpa [abs_mul,abs_pow] using hh
  have hm := mul_le_mul_of_nonneg_right (abs_le.mp hb).1 (sq_nonneg u)
  rw [show u^(j.val+3)=u^(j.val+1)*u^2 by rw [←pow_add]; congr 1; omega]
  nlinarith

theorem high_positive (i : Fin 2) {x : ℝ} (hx : x∈Icc 0 (7/10:ℝ)) :
    (boundaryReserve .high i.castSucc:ℝ)<aeval x (boundary .high (numerator (.negative i.castSucc))) := by
  let u : ℝ := x-7/20
  have hu : |u|≤7/20 := by
    apply abs_le.mpr
    dsimp [u]
    constructor <;> linarith [hx.1,hx.2]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => high_tail_lower i hu j)
  have he : (∑j : Fin 18,-(|(highCoefficient i.castSucc (j.val+3):ℝ)|*(7/20)^(j.val+1))*u^2)=
      -(highTail i.castSucc:ℝ)*u^2 := by simp [highTail,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [he] at hsum
  have hid := congrArg (fun p : ℚ[X] => aeval u p) (high_certificate i).1
  simp only [map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X] at hid
  have hquadratic : (highCoefficient i.castSucc 0:ℝ)+(highCoefficient i.castSucc 1:ℝ)*u+
      (highCurvature i.castSucc:ℝ)*u^2≤aeval u (highCentered i.castSucc) := by
    dsimp [highCurvature]
    push_cast
    linarith
  have hκ : (0:ℝ)<(highCurvature i.castSucc:ℝ) := by exact_mod_cast (high_certificate i).2.1
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(highCoefficient i.castSucc 0:ℝ)) (b:=(highCoefficient i.castSucc 1:ℝ)) (x:=u) hκ
  have hreserve : (boundaryReserve .high i.castSucc:ℝ)<(highCoefficient i.castSucc 0:ℝ)-
      (highCoefficient i.castSucc 1:ℝ)^2/(4*(highCurvature i.castSucc:ℝ)) := by
    exact_mod_cast (high_certificate i).2.2
  have hvalue : aeval u (highCentered i.castSucc)=
      aeval x (boundary .high (numerator (.negative i.castSucc))) := by
    simp [highCentered,aeval_comp,u]
  rw [hvalue] at hquadratic
  linarith

theorem boundary_positive (b : Boundary) (i : Fin 3)
    {x : ℝ} (hx : x∈Icc 0 (boundaryLength b:ℝ)) :
    0<aeval x (boundary b (numerator (.negative i))) := by
  have hr : (0:ℝ)<(boundaryReserve b i:ℝ) := by
    cases b <;> fin_cases i <;> norm_num [boundaryReserve]
  apply hr.trans
  cases b
  · exact direct_boundary_positive .low i (Or.inl (by decide)) hx
  · exact direct_boundary_positive .equal i (Or.inl (by decide)) hx
  · fin_cases i
    · exact high_positive 0 hx
    · exact high_positive 1 hx
    · exact direct_boundary_positive .high 2 (Or.inr rfl) hx

theorem slope_positive {E : ℝ} (hE : E∈Icc 0 (7/10:ℝ)) :
    (13/200:ℝ)<aeval E slopePolynomial := by
  obtain ⟨hid,h0,h1,h2,h3,h4⟩ := slope_certificate
  have hc0 : (361/5000:ℝ)<(slopePolynomial.coeff 0:ℝ) := by exact_mod_cast h0
  have hc1 : (173/1000:ℝ)<(slopePolynomial.coeff 1:ℝ) := by exact_mod_cast h1
  have hc2 : (101/10000:ℝ)<(slopePolynomial.coeff 2:ℝ) := by exact_mod_cast h2
  have hc3 : -(91/5000:ℝ)<(slopePolynomial.coeff 3:ℝ) := by exact_mod_cast h3
  have hc4 : -(7/2500:ℝ)<(slopePolynomial.coeff 4:ℝ) := by exact_mod_cast h4
  have hm1 := mul_le_mul_of_nonneg_right hc1.le hE.1
  have hm2 := mul_le_mul_of_nonneg_right hc2.le (sq_nonneg E)
  have hm3 := mul_le_mul_of_nonneg_right hc3.le (pow_nonneg hE.1 3)
  have hm4 := mul_le_mul_of_nonneg_right hc4.le (pow_nonneg hE.1 4)
  have hp3 := pow_le_pow_left₀ hE.1 hE.2 3
  have hp4 := pow_le_pow_left₀ hE.1 hE.2 4
  have heval := congrArg (fun p : ℚ[X] => aeval E p) hid
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at heval
  nlinarith only [hc0,hm1,hm2,hm3,hm4,hp3,hp4,hE.1,sq_nonneg E]

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Certificate
