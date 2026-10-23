module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTPairedPolynomialData

/-!
# Exact whole-domain coefficients for paired nonpositive T

Uncompiled equations (31)--(35).  The finite rational identities below
use the stated tensor Chebyshev bound once on each native trapezoid;
the nine V boundaries use their full intervals.  No state subdivision
or sampled lower bound enters the certificate.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_certificate (f : Kind) (j : Fin 3) :
    transform f (mass f j)=expansion 3 (transform f (mass f j)) ∧
      (1:ℚ)<lowerOn f 3 (mass f j) := by
  cases f with
  | equal => fin_cases j <;> decide
  | positive i => fin_cases i <;> fin_cases j <;> decide
  | diagonal => fin_cases j <;> decide
  | negative i => fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem whole_certificate (f : Kind) (hf : Whole f) :
    transform f (numerator f)=expansion (degree f) (transform f (numerator f)) ∧
      wholeReserve f<lowerOn f (degree f) (numerator f) := by
  cases f with
  | equal => decide
  | positive i => fin_cases i <;> decide
  | diagonal => decide
  | negative i => exact hf.elim

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem boundary_certificate (b : Boundary) (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 (boundaryLength b) (boundary b (numerator (.negative i)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength b) (boundary b (numerator (.negative i)))) ∧
    boundaryReserve b i<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength b)
      (boundary b (numerator (.negative i))) := by
  cases b <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem slope_certificate :
    slopePolynomial=C (slopePolynomial.coeff 0)+C (slopePolynomial.coeff 1)*X+
      C (slopePolynomial.coeff 2)*X^2+C (slopePolynomial.coeff 3)*X^3+
        C (slopePolynomial.coeff 4)*X^4 ∧
    (411/10000:ℚ)<slopePolynomial.coeff 0 ∧ (1407/10000:ℚ)<slopePolynomial.coeff 1 ∧
    -(2/625:ℚ)<slopePolynomial.coeff 2 ∧ -(99/5000:ℚ)<slopePolynomial.coeff 3 ∧
    -(7/2500:ℚ)<slopePolynomial.coeff 4 := by decide

theorem mass_positive (f : Kind) (j : Fin 3) {x E : ℝ} (hd : Domain f x E) :
    (1:ℝ)<evaluate x E (mass f j) :=
  positive_on_domain (mass_certificate f j).1 (mass_certificate f j).2 hd

theorem whole_positive (f : Kind) (hf : Whole f) {x E : ℝ} (hd : Domain f x E) :
    0<evaluate x E (numerator f) := by
  have hh := positive_on_domain (whole_certificate f hf).1 (whole_certificate f hf).2 hd
  have hv : (0:ℝ)<(wholeReserve f:ℝ) := by
    cases f with
    | equal => norm_num [wholeReserve]
    | positive i => fin_cases i <;> norm_num [wholeReserve]
    | diagonal => norm_num [wholeReserve]
    | negative i => exact hf.elim
  exact hv.trans hh

theorem boundary_positive (b : Boundary) (i : Fin 3)
    {x : ℝ} (hx : x∈Icc 0 (boundaryLength b:ℝ)) :
    0<aeval x (boundary b (numerator (.negative i))) := by
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by cases b <;> norm_num [boundaryLength,L,M,h])
    (boundary_certificate b i).1 (boundary_certificate b i).2 hx
  have hr : (0:ℝ)<(boundaryReserve b i:ℝ) := by
    cases b <;> fin_cases i <;> norm_num [boundaryReserve]
  exact hr.trans hh

theorem slope_positive {E : ℝ} (hE : E∈Icc 0 (7/10:ℝ)) :
    (4/125:ℝ)<aeval E slopePolynomial := by
  obtain ⟨hid,h0,h1,h2,h3,h4⟩ := slope_certificate
  have hc0 : (411/10000:ℝ)<(slopePolynomial.coeff 0:ℝ) := by exact_mod_cast h0
  have hc1 : (1407/10000:ℝ)<(slopePolynomial.coeff 1:ℝ) := by exact_mod_cast h1
  have hc2 : -(2/625:ℝ)<(slopePolynomial.coeff 2:ℝ) := by exact_mod_cast h2
  have hc3 : -(99/5000:ℝ)<(slopePolynomial.coeff 3:ℝ) := by exact_mod_cast h3
  have hc4 : -(7/2500:ℝ)<(slopePolynomial.coeff 4:ℝ) := by exact_mod_cast h4
  have hm1 := mul_le_mul_of_nonneg_right hc1.le hE.1
  have hm2 := mul_le_mul_of_nonneg_right hc2.le (sq_nonneg E)
  have hm3 := mul_le_mul_of_nonneg_right hc3.le (pow_nonneg hE.1 3)
  have hm4 := mul_le_mul_of_nonneg_right hc4.le (pow_nonneg hE.1 4)
  have hp2 := pow_le_pow_left₀ hE.1 hE.2 2
  have hp3 := pow_le_pow_left₀ hE.1 hE.2 3
  have hp4 := pow_le_pow_left₀ hE.1 hE.2 4
  have heval := congrArg (fun P : ℚ[X] => aeval E P) hid
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at heval
  nlinarith only [hc0,hm1,hm2,hm3,hm4,hp2,hp3,hp4,hE.1]

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Certificate
