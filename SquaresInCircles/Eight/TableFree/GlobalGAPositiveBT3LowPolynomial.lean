module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LargePolynomial

/-!
# The two small-total BT3 endpoint certificates

Uncompiled transcription of Section 6. Both certificates use the
same three positive cubic masses. The A endpoint is bounded directly
on `[0,1/6]`; the T endpoint decreases to a positive right endpoint.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LowCertificate
open NonnegativeTotals

abbrev L : ℚ := 1/6
abbrev C10 := PositiveTD.Certificate.C10
abbrev S9 := PositiveTD.Certificate.S9
abbrev S11 := PositiveTD.Certificate.S11
abbrev Rbar := NonnegativeTotals.Certificate.Rbar
abbrev abar := NonnegativeTotals.Certificate.abar
abbrev sigmabar := NonnegativeTotals.Certificate.sigmabar
abbrev cbar : ℚ := 449607033/500000000

def k : ℚ[X] := C (2933/5000)+C (1239/2500)*X
def m : ℚ[X] := C (5821/5000)-C (4437/5000)*X
def J : ℚ[X] := C (1/2)*(C10-1)+C (1/2-abar)*S9

def ABase : Endpoint → ℚ[X]
  | .atA => C 2*k+C (11/2-cbar)+m*C (5/2-cbar)+J
  | .atT => C 2*k+C (11/2-cbar)+m*
      (1+C (3/2-cbar)*C10+C (1/2+(293/1000)*(1-cbar)-sigmabar)*S9)
def A (ep : Endpoint) : ℚ[X] := ABase ep+C10-1

def P : Fin 3 → ℚ[X] := ![1+k^2-C 2*k*S11,1+k^2,1+m^2]
def rho : Fin 3 → ℚ := ![579676539/500000000,579676539/500000000,1534718749/1000000000]

def truncate3 (p : ℚ[X]) : ℚ[X] := ∑i : Fin 4,C (p.coeff i.val)*X^i.val
def mass (i : Fin 3) : ℚ[X] :=
  let p := P i
  let w := C (1/p.eval 0)*(truncate3 p-C (p.eval 0))
  C (rho i)*truncate3 (1+C (1/2)*w-C (1/8)*w^2+C (1/16)*w^3)
def numerator (ep : Endpoint) : ℚ[X] :=
  PositiveTD.Certificate.num3 (A ep) (P 0) (P 1) (P 2) (mass 0) (mass 1) (mass 2)
def degree : Endpoint → ℕ | .atA => 19 | .atT => 20

@[simp] theorem k_eval (t : ℝ) : aeval t k=lowK t := by
  simp [k,lowK]
@[simp] theorem m_eval (t : ℝ) : aeval t m=lowM t := by
  simp [m,lowM,Cmax]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_certificate (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 L (mass i)=
      WholeIntervalPolynomial.expansion 3 (WholeIntervalPolynomial.centered 0 L (mass i)) ∧
    (11/10:ℚ)<WholeIntervalPolynomial.lowerOn 3 0 L (mass i) := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem A_certificate :
    WholeIntervalPolynomial.centered 0 L (numerator .atA)=
      WholeIntervalPolynomial.expansion 19 (WholeIntervalPolynomial.centered 0 L (numerator .atA)) ∧
    (61/50000:ℚ)<WholeIntervalPolynomial.lowerOn 19 0 L (numerator .atA) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem T_certificate :
    WholeIntervalPolynomial.centered 0 L (numerator .atT).derivative=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 L (numerator .atT).derivative) ∧
    WholeIntervalPolynomial.upperOn 20 0 L (numerator .atT).derivative<-(13/500:ℚ) ∧
    (117/25000:ℚ)<(numerator .atT).eval L := by decide

theorem mass_positive (i : Fin 3) {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    0<aeval t (mass i) := by
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<L) (mass_certificate i).1 (mass_certificate i).2 ht
  linarith

theorem A_positive {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    (1/1000:ℝ)<aeval t (numerator .atA) := by
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<L) A_certificate.1 A_certificate.2 ht
  linarith

theorem T_antitone : AntitoneOn (fun t : ℝ => aeval t (numerator .atT))
    (Icc (0:ℝ) (1/6)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun t _ => (CenteredMonomialBounds.aeval_hasDerivAt (numerator .atT) t).continuousAt.continuousWithinAt)
    (fun t _ => CenteredMonomialBounds.aeval_hasDerivAt (numerator .atT) t)
  intro t ht
  have hh := (WholeIntervalPolynomial.interval_bounds
    (by norm_num : (0:ℚ)<L) T_certificate.1 (Ioo_subset_Icc_self ht)).2
  have hr : (WholeIntervalPolynomial.upperOn 20 0 L (numerator .atT).derivative:ℝ)<-(13/500:ℝ) := by
    exact_mod_cast T_certificate.2.1
  linarith

theorem T_positive {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    (1/1000:ℝ)<aeval t (numerator .atT) := by
  have hh := T_antitone ht (show (1/6:ℝ)∈Icc 0 (1/6) by norm_num) ht.2
  have he : (117/25000:ℝ)<aeval (1/6:ℝ) (numerator .atT) := by
    have hc : (117/25000:ℝ)<((numerator .atT).eval L:ℝ) := by
      exact_mod_cast T_certificate.2.2
    simpa only [←NonnegativeTotals.Certificate.eval_rat,L] using hc
  linarith

theorem numerator_positive (ep : Endpoint) {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    (1/1000:ℝ)<aeval t (numerator ep) := by
  cases ep
  · exact A_positive ht
  · exact T_positive ht

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.LowCertificate
