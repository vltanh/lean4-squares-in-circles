module

public import SquaresInCircles.Eight.TableFree.SoleScalarData

/-!
# A whole-interval polynomial gap for the low sole-E family

Uncompiled source. These are the two positive-sided squarings in (55)
of the sole-EH hand proof. The radius parameter is the lower endpoint
qLow, so the later comparison applies to the original common radius.
All three identities and coefficient bounds cover the complete interval
[0,1/5]. The exact reductions below have not been run.
-/

@[expose] public section
namespace SquaresInCircles.Eight.TableFree.SoleLowGapPolynomials
open Polynomial WholeIntervalPolynomial HighOrderTaylor SoleECoefficients

def sinCap : ℚ := PositiveScalarPolynomials.sine.eval (7/10)
def cosLower : ℚ[X] :=
  PositiveScalarPolynomials.cosine-C (1/20922789888000)*X^16
def cosCap : ℚ := cosLower.eval (7/10)
def sinUpper : ℚ[X] :=
  PositiveScalarPolynomials.sine+C (1/1307674368000)*X^15
def l : ℚ[X] := SoleScalarPolynomials.ell .low
def c : ℚ[X] := SoleScalarPolynomials.c .low
def q : ℚ := 19577/5000
def normSquare : ℚ[X] := l^2+c^2-2*l*c*C sinCap
def squareGap : ℚ[X] := 2*l*c*(C sinCap-sinUpper)
def demand : ℚ[X] := C (43/100)+c*(PositiveScalarPolynomials.cosine-C cosCap)
def firstSquare : ℚ[X] := C q*squareGap-demand^2
def certificate : ℚ[X] := firstSquare^2-4*C q*demand^2*normSquare

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem demand_identity : centered 0 (1/5) demand=
    expansion 18 (centered 0 (1/5) demand) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem firstSquare_identity : centered 0 (1/5) firstSquare=
    expansion 36 (centered 0 (1/5) firstSquare) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificate_identity : centered 0 (1/5) certificate=
    expansion 72 (centered 0 (1/5) certificate) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem demand_reserve : (63/100 : ℚ)<lowerOn 18 0 (1/5) demand := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem firstSquare_reserve : (17/10 : ℚ)<lowerOn 36 0 (1/5) firstSquare := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificate_reserve : (4/25 : ℚ)<lowerOn 72 0 (1/5) certificate := by decide

theorem reserves {t : ℝ} (ht : t∈domain .low) :
    63/100<aeval t demand ∧ 17/10<aeval t firstSquare ∧
      4/25<aeval t certificate := by
  have ht' : t∈Set.Icc ((0:ℚ):ℝ) ((1/5:ℚ):ℝ) := by
    simpa [domain] using ht
  exact ⟨positive_on_interval (by norm_num) demand_identity demand_reserve ht',
    positive_on_interval (by norm_num) firstSquare_identity firstSquare_reserve ht',
    positive_on_interval (by norm_num) certificate_identity certificate_reserve ht'⟩

theorem sinCap_eq : (sinCap:ℝ)=S15 frameCap := by
  norm_num [sinCap,PositiveScalarPolynomials.sine,S15,S13,S11,
    Arithmetic.sin9,Arithmetic.sin7,frameCap]

theorem cosCap_eq : (cosCap:ℝ)=C14 frameCap := by
  norm_num [cosCap,cosLower,PositiveScalarPolynomials.cosine,C14,C12,
    Arithmetic.cos10,Arithmetic.cos8,frameCap]

theorem sinUpper_eval (t : ℝ) : aeval t sinUpper=S13 t := by
  simp only [sinUpper,map_add,map_mul,aeval_C,aeval_pow,aeval_X,
    PositiveScalarPolynomials.sine_eval]
  dsimp [S15]
  push_cast
  ring

theorem coefficients_eval (t : ℝ) :
    aeval t l=ell .low t ∧ aeval t c=SoleECoefficients.c .low t := by
  have hh := SoleScalarData.polynomial_parameters .low t
  simpa [l,c,SoleScalarPolynomials.origin] using ⟨hh.2.1,hh.2.2.1⟩

theorem normSquare_eval (t : ℝ) : aeval t normSquare=
    (ell .low t)^2+(SoleECoefficients.c .low t)^2-
      2*ell .low t*SoleECoefficients.c .low t*S15 frameCap := by
  simp only [normSquare,map_sub,map_add,map_mul,map_pow,map_ofNat,aeval_C,
    (coefficients_eval t).1,(coefficients_eval t).2,sinCap_eq]

theorem squareGap_eval (t : ℝ) : aeval t squareGap=
    2*ell .low t*SoleECoefficients.c .low t*(S15 frameCap-S13 t) := by
  simp only [squareGap,map_sub,map_mul,map_ofNat,aeval_C,
    (coefficients_eval t).1,(coefficients_eval t).2,sinCap_eq,sinUpper_eval]

theorem demand_eval (t : ℝ) : aeval t demand=
    43/100+SoleECoefficients.c .low t*(C16 t-C14 frameCap) := by
  simp only [demand,map_add,map_mul,map_sub,aeval_C,
    (coefficients_eval t).2,PositiveScalarPolynomials.cosine_eval,cosCap_eq]
  norm_num

theorem firstSquare_eval (t : ℝ) : aeval t firstSquare=
    qLow*aeval t squareGap-(aeval t demand)^2 := by
  simp [firstSquare,q,qLow]

theorem certificate_eval (t : ℝ) : aeval t certificate=
    (aeval t firstSquare)^2-4*qLow*(aeval t demand)^2*aeval t normSquare := by
  simp [certificate,q,qLow]

end SquaresInCircles.Eight.TableFree.SoleLowGapPolynomials
