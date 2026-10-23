module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2PolynomialData

/-!
# Whole-interval positivity of all eighteen negative-DE numerators

Uncompiled transcription of equations (55)--(57), (63), and (66)--(73).
Each rational certificate is the coefficient identity from the hand
proof.  The two low T endpoints retain only adverse power coefficients;
the tight mixed and equal-angle numerators retain their Chebyshev
quadratic, and the high G numerators retain their cubic.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
open Polynomial WholeIntervalPolynomial ChebyshevLeadingBounds
open PositiveTD.Certificate (L h C4)

theorem eval_rat (p : ℚ[X]) (x : ℚ) : aeval (x:ℝ) p=(p.eval x:ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp

inductive Direct where
  | lowTSH | lowTSG | lowAM | lowASH | lowASG | highTB | highAB | derivativeH | derivativeG
  deriving DecidableEq, Fintype
def directPolynomial : Direct → ℚ[X]
  | .lowTSH => NSH .atT | .lowTSG => NSG .atT | .lowAM => NM .atA
  | .lowASH => NSH .atA | .lowASG => NSG .atA
  | .highTB => NB .atT | .highAB => NB .atA
  | .derivativeH => derivativeNumerator true | .derivativeG => derivativeNumerator false
def directFamily : Direct → Family
  | .lowTSH => .low | .lowTSG => .low | .lowAM => .low
  | .lowASH => .low | .lowASG => .low | _ => .high
def directDegree : Direct → ℕ
  | .lowTSH => 30 | .lowTSG => 32 | .lowAM => 21 | .lowASH => 16 | .lowASG => 18
  | .highTB => 41 | .highAB => 32 | .derivativeH => 58 | .derivativeG => 61
def directReserve : Direct → ℚ
  | .lowTSH => 3021758/10000000 | .lowTSG => 1617320/10000000
  | .lowAM => 475408/10000000 | .lowASH => 3024216/10000000
  | .lowASG => 1682265/10000000 | .highTB => 16343/10000000
  | .highAB => 669354/10000000 | .derivativeH => 5310/10000
  | .derivativeG => 4744/100000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem direct_identity (e : Direct) :
    centered (left (directFamily e)) (right (directFamily e)) (directPolynomial e)=
      expansion (directDegree e)
        (centered (left (directFamily e)) (right (directFamily e)) (directPolynomial e)) := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem direct_reserve (e : Direct) : directReserve e<
    lowerOn (directDegree e) (left (directFamily e)) (right (directFamily e))
      (directPolynomial e) := by
  cases e <;> decide

theorem direct_positive (e : Direct) {θ : ℝ}
    (hθ : θ∈Set.Icc (left (directFamily e):ℝ) (right (directFamily e):ℝ)) :
    (directReserve e:ℝ)<aeval θ (directPolynomial e) := by
  apply positive_on_interval _ (direct_identity e) (direct_reserve e) hθ
  cases e <;> norm_num [directFamily,left,right,L,h]

def lowPowerPolynomial (atZ : Bool) : ℚ[X] := if atZ then NZ .low .atT else NH .low .atT
def lowPowerDegree : Bool → ℕ | false => 33 | true => 64
def lowPowerReserve : Bool → ℚ | false => 18458/10000000 | true => 18219/10000000
def lowReverse (atZ : Bool) : ℚ[X] := DirectedPowerBounds.reverse L (lowPowerPolynomial atZ)
def lowEndpointAggregate (atZ : Bool) : ℚ := (lowReverse atZ).coeff 0-
  DirectedPowerBounds.negativeNorm (lowReverse atZ) 1 (lowPowerDegree atZ) L

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_power_identity (atZ : Bool) : lowReverse atZ=C ((lowReverse atZ).coeff 0)+
    PowerTailBounds.tail (lowReverse atZ) 1 (lowPowerDegree atZ) := by
  cases atZ <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_power_reserve (atZ : Bool) : lowPowerReserve atZ<lowEndpointAggregate atZ := by
  cases atZ <;> decide

theorem low_power_positive (atZ : Bool) {θ : ℝ} (hθ : θ∈Set.Icc (0:ℝ) (1/6)) :
    (lowPowerReserve atZ:ℝ)<aeval θ (lowPowerPolynomial atZ) := by
  let x : ℝ := 1/6-θ
  have hx : x∈Set.Icc 0 (L:ℝ) := by
    dsimp [x,L]
    exact ⟨by linarith [hθ.2],by linarith [hθ.1]⟩
  have ht := DirectedPowerBounds.tail_lower (p:=lowReverse atZ) (k:=0)
    (n:=lowPowerDegree atZ) hx
  have hi := congrArg (fun p : ℚ[X] => aeval x p) (low_power_identity atZ)
  simp only [map_add,aeval_C] at hi
  have hr : (lowPowerReserve atZ:ℝ)<(lowEndpointAggregate atZ:ℝ) := by
    exact_mod_cast low_power_reserve atZ
  have he : aeval x (lowReverse atZ)=aeval θ (lowPowerPolynomial atZ) := by
    simp [lowReverse,x,L]
  rw [he] at hi
  simp only [pow_zero,mul_one] at ht
  dsimp [lowEndpointAggregate] at hr
  push_cast at hr
  linarith

inductive Quadratic where | lowTM | highTZ | highAZ | highQStar
  deriving DecidableEq, Fintype
def quadraticPolynomial : Quadratic → ℚ[X]
  | .lowTM => NM .atT | .highTZ => NZ .high .atT | .highAZ => NZ .high .atA
  | .highQStar => qStar-mu .high .atT
def quadraticFamily : Quadratic → Family | .lowTM => .low | _ => .high
def quadraticDegree : Quadratic → ℕ | .lowTM => 33 | .highTZ => 77 | .highAZ => 54 | .highQStar => 8
def quadraticReserveValue : Quadratic → ℚ
  | .lowTM => 304587/10000000 | .highTZ => 3948/10000000
  | .highAZ => 1815/10000000 | .highQStar => 51799/10000000
def quadraticCoefficient (e : Quadratic) : ℕ → ℚ := coefficient (quadraticDegree e)
  (centered (left (quadraticFamily e)) (right (quadraticFamily e)) (quadraticPolynomial e))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quadratic_identity (e : Quadratic) :
    centered (left (quadraticFamily e)) (right (quadraticFamily e)) (quadraticPolynomial e)=
      C (quadraticCoefficient e 0-quadraticCoefficient e 2)+C (quadraticCoefficient e 1)*X+
        C (2*quadraticCoefficient e 2)*X^2+tail (quadraticCoefficient e) 3 (quadraticDegree e-2) := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quadratic_reserve (e : Quadratic) : 0<quadraticCoefficient e 2 ∧
    quadraticReserveValue e<quadraticReserve (quadraticCoefficient e) (quadraticDegree e-2) := by
  cases e <;> decide

theorem quadratic_positive (e : Quadratic) {θ : ℝ}
    (hθ : θ∈Set.Icc (left (quadraticFamily e):ℝ) (right (quadraticFamily e):ℝ)) :
    (quadraticReserveValue e:ℝ)<aeval θ (quadraticPolynomial e) := by
  have hb := quadratic_on_interval
    (by cases e <;> norm_num [quadraticFamily,left,right,L,h] :
      left (quadraticFamily e)<right (quadraticFamily e))
    (quadratic_identity e) (quadratic_reserve e).1 hθ
  have hr : (quadraticReserveValue e:ℝ)<
      (quadraticReserve (quadraticCoefficient e) (quadraticDegree e-2):ℝ) := by
    exact_mod_cast (quadratic_reserve e).2
  exact hr.trans_le hb

def cubicDegree : Split → ℕ | .atT => 45 | .atA => 31
def cubicCoefficient (e : Split) : ℕ → ℚ := coefficient (cubicDegree e) (centered L h (NG e))
def cubicReserveValue : Split → ℚ | .atT => 6044/10000000 | .atA => 3537/10000000
def cubicCurvature : Split → ℚ | .atT => 46795/10000000 | .atA => 35767/10000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cubic_identity (e : Split) : centered L h (NG e)=
    C (cubicCoefficient e 0-cubicCoefficient e 2)+
      C (cubicCoefficient e 1-3*cubicCoefficient e 3)*X+C (2*cubicCoefficient e 2)*X^2+
      C (4*cubicCoefficient e 3)*X^3+tail (cubicCoefficient e) 4 (cubicDegree e-3) := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cubic_reserve (e : Split) :
    cubicCurvature e<2*cubicCoefficient e 2-4*|cubicCoefficient e 3| ∧
    cubicReserveValue e<cubicReserve (cubicCoefficient e) (cubicDegree e-3) := by
  cases e <;> decide

theorem high_G_positive (e : Split) {θ : ℝ} (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) :
    (cubicReserveValue e:ℝ)<aeval θ (NG e) := by
  have hc : 0<2*cubicCoefficient e 2-4*|cubicCoefficient e 3| :=
    (by cases e <;> norm_num [cubicCurvature] : 0<cubicCurvature e).trans (cubic_reserve e).1
  have hb := cubic_on_interval (by norm_num [L,h] : L<h) (cubic_identity e) hc hθ
  have hr : (cubicReserveValue e:ℝ)<
      (cubicReserve (cubicCoefficient e) (cubicDegree e-3):ℝ) := by
    exact_mod_cast (cubic_reserve e).2
  exact hr.trans_le hb

def lowDerivativePolynomial (atZ : Bool) : ℚ[X] :=
  if atZ then NZ .low .atA else NH .low .atA
def lowDerivativeDegree : Bool → ℕ | false => 18 | true => 39
def lowDerivativeBound : Bool → ℚ | false => -(9115/10000) | true => -(8814/10000)
def lowDerivativeEndpoint : Bool → ℚ | false => 125371/10000000 | true => 129080/10000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_derivative_certificate (atZ : Bool) :
    centered 0 L (lowDerivativePolynomial atZ).derivative=
      expansion (lowDerivativeDegree atZ) (centered 0 L (lowDerivativePolynomial atZ).derivative) ∧
    upperOn (lowDerivativeDegree atZ) 0 L (lowDerivativePolynomial atZ).derivative<
      lowDerivativeBound atZ ∧
    lowDerivativeEndpoint atZ<(lowDerivativePolynomial atZ).eval L := by
  cases atZ <;> decide

theorem low_A_monotone_positive (atZ : Bool) {θ : ℝ} (hθ : θ∈Set.Icc (0:ℝ) (1/6)) :
    (lowDerivativeEndpoint atZ:ℝ)<aeval θ (lowDerivativePolynomial atZ) := by
  have hc := low_derivative_certificate atZ
  have hm : AntitoneOn (fun x : ℝ => aeval x (lowDerivativePolynomial atZ))
      (Set.Icc (0:ℝ) (1/6)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt _ x).continuousAt.continuousWithinAt)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt _ x)
    intro x hx
    have hb := (interval_bounds (by norm_num [L] : (0:ℚ)<L)
      hc.1 (Set.Ioo_subset_Icc_self hx)).2
    have hr : (upperOn (lowDerivativeDegree atZ) 0 L (lowDerivativePolynomial atZ).derivative:ℝ)<
        (lowDerivativeBound atZ:ℝ) := by exact_mod_cast hc.2.1
    have hn : (lowDerivativeBound atZ:ℝ)<0 := by cases atZ <;> norm_num [lowDerivativeBound]
    linarith
  have he : (lowDerivativeEndpoint atZ:ℝ)<aeval (1/6:ℝ) (lowDerivativePolynomial atZ) := by
    have hr : (lowDerivativeEndpoint atZ:ℝ)<((lowDerivativePolynomial atZ).eval L:ℝ) := by
      exact_mod_cast hc.2.2
    simpa only [←eval_rat,L] using hr
  exact he.trans_le (hm hθ (by norm_num) hθ.2)

def highDerivativeDegree : Split → ℕ | .atT => 41 | .atA => 27
def highDerivativeBound : Split → ℚ | .atT => 275690/10000000 | .atA => 77290/10000000
def highDerivativeEndpoint : Split → ℚ | .atT => 12686/10000000 | .atA => 10199/10000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_derivative_certificate (e : Split) :
    centered L h (NH .high e).derivative=
      expansion (highDerivativeDegree e) (centered L h (NH .high e).derivative) ∧
    highDerivativeBound e<lowerOn (highDerivativeDegree e) L h (NH .high e).derivative ∧
    highDerivativeEndpoint e<(NH .high e).eval L := by
  cases e <;> decide

theorem high_H_positive (e : Split) {θ : ℝ} (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) :
    (highDerivativeEndpoint e:ℝ)<aeval θ (NH .high e) := by
  have hc := high_derivative_certificate e
  have hm : MonotoneOn (fun x : ℝ => aeval x (NH .high e)) (Set.Icc (1/6:ℝ) (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt _ x).continuousAt.continuousWithinAt)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt _ x)
    intro x hx
    have hb := positive_on_interval (by norm_num [L,h] : L<h)
      hc.1 hc.2.1 (Set.Ioo_subset_Icc_self hx)
    have hr : (0:ℝ)<(highDerivativeBound e:ℝ) := by cases e <;> norm_num [highDerivativeBound]
    exact (hr.trans hb).le
  have he : (highDerivativeEndpoint e:ℝ)<aeval (1/6:ℝ) (NH .high e) := by
    have hr : (highDerivativeEndpoint e:ℝ)<((NH .high e).eval L:ℝ) := by exact_mod_cast hc.2.2
    simpa only [←eval_rat,L] using hr
  exact he.trans_le (hm (by norm_num) hθ hθ.1)

theorem low_numerators_positive (e : Split) {θ : ℝ} (hθ : θ∈Set.Icc (0:ℝ) (1/6)) :
    0<aeval θ (NH .low e) ∧ 0<aeval θ (NM e) ∧
      0<aeval θ (NSH e) ∧ 0<aeval θ (NSG e) ∧ 0<aeval θ (NZ .low e) := by
  cases e
  · have hH := low_power_positive false hθ
    have hM := quadratic_positive .lowTM hθ
    have hSH := direct_positive .lowTSH hθ
    have hSG := direct_positive .lowTSG hθ
    have hZ := low_power_positive true hθ
    norm_num [lowPowerReserve,lowPowerPolynomial,quadraticReserveValue,quadraticPolynomial,
      directReserve,directPolynomial] at hH hM hSH hSG hZ
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  · have hH := low_A_monotone_positive false hθ
    have hM := direct_positive .lowAM hθ
    have hSH := direct_positive .lowASH hθ
    have hSG := direct_positive .lowASG hθ
    have hZ := low_A_monotone_positive true hθ
    norm_num [lowDerivativeEndpoint,lowDerivativePolynomial,directReserve,directPolynomial]
      at hH hM hSH hSG hZ
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem high_numerators_positive (e : Split) {θ : ℝ} (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) :
    0<aeval θ (NH .high e) ∧ 0<aeval θ (NG e) ∧
      0<aeval θ (NB e) ∧ 0<aeval θ (NZ .high e) := by
  have hH := high_H_positive e hθ
  have hG := high_G_positive e hθ
  cases e
  · have hB := direct_positive .highTB hθ
    have hZ := quadratic_positive .highTZ hθ
    norm_num [highDerivativeEndpoint,cubicReserveValue,directReserve,directPolynomial,
      quadraticReserveValue,quadraticPolynomial] at hH hG hB hZ
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · have hB := direct_positive .highAB hθ
    have hZ := quadratic_positive .highAZ hθ
    norm_num [highDerivativeEndpoint,cubicReserveValue,directReserve,directPolynomial,
      quadraticReserveValue,quadraticPolynomial] at hH hG hB hZ
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

def lowAuxiliary (e : Split) : Fin 9 → ℚ[X] :=
  ![RH .low,RG .low,RB .low e,RHminus .low,RHcap,RGcap,
    C4*RH .low,C4*RG .low,C4*RB .low e]
def highAuxiliary (e : Split) : Fin 11 → ℚ[X] :=
  ![RH .high,RG .high,RB .high e,RD,RHminus .high,RGminus,RBminus e,
    C4*RH .high,C4*RG .high,C4*RB .high e,secantR]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_auxiliary_certificate (e : Split) (i : Fin 9) :
    centered 0 L (lowAuxiliary e i)=expansion 8 (centered 0 L (lowAuxiliary e i)) ∧
    (37/50:ℚ)<lowerOn 8 0 L (lowAuxiliary e i) := by
  cases e <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_auxiliary_certificate (e : Split) (i : Fin 11) :
    centered L h (highAuxiliary e i)=expansion 12 (centered L h (highAuxiliary e i)) ∧
    (3/5:ℚ)<lowerOn 12 L h (highAuxiliary e i) := by
  cases e <;> fin_cases i <;> decide

theorem low_auxiliary_positive (e : Split) (i : Fin 9) {θ : ℝ}
    (hθ : θ∈Set.Icc (0:ℝ) (1/6)) : 0<aeval θ (lowAuxiliary e i) := by
  have hc := low_auxiliary_certificate e i
  have hp := positive_on_interval (by norm_num [L] : (0:ℚ)<L) hc.1 hc.2 hθ
  norm_num at hp
  linarith

theorem high_auxiliary_positive (e : Split) (i : Fin 11) {θ : ℝ}
    (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) : 0<aeval θ (highAuxiliary e i) := by
  have hc := high_auxiliary_certificate e i
  have hp := positive_on_interval (by norm_num [L,h] : L<h) hc.1 hc.2 hθ
  norm_num at hp
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem multiplied_baseline_certificate (f : Family) (e : Split) :
    let p := if f=.low then lowB e+C dbar else highB e-1
    centered (left f) (right f) p=expansion 14 (centered (left f) (right f) p) ∧
      (1:ℚ)<lowerOn 14 (left f) (right f) p := by
  cases f <;> cases e <;> decide

theorem multiplied_baseline_positive (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Set.Icc (left f:ℝ) (right f:ℝ)) :
    0<aeval θ (if f=.low then lowB e+C dbar else highB e-1) := by
  have hc := multiplied_baseline_certificate f e
  have hp := positive_on_interval
    (by cases f <;> norm_num [left,right,L,h] : left f<right f) hc.1 hc.2 hθ
  norm_num at hp
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem qStar_A_certificate :
    centered L h (qStar-c .high)=expansion 3 (centered L h (qStar-c .high)) ∧
    lowerOn 3 L h (qStar-c .high)=(796/1000000:ℚ) := by decide

theorem qStar_A_positive {θ : ℝ} (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) :
    0<aeval θ (qStar-c .high) := by
  have hp := (interval_bounds (by norm_num [L,h] : L<h) qStar_A_certificate.1 hθ).1
  rw [qStar_A_certificate.2] at hp
  norm_num at hp
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
