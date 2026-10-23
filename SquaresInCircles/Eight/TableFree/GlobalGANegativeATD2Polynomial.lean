module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2PolynomialData

/-!
# Whole-interval positivity of the fourteen negative-A / TD2 numerators

Uncompiled transcription of equations (50)--(56) and (64)--(66) in the
complete scalar companion. The two tight low numerators keep their
displayed leading terms, the mixed numerator keeps its Chebyshev
quadratic, and the three endpoint quotients keep their positive constant.
Every remaining bound is the stated whole-interval coefficient sum.
The rational identities are proof terms, not executed certificates.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Polynomial WholeIntervalPolynomial ChebyshevLeadingBounds
open PositiveTD.Certificate (h)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_H_identity : lowHFlip=C (lowHFlip.coeff 0)+C (lowHFlip.coeff 1)*X+
    C (lowHFlip.coeff 2)*X^2+X^3*lowHTail := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_H_coefficients :
    (161/100000:ℚ)<lowHFlip.coeff 0 ∧
    (-173/5000:ℚ)<lowHFlip.coeff 1 ∧
    (-191/500:ℚ)<lowHFlip.coeff 2 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_H_tail_expansion : centered 0 split lowHTail=
    expansion 34 (centered 0 split lowHTail) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_H_tail_reserve : (158/5:ℚ)<lowerOn 34 0 split lowHTail := by decide

theorem low_H_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    (97/100000:ℝ)<aeval z (NH .low) := by
  let u : ℝ := 1/5-z
  have hu : u∈Set.Icc (0:ℝ) (split:ℝ) := by
    norm_num [u,split]
    exact ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have ht := positive_on_interval (by norm_num [split] : (0:ℚ)<split)
    low_H_tail_expansion low_H_tail_reserve hu
  have h0 : (161/100000:ℝ)<(lowHFlip.coeff 0:ℝ) := by
    exact_mod_cast low_H_coefficients.1
  have h1 : (-173/5000:ℝ)<(lowHFlip.coeff 1:ℝ) := by
    exact_mod_cast low_H_coefficients.2.1
  have h2 : (-191/500:ℝ)<(lowHFlip.coeff 2:ℝ) := by
    exact_mod_cast low_H_coefficients.2.2
  have he := congrArg (fun p : ℚ[X] => aeval u p) low_H_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at he
  have hrefl : aeval u lowHFlip=aeval z (NH .low) := by
    simp [lowHFlip,u,split]
  rw [hrefl] at he
  have hlinear := mul_le_mul_of_nonneg_right h1.le hu.1
  have hquadratic := mul_le_mul_of_nonneg_right h2.le (sq_nonneg u)
  have hcubic := mul_le_mul_of_nonneg_left ht.le (pow_nonneg hu.1 3)
  have hretained := mul_nonneg hu.1 (sq_nonneg (u-1/50))
  have hcomplete := sq_nonneg (u-(1181/25000)/(2*(441/500)))
  norm_num at ht hcubic
  nlinarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_Z_identity : lowZFlip=C (lowZFlip.coeff 0)+C (lowZFlip.coeff 1)*X+
    X^2*lowZTail := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_Z_coefficients :
    (753/500000:ℚ)<lowZFlip.coeff 0 ∧
    (-987/10000:ℚ)<lowZFlip.coeff 1 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_Z_tail_expansion : centered 0 split lowZTail=
    expansion 64 (centered 0 split lowZTail) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_Z_tail_reserve : (77/10:ℚ)<lowerOn 64 0 split lowZTail := by decide

theorem low_Z_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    (59/50000:ℝ)<aeval z (NZ .low) := by
  let u : ℝ := 1/5-z
  have hu : u∈Set.Icc (0:ℝ) (split:ℝ) := by
    norm_num [u,split]
    exact ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have ht := positive_on_interval (by norm_num [split] : (0:ℚ)<split)
    low_Z_tail_expansion low_Z_tail_reserve hu
  have h0 : (753/500000:ℝ)<(lowZFlip.coeff 0:ℝ) := by
    exact_mod_cast low_Z_coefficients.1
  have h1 : (-987/10000:ℝ)<(lowZFlip.coeff 1:ℝ) := by
    exact_mod_cast low_Z_coefficients.2
  have he := congrArg (fun p : ℚ[X] => aeval u p) low_Z_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at he
  have hrefl : aeval u lowZFlip=aeval z (NZ .low) := by
    simp [lowZFlip,u,split]
  rw [hrefl] at he
  have hlinear := mul_le_mul_of_nonneg_right h1.le hu.1
  have hquadratic := mul_le_mul_of_nonneg_left ht.le (sq_nonneg u)
  norm_num at ht hquadratic
  nlinarith [sq_nonneg (u-(987/10000)/(2*(77/10)))]

def mixedCoefficient : ℕ→ℚ := coefficient 40 (centered 0 split NM)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_mixed_identity : centered 0 split NM=
    C (mixedCoefficient 0-mixedCoefficient 2)+C (mixedCoefficient 1)*X+
      C (2*mixedCoefficient 2)*X^2+tail mixedCoefficient 3 38 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_mixed_reserve : 0<mixedCoefficient 2 ∧
    (153/5000:ℚ)<quadraticReserve mixedCoefficient 38 := by decide

theorem low_M_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    (153/5000:ℝ)<aeval z NM := by
  have hb := quadratic_on_interval (by norm_num [split] : (0:ℚ)<split)
    low_mixed_identity low_mixed_reserve.1 hz
  have hr : (153/5000:ℝ)<(quadraticReserve mixedCoefficient 38:ℝ) := by
    exact_mod_cast low_mixed_reserve.2
  exact hr.trans_le hb

/-- The eight direct coefficient-norm certificates in the companion. -/
inductive Direct where
  | lowSH | lowSG | highB | highZ | highZA | cutGAB | cutABG | cutABH
  deriving DecidableEq, Fintype
def directPolynomial : Direct→ℚ[X]
  | .lowSH => NSH | .lowSG => NSG | .highB => NB | .highZ => NZ .high
  | .highZA => NZA | .cutGAB => cutN .gaB | .cutABG => cutN .abG | .cutABH => cutN .abH
def directDegree : Direct→ℕ
  | .lowSH => 32 | .lowSG => 35 | .highB => 36 | .highZ => 72
  | .highZA => 72 | .cutGAB => 36 | .cutABG => 40 | .cutABH => 38
def directLeft : Direct→ℚ
  | .lowSH => 0 | .lowSG => 0 | .highB => split | .highZ => split
  | .highZA => split | .cutGAB => 1/4 | .cutABG => 19/50 | .cutABH => 19/50
def directRight : Direct→ℚ | .lowSH => split | .lowSG => split | _ => h
def directReserve : Direct→ℚ
  | .lowSH => 231/1250 | .lowSG => 157/5000 | .highB => 1/200
  | .highZ => 91/50000 | .highZA => 51/12500 | .cutGAB => 21/3125
  | .cutABG => 107/2000 | .cutABH => 111/2000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem direct_expansion (e : Direct) :
    centered (directLeft e) (directRight e) (directPolynomial e)=
      expansion (directDegree e)
        (centered (directLeft e) (directRight e) (directPolynomial e)) := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem direct_reserve (e : Direct) : directReserve e<
    lowerOn (directDegree e) (directLeft e) (directRight e) (directPolynomial e) := by
  cases e <;> decide

theorem direct_positive (e : Direct) {z : ℝ}
    (hz : z∈Set.Icc (directLeft e:ℝ) (directRight e:ℝ)) :
    (directReserve e:ℝ)<aeval z (directPolynomial e) := by
  apply positive_on_interval _ (direct_expansion e) (direct_reserve e) hz
  cases e <;> norm_num [directLeft,directRight,split,h]

/-- The three positive secant quotients. -/
inductive Quotient where | highH | highG | cutGAH
  deriving DecidableEq, Fintype
def quotientPolynomial : Quotient→ℚ[X]
  | .highH => highHQuotient | .highG => highGQuotient | .cutGAH => cutHQuotient
def quotientNumerator : Quotient→ℚ[X]
  | .highH => NH .high | .highG => NG | .cutGAH => cutN .gaH
def quotientLeft : Quotient→ℚ | .highH => split | .highG => split | .cutGAH => 1/4
def quotientDegree : Quotient→ℕ | .highH => 37 | .highG => 39 | .cutGAH => 37
def quotientReserve : Quotient→ℚ | .highH => 53/2500 | .highG => 457/5000 | .cutGAH => 453/1000
def quotientEndpoint : Quotient→ℚ | .highH => 57/25000 | .highG => 173/20000 | .cutGAH => 33/5000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quotient_identity (e : Quotient) :
    quotientNumerator e=C ((quotientNumerator e).eval (quotientLeft e))+
      (X-C (quotientLeft e))*quotientPolynomial e := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quotient_expansion (e : Quotient) :
    centered (quotientLeft e) h (quotientPolynomial e)=
      expansion (quotientDegree e) (centered (quotientLeft e) h (quotientPolynomial e)) := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quotient_reserve (e : Quotient) :
    quotientReserve e<lowerOn (quotientDegree e) (quotientLeft e) h (quotientPolynomial e) ∧
    quotientEndpoint e<(quotientNumerator e).eval (quotientLeft e) := by
  cases e <;> decide

theorem quotient_positive (e : Quotient) {z : ℝ}
    (hz : z∈Set.Icc (quotientLeft e:ℝ) (h:ℝ)) :
    (quotientEndpoint e:ℝ)<aeval z (quotientNumerator e) := by
  have ht := positive_on_interval
    (by cases e <;> norm_num [quotientLeft,split,h] : quotientLeft e<h)
    (quotient_expansion e) (quotient_reserve e).1 hz
  have hp : 0≤aeval z (quotientPolynomial e) := by
    have hr : (0:ℝ)<(quotientReserve e:ℝ) := by
      cases e <;> norm_num [quotientReserve]
    exact (hr.trans ht).le
  have he := congrArg (fun p : ℚ[X] => aeval z p) (quotient_identity e)
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X] at he
  have hleft : (quotientEndpoint e:ℝ)<
      ((quotientNumerator e).eval (quotientLeft e):ℝ) := by
    exact_mod_cast (quotient_reserve e).2
  have hterm := mul_nonneg (sub_nonneg.mpr hz.1) hp
  linarith

theorem low_numerators_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    0<aeval z (NH .low) ∧ 0<aeval z (NZ .low) ∧ 0<aeval z NM ∧
      0<aeval z NSH ∧ 0<aeval z NSG := by
  have hH := low_H_positive hz
  have hZ := low_Z_positive hz
  have hM := low_M_positive hz
  have hSH := direct_positive .lowSH hz
  have hSG := direct_positive .lowSG hz
  norm_num [directReserve,directPolynomial] at hSH hSG
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem high_numerators_positive {z : ℝ} (hz : z∈Set.Icc (1/5:ℝ) (7/10:ℝ)) :
    0<aeval z (NH .high) ∧ 0<aeval z NG ∧ 0<aeval z NB ∧
      0<aeval z (NZ .high) ∧ 0<aeval z NZA := by
  have hH := quotient_positive .highH hz
  have hG := quotient_positive .highG hz
  have hB := direct_positive .highB hz
  have hZ := direct_positive .highZ hz
  have hZA := direct_positive .highZA hz
  norm_num [quotientEndpoint,quotientNumerator] at hH hG
  norm_num [directReserve,directPolynomial] at hB hZ hZA
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem cut_numerator_positive (e : Cut) {z : ℝ}
    (hz : z∈Set.Icc (cutAngle e:ℝ) (h:ℝ)) : 0<aeval z (cutN e) := by
  cases e
  · have hh := quotient_positive .cutGAH hz
    norm_num [quotientEndpoint,quotientNumerator] at hh
    linarith
  · have hh := direct_positive .cutGAB hz
    norm_num [directReserve,directPolynomial] at hh
    linarith
  · have hh := direct_positive .cutABG hz
    norm_num [directReserve,directPolynomial] at hh
    linarith
  · have hh := direct_positive .cutABH hz
    norm_num [directReserve,directPolynomial] at hh
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
