module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2Weights
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDScalarBounds
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# Whole-interval comparisons for the tilted negative-A weights

Uncompiled transcription of equations (28)--(35) in the complete scalar
companion. The low coarse bounds keep the displayed positive quadratic;
the remaining comparisons use the stated Chebyshev coefficient sums.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Polynomial WholeIntervalPolynomial
open PositiveTD.Certificate (h)

inductive Comparison where
  | lowMUpper | highKUpper | highMUpper | highMQuarter | highMThreeTenths
  | highMThird | highMLower | highMEnvelope | highMCoarseSlope
  deriving DecidableEq, Fintype
def coarseHighDifference : ℚ[X] := mCoarse .high-C (77/100)*l .high
def comparison : Comparison→ℚ[X]
  | .lowMUpper => C (71/50)*l .low-mHi .low
  | .highKUpper => C (41/50)*l .high-k .high
  | .highMUpper => C (129/125)*l .high-mHi .high
  | .highMQuarter => l .high-mHi .high
  | .highMThreeTenths => C (47/50)*l .high-mHi .high
  | .highMThird => C (23/25)*l .high-mHi .high
  | .highMLower => mLo .high-C (4/5)*l .high
  | .highMEnvelope => qStar .high-mHi .high
  | .highMCoarseSlope => -coarseHighDifference.derivative
def comparisonDegree : Comparison→ℕ
  | .highKUpper => 3 | .highMLower => 13 | .highMCoarseSlope => 4 | _ => 14
def comparisonLeft : Comparison→ℚ
  | .lowMUpper => 0 | .highMQuarter => 1/4 | .highMThreeTenths => 3/10
  | .highMThird => 1/3 | _ => split
def comparisonRight : Comparison→ℚ
  | .lowMUpper => split | .highMLower => 19/50 | _ => h
def comparisonReserve : Comparison→ℚ
  | .lowMUpper => 989/100000 | .highKUpper => 1027/50000 | .highMUpper => 119/6250
  | .highMQuarter => 2773/100000 | .highMThreeTenths => 303/100000
  | .highMThird => 499/100000 | .highMLower => 217/2500
  | .highMEnvelope => 31/25000 | .highMCoarseSlope => 197/1250

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem comparison_expansion (e : Comparison) :
    centered (comparisonLeft e) (comparisonRight e) (comparison e)=
      expansion (comparisonDegree e)
        (centered (comparisonLeft e) (comparisonRight e) (comparison e)) := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem comparison_reserve (e : Comparison) : comparisonReserve e<
    lowerOn (comparisonDegree e) (comparisonLeft e) (comparisonRight e) (comparison e) := by
  cases e <;> decide

theorem comparison_positive (e : Comparison) {z : ℝ}
    (hz : z∈Set.Icc (comparisonLeft e:ℝ) (comparisonRight e:ℝ)) :
    (comparisonReserve e:ℝ)<aeval z (comparison e) := by
  apply positive_on_interval _ (comparison_expansion e) (comparison_reserve e) hz
  cases e <;> norm_num [comparisonLeft,comparisonRight,split,h]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coarse_high_endpoint : (9/2000:ℚ)<coarseHighDifference.eval h := by decide

theorem coarse_high_positive {z : ℝ} (hz : z∈Set.Icc (1/5:ℝ) (7/10:ℝ)) :
    (9/2000:ℝ)<aeval z coarseHighDifference := by
  have hanti : AntitoneOn (fun x : ℝ => aeval x coarseHighDifference)
      (Set.Icc (1/5:ℝ) (7/10:ℝ)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt coarseHighDifference x).continuousAt.continuousWithinAt)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt coarseHighDifference x)
    intro x hx
    have hh := comparison_positive .highMCoarseSlope (Set.Ioo_subset_Icc_self hx)
    norm_num [comparisonReserve,comparison,map_neg] at hh
    linarith
  have hh := hanti hz (show (7/10:ℝ)∈Set.Icc (1/5:ℝ) (7/10:ℝ) by norm_num) hz.2
  have hr : (9/2000:ℝ)<aeval (7/10:ℝ) coarseHighDifference := by
    have he : aeval (7/10:ℝ) coarseHighDifference=(coarseHighDifference.eval h:ℝ) := by
      norm_num [coarseHighDifference,mCoarse,C2,S3,c,l,t,split,PositiveTD.Certificate.etaQ,h]
    rw [he]
    exact_mod_cast coarse_high_endpoint
  exact hr.trans_le hh

inductive CoarseLow where | tilted | secant
  deriving DecidableEq, Fintype
def coarseLowPolynomial : CoarseLow→ℚ[X]
  | .tilted => mCoarse .low-l .low
  | .secant => C (4643/5000)*(mCoarse .low+C (2/5)*X)-l .low
def coarseLowLower : CoarseLow→ℚ[X]
  | .tilted => C (33/2500)+C (163/125)*X+
      X^2*(C (631/250)-C (3153/200)*X+C (38211/200)*X^2)+C (83/100)*X^5
  | .secant => C (167/12500)+C (429/500)*X+
      X^2*(C (327/250)-C (15621/1000)*X+C (19169/100)*X^2)+C (77/100)*X^5
def coarseLowRemainder (e : CoarseLow) : ℚ[X] :=
  (coarseLowPolynomial e).comp (C split-X)-coarseLowLower e

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coarse_low_identity (e : CoarseLow) :
    coarseLowRemainder e=
      ∑ i : Fin 6,C ((coarseLowRemainder e).coeff i.val)*X^i.val := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coarse_low_coefficients (e : CoarseLow) (i : Fin 6) :
    0≤(coarseLowRemainder e).coeff i.val := by
  cases e <;> fin_cases i <;> decide

theorem coarse_low_remainder_nonneg (e : CoarseLow) {u : ℝ} (hu : 0≤u) :
    0≤aeval u (coarseLowRemainder e) := by
  rw [coarse_low_identity]
  simp only [map_sum,map_mul,map_pow,aeval_C,aeval_X]
  apply Finset.sum_nonneg
  intro i _
  have hc : (0:ℝ)≤((coarseLowRemainder e).coeff i.val:ℝ) := by
    exact_mod_cast coarse_low_coefficients e i
  exact mul_nonneg hc (pow_nonneg hu _)

theorem coarse_low_lower_positive (e : CoarseLow) {u : ℝ} (hu : 0≤u) :
    0<aeval u (coarseLowLower e) := by
  cases e
  · have hq : (0:ℝ)<631/250-(3153/200)*u+(38211/200)*u^2 := by
      nlinarith [sq_nonneg (u-(3153/200)/(2*(38211/200)))]
    have hp := mul_nonneg (sq_nonneg u) hq.le
    have h5 := pow_nonneg hu 5
    norm_num [coarseLowLower]
    nlinarith
  · have hq : (0:ℝ)<327/250-(15621/1000)*u+(19169/100)*u^2 := by
      nlinarith [sq_nonneg (u-(15621/1000)/(2*(19169/100)))]
    have hp := mul_nonneg (sq_nonneg u) hq.le
    have h5 := pow_nonneg hu 5
    norm_num [coarseLowLower]
    nlinarith

theorem coarse_low_positive (e : CoarseLow) {z : ℝ}
    (hz : z∈Set.Icc 0 (1/5:ℝ)) : 0<aeval z (coarseLowPolynomial e) := by
  have hu : 0≤1/5-z := by linarith [hz.2]
  have hr := coarse_low_remainder_nonneg e hu
  have hl := coarse_low_lower_positive e hu
  have he : aeval (1/5-z) (coarseLowRemainder e)=
      aeval z (coarseLowPolynomial e)-aeval (1/5-z) (coarseLowLower e) := by
    simp [coarseLowRemainder,aeval_comp,split]
  rw [he] at hr
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
