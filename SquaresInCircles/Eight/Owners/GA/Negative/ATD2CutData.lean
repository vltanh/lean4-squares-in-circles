module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Weights
public import SquaresInCircles.Eight.Owners.GA.Positive.TDScalarBounds

/-!
# Eight squares: the four original negative-A cut endpoints

The GA angle remains 1/4 and the AB angle remains 19/50.
Their rotated H/G/B norms are the unaffected pairs from the original
secant assignment.
-/

section
/-!
## Whole-interval comparisons for the tilted negative-A weights

The low coarse bounds keep the displayed positive quadratic;
the remaining comparisons use the stated Chebyshev coefficient sums.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
open Polynomial WholeIntervalPolynomial
open PositiveTD.Certificate (h)

inductive Comparison where
  | lowMUpper | highKUpper | highMUpper | highMQuarter | highMThreeTenths
  | highMThird | highMLower | highMEnvelope | highMCoarseSlope
  deriving DecidableEq

instance : Fintype Comparison where
  elems := {.lowMUpper, .highKUpper, .highMUpper, .highMQuarter, .highMThreeTenths, .highMThird, .highMLower, .highMEnvelope, .highMCoarseSlope}
  complete x := by cases x <;> decide
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


/-! ### Kernel certificates

The comparison polynomials are mirrored by scaled integer coefficient lists
(`PolynomialCertificates`); their re-expansion identities and reserves are
integer computations checked by the kernel. -/

section R41Certificates
open WholeIntervalPolynomial.Certificate

private theorem r41_lt_of_int {r : ℚ} {n d s m : ℕ} {Z : ℤ} (hr : r=(n:ℚ)/d) (hd : 0<d)
    (hs : 0<s) (h : (n:ℤ)*(s*2^m)<2*d*Z) : r<(Z:ℚ)/(s*2^m/2) := by
  have hd' : (0:ℚ)<d := by exact_mod_cast hd
  have hs' : (0:ℚ)<(s:ℚ)*2^m/2 := by positivity
  rw [hr,div_lt_div_iff₀ hd' hs']
  have h' := (Int.cast_lt (R := ℚ)).mpr h
  push_cast at h'
  linarith

private def r41S5 : Scaled :=
  (Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))
private theorem r41_rep_S5 : r41S5.Rep PositiveTD.Certificate.S5 :=
  (Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))
private def r41S9 : Scaled :=
  (r41S5.sub ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))).add
    ((Scaled.const (1/362880)).mul (Scaled.var.pow 9))
private theorem r41_rep_S9 : r41S9.Rep PositiveTD.Certificate.S9 :=
  (r41_rep_S5.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 9))
private def r41S11 : Scaled := r41S9.sub ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11))
private theorem r41_rep_S11 : r41S11.Rep PositiveTD.Certificate.S11 :=
  r41_rep_S9.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11))
private def r41C4 : Scaled :=
  ((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))
private theorem r41_rep_C4 : r41C4.Rep PositiveTD.Certificate.C4 :=
  (Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))
private def r41C10 : Scaled :=
  ((r41C4.sub ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
    ((Scaled.const (1/40320)).mul (Scaled.var.pow 8))).sub
    ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10))
private theorem r41_rep_C10 : r41C10.Rep PositiveTD.Certificate.C10 :=
  ((r41_rep_C4.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10))
private def r41C12 : Scaled :=
  r41C10.add ((Scaled.const (1/479001600)).mul (Scaled.var.pow 12))
private theorem r41_rep_C12 : r41C12.Rep PositiveTD.Certificate.C12 :=
  r41_rep_C10.add ((Scaled.rep_const _).mul (Scaled.rep_var.pow 12))

private def r41Tl : Scaled := (Scaled.const split).sub Scaled.var
private theorem r41_rep_Tl : r41Tl.Rep (t .low) := (Scaled.rep_const _).sub Scaled.rep_var
private def r41Th : Scaled := Scaled.var.sub (Scaled.const split)
private theorem r41_rep_Th : r41Th.Rep (t .high) := Scaled.rep_var.sub (Scaled.rep_const _)

private def r41Kh : Scaled :=
  (((Scaled.const (169/250)).add ((Scaled.const (1/5)).mul r41Th)).add
    ((Scaled.const (9/10)).mul (r41Th.pow 2))).sub ((Scaled.const (13/10)).mul (r41Th.pow 3))
private theorem r41_rep_Kh : r41Kh.Rep (k .high) :=
  (((Scaled.rep_const _).add ((Scaled.rep_const _).mul r41_rep_Th)).add
    ((Scaled.rep_const _).mul (r41_rep_Th.pow 2))).sub
    ((Scaled.rep_const _).mul (r41_rep_Th.pow 3))

private def r41Ll : Scaled :=
  ((((Scaled.const (41/40)).sub ((Scaled.const (1/4)).mul r41Tl)).add
    ((Scaled.const (29/2)).mul (r41Tl.pow 2))).add
    ((Scaled.const (55/4)).mul (r41Tl.pow 3))).sub ((Scaled.const 200).mul (r41Tl.pow 4))
private theorem r41_rep_Ll : r41Ll.Rep (l .low) :=
  ((((Scaled.rep_const _).sub ((Scaled.rep_const _).mul r41_rep_Tl)).add
    ((Scaled.rep_const _).mul (r41_rep_Tl.pow 2))).add
    ((Scaled.rep_const _).mul (r41_rep_Tl.pow 3))).sub
    ((Scaled.rep_const _).mul (r41_rep_Tl.pow 4))
private def r41Lh : Scaled :=
  ((Scaled.const (41/40)).add ((Scaled.const (11/50)).mul r41Th)).sub
    ((Scaled.const (3/10)).mul (r41Th.pow 2))
private theorem r41_rep_Lh : r41Lh.Rep (l .high) :=
  ((Scaled.rep_const _).add ((Scaled.rep_const _).mul r41_rep_Th)).sub
    ((Scaled.rep_const _).mul (r41_rep_Th.pow 2))

private def r41Cl : Scaled :=
  ((Scaled.ofNat 1).add ((Scaled.const (11/10)).mul r41Tl)).add
    ((Scaled.const 17).mul (r41Tl.pow 2))
private theorem r41_rep_Cl : r41Cl.Rep (c .low) :=
  (Scaled.rep_one.add ((Scaled.rep_const _).mul r41_rep_Tl)).add
    ((Scaled.rep_const _).mul (r41_rep_Tl.pow 2))
private def r41Ch : Scaled :=
  ((Scaled.ofNat 1).sub ((Scaled.const (7/10)).mul r41Th)).add
    ((Scaled.const (22/25)).mul (r41Th.pow 2))
private theorem r41_rep_Ch : r41Ch.Rep (c .high) :=
  (Scaled.rep_one.sub ((Scaled.rep_const _).mul r41_rep_Th)).add
    ((Scaled.rep_const _).mul (r41_rep_Th.pow 2))

private def r41MHl : Scaled :=
  r41Cl.mul (r41C12.add ((Scaled.const PositiveTD.Certificate.etaQ).mul r41S9))
private theorem r41_rep_MHl : r41MHl.Rep (mHi .low) :=
  r41_rep_Cl.mul (r41_rep_C12.add ((Scaled.rep_const _).mul r41_rep_S9))
private def r41MHh : Scaled :=
  r41Ch.mul (r41C12.add ((Scaled.const PositiveTD.Certificate.etaQ).mul r41S9))
private theorem r41_rep_MHh : r41MHh.Rep (mHi .high) :=
  r41_rep_Ch.mul (r41_rep_C12.add ((Scaled.rep_const _).mul r41_rep_S9))
private def r41MLh : Scaled :=
  r41Ch.mul (r41C10.add ((Scaled.const PositiveTD.Certificate.etaQ).mul r41S11))
private theorem r41_rep_MLh : r41MLh.Rep (mLo .high) :=
  r41_rep_Ch.mul (r41_rep_C10.add ((Scaled.rep_const _).mul r41_rep_S11))
private def r41Qh : Scaled :=
  r41Lh.add ((Scaled.const (3/100)).mul
    ((Scaled.const PositiveTD.Certificate.h).sub Scaled.var))
private theorem r41_rep_Qh : r41Qh.Rep (qStar .high) :=
  r41_rep_Lh.add ((Scaled.rep_const _).mul ((Scaled.rep_const _).sub Scaled.rep_var))

private theorem r41_slope_eq : comparison .highMCoarseSlope=
    C (1211833/1250000)+C (-53791/125000)*X+C (-5448383/2500000)*X^2+
      C (582941/375000)*X^3+C (3223/15000)*X^4 := by
  show -coarseHighDifference.derivative=_
  simp only [coarseHighDifference,mCoarse,c,l,t,C2,S3,derivative_sub,
    derivative_add,derivative_mul,derivative_C,derivative_X,derivative_one,derivative_pow]
  refine Polynomial.funext fun x => ?_
  simp only [eval_neg,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_one,eval_zero]
  norm_num [split,PositiveTD.Certificate.etaQ]
  ring

private def r41Slope : Scaled :=
  ((((Scaled.const (1211833/1250000)).add ((Scaled.const (-53791/125000)).mul Scaled.var)).add
    ((Scaled.const (-5448383/2500000)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (582941/375000)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (3223/15000)).mul (Scaled.var.pow 4))

private def r41Cmp : Comparison→Scaled
  | .lowMUpper => ((Scaled.const (71/50)).mul r41Ll).sub r41MHl
  | .highKUpper => ((Scaled.const (41/50)).mul r41Lh).sub r41Kh
  | .highMUpper => ((Scaled.const (129/125)).mul r41Lh).sub r41MHh
  | .highMQuarter => r41Lh.sub r41MHh
  | .highMThreeTenths => ((Scaled.const (47/50)).mul r41Lh).sub r41MHh
  | .highMThird => ((Scaled.const (23/25)).mul r41Lh).sub r41MHh
  | .highMLower => r41MLh.sub ((Scaled.const (4/5)).mul r41Lh)
  | .highMEnvelope => r41Qh.sub r41MHh
  | .highMCoarseSlope => r41Slope

private theorem r41_rep_cmp (e : Comparison) : (r41Cmp e).Rep (comparison e) := by
  cases e
  · exact ((Scaled.rep_const _).mul r41_rep_Ll).sub r41_rep_MHl
  · exact ((Scaled.rep_const _).mul r41_rep_Lh).sub r41_rep_Kh
  · exact ((Scaled.rep_const _).mul r41_rep_Lh).sub r41_rep_MHh
  · exact r41_rep_Lh.sub r41_rep_MHh
  · exact ((Scaled.rep_const _).mul r41_rep_Lh).sub r41_rep_MHh
  · exact ((Scaled.rep_const _).mul r41_rep_Lh).sub r41_rep_MHh
  · exact r41_rep_MLh.sub ((Scaled.rep_const _).mul r41_rep_Lh)
  · exact r41_rep_Qh.sub r41_rep_MHh
  · rw [r41_slope_eq]
    exact ((((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).add
      ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
      ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
      ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))

/-- The centring data `(a+b)/2=s/den`, `(b-a)/2=t/den` of each comparison interval. -/
private def r41Den : Comparison→ℕ
  | .lowMUpper => 10 | .highMQuarter => 40 | .highMThird => 60 | .highMLower => 100
  | _ => 20
private def r41Mid : Comparison→ℤ
  | .lowMUpper => 1 | .highMQuarter => 19 | .highMThreeTenths => 10 | .highMThird => 31
  | .highMLower => 29 | _ => 9
private def r41Half : Comparison→ℤ
  | .lowMUpper => 1 | .highMQuarter => 9 | .highMThreeTenths => 4 | .highMThird => 11
  | .highMLower => 9 | _ => 5

private theorem r41_rep_centered (e : Comparison) :
    ((r41Cmp e).center 1 (r41Den e) (r41Mid e) (r41Half e)).Rep
      (centered (comparisonLeft e) (comparisonRight e) (comparison e)) :=
  (r41_rep_cmp e).centered 1 (r41Den e) (r41Mid e) (r41Half e)
    (by cases e <;> norm_num [r41Den])
    (by cases e <;> norm_num [comparisonLeft,comparisonRight,r41Den,r41Mid,split,h])
    (by cases e <;> norm_num [comparisonLeft,comparisonRight,r41Den,r41Half,split,h])

end R41Certificates

theorem comparison_expansion (e : Comparison) :
    centered (comparisonLeft e) (comparisonRight e) (comparison e)=
      expansion (comparisonDegree e)
        (centered (comparisonLeft e) (comparisonRight e) (comparison e)) := by
  cases e <;>
    exact (r41_rep_centered _).eq_expansion (by decide +kernel) (by decide +kernel)

theorem comparison_reserve (e : Comparison) : comparisonReserve e<
    lowerOn (comparisonDegree e) (comparisonLeft e) (comparisonRight e) (comparison e) := by
  cases e <;>
    rw [WholeIntervalPolynomial.Certificate.lowerOn_eq_of_rep (r41_rep_centered _)
      (by decide +kernel) (by decide +kernel)]
  · exact r41_lt_of_int (n:=989) (d:=100000) (by norm_num [comparisonReserve]) (by norm_num)
      (by decide +kernel) (by decide +kernel)
  · exact r41_lt_of_int (n:=1027) (d:=50000) (by norm_num [comparisonReserve]) (by norm_num)
      (by decide +kernel) (by decide +kernel)
  · exact r41_lt_of_int (n:=119) (d:=6250) (by norm_num [comparisonReserve]) (by norm_num)
      (by decide +kernel) (by decide +kernel)
  · exact r41_lt_of_int (n:=2773) (d:=100000) (by norm_num [comparisonReserve]) (by norm_num)
      (by decide +kernel) (by decide +kernel)
  · exact r41_lt_of_int (n:=303) (d:=100000) (by norm_num [comparisonReserve]) (by norm_num)
      (by decide +kernel) (by decide +kernel)
  · exact r41_lt_of_int (n:=499) (d:=100000) (by norm_num [comparisonReserve]) (by norm_num)
      (by decide +kernel) (by decide +kernel)
  · exact r41_lt_of_int (n:=217) (d:=2500) (by norm_num [comparisonReserve]) (by norm_num)
      (by decide +kernel) (by decide +kernel)
  · exact r41_lt_of_int (n:=31) (d:=25000) (by norm_num [comparisonReserve]) (by norm_num)
      (by decide +kernel) (by decide +kernel)
  · exact r41_lt_of_int (n:=197) (d:=1250) (by norm_num [comparisonReserve]) (by norm_num)
      (by decide +kernel) (by decide +kernel)

theorem comparison_positive (e : Comparison) {z : ℝ}
    (hz : z∈Set.Icc (comparisonLeft e:ℝ) (comparisonRight e:ℝ)) :
    (comparisonReserve e:ℝ)<aeval z (comparison e) := by
  apply positive_on_interval _ (comparison_expansion e) (comparison_reserve e) hz
  cases e <;> norm_num [comparisonLeft,comparisonRight,split,h]

theorem coarse_high_endpoint : (9/2000:ℚ)<coarseHighDifference.eval h := by
  norm_num [coarseHighDifference,mCoarse,C2,S3,c,l,t,split,PositiveTD.Certificate.etaQ,h]

theorem coarse_high_positive {z : ℝ} (hz : z∈Set.Icc (1/5:ℝ) (7/10:ℝ)) :
    (9/2000:ℝ)<aeval z coarseHighDifference := by
  have hanti : AntitoneOn (fun x : ℝ => aeval x coarseHighDifference)
      (Set.Icc (1/5:ℝ) (7/10:ℝ)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt coarseHighDifference x).continuousAt.continuousWithinAt)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt coarseHighDifference x)
    intro x hx
    have hh := comparison_positive .highMCoarseSlope (z:=x) (by
      norm_num [comparisonLeft,comparisonRight,split,h]
      exact ⟨hx.1.le,hx.2.le⟩)
    simp only [comparisonReserve,comparison,map_neg] at hh
    push_cast at hh
    linarith
  have hh := hanti hz (show (7/10:ℝ)∈Set.Icc (1/5:ℝ) (7/10:ℝ) by norm_num) hz.2
  have hr : (9/2000:ℝ)<aeval (7/10:ℝ) coarseHighDifference := by
    have hcast : ∀ (r : ℚ) (p : ℚ[X]),aeval (r:ℝ) p=((p.eval r:ℚ):ℝ) := fun r p => by
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp [hp,hq]
      | monomial n a => simp
    rw [show (7/10:ℝ)=((h:ℚ):ℝ) by norm_num [h],hcast]
    have hc := (Rat.cast_lt (K:=ℝ)).mpr coarse_high_endpoint
    rw [show ((9/2000:ℚ):ℝ)=9/2000 by norm_num] at hc
    exact hc
  exact hr.trans_le hh

inductive CoarseLow where | tilted | secant
  deriving DecidableEq

instance : Fintype CoarseLow where
  elems := {.tilted, .secant}
  complete x := by cases x <;> decide
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

private theorem r41_tilted_explicit : coarseLowRemainder .tilted=
    C (7/750000)*X^0+C (6677/7500000)*X^1+C (607/1500000)*X^2+C (67/300000)*X^3+
      C (37/60000)*X^4+C (1/6000)*X^5 := by
  refine Polynomial.funext fun x => ?_
  simp only [coarseLowRemainder,coarseLowPolynomial,coarseLowLower,mCoarse,c,l,t,C2,S3,
    eval_comp,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_one,split,
    PositiveTD.Certificate.etaQ]
  ring

private theorem r41_secant_explicit : coarseLowRemainder .secant=
    C (34451/3750000000)*X^0+C (4916311/37500000000)*X^1+C (6466301/7500000000)*X^2+
      C (117581/1500000000)*X^3+C (1273691/300000000)*X^4+C (26783/30000000)*X^5 := by
  refine Polynomial.funext fun x => ?_
  simp only [coarseLowRemainder,coarseLowPolynomial,coarseLowLower,mCoarse,c,l,t,C2,S3,
    eval_comp,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_one,split,
    PositiveTD.Certificate.etaQ]
  ring

theorem coarse_low_identity (e : CoarseLow) :
    coarseLowRemainder e=
      ∑ i : Fin 6,C ((coarseLowRemainder e).coeff i.val)*X^i.val := by
  rw [Fin.sum_univ_eq_sum_range (fun i => C ((coarseLowRemainder e).coeff i)*X^i) 6]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  cases e
  · rw [r41_tilted_explicit]
    simp only [coeff_add,coeff_C_mul_X_pow]
    norm_num
  · rw [r41_secant_explicit]
    simp only [coeff_add,coeff_C_mul_X_pow]
    norm_num

theorem coarse_low_coefficients (e : CoarseLow) (i : Fin 6) :
    0≤(coarseLowRemainder e).coeff i.val := by
  cases e
  · rw [r41_tilted_explicit]
    fin_cases i <;> simp only [coeff_add,coeff_C_mul_X_pow] <;> norm_num
  · rw [r41_secant_explicit]
    fin_cases i <;> simp only [coeff_add,coeff_C_mul_X_pow] <;> norm_num

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

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
end
end
end

section
/-!
## The exact negative-flat-A / TD2 scalar baseline

The original GA and AB alternatives keep their separate secant weights.
Only the high family's D support is enlarged to its full-circle bound
inside the analytic lower estimate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate (Family)

def secant (l s : ℝ) : ℝ := l/Real.cos s
def lambdaG (atG : Bool) (l s : ℝ) : ℝ := if atG then secant l s else l
def lambdaB (atG : Bool) (l s : ℝ) : ℝ := if atG then l else secant l s

def baseline (atG : Bool) (k l c s z : ℝ) : ℝ :=
  k+lambdaG atG l s+lambdaB atG l s+PositiveTD.tilted c z+c*edgeWidth z+2-
    c*PositiveTD.sigma*Real.sin z-fullSupport 1 k-fullSupport (lambdaG atG l s) k-
    fullSupport (PositiveTD.tilted c z) (lambdaB atG l s)-clippedSupport 1 c+
    secant l s*(edgeWidth s-1)+(7/12)*l*Real.tan s

def nonradical (f : Family) (z : ℝ) : ℝ :=
  2*Explicit.k f z+3*Explicit.l f z+(3/2)*Explicit.m f z+
    Explicit.c f z*edgeWidth z+5/2-Explicit.c f z*PositiveTD.sigma*Real.sin z+
    if f=.low then -(1+Explicit.c f z)*GlobalGA.Secondary.diagonal else (1+Explicit.c f z)/2

def reducedBaseline (f : Family) (atG : Bool) (s z : ℝ) : ℝ :=
  baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z+
    if f=.low then 0 else clippedSupport 1 (Explicit.c f z)-fullSupport 1 (Explicit.c f z)

def norms (atG : Bool) (k l c s z : ℝ) : Fin 4→ℝ :=
  ![pairNorm k 1 0,pairNorm k (lambdaG atG l s) 0,
    pairNorm (lambdaB atG l s) (PositiveTD.tilted c z) 0,pairNorm c 1 0]
def normSum (f : Family) (n : Fin 4→ℝ) : ℝ :=
  if f=.low then n 0+n 1+n 2 else n 0+n 1+n 2+n 3
def scaledNorms (f : Family) (atG : Bool) (s z : ℝ) (i : Fin 4) : ℝ :=
  Real.cos s*norms atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z i

theorem baseline_zero (atG : Bool) (k l c z : ℝ) :
    baseline atG k l c 0 z=PositiveTD.baseline k l c z := by
  cases atG <;> simp [baseline,lambdaG,lambdaB,secant,PositiveTD.baseline,edgeWidth_zero] <;> ring

theorem reduced_le_baseline (f : Family) (atG : Bool) (s z : ℝ) :
    reducedBaseline f atG s z≤
      baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z := by
  have hD := PositiveTD.Certificate.clippedSupport_le_fullSupport 1 (Explicit.c f z)
  cases f <;> simp only [reducedBaseline,↓reduceIte,add_zero,reduceCtorEq] <;> linarith

theorem secant_width_identity {l s : ℝ} (hs : s∈Icc 0 frameCap) :
    (3/2)*(secant l s-l)+secant l s*(edgeWidth s-1)+(7/12)*l*Real.tan s=
      secant l s-l+(13/12)*l*Real.tan s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [edgeWidth_positive_formula hs,Real.tan_eq_sin_div_cos]
  dsimp [secant]
  field_simp [hc.ne']
  ring

theorem reduced_identity (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 frameCap) :
    reducedBaseline f atG s z=
      nonradical f z+secant (Explicit.l f z) s-Explicit.l f z+
        (13/12)*Explicit.l f z*Real.tan s-
        R*normSum f (norms atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z) := by
  have hwidth := secant_width_identity (l:=Explicit.l f z) hs
  cases f
  · have hz' : z∈Icc 0 (1/5:ℝ) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
      exact ⟨hz.1,by linarith [hz.2]⟩
    have hc := (Explicit.low_ranges hz').2.2.2.2.1
    cases atG <;>
      simp only [reducedBaseline,baseline,nonradical,normSum,norms,
        lambdaG,lambdaB,↓reduceIte,Bool.false_eq_true,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,
        fullSupport_pair,clippedSupport,hc,diagonalSupport,Explicit.m] at ⊢
      <;> linarith only [hwidth]
  · cases atG <;>
      simp only [reducedBaseline,baseline,nonradical,normSum,norms,
        lambdaG,lambdaB,↓reduceIte,Bool.false_eq_true,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two,fullSupport_pair,Explicit.m] at ⊢
      <;> linarith only [hwidth]

theorem scaled_identity (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 frameCap) :
    Real.cos s*reducedBaseline f atG s z=
      Real.cos s*(nonradical f z-Explicit.l f z)+Explicit.l f z+
        (13/12)*Explicit.l f z*Real.sin s-
        R*normSum f (scaledNorms f atG s z) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [reduced_identity f atG hz hs,Real.tan_eq_sin_div_cos]
  dsimp [secant,scaledNorms,normSum]
  split_ifs <;> field_simp [hc.ne'] <;> ring

theorem norms_nonnegative (atG : Bool) (k l c s z : ℝ) (i : Fin 4) :
    0≤norms atG k l c s z i := by
  fin_cases i <;> simp only [norms] <;>
    exact Real.sqrt_nonneg _

theorem scaled_norms_nonnegative (f : Family) (atG : Bool) {s z : ℝ}
    (hs : s∈Icc 0 frameCap) (i : Fin 4) : 0≤ scaledNorms f atG s z i := by
  have hc : 0≤Real.cos s := by linarith [(transport_trig hs).1]
  exact mul_nonneg hc (norms_nonnegative atG _ _ _ s z i)

def mixedG (k l z : ℝ) : ℝ :=
  k*(PositiveAngularEnvelope.phi (frameCap-z)-1)+l*(Real.cos frameCap-1)-
    R*(pairNorm k l (-z)-pairNorm k l 0)

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD
end
end
end

section
/-!
## Actual trigonometric coefficient ranges for the negative-A stress

Polynomial bounds are transferred to the actual
tilted BT multiplier, including the low secant-weight comparison and
the restricted high-interval comparisons at the original angle cuts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Explicit
open Candidate Secondary Polynomial
open Certificate (Family)

private lemma r42_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact ⟨hz.1,by linarith [hz.2]⟩

private lemma r42_high_dom {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
  exact ⟨by linarith [hz.1],by linarith [hz.2]⟩

private lemma r42_cmp_dom (e : Certificate.Comparison) {a b z : ℝ}
    (ha : (Certificate.comparisonLeft e:ℝ)=a) (hb : (Certificate.comparisonRight e:ℝ)=b)
    (hz : z∈Icc a b) :
    z∈Icc (Certificate.comparisonLeft e:ℝ) (Certificate.comparisonRight e:ℝ) := by
  rw [ha,hb]; exact hz

theorem tilted_bounds (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    0<aeval z (Certificate.mLo f) ∧ aeval z (Certificate.mLo f)≤ m f z ∧
      m f z≤aeval z (Certificate.mHi f) := by
  have hh := PositiveTD.Certificate.tilted_polynomial_bounds
    (c:=Certificate.c f) (family_frame_domain f hz)
    (by simpa using (family_positive f hz).2.2.1)
  simpa [Certificate.mLo,Certificate.mHi,m] using hh

theorem coarse_tilted_lower (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    aeval z (Certificate.mCoarse f)≤ m f z := by
  have hz0 := (family_frame_domain f hz).1
  have hc := (family_positive f hz).2.2.1
  have hs := Real.sin_ge_sub_cube hz0
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hbase : 1-z^2/2+(293/1000)*(z-z^3/6)≤
      Real.cos z+(293/1000)*Real.sin z := by linarith
  have hh := mul_le_mul_of_nonneg_left hbase hc.le
  norm_num [Certificate.mCoarse,Certificate.C2,Certificate.S3,
    PositiveTD.Certificate.etaQ,m,PositiveTD.tilted,PositiveTD.eta] at ⊢
  nlinarith only [hh]

theorem low_tilted {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    l .low z< m .low z ∧ m .low z<(71/50)*l .low z := by
  have hpoly := Certificate.coarse_low_positive .tilted hz
  have hcoarse := coarse_tilted_lower .low (r42_low_dom hz)
  have hupper := Certificate.comparison_positive .lowMUpper
    (r42_cmp_dom .lowMUpper (by norm_num [Certificate.comparisonLeft])
      (by norm_num [Certificate.comparisonRight,Certificate.split]) hz)
  have hb := (tilted_bounds .low (r42_low_dom hz)).2.2
  norm_num [Certificate.coarseLowPolynomial] at hpoly
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hupper
  exact ⟨by linarith,by linarith⟩

theorem AB_cut_cosine {s : ℝ} (hs : s∈Icc 0 (19/50:ℝ)) :
    (4643/5000:ℝ)<Real.cos s := by
  have hh := trig_bracket (l:=(0:ℝ)) (u:=(19/50:ℝ)) (x:=s)
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  norm_num at hh
  linarith [hh.2.2.1]

theorem GA_cut_cosine {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    (9689/10000:ℝ)<Real.cos s := by
  have hh := trig_bracket (l:=(0:ℝ)) (u:=(1/4:ℝ)) (x:=s)
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  norm_num at hh
  linarith [hh.2.2.1]

theorem low_secant {z s : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 (19/50:ℝ)) : l .low z/Real.cos s< m .low z+(2/5)*z := by
  have hpoly := Certificate.coarse_low_positive .secant hz
  have hcoarse := coarse_tilted_lower .low (r42_low_dom hz)
  have hcos := AB_cut_cosine hs
  have hm : 0< m .low z+(2/5)*z := by
    have hpos := (family_positive .low (r42_low_dom hz)).2.2.2
    nlinarith [hz.1]
  have h0 : 0<Real.cos s := by linarith
  apply (div_lt_iff₀ h0).2
  have hp := mul_lt_mul_of_pos_right hcos hm
  norm_num [Certificate.coarseLowPolynomial] at hpoly
  nlinarith

theorem high_tilted {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    (77/100)*l .high z< m .high z ∧ m .high z<(129/125)*l .high z ∧
      k .high z<(41/50)*l .high z := by
  have hlo := Certificate.coarse_high_positive hz
  have hcoarse := coarse_tilted_lower .high (r42_high_dom hz)
  have hupper := Certificate.comparison_positive .highMUpper
    (r42_cmp_dom .highMUpper (by norm_num [Certificate.comparisonLeft,Certificate.split])
      (by norm_num [Certificate.comparisonRight,PositiveTD.Certificate.h]) hz)
  have hkupper := Certificate.comparison_positive .highKUpper
    (r42_cmp_dom .highKUpper (by norm_num [Certificate.comparisonLeft,Certificate.split])
      (by norm_num [Certificate.comparisonRight,PositiveTD.Certificate.h]) hz)
  have hb := (tilted_bounds .high (r42_high_dom hz)).2.2
  norm_num [Certificate.coarseHighDifference] at hlo
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hupper hkupper
  exact ⟨by linarith,by linarith,by linarith⟩

theorem high_tilted_quarter {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    m .high z<l .high z := by
  have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := ⟨by linarith [hz.1],hz.2⟩
  have hh := Certificate.comparison_positive .highMQuarter
    (r42_cmp_dom .highMQuarter (by norm_num [Certificate.comparisonLeft])
      (by norm_num [Certificate.comparisonRight,PositiveTD.Certificate.h]) hz)
  have hb := (tilted_bounds .high (r42_high_dom hz')).2.2
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hh
  linarith

theorem high_tilted_third {z : ℝ} (hz : z∈Icc (1/3:ℝ) (7/10:ℝ)) :
    m .high z<(23/25)*l .high z := by
  have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := ⟨by linarith [hz.1],hz.2⟩
  have hh := Certificate.comparison_positive .highMThird
    (r42_cmp_dom .highMThird (by norm_num [Certificate.comparisonLeft])
      (by norm_num [Certificate.comparisonRight,PositiveTD.Certificate.h]) hz)
  have hb := (tilted_bounds .high (r42_high_dom hz')).2.2
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hh
  linarith

theorem high_tilted_lower_to_AB_cut {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (19/50:ℝ)) : (4/5)*l .high z< m .high z := by
  have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := ⟨hz.1,by linarith [hz.2]⟩
  have hh := Certificate.comparison_positive .highMLower
    (r42_cmp_dom .highMLower (by norm_num [Certificate.comparisonLeft,Certificate.split])
      (by norm_num [Certificate.comparisonRight]) hz)
  have hb := (tilted_bounds .high (r42_high_dom hz')).2.1
  norm_num [Certificate.comparison,Certificate.comparisonReserve] at hh
  linarith

theorem high_tilted_envelope {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    max (l .high z) (m .high z)≤l .high z+(3/100)*(frameCap-z) := by
  have hh := Certificate.comparison_positive .highMEnvelope
    (r42_cmp_dom .highMEnvelope (by norm_num [Certificate.comparisonLeft,Certificate.split])
      (by norm_num [Certificate.comparisonRight,PositiveTD.Certificate.h]) hz)
  have hb := (tilted_bounds .high (r42_high_dom hz)).2.2
  norm_num [Certificate.comparison,Certificate.comparisonReserve,Certificate.qStar,
    PositiveTD.Certificate.h] at hh
  dsimp [frameCap]
  apply max_le
  · linarith [hz.2]
  · linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Explicit
end
end
end

section
/-!
## Elementary-term bounds for the fourteen negative-A endpoints

In particular the positive factor in the
equal-angle cosine multiplication is proved from the weight ranges.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial Explicit
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 Rbar cbar sigmabar etaQ h)

theorem elementary_lower (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) : aeval z (elementary f)≤nonradical f z := by
  have hz' := family_frame_domain f hz
  have hc := (family_positive f hz).2.2.1
  have ht := PositiveTD.Certificate.taylor_bounds hz'
  have hm := (tilted_bounds f hz).2.1
  have hs := PositiveTD.Certificate.sigma_sine_upper hz' hc.le
  have hw0 := mul_le_mul_of_nonneg_left
    (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
  have hw : Explicit.c f z*aeval z widthLo≤Explicit.c f z*edgeWidth z := by
    rw [edgeWidth_positive_formula hz']
    simp only [widthLo,map_mul,map_add,map_one,aeval_C,eq_ratCast]
    push_cast
    nlinarith only [hw0]
  have hD := mul_le_mul_of_nonneg_left PositiveTD.Certificate.diagonal_le_cbar
    (show 0≤1+Explicit.c f z by linarith)
  cases f <;>
    simp only [elementary,nonradical,↓reduceIte,reduceCtorEq,
      map_add,map_sub,map_mul,map_neg,map_one,aeval_C,eq_ratCast,k_eval,l_eval,c_eval] at ⊢ <;>
    push_cast at hs hD ⊢ <;>
    linarith only [hm,hs,hw,hD]

theorem sine_upper_polynomial_le {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z S9≤z := by
  have hz1 : z≤1 := by dsimp [frameCap] at hz; linarith [hz.2]
  have hz2 := pow_le_pow_left₀ hz.1 hz1 2
  have h3 := mul_nonneg (pow_nonneg hz.1 3)
    (show 0≤1/6-z^2/120 by nlinarith)
  have h7 := mul_nonneg (pow_nonneg hz.1 7)
    (show 0≤1/5040-z^2/362880 by nlinarith)
  norm_num [S9,S5]
  nlinarith

theorem elementary_minus_l_positive (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) :
    (5:ℝ)<aeval z (elementary f)-Explicit.l f z := by
  have hz' := family_frame_domain f hz
  have hc := (family_positive f hz).2.2.1
  have ht := PositiveTD.Certificate.taylor_bounds hz'
  have hs9 := sine_upper_polynomial_le hz'
  have hs90 : 0≤aeval z S9 := le_trans (transport_trig hz').2.2.1 ht.2.2.1
  have hfactor : (1/2:ℝ)≤aeval z C10+(etaQ:ℝ)*aeval z S11 := by
    have he : (0:ℝ)≤(etaQ:ℝ)*aeval z S11 := mul_nonneg (by norm_num [etaQ]) ht.1
    linarith [ht.2.2.2.1]
  have hm0 := mul_le_mul_of_nonneg_left hfactor hc.le
  have hm : Explicit.c f z/2≤aeval z (mLo f) := by
    simp only [mLo,PositiveTD.Certificate.mMinus,map_mul,map_add,aeval_C,eq_ratCast,c_eval]
    linarith only [hm0]
  have hw0 : (3/4:ℝ)≤aeval z widthLo := by
    simp only [widthLo,map_mul,map_add,map_one,aeval_C,eq_ratCast]
    push_cast
    linarith [ht.1,ht.2.2.2.1]
  have hw := mul_le_mul_of_nonneg_left hw0 hc.le
  have hsig : (sigmabar:ℝ)=1415477291/1000000000 := by norm_num [sigmabar]
  have hcb : (cbar:ℝ)=899214066/1000000000 := by norm_num [cbar]
  cases f
  · have hzl : z∈Icc 0 (1/5:ℝ) := by
      norm_num [left,right,split] at hz
      exact ⟨hz.1,by linarith [hz.2]⟩
    obtain ⟨hk,_,hl,_,hclo,hchi⟩ := low_ranges hzl
    have hs9hi : aeval z S9≤(1/5:ℝ) := by linarith [hzl.2]
    have hp := mul_le_mul hchi hs9hi hs90 (by norm_num : (0:ℝ)≤19/10)
    have hs := mul_le_mul_of_nonneg_right hp
      (by norm_num [sigmabar] : (0:ℝ)≤(sigmabar:ℝ))
    have hd := mul_le_mul_of_nonneg_left
      (by norm_num [cbar] : (cbar:ℝ)≤9/10)
      (show 0≤1+Explicit.c .low z by linarith)
    simp only [elementary,↓reduceIte,map_add,map_sub,map_mul,map_neg,map_one,
      aeval_C,eq_ratCast,k_eval,l_eval,c_eval] at ⊢
    push_cast
    linarith only [hk,hl,hclo,hm,hw,hs,hd,hsig]
  · have hzh : z∈Icc (1/5:ℝ) (7/10:ℝ) := by
      norm_num [left,right,split,PositiveTD.Certificate.h] at hz
      exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
    obtain ⟨hk,_,hl,_,hclo,hchi,_,_⟩ := high_ranges hzh
    have hs9hi : aeval z S9≤(7/10:ℝ) := by linarith [hzh.2]
    have hp := mul_le_mul hchi hs9hi hs90 (by norm_num : (0:ℝ)≤1)
    have hs := mul_le_mul_of_nonneg_right hp
      (by norm_num [sigmabar] : (0:ℝ)≤(sigmabar:ℝ))
    simp only [elementary,↓reduceIte,reduceCtorEq,map_add,map_sub,map_mul,
      map_one,aeval_C,eq_ratCast,k_eval,l_eval,c_eval] at ⊢
    push_cast
    linarith only [hk,hl,hclo,hm,hw,hs,hsig]

theorem equal_elementary_lower (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) :
    aeval z (AZ f)≤Real.cos z*(nonradical f z-Explicit.l f z)+
      Explicit.l f z+(13/12)*Explicit.l f z*Real.sin z := by
  have ht := PositiveTD.Certificate.taylor_bounds (family_frame_domain f hz)
  have hI := elementary_lower f hz
  have hI0 : 0≤aeval z (elementary f)-Explicit.l f z := by
    linarith [elementary_minus_l_positive f hz]
  have hc0 : 0≤Real.cos z := by linarith [(transport_trig (family_frame_domain f hz)).1]
  have hp := mul_le_mul ht.2.2.2.2.1
    (sub_le_sub_right hI (Explicit.l f z)) hI0 hc0
  have hs := mul_le_mul_of_nonneg_left ht.2.1
    (show 0≤(13/12)*Explicit.l f z by have hh := (family_positive f hz).2.1; positivity)
  simp only [AZ,map_add,map_sub,map_mul,aeval_C,eq_ratCast,l_eval]
  push_cast
  linarith only [hp,hs]

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
end
end
end

section
/-!
## Removing the negative-A and nonnegative-TD2 errors

The secant weights and all other signed errors stay as they are. The two fixed errors are deleted
only from the algebraic block vector; the resulting positive and negative totals keep their exact
balance (`original_budgets`, `block_budgets`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

def aError (C : SignedCycle) (atG : Bool) : ℝ :=
  if atG then delta C.theta G else delta C.theta A
def owners (hg : Fin 4) (atG : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,2,2,2,0]
def weights (atG : Bool) (k l c s z : ℝ) : Vertex→ℝ :=
  ![k,lambdaG atG l s,lambdaB atG l s,PositiveTD.tilted c z,c,1,1]
def pWeights (atG : Bool) (k l m s : ℝ) : Fin 4→ℝ :=
  ![k,k,min (lambdaB atG l s) m,k]
def qWeights (atG : Bool) (_k l m s : ℝ) : Fin 4→ℝ :=
  ![1,lambdaG atG l s,max (lambdaB atG l s) m,1]
def blocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c s : ℝ) : Fin 4→Block :=
  ![⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨k,lambdaG atG l s,if hg=0 then delta C.theta H else 0,
      if atG then 0 else delta C.theta G⟩,
    ⟨lambdaB atG l s,PositiveTD.tilted c (delta C.theta T),
      if atG then delta C.theta A else 0,delta C.theta B⟩,
    ⟨k,1,delta C.theta D,0⟩]

theorem secant_nonnegative {l s : ℝ} (hl : 0≤l) (hs : s∈Icc 0 frameCap) :
    0≤ secant l s := div_nonneg hl (by linarith [(transport_trig hs).1])

theorem weights_nonnegative (atG : Bool) {k l c s z : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) (i : Vertex) :
    0≤weights atG k l c s z i := by
  have hp := secant_nonnegative hl hs
  have hm := (PositiveTD.tilted_pos hc hz).le
  cases atG <;> fin_cases i <;> simp [weights,lambdaG,lambdaB] <;> positivity

theorem coefficient_domain {atG : Bool} {k l m s : ℝ}
    (hk : k∈Icc (1/2:ℝ) (17/20:ℝ))
    (hG : lambdaG atG l s∈Icc k (2*k))
    (hB : 0<lambdaB atG l s) (hm : 0< m)
    (hratio : lambdaB atG l s≤2*m ∧ m≤2*lambdaB atG l s) (i : Fin 4) :
    0<pWeights atG k l m s i ∧ pWeights atG k l m s i≤qWeights atG k l m s i ∧
      qWeights atG k l m s i≤2*pWeights atG k l m s i := by
  have hk0 : 0<k := by linarith [hk.1]
  have h0 : 0<pWeights atG k l m s 0 ∧ pWeights atG k l m s 0≤qWeights atG k l m s 0 ∧
      qWeights atG k l m s 0≤2*pWeights atG k l m s 0 := by
    simp only [pWeights,qWeights,Matrix.cons_val_zero]
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1]⟩
  have h1 : 0<pWeights atG k l m s 1 ∧ pWeights atG k l m s 1≤qWeights atG k l m s 1 ∧
      qWeights atG k l m s 1≤2*pWeights atG k l m s 1 := by
    simp only [pWeights,qWeights,Matrix.cons_val_one]
    exact ⟨hk0,hG.1,hG.2⟩
  have h2 : 0<pWeights atG k l m s 2 ∧ pWeights atG k l m s 2≤qWeights atG k l m s 2 ∧
      qWeights atG k l m s 2≤2*pWeights atG k l m s 2 := by
    change 0< min (lambdaB atG l s) m ∧
      min (lambdaB atG l s) m ≤ max (lambdaB atG l s) m ∧
      max (lambdaB atG l s) m ≤ 2*min (lambdaB atG l s) m
    refine ⟨lt_min hB hm,min_le_max,?_⟩
    rcases le_total (lambdaB atG l s) m with hh | hh
    · rw [min_eq_left hh,max_eq_right hh]; exact hratio.2
    · rw [min_eq_right hh,max_eq_left hh]; exact hratio.1
  have h3 : 0<pWeights atG k l m s 3 ∧ pWeights atG k l m s 3≤qWeights atG k l m s 3 ∧
      qWeights atG k l m s 3≤2*pWeights atG k l m s 3 := by
    change 0<k ∧ k≤1 ∧ 1≤2*k
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1]⟩
  fin_cases i
  exacts [h0,h1,h2,h3]

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} {atG : Bool} {k l c s : ℝ}
    (hk : k≤1) (hG : k≤lambdaG atG l s) (i : Fin 4) :
    (blocks C hg atG k l c s i).p=pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s i ∧
    (blocks C hg atG k l c s i).q=qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s i := by
  fin_cases i <;>
    simp [blocks,Block.p,Block.q,pWeights,qWeights,min_eq_left hk,max_eq_right hk,
      min_eq_left hG,max_eq_right hG]

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c s : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑ i,(f (blocks C hg atG k l c s i).u+f (blocks C hg atG k l c s i).v))=
      (∑ j,f (delta C.theta j))-f (delta C.theta T)-f (aError C atG) := by
  cases atG <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem original_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ) {s : ℝ}
    (hs : 0≤ s) (ha : aError C atG=-s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T) :
    delta C.theta T∈Icc 0 frameCap ∧
    (∑ i,(blocks C hg atG k l c s i).P)=positiveVariation C.theta-delta C.theta T ∧
    (∑ i,(blocks C hg atG k l c s i).N)=negativeVariation C.theta-s ∧
    (∑ i,(blocks C hg atG k l c s i).P)≤frameCap-delta C.theta T ∧
    (∑ i,(blocks C hg atG k l c s i).N)≤frameCap-s ∧
    (∑ i,(blocks C hg atG k l c s i).N)-
      (∑ i,(blocks C hg atG k l c s i).P)=delta C.theta T-s := by
  have hp := sum_parts C hg atG k l c s positivePart positivePart_zero
  have hn := sum_parts C hg atG k l c s negativePart negativePart_zero
  have hpz : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hnz : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hpa : positivePart (aError C atG)=0 := by
    rw [ha]
    exact max_eq_right (by linarith)
  have hna : negativePart (aError C atG)=s := by
    rw [ha]
    simpa [negativePart] using max_eq_left hs
  have hp' : (∑ i,(blocks C hg atG k l c s i).P)=
      positiveVariation C.theta-delta C.theta T := by
    change (∑ i,(positivePart (blocks C hg atG k l c s i).u+
      positivePart (blocks C hg atG k l c s i).v))=_
    simpa only [hpz,hpa,positiveVariation,sub_zero] using hp
  have hn' : (∑ i,(blocks C hg atG k l c s i).N)=negativeVariation C.theta-s := by
    change (∑ i,(negativePart (blocks C hg atG k l c s i).u+
      negativePart (blocks C hg atG k l c s i).v))=_
    simpa only [hnz,hna,negativeVariation,sub_zero] using hn
  have hp0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg atG k l c s i).P_nonneg)
  have heq := variations_equal C.theta
  exact ⟨⟨hz,by linarith⟩,hp',hn',by linarith,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ) {s : ℝ}
    (hs : 0≤ s) (ha : aError C atG=-s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T) (i : Fin 4) :
    (blocks C hg atG k l c s i).P≤frameCap ∧ (blocks C hg atG k l c s i).N≤frameCap := by
  have hb := original_budgets hg atG k l c hs ha hvar hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c s j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c s j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.2.2.2.1],by linarith [hb.2.2.2.2.1]⟩

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Source
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity Explicit
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 h)

private theorem r41_high_dom {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    z∈Icc ((left .high:ℚ):ℝ) ((right .high:ℚ):ℝ) := by
  norm_num [left,right,split,PositiveTD.Certificate.h]
  exact hz

theorem cut_domain (e : Cut) : (cutAngle e:ℝ)∈Icc 0 frameCap := by
  cases e <;> norm_num [cutAngle,cutAtG,frameCap]

theorem cut_high_domain (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) : z∈Icc (1/5:ℝ) (7/10:ℝ) := by
  cases e <;> norm_num [cutAngle,cutAtG,PositiveTD.Certificate.h] at hz <;>
    exact ⟨by linarith [hz.1],hz.2⟩

theorem cut_theta_domain (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) : z-(cutAngle e:ℝ)∈Icc 0 frameCap := by
  have hs := cut_domain e
  have hh : ((PositiveTD.Certificate.h:ℚ):ℝ)=7/10 := by norm_num [PositiveTD.Certificate.h]
  have hf : frameCap=7/10 := rfl
  have h2 : z≤7/10 := hz.2.trans_eq hh
  rw [hf] at hs ⊢
  exact ⟨by linarith [hz.1],by linarith [h2,hs.1]⟩

@[simp] theorem gammaLo_cast (e : Cut) :
    (gammaLo e:ℝ)=aeval (cutAngle e:ℝ) C10 := by
  cases e <;> norm_num [gammaLo,cutAngle,cutAtG,C10,C4]
@[simp] theorem gammaHi_cast (e : Cut) :
    (gammaHi e:ℝ)=aeval (cutAngle e:ℝ) C12 := by
  cases e <;> norm_num [gammaHi,cutAngle,cutAtG,C12,C10,C4]
@[simp] theorem tauLo_cast (e : Cut) :
    (tauLo e:ℝ)=aeval (cutAngle e:ℝ) S11 := by
  cases e <;> norm_num [tauLo,cutAngle,cutAtG,S11,S9,S5]
@[simp] theorem tauHi_cast (e : Cut) :
    (tauHi e:ℝ)=aeval (cutAngle e:ℝ) S9 := by
  cases e <;> norm_num [tauHi,cutAngle,cutAtG,S9,S5]

theorem cut_trig_bounds (e : Cut) :
    0≤(gammaLo e:ℝ) ∧ (gammaLo e:ℝ)≤Real.cos (cutAngle e:ℝ) ∧
    Real.cos (cutAngle e:ℝ)≤(gammaHi e:ℝ) ∧
    0≤(tauLo e:ℝ) ∧ (tauLo e:ℝ)≤Real.sin (cutAngle e:ℝ) ∧
    Real.sin (cutAngle e:ℝ)≤(tauHi e:ℝ) := by
  have hh := PositiveTD.Certificate.taylor_bounds (cut_domain e)
  simp only [gammaLo_cast,gammaHi_cast,tauLo_cast,tauHi_cast]
  exact ⟨by linarith [hh.2.2.2.1],hh.2.2.2.2.1,hh.2.2.2.2.2,
    hh.1,hh.2.1,hh.2.2.1⟩

theorem theta_trig_lower (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    aeval z (thetaCosLo e)≤Real.cos (z-(cutAngle e:ℝ)) ∧
      aeval z (thetaSinLo e)≤Real.sin (z-(cutAngle e:ℝ)) := by
  have hz' := family_frame_domain .high (r41_high_dom (cut_high_domain e hz))
  have ht := PositiveTD.Certificate.taylor_bounds hz'
  obtain ⟨hg0,hglo,hghi,hs0,hslo,hshi⟩ := cut_trig_bounds e
  have hcos0 : 0≤Real.cos (cutAngle e:ℝ) := by
    linarith [(transport_trig (cut_domain e)).1]
  have hsin0 : 0≤Real.sin (cutAngle e:ℝ) := (transport_trig (cut_domain e)).2.2.1
  have hzcos0 : 0≤Real.cos z := by linarith [(transport_trig hz').1]
  have hzsin0 : 0≤Real.sin z := (transport_trig hz').2.2.1
  have hC0 : 0≤aeval z C10 := by linarith [ht.2.2.2.1]
  have hCC := mul_le_mul hglo ht.2.2.2.2.1 hC0 hcos0
  have hSS := mul_le_mul hslo ht.2.1 ht.1 hsin0
  have hCS := mul_le_mul hglo ht.2.1 ht.1 hcos0
  have hSC := mul_le_mul hshi ht.2.2.2.2.2 hzcos0
    (show 0≤(tauHi e:ℝ) by linarith)
  constructor
  · simp only [thetaCosLo,map_add,map_mul,aeval_C,eq_ratCast,Real.cos_sub]
    linarith only [hCC,hSS]
  · simp only [thetaSinLo,map_sub,map_mul,aeval_C,eq_ratCast,Real.sin_sub]
    linarith only [hCS,hSC]

def cutPCoefficient : Cut→ℝ→ℝ
  | .gaH,z => Explicit.k .high z | .gaB,z => Explicit.l .high z
  | .abG,z => Explicit.k .high z | .abH,z => Explicit.k .high z
def cutQCoefficient : Cut→ℝ→ℝ
  | .gaH,_ => 1 | .gaB,z => Explicit.m .high z
  | .abG,z => Explicit.l .high z | .abH,_ => 1
def cutCostCoefficient (e : Cut) (z : ℝ) : ℝ :=
  if cutRole e=0 then 1 else Explicit.l .high z
def cutV (e : Cut) (z : ℝ) : ℝ :=
  cutCostCoefficient e z*(Real.cos (z-(cutAngle e:ℝ))-1)-
    R*(pairNorm (cutPCoefficient e z) (cutQCoefficient e z) (-(z-(cutAngle e:ℝ)))-
      pairNorm (cutPCoefficient e z) (cutQCoefficient e z) 0)
def cutNorms (e : Cut) (z : ℝ) : Fin 4→ℝ :=
  Function.update (scaledNorms .high (cutAtG e) (cutAngle e:ℝ) z) (cutRole e)
    (Real.cos (cutAngle e:ℝ)*
      pairNorm (cutPCoefficient e z) (cutQCoefficient e z) (-(z-(cutAngle e:ℝ))))

theorem cut_coefficients_positive (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    0<cutPCoefficient e z ∧ 0<cutQCoefficient e z ∧ 0<cutCostCoefficient e z := by
  obtain ⟨hk,hl,_,hm⟩ := family_positive .high (r41_high_dom (cut_high_domain e hz))
  cases e
  · exact ⟨hk,one_pos,one_pos⟩
  · exact ⟨hl,hm,hl⟩
  · exact ⟨hk,hl,hl⟩
  · exact ⟨hk,one_pos,one_pos⟩

theorem cut_norms_nonnegative (e : Cut) {z : ℝ}
    (_hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) (i : Fin 4) : 0≤cutNorms e z i := by
  have hc : 0≤Real.cos (cutAngle e:ℝ) := by
    linarith [(transport_trig (cut_domain e)).1]
  by_cases hi : i=cutRole e
  · subst i
    simpa [cutNorms] using mul_nonneg hc
      (PositiveTD.Certificate.pairNorm_nonneg (cutPCoefficient e z)
        (cutQCoefficient e z) (-(z-(cutAngle e:ℝ))))
  · simpa [cutNorms,hi] using scaled_norms_nonnegative .high (cutAtG e)
      (z:=z) (cut_domain e) i

theorem cut_scaled_identity (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    Real.cos (cutAngle e:ℝ)*
        (reducedBaseline .high (cutAtG e) (cutAngle e:ℝ) z+cutV e z)=
      Real.cos (cutAngle e:ℝ)*(nonradical .high z-Explicit.l .high z)+Explicit.l .high z+
        (13/12)*Explicit.l .high z*Real.sin (cutAngle e:ℝ)+
        Real.cos (cutAngle e:ℝ)*cutCostCoefficient e z*(Real.cos (z-(cutAngle e:ℝ))-1)-
        R*normSum .high (cutNorms e z) := by
  have he := scaled_identity .high (cutAtG e) (r41_high_dom (cut_high_domain e hz)) (cut_domain e)
  cases e <;>
    simp only [cutNorms,cutV,cutPCoefficient,cutQCoefficient,cutCostCoefficient,
      cutRole,cutAtG,normSum,scaledNorms,norms,lambdaG,lambdaB,
      Function.update_apply,↓reduceIte,Bool.false_eq_true,reduceCtorEq,Fin.reduceEq,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.tail_cons,Matrix.head_cons,Explicit.m] at he ⊢ <;>
    linear_combination he

theorem cut_elementary_lower (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    aeval z (cutA e)≤
      Real.cos (cutAngle e:ℝ)*(nonradical .high z-Explicit.l .high z)+Explicit.l .high z+
        (13/12)*Explicit.l .high z*Real.sin (cutAngle e:ℝ)+
        Real.cos (cutAngle e:ℝ)*cutCostCoefficient e z*(Real.cos (z-(cutAngle e:ℝ))-1) := by
  have hz' := r41_high_dom (cut_high_domain e hz)
  obtain ⟨hg0,hglo,hghi,hs0,hslo,hshi⟩ := cut_trig_bounds e
  have hc0 : 0≤Real.cos (cutAngle e:ℝ) := by
    linarith [(transport_trig (cut_domain e)).1]
  have hgHi0 : 0≤(gammaHi e:ℝ) := hc0.trans hghi
  have hI := elementary_lower .high hz'
  have hI0 : 0≤aeval z (elementary .high)-Explicit.l .high z := by
    linarith [elementary_minus_l_positive .high hz']
  have hprod := mul_le_mul hglo (sub_le_sub_right hI (Explicit.l .high z)) hI0 hc0
  have hsine := mul_le_mul_of_nonneg_left hslo
    (show 0≤(13/12)*Explicit.l .high z by
      have hh := (family_positive .high hz').2.1; positivity)
  have hq := (cut_coefficients_positive e hz).2.2
  have htheta := (theta_trig_lower e hz).1
  have hcos₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right htheta 1)
    (show 0≤(gammaHi e:ℝ)*cutCostCoefficient e z by positivity)
  have hcos₂ := mul_le_mul_of_nonpos_right
    (mul_le_mul_of_nonneg_right hghi hq.le)
    (sub_nonpos.mpr (Real.cos_le_one (z-(cutAngle e:ℝ))))
  have hqeval : aeval z (if cutRole e=0 then (1:ℚ[X]) else l .high)=cutCostCoefficient e z := by
    by_cases hh : cutRole e=0 <;> simp [hh,cutCostCoefficient]
  simp only [cutA,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,l_eval,hqeval]
  push_cast
  linarith only [hprod,hsine,hcos₁,hcos₂]

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
end
end
end
