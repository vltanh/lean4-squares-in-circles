module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PolynomialData
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: whole-interval comparisons for the tilted negative-A weights

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
