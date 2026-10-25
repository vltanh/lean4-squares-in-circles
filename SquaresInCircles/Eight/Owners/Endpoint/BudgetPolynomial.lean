module

public import Mathlib.Tactic
public import SquaresInCircles.Eight.Arithmetic.PolynomialExpressions

/-!
# Eight squares: one whole-interval polynomial for the narrow endpoint budget

This is a direct squared version of the
H/D endpoint-circle comparison on `0≤α≤1/2`.  Its polynomial is formed
from the degree-five sine upper bound, degree-six cosine lower bound,
and exact rational upper bounds for the two original radius radicals.
Expansion at `31/200` gives a positive quadratic lower bound on the
entire interval.  No angle rows or sampled acceptance values occur.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.EndpointBudgetPolynomial
open Polynomial PolynomialExpressions

def kbar : ℚ := 914576/1000000
def sbar : ℚ := 415026/1000000
def reserve : ℚ := 1/8000
def center : ℚ := 31/200
def span : ℚ := 69/200

def S5 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5
def C6 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6
def primary : ℚ[X] := C (3/2)-C (1/2)*(C kbar*S5+C (1/2)*(1-C6))
def transverse : ℚ[X] := C ((3-sbar-reserve)/2)+C (25/49)*X
def certificate : ℚ[X] := primary^2+transverse^2-C (9789/2500)
def shifted : ℚ[X] := certificate.comp (C center+X)
def remainder : ℚ[X] :=
  ∑ j : Fin 10,C (shifted.coeff (j.val+3))*X^(j.val+3)

/-! The kernel computes the integer coefficients of `shifted` (`PolyExpr`) and checks the
coefficient facts below on them. -/

/-- Unfold `shifted` into an expression. -/
local macro "reify" : tactic => `(tactic| simp only [shifted,certificate,primary,transverse,S5,C6,
  reify_C,reify_X,reify_one,reify_add,reify_sub,reify_mul,reify_pow,reify_comp])

private def certOK (e : PolyExpr) : Bool :=
  cmSeries 12 e && (coeffGt 0 (1/20000) e && (coeffAbsLt 1 (1/2000) e &&
    quadReserveGt 10 span (1/8) e))

private theorem cert : ∃ e : PolyExpr, shifted=e.poly ∧ certOK e=true := by
  refine ⟨_,by reify; rfl,?_⟩
  decide +kernel

theorem expansion_identity :
    shifted=C (shifted.coeff 0)+C (shifted.coeff 1)*X+
      C (shifted.coeff 2)*X^2+remainder := by
  obtain ⟨e,he,h⟩ := cert
  simp only [certOK,Bool.and_eq_true] at h
  have hdeg : shifted.natDegree<13 := by
    rw [he]
    have := natDegree_of_check h.1
    omega
  conv_lhs => rw [as_sum_range_C_mul_X_pow' shifted hdeg]
  rw [show (13:ℕ)=3+10 from rfl,Finset.sum_range_add,remainder,
    Fin.sum_univ_eq_sum_range (fun j => C (shifted.coeff (j+3))*X^(j+3)) 10]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,mul_one,zero_add]

theorem coefficient_reserves :
    (1/20000 : ℚ)<shifted.coeff 0 ∧
      |shifted.coeff 1|<1/2000 ∧
      (1/8 : ℚ)<shifted.coeff 2-
        ∑ j : Fin 10,|shifted.coeff (j.val+3)| *span^(j.val+1) := by
  obtain ⟨e,he,h⟩ := cert
  simp only [certOK,Bool.and_eq_true] at h
  rw [he]
  exact ⟨coeff_gt_of_check h.2.1,coeff_abs_of_check h.2.2.1,quadReserve_of_check h.2.2.2⟩

/-- The tail estimate is a coefficient norm for one continuous interval.
Its sign-independent remainder is charged only against the quadratic. -/
theorem shifted_positive {x : ℝ} (hx : |x|≤(span:ℝ)) :
    0<aeval x shifted := by
  have hspan : (0:ℝ)≤(span:ℝ) := by norm_num [span]
  have hterm (j : Fin 10) :
      -|(shifted.coeff (j.val+3):ℝ)| *(span:ℝ)^(j.val+1)*x^2≤
        (shifted.coeff (j.val+3):ℝ)*x^(j.val+3) := by
    have hpow : |x^(j.val+1)|≤(span:ℝ)^(j.val+1) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg x) hx _
    have hm := mul_le_mul_of_nonneg_left hpow
      (abs_nonneg (shifted.coeff (j.val+3):ℝ))
    rw [← abs_mul] at hm
    have hlo := (abs_le.mp hm).1
    have hmul := mul_le_mul_of_nonneg_right hlo (sq_nonneg x)
    have he : (shifted.coeff (j.val+3):ℝ)*x^(j.val+3)=
        ((shifted.coeff (j.val+3):ℝ)*x^(j.val+1))*x^2 := by
      rw [show j.val+3=(j.val+1)+2 by omega,pow_add]
      ring
    rw [he]
    linarith
  have htail := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  have htail' :
      -(∑ j : Fin 10,|(shifted.coeff (j.val+3):ℝ)| *(span:ℝ)^(j.val+1))*x^2≤
        aeval x remainder := by
    simp only [remainder,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
    simpa only [neg_mul,Finset.sum_neg_distrib,Finset.sum_mul] using htail
  have hc0 : (1/20000 : ℝ)<(shifted.coeff 0:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr coefficient_reserves.1
    push_cast at h
    exact h
  have hc1 : |(shifted.coeff 1:ℝ)|<1/2000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr coefficient_reserves.2.1
    push_cast at h
    exact h
  have hc2 : (1/8 : ℝ)<(shifted.coeff 2:ℝ)-
      ∑ j : Fin 10,|(shifted.coeff (j.val+3):ℝ)| *(span:ℝ)^(j.val+1) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr coefficient_reserves.2.2
    push_cast at h
    exact h
  have hlinear : -(1/2000)*|x|≤(shifted.coeff 1:ℝ)*x := by
    have hm := mul_le_mul_of_nonneg_right hc1.le (abs_nonneg x)
    rw [← abs_mul] at hm
    rw [neg_mul]
    exact (abs_le.mp hm).1
  have hquadratic := mul_le_mul_of_nonneg_right hc2.le (sq_nonneg x)
  have he := congrArg (fun p : ℚ[X] => aeval x p) expansion_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have hsq := sq_nonneg (|x|-(1/500 : ℝ))
  nlinarith [sq_abs x]

theorem certificate_positive {a : ℝ} (ha : a∈Set.Icc 0 (1/2 : ℝ)) :
    0<aeval a certificate := by
  have hx : |a-(center:ℝ)|≤(span:ℝ) := by
    rw [abs_le]
    norm_num [center,span]
    constructor <;> linarith [ha.1,ha.2]
  have h := shifted_positive hx
  have he : aeval (a-(center:ℝ)) shifted=aeval a certificate := by
    have harg : aeval (a-(center:ℝ)) (C center+X)=a := by
      simp
    rw [shifted,aeval_comp]
    rw [harg]
  rw [he] at h
  exact h

@[simp] theorem primary_eval (a : ℝ) :
    aeval a primary=3/2-
      ((kbar:ℝ)*(a-a^3/6+a^5/120)+(1-(1-a^2/2+a^4/24-a^6/720))/2)/2 := by
  simp [primary,S5,C6]
  ring

@[simp] theorem transverse_eval (a : ℝ) :
    aeval a transverse=((3:ℝ)-(sbar:ℝ)-(reserve:ℝ))/2+(25/49)*a := by
  simp [transverse]

theorem real_certificate_positive {a : ℝ} (ha : a∈Set.Icc 0 (1/2 : ℝ)) :
    (aeval a primary)^2+
      (((3:ℝ)-(sbar:ℝ)-(reserve:ℝ))/2+(25/49)*a)^2>(9789/2500 : ℝ) := by
  have h := certificate_positive ha
  simp only [certificate,map_sub,map_add,map_pow,aeval_C,transverse_eval,eq_ratCast] at h
  have h9 : ((9789/2500:ℚ):ℝ)=9789/2500 := by norm_num
  rw [h9] at h
  linarith

end SquaresInCircles.Eight.EndpointBudgetPolynomial
