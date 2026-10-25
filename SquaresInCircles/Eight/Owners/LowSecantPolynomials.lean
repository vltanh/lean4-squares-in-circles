module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.PolynomialExpressions
public import SquaresInCircles.Eight.Owners.SecantGainPolynomial

/-!
# Eight squares: two whole-interval low-coefficient secant comparisons

These are single polynomial bounds on the full interval. No angle grid
or stored certificate array is used; the kernel computes on integer coefficient lists.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.LowSecantPolynomials
open Polynomial WholeIntervalPolynomial PolynomialExpressions

inductive Case where | tilted | unit

def q : Case → ℚ | .tilted => 863/1000 | .unit => 1
def a : Case → ℚ | .tilted => 8627/10000 | .unit => 4461/5000
def b : Case → ℚ | .tilted => 47/250 | .unit => 359/2000
def reserve : Case → ℚ | .tilted => 44/625 | .unit => 93/2000

def numerator (i : Case) : ℚ[X] :=
  C (q i)*(VaryingBCertificate.C10-1)+C (a i)*VaryingBCertificate.S11+
    C (b i)*VaryingBCertificate.S11^2-C (35643/50000)*X+C (1199/5000)*X^2
def certificate (i : Case) : ℚ[X] := (numerator i).divX

/-! ### Integer values

The kernel computes the integer coefficients of `numerator i` (`PolyExpr`) and the Chebyshev
coefficients of the centered `certificate i` on `[0,7/10]` from them. -/

/-- Unfold the polynomials of this file into expressions. -/
local macro "reify" : tactic => `(tactic| simp only [numerator,q,a,b,
  VaryingBCertificate.C10,VaryingBCertificate.S11,VaryingBCertificate.S9,
  reify_C,reify_X,reify_one,reify_ofNat,reify_add,reify_sub,reify_neg,reify_mul,reify_pow])

private def certOK (i : Case) (e : PolyExpr) : Bool :=
  coeffZero 0 e && chebLowerGt 21 7 20 1 1 (reserve i) e.divX

private theorem cert_tilted :
    ∃ e : PolyExpr, numerator .tilted=e.poly ∧ certOK .tilted e=true := by
  refine ⟨_,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_unit : ∃ e : PolyExpr, numerator .unit=e.poly ∧ certOK .unit e=true := by
  refine ⟨_,by reify; rfl,?_⟩
  decide +kernel

private theorem cert (i : Case) : ∃ e : PolyExpr, numerator i=e.poly ∧ certOK i e=true := by
  cases i
  · exact cert_tilted
  · exact cert_unit

private theorem chebyshev_facts (i : Case) :
    centered 0 (7/10) (certificate i)=expansion 21 (centered 0 (7/10) (certificate i)) ∧
      reserve i<lowerOn 21 0 (7/10) (certificate i) := by
  obtain ⟨e,he,h⟩ := cert i
  simp only [certOK,Bool.and_eq_true] at h
  rw [certificate,he,← PolyExpr.poly_divX]
  exact chebLower_of_check h.2 (by norm_num) (by norm_num) (by norm_num)

theorem zero_identity (i : Case) : X*certificate i=numerator i := by
  obtain ⟨e,he,h⟩ := cert i
  simp only [certOK,Bool.and_eq_true] at h
  have h0 : (numerator i).coeff 0=0 := by rw [he]; exact coeff_zero_of_check h.1
  have hh := X_mul_divX_add (numerator i)
  rw [h0,map_zero,add_zero] at hh
  exact hh

theorem expansion_identity (i : Case) :
    centered 0 (7/10) (certificate i)=expansion 21 (centered 0 (7/10) (certificate i)) :=
  (chebyshev_facts i).1

theorem coefficient_reserve (i : Case) :
    reserve i<lowerOn 21 0 (7/10) (certificate i) :=
  (chebyshev_facts i).2

theorem polynomial_positive (i : Case) {s : ℝ} (hs : s∈Set.Icc 0 frameCap) :
    (reserve i:ℝ)<aeval s (certificate i) := by
  have hs' : s∈Set.Icc ((0:ℚ):ℝ) ((7/10:ℚ):ℝ) := by
    have h2 : s≤7/10 := hs.2
    push_cast
    exact ⟨hs.1,h2⟩
  exact positive_on_interval (by norm_num) (expansion_identity i) (coefficient_reserve i) hs'

theorem numerator_positive (i : Case) {s : ℝ} (hs : s∈Set.Ioc 0 frameCap) :
    0<aeval s (numerator i) := by
  have hh := congrArg (fun p : ℚ[X] => aeval s p) (zero_identity i)
  simp only [map_mul,aeval_X] at hh
  rw [← hh]
  have hr : (0:ℝ)<(reserve i:ℝ) := by cases i <;> norm_num [reserve]
  exact mul_pos hs.1 (hr.trans (polynomial_positive i (Set.Ioc_subset_Icc_self hs)))

/-- The original trigonometric quadratic minorant is strictly larger
than the secant-chord polynomial, throughout the full open-positive interval. -/
theorem trigonometric_positive (i : Case) {s : ℝ} (hs : s∈Set.Ioc 0 frameCap) :
    (35643/50000)*s-(1199/5000)*s^2<
      (q i:ℝ)*(Real.cos s-1)+(a i:ℝ)*Real.sin s+(b i:ℝ)*(Real.sin s)^2 := by
  have hp := numerator_positive i hs
  have hs0 := SecantGainPolynomial.sine11_nonneg (Set.Ioc_subset_Icc_self hs)
  have hS := HighOrderTaylor.S11_le_sin hs.1.le
  have hC := Arithmetic.cos10_le_cos hs.1.le
  have hs2 := pow_le_pow_left₀ hs0 hS 2
  have hq0 : (0:ℝ)≤(q i:ℝ) := by cases i <;> norm_num [q]
  have ha0 : (0:ℝ)≤(a i:ℝ) := by cases i <;> norm_num [a]
  have hb0 : (0:ℝ)≤(b i:ℝ) := by cases i <;> norm_num [b]
  have hcos := mul_le_mul_of_nonneg_left hC hq0
  have hsin := mul_le_mul_of_nonneg_left hS ha0
  have hsine2 := mul_le_mul_of_nonneg_left hs2 hb0
  simp only [numerator,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    VaryingBCertificate.C10_eval,VaryingBCertificate.S11_eval] at hp
  norm_num at hp
  linarith

theorem coefficient_squares (i : Case) :
    (a i:ℝ)^2*((1263/2500 : ℝ)^2+(q i:ℝ)^2)<
      qCap*(1263/2500)^2*(q i:ℝ)^2 ∧
    4*(b i:ℝ)^2*((1263/2500 : ℝ)^2+(q i:ℝ)^2)^3<
      qCap*(1263/2500)^4*(q i:ℝ)^4 := by
  cases i <;> norm_num [a,b,q,qCap]

end SquaresInCircles.Eight.LowSecantPolynomials
