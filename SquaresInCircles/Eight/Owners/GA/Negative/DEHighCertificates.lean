module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.PowerTailBounds

/-!
# Eight squares: the literal high-DE third-derivative polynomial certificates

The early degree-nine polynomial keeps its centered quadratic. The late logarithmic-derivative
numerator, a quartic, is a positive combination of squares and products of the distances to the
ends of `[0.613, 0.843]` (`late_fraction_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape.Certificate
open Polynomial

def early : ℚ[X] := C (6/25)+C 3*X*(1-X^2)^2*
  (-C (3577/10000)+C ((5/2)*(6423/10000)*(1319/2500))*X^2+
    C ((35/8)*(6423/10000)*(1319/2500)^2)*X^4)
def earlyCenter : ℚ[X] := CenteredMonomialBounds.translated (3/10) early
def earlyQuadratic : ℚ := earlyCenter.coeff 2-PowerTailBounds.norm earlyCenter 3 7 (3/10)

/-- The centered early polynomial, coefficient by coefficient. -/
private theorem r73_earlyCenter_eq : earlyCenter=
      C (3495832380142334529/100000000000000000000:ℚ)+
      C (287168023740894387/10000000000000000000:ℚ)*X+
      C (774769922213526279/250000000000000000:ℚ)*X^2+
      C (19820351254900317/25000000000000000:ℚ)*X^3+
      C (-35146473393297933/5000000000000000:ℚ)*X^4+
      C (-2740677778025511/500000000000000:ℚ)*X^5+
      C (20090207378871/25000000000000:ℚ)*X^6+
      C (13628542421853/2500000000000:ℚ)*X^7+
      C (6335932940001/1000000000000:ℚ)*X^8+
      C (234664182963/100000000000:ℚ)*X^9 := by
  apply Polynomial.funext
  intro x
  simp only [earlyCenter,CenteredMonomialBounds.translated,early,eval_comp,eval_add,eval_mul,
    eval_sub,eval_neg,eval_pow,eval_C,eval_X,eval_one]
  ring

theorem early_identity : earlyCenter=C (earlyCenter.coeff 0)+C (earlyCenter.coeff 1)*X+
    C (earlyCenter.coeff 2)*X^2+PowerTailBounds.tail earlyCenter 3 7 := by
  rw [r73_earlyCenter_eq]
  simp only [PowerTailBounds.tail,Fin.sum_univ_seven,Fin.val_zero,Fin.val_one,Fin.val_two,
    coeff_add,coeff_C_mul,coeff_X_pow,coeff_C,coeff_X]
  norm_num
  ring_nf

theorem early_reserve : (20557/10000:ℚ)<earlyQuadratic ∧
    (87/2500:ℚ)<earlyCenter.coeff 0-(earlyCenter.coeff 1)^2/(4*earlyQuadratic) := by
  simp only [earlyQuadratic,PowerTailBounds.norm,Fin.sum_univ_seven,r73_earlyCenter_eq,
    coeff_add,coeff_C_mul,coeff_X_pow,coeff_C,coeff_X]
  norm_num

theorem early_lower {y : ℝ} (hy : y∈Icc (0:ℝ) (3/5)) :
    (87/2500:ℝ)<aeval y early := by
  have hu : |y-3/10|≤(3/10:ℝ) := abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hq : (0:ℝ)<(earlyQuadratic:ℝ) := by
    have hh := Rat.cast_lt (K:=ℝ).mpr early_reserve.1
    push_cast at hh
    linarith
  have htail := PowerTailBounds.quadratic_lower early_identity (by norm_num : (0:ℚ)≤3/10)
    (by rw [show ((3/10:ℚ):ℝ)=3/10 by norm_num]; exact hu)
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(earlyCenter.coeff 0:ℝ)) (b:=(earlyCenter.coeff 1:ℝ)) (x:=y-3/10) hq
  have hr : (87/2500:ℝ)<(earlyCenter.coeff 0:ℝ)-
      (earlyCenter.coeff 1:ℝ)^2/(4*(earlyQuadratic:ℝ)) := by
    have hh := Rat.cast_lt (K:=ℝ).mpr early_reserve.2
    push_cast at hh
    exact hh
  have he : aeval (y-3/10) earlyCenter=aeval y early := by
    simp only [earlyCenter,CenteredMonomialBounds.translated,aeval_comp,map_add,aeval_C,aeval_X]
    congr 1
    simp only [eq_ratCast]
    push_cast
    ring_nf
  rw [he] at htail
  have hqq : (earlyQuadratic:ℝ)=(earlyCenter.coeff 2:ℝ)-
      (PowerTailBounds.norm earlyCenter 3 7 (3/10):ℝ) := by
    simp only [earlyQuadratic]
    push_cast
    ring
  rw [← hqq] at htail
  linarith

theorem late_fraction_lower {x : ℝ} (hx : x∈Icc (613/1000:ℝ) (843/1000)) :
    (637/5000:ℝ)<(27/20)*(1+x^2)*(1+x^2+827/1000)-
      x*(1+x^2+6*(827/1000)) := by
  have h1 : 0≤x-613/1000 := sub_nonneg.2 hx.1
  have h2 : 0≤843/1000-x := sub_nonneg.2 hx.2
  have hs := sq_nonneg (x-18/25)
  linarith [mul_nonneg hs h1,mul_nonneg (mul_nonneg hs h1) h2,
    mul_nonneg (sq_nonneg (x-3/4)) (pow_nonneg h2 2)]

end SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape.Certificate
