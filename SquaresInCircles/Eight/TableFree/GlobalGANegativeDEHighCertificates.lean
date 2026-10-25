module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEHighOrdinaryShape
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds
public import SquaresInCircles.Eight.TableFree.PowerTailBounds
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# The literal high-DE third-derivative polynomial certificates

Uncompiled transcription of the strengthened BT3 companion, (35)--(36)
and (39). The early degree-nine polynomial keeps its centered quadratic;
the late logarithmic-derivative numerator uses one exact coefficient
bound over the entire interval [.613,.843].
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape.Certificate
open Polynomial WholeIntervalPolynomial
open WholeIntervalPolynomial.Certificate (Scaled lowerOn_eq_of_rep)

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

def lateFraction : ℚ[X] := C (27/20)*(1+X^2)*(1+X^2+C (827/1000))-
  X*(1+X^2+C (6*(827/1000)))

private def r73late : Scaled :=
  (((Scaled.const (27/20)).mul ((Scaled.ofNat 1).add (Scaled.var.pow 2))).mul
    (((Scaled.ofNat 1).add (Scaled.var.pow 2)).add (Scaled.const (827/1000)))).sub
    (Scaled.var.mul (((Scaled.ofNat 1).add (Scaled.var.pow 2)).add (Scaled.const (6*(827/1000)))))
private theorem r73late_rep : r73late.Rep lateFraction :=
  (((Scaled.rep_const _).mul (Scaled.rep_one.add (Scaled.rep_var.pow 2))).mul
    ((Scaled.rep_one.add (Scaled.rep_var.pow 2)).add (Scaled.rep_const _))).sub
    (Scaled.rep_var.mul ((Scaled.rep_one.add (Scaled.rep_var.pow 2)).add (Scaled.rep_const _)))
private theorem r73late_centered :
    (r73late.center 1 1000 728 115).Rep (centered (613/1000) (843/1000) lateFraction) :=
  r73late_rep.centered 1 1000 728 115 (by norm_num) (by norm_num) (by norm_num)

theorem late_fraction_identity :
    centered (613/1000) (843/1000) lateFraction=
      expansion 4 (centered (613/1000) (843/1000) lateFraction) :=
  r73late_centered.eq_expansion (by decide +kernel) (by decide +kernel)

theorem late_fraction_reserve : (637/5000:ℚ)<
    lowerOn 4 (613/1000) (843/1000) lateFraction := by
  rw [lowerOn_eq_of_rep r73late_centered (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem late_fraction_lower {x : ℝ} (hx : x∈Icc (613/1000:ℝ) (843/1000)) :
    (637/5000:ℝ)<(27/20)*(1+x^2)*(1+x^2+827/1000)-
      x*(1+x^2+6*(827/1000)) := by
  have hh := positive_on_interval (x:=x) (by norm_num : (613/1000:ℚ)<843/1000)
    late_fraction_identity late_fraction_reserve
    (by constructor <;> push_cast <;> linarith [hx.1,hx.2])
  simp only [lateFraction,map_sub,map_add,map_mul,map_pow,map_one,aeval_C,aeval_X,
    eq_ratCast] at hh
  push_cast at hh
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape.Certificate
