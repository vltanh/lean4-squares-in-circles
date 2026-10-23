module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEHighOrdinaryShape
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds
public import SquaresInCircles.Eight.TableFree.PowerTailBounds

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

def early : ℚ[X] := C (6/25)+C 3*X*(1-X^2)^2*
  (-C (3577/10000)+C ((5/2)*(6423/10000)*(1319/2500))*X^2+
    C ((35/8)*(6423/10000)*(1319/2500)^2)*X^4)
def earlyCenter : ℚ[X] := CenteredMonomialBounds.translated (3/10) early
def earlyQuadratic : ℚ := earlyCenter.coeff 2-PowerTailBounds.norm earlyCenter 3 7 (3/10)

theorem early_identity : earlyCenter=C (earlyCenter.coeff 0)+C (earlyCenter.coeff 1)*X+
    C (earlyCenter.coeff 2)*X^2+PowerTailBounds.tail earlyCenter 3 7 := by decide

theorem early_reserve : (20557/10000:ℚ)<earlyQuadratic ∧
    (87/2500:ℚ)<earlyCenter.coeff 0-(earlyCenter.coeff 1)^2/(4*earlyQuadratic) := by decide

theorem early_lower {y : ℝ} (hy : y∈Icc (0:ℝ) (3/5)) :
    (87/2500:ℝ)<aeval y early := by
  have hu : |y-3/10|≤(3/10:ℝ) := abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hq : (0:ℝ)<(earlyQuadratic:ℝ) := by
    have hh : (20557/10000:ℝ)<(earlyQuadratic:ℝ) := by exact_mod_cast early_reserve.1
    linarith
  have htail := PowerTailBounds.quadratic_lower early_identity (by norm_num : (0:ℚ)≤3/10) hu
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(earlyCenter.coeff 0:ℝ)) (b:=(earlyCenter.coeff 1:ℝ)) (x:=y-3/10) hq
  have hr : (87/2500:ℝ)<(earlyCenter.coeff 0:ℝ)-
      (earlyCenter.coeff 1:ℝ)^2/(4*(earlyQuadratic:ℝ)) := by exact_mod_cast early_reserve.2
  have he : aeval (y-3/10) earlyCenter=aeval y early := by
    simp only [earlyCenter,CenteredMonomialBounds.translated,aeval_comp,map_add,aeval_C,aeval_X]
    congr 1
    ring
  rw [he] at htail
  dsimp [earlyQuadratic] at hmin
  push_cast at hmin
  linarith

def lateFraction : ℚ[X] := C (27/20)*(1+X^2)*(1+X^2+C (827/1000))-
  X*(1+X^2+C (6*(827/1000)))

theorem late_fraction_identity :
    centered (613/1000) (843/1000) lateFraction=
      expansion 4 (centered (613/1000) (843/1000) lateFraction) := by decide

theorem late_fraction_reserve : (637/5000:ℚ)<
    lowerOn 4 (613/1000) (843/1000) lateFraction := by decide

theorem late_fraction_lower {x : ℝ} (hx : x∈Icc (613/1000:ℝ) (843/1000)) :
    (637/5000:ℝ)<(27/20)*(1+x^2)*(1+x^2+827/1000)-
      x*(1+x^2+6*(827/1000)) := by
  have hh := positive_on_interval (by norm_num : (613/1000:ℚ)<843/1000)
    late_fraction_identity late_fraction_reserve hx
  simpa [lateFraction] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape.Certificate
