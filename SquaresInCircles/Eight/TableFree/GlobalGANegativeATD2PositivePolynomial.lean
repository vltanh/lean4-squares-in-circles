module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2NegativeSlopes

/-!
# The two prescribed positive-angle quartics

Uncompiled transcription of (28)--(29) and (35)--(36) in the negative-A
angle companion. Each positivity statement uses exactly the centered
monomial coefficient norm in the hand proof, on its full stated interval.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.PositivePolynomial
open Polynomial PowerTailBounds DirectedPowerBounds

def PU : ℚ[X] := (C (3/5)+C (557/1000)*X)^2*
  (1+X^2+C (741/1000)*X)-C ((1839/1000)^2)*X^2
def PA : ℚ[X] := (C (13/12+371/1000)+C (557/1000)*X)^2*
  (1+C (861/1000)*X^2)-C (9789/2500)*(C (371/1000)+X)^2
def centeredU : ℚ[X] := shift (3/4) PU
def centeredA : ℚ[X] := shift (47/50) PA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem PU_certificate :
    centeredU=C (centeredU.coeff 0)+tail centeredU 1 4 ∧
    centeredU.coeff 0-PowerTailBounds.norm centeredU 1 4 (1/4)=
      (30312841/250000000:ℚ) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem PA_certificate :
    centeredA=C (centeredA.coeff 0)+tail centeredA 1 4 ∧
    centeredA.coeff 0-PowerTailBounds.norm centeredA 1 4 (7/50)=
      (2092249892523197/28125000000000000:ℚ) := by decide

theorem PU_positive {r : ℝ} (hr : r∈Set.Icc (1/2:ℝ) 1) :
    0<(3/5+(557/1000)*r)^2*(1+r^2+(741/1000)*r)-(1839/1000)^2*r^2 := by
  have hx : |r-(3/4:ℝ)|≤(1/4:ℝ) := by
    apply abs_le.mpr
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hh := constant_lower PU_certificate.1 hx
  have hreserve : (0:ℝ)<(centeredU.coeff 0:ℝ)-
      (PowerTailBounds.norm centeredU 1 4 (1/4):ℝ) := by
    have he : (0:ℚ)<centeredU.coeff 0-PowerTailBounds.norm centeredU 1 4 (1/4) := by
      rw [PU_certificate.2]
      norm_num
    exact_mod_cast he
  have he : aeval (r-(3/4:ℝ)) centeredU=
      (3/5+(557/1000)*r)^2*(1+r^2+(741/1000)*r)-(1839/1000)^2*r^2 := by
    norm_num [centeredU,shift_eval,PU]
  rw [he] at hh
  exact hreserve.trans_le hh

theorem PA_positive {r : ℝ} (hr : r∈Set.Icc (4/5:ℝ) (27/25:ℝ)) :
    0<(13/12+371/1000+(557/1000)*r)^2*(1+(861/1000)*r^2)-
      qCap*(371/1000+r)^2 := by
  have hx : |r-(47/50:ℝ)|≤(7/50:ℝ) := by
    apply abs_le.mpr
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hh := constant_lower PA_certificate.1 hx
  have hreserve : (0:ℝ)<(centeredA.coeff 0:ℝ)-
      (PowerTailBounds.norm centeredA 1 4 (7/50):ℝ) := by
    have he : (0:ℚ)<centeredA.coeff 0-PowerTailBounds.norm centeredA 1 4 (7/50) := by
      rw [PA_certificate.2]
      norm_num
    exact_mod_cast he
  have he : aeval (r-(47/50:ℝ)) centeredA=
      (13/12+371/1000+(557/1000)*r)^2*(1+(861/1000)*r^2)-
        qCap*(371/1000+r)^2 := by
    norm_num [centeredA,shift_eval,PA,qCap]
  rw [he] at hh
  exact hreserve.trans_le hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.PositivePolynomial
