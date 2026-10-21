module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDLowPolynomial

/-!
# Whole-interval polynomial reserves for the upper TD2 family

Uncompiled source.  The coefficient formulas change only at their common
clamp.  The tight H numerator on the first interval retains its positive
quadratic; the other three numerators use one centered coefficient sum.
All identities and reserves below concern the explicitly defined
polynomials on their entire natural coefficient interval.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Certificate
open Polynomial PowerTailBounds Explicit

def upperMid (a : Upper) : ℚ := (left a+right a)/2
def upperRadius (a : Upper) : ℚ := (right a-left a)/2
def upperMass (a : Upper) : Fin 5→ℚ[X] :=
  ![upperRk a,upperRm a,upperRc a,upperRHminus a,upperRBminus a]
def upperMassCentered (a : Upper) (i : Fin 5) : ℚ[X] :=
  DirectedPowerBounds.shift (upperMid a) (upperMass a i)
def upperHShifted : ℚ[X] := DirectedPowerBounds.shift L (upperPH .varying)
def upperBCentered (a : Upper) : ℚ[X] :=
  DirectedPowerBounds.shift (upperMid a) (upperPB a)
def upperHClampedCentered : ℚ[X] :=
  DirectedPowerBounds.shift (upperMid .clamped) (upperPH .clamped)

theorem upper_centered_domain (a : Upper) {z : ℝ}
    (hz : z∈Set.Icc (left a:ℝ) (right a:ℝ)) :
    |z-(upperMid a:ℝ)|≤(upperRadius a:ℝ) := by
  rw [abs_le]
  norm_num [upperMid,upperRadius]
  constructor <;> linarith [hz.1,hz.2]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upper_mass_identity (a : Upper) (i : Fin 5) :
    upperMassCentered a i=C ((upperMassCentered a i).coeff 0)+
      tail (upperMassCentered a i) 1 6 := by
  cases a <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upper_mass_reserve (a : Upper) (i : Fin 5) :
    (17/25:ℚ)<(upperMassCentered a i).coeff 0-
      PowerTailBounds.norm (upperMassCentered a i) 1 6 (upperRadius a) := by
  cases a <;> fin_cases i <;> decide

theorem upper_mass_lower (a : Upper) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc (left a:ℝ) (right a:ℝ)) :
    (17/25:ℝ)<aeval z (upperMass a i) := by
  have hb := DirectedPowerBounds.constant_lower (upper_mass_identity a i)
    (upper_centered_domain a hz)
  have hr : (17/25:ℝ)<((upperMassCentered a i).coeff 0:ℝ)-
      (PowerTailBounds.norm (upperMassCentered a i) 1 6 (upperRadius a):ℝ) := by
    exact_mod_cast upper_mass_reserve a i
  have he : aeval (z-(upperMid a:ℝ)) (upperMassCentered a i)=
      aeval z (upperMass a i) := by simp [upperMassCentered]
  rw [he] at hb
  exact hr.trans_le hb

theorem upper_masses_positive (a : Upper) {z : ℝ}
    (hz : z∈Set.Icc (left a:ℝ) (right a:ℝ)) :
    0<aeval z (upperRk a) ∧ 0<aeval z (upperRm a) ∧
      0<aeval z (upperRc a) ∧ 0<aeval z (upperRHminus a) ∧
      0<aeval z (upperRBminus a) := by
  have h0 := upper_mass_lower a 0 hz
  have h1 := upper_mass_lower a 1 hz
  have h2 := upper_mass_lower a 2 hz
  have h3 := upper_mass_lower a 3 hz
  have h4 := upper_mass_lower a 4 hz
  norm_num [upperMass] at h0 h1 h2 h3 h4
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upper_H_shifted_identity :
    upperHShifted=C (upperHShifted.coeff 0)+C (upperHShifted.coeff 1)*X+
      C (upperHShifted.coeff 2)*X^2+tail upperHShifted 3 31 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upper_H_shifted_reserve :
    (77/50000:ℚ)<upperHShifted.coeff 0 ∧
      (109/1000:ℚ)<upperHShifted.coeff 1 ∧
      (77/100:ℚ)<upperHShifted.coeff 2-
        DirectedPowerBounds.negativeNorm upperHShifted 3 31 (71/240) := by decide

theorem upperPH_varying_positive {z : ℝ}
    (hz : z∈Set.Icc (left .varying:ℝ) (right .varying:ℝ)) :
    0<aeval z (upperPH .varying) := by
  have hx : z-1/6∈Set.Icc 0 (71/240:ℝ) := by
    norm_num [left,right] at hz
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.quadratic_lower upper_H_shifted_identity hx
  have h0 : (0:ℝ)<(upperHShifted.coeff 0:ℝ) := by
    exact_mod_cast lt_trans (by norm_num : (0:ℚ)<77/50000) upper_H_shifted_reserve.1
  have h1 : (0:ℝ)≤(upperHShifted.coeff 1:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<109/1000)
      upper_H_shifted_reserve.2.1).le
  have h2 : (0:ℝ)≤(upperHShifted.coeff 2:ℝ)-
      (DirectedPowerBounds.negativeNorm upperHShifted 3 31 (71/240):ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<77/100)
      upper_H_shifted_reserve.2.2).le
  have he : aeval (z-1/6) upperHShifted=aeval z (upperPH .varying) := by
    simp [upperHShifted,L]
  rw [he] at hb
  have hl := mul_nonneg h1 hx.1
  have hq := mul_nonneg h2 (sq_nonneg (z-1/6))
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upper_B_centered_identity (a : Upper) :
    upperBCentered a=C ((upperBCentered a).coeff 0)+tail (upperBCentered a) 1 29 := by
  cases a <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upper_B_centered_reserve (a : Upper) :
    (3/100:ℚ)<(upperBCentered a).coeff 0-
      PowerTailBounds.norm (upperBCentered a) 1 29 (upperRadius a) := by
  cases a <;> decide

theorem upperPB_positive (a : Upper) {z : ℝ}
    (hz : z∈Set.Icc (left a:ℝ) (right a:ℝ)) :
    0<aeval z (upperPB a) := by
  have hb := DirectedPowerBounds.constant_lower (upper_B_centered_identity a)
    (upper_centered_domain a hz)
  have hr : (3/100:ℝ)<((upperBCentered a).coeff 0:ℝ)-
      (PowerTailBounds.norm (upperBCentered a) 1 29 (upperRadius a):ℝ) := by
    exact_mod_cast upper_B_centered_reserve a
  have he : aeval (z-(upperMid a:ℝ)) (upperBCentered a)=aeval z (upperPB a) := by
    simp [upperBCentered]
  rw [he] at hb
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upper_H_clamped_identity :
    upperHClampedCentered=C (upperHClampedCentered.coeff 0)+
      tail upperHClampedCentered 1 29 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upper_H_clamped_reserve :
    (1/10:ℚ)<upperHClampedCentered.coeff 0-
      PowerTailBounds.norm upperHClampedCentered 1 29 (upperRadius .clamped) := by decide

theorem upperPH_clamped_positive {z : ℝ}
    (hz : z∈Set.Icc (left .clamped:ℝ) (right .clamped:ℝ)) :
    0<aeval z (upperPH .clamped) := by
  have hb := DirectedPowerBounds.constant_lower upper_H_clamped_identity
    (upper_centered_domain .clamped hz)
  have hr : (1/10:ℝ)<(upperHClampedCentered.coeff 0:ℝ)-
      (PowerTailBounds.norm upperHClampedCentered 1 29 (upperRadius .clamped):ℝ) := by
    exact_mod_cast upper_H_clamped_reserve
  have he : aeval (z-(upperMid .clamped:ℝ)) upperHClampedCentered=
      aeval z (upperPH .clamped) := by simp [upperHClampedCentered]
  rw [he] at hb
  linarith

theorem upperPH_positive (a : Upper) {z : ℝ}
    (hz : z∈Set.Icc (left a:ℝ) (right a:ℝ)) :
    0<aeval z (upperPH a) := by
  cases a
  · exact upperPH_varying_positive hz
  · exact upperPH_clamped_positive hz

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Certificate
