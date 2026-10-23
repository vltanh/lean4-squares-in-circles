module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDPolynomialData

/-!
# Four whole-interval polynomial reserves on the low TD2 interval

Uncompiled source.  The tight first numerator retains its positive cubic
at the right endpoint; the mixed numerator retains a quadratic at the
midpoint.  The two separated numerators use respectively one centered
coefficient sum and their exact secant quotient.  All rational reductions
are written as kernel proof terms and have not been executed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Certificate
open Polynomial PowerTailBounds

def lowMass : Fin 3→ℚ[X] := ![lowRH,lowRG,lowRB]
def lowMassReserve : Fin 3→ℚ := ![109/100,29/25,71/50]
def lowMassCentered (i : Fin 3) : ℚ[X] := DirectedPowerBounds.shift (1/12) (lowMass i)
def lowReversed : ℚ[X] := DirectedPowerBounds.reverse L lowP
def lowMixedCentered : ℚ[X] := DirectedPowerBounds.shift (1/12) lowPM
def lowSHCentered : ℚ[X] := DirectedPowerBounds.shift (1/12) lowPSH
def lowQuotientCentered : ℚ[X] := DirectedPowerBounds.shift (1/12) lowChordQuotient

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_mass_identity (i : Fin 3) :
    lowMassCentered i=C ((lowMassCentered i).coeff 0)+tail (lowMassCentered i) 1 4 := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_mass_reserve (i : Fin 3) :
    lowMassReserve i<(lowMassCentered i).coeff 0-
      PowerTailBounds.norm (lowMassCentered i) 1 4 (1/12) := by
  fin_cases i <;> decide

theorem low_mass_lower (i : Fin 3) {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    (lowMassReserve i:ℝ)<aeval z (lowMass i) := by
  have hx : |z-1/12|≤(1/12:ℝ) := abs_le.mpr
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower (low_mass_identity i) hx
  have hr : (lowMassReserve i:ℝ)<((lowMassCentered i).coeff 0:ℝ)-
      (PowerTailBounds.norm (lowMassCentered i) 1 4 (1/12):ℝ) := by
    exact_mod_cast low_mass_reserve i
  have he : aeval (z-1/12) (lowMassCentered i)=aeval z (lowMass i) := by
    simp [lowMassCentered]
  rw [he] at hb
  exact hr.trans_le hb

theorem low_masses_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowRH ∧ 0<aeval z lowRG ∧ 0<aeval z lowRB := by
  have h0 := low_mass_lower 0 hz
  have h1 := low_mass_lower 1 hz
  have h2 := low_mass_lower 2 hz
  norm_num [lowMass,lowMassReserve] at h0 h1 h2
  exact ⟨by linarith,by linarith,by linarith⟩

theorem low_den_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowDen := by
  obtain ⟨h0,h1,h2⟩ := low_masses_positive hz
  simp only [lowDen,map_mul,aeval_C]
  norm_num
  positivity

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_reversed_identity :
    lowReversed=C (lowReversed.coeff 0)+C (lowReversed.coeff 1)*X+
      C (lowReversed.coeff 2)*X^2+C (lowReversed.coeff 3)*X^3+
        tail lowReversed 4 31 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_reversed_reserve :
    (199/100000:ℚ)<lowReversed.coeff 0 ∧
      (43/2500:ℚ)<lowReversed.coeff 1 ∧
      (277/50:ℚ)<lowReversed.coeff 2 ∧
      (297/100:ℚ)<lowReversed.coeff 3-
        DirectedPowerBounds.negativeNorm lowReversed 4 31 L := by decide

theorem lowP_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowP := by
  let x : ℝ := 1/6-z
  have hx : x∈Set.Icc 0 (L:ℝ) := by
    norm_num [x,L]
    exact ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hb := DirectedPowerBounds.cubic_lower low_reversed_identity hx
  have h0 : (0:ℝ)<(lowReversed.coeff 0:ℝ) := by
    exact_mod_cast lt_trans (by norm_num : (0:ℚ)<199/100000) low_reversed_reserve.1
  have h1 : (0:ℝ)≤(lowReversed.coeff 1:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<43/2500) low_reversed_reserve.2.1).le
  have h2 : (0:ℝ)≤(lowReversed.coeff 2:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<277/50) low_reversed_reserve.2.2.1).le
  have h3 : (0:ℝ)≤(lowReversed.coeff 3:ℝ)-
      (DirectedPowerBounds.negativeNorm lowReversed 4 31 L:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<297/100) low_reversed_reserve.2.2.2).le
  have he : aeval x lowReversed=aeval z lowP := by
    simp [lowReversed,x,L]
  rw [he] at hb
  have h1x := mul_nonneg h1 hx.1
  have h2x := mul_nonneg h2 (sq_nonneg x)
  have h3x := mul_nonneg h3 (pow_nonneg hx.1 3)
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_mixed_identity :
    lowMixedCentered=C (lowMixedCentered.coeff 0)+C (lowMixedCentered.coeff 1)*X+
      C (lowMixedCentered.coeff 2)*X^2+tail lowMixedCentered 3 32 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_mixed_reserve :
    (23/625:ℚ)<lowMixedCentered.coeff 0 ∧
      |lowMixedCentered.coeff 1|<19/40 ∧
      (187/25:ℚ)<lowMixedCentered.coeff 2-
        PowerTailBounds.norm lowMixedCentered 3 32 (1/12) := by decide

theorem lowPM_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPM := by
  let x : ℝ := z-1/12
  have hx : |x|≤(1/12:ℝ) := abs_le.mpr
    ⟨by dsimp [x]; linarith [hz.1],by dsimp [x]; linarith [hz.2]⟩
  have hb := PowerTailBounds.quadratic_lower low_mixed_identity (by norm_num) hx
  have h0 : (23/625:ℝ)<(lowMixedCentered.coeff 0:ℝ) := by
    exact_mod_cast low_mixed_reserve.1
  have h1 : |(lowMixedCentered.coeff 1:ℝ)|<19/40 := by
    exact_mod_cast low_mixed_reserve.2.1
  have h2 : (187/25:ℝ)<(lowMixedCentered.coeff 2:ℝ)-
      (PowerTailBounds.norm lowMixedCentered 3 32 (1/12):ℝ) := by
    exact_mod_cast low_mixed_reserve.2.2
  have hlinear : -(19/40)*|x|≤(lowMixedCentered.coeff 1:ℝ)*x := by
    have hh := mul_le_mul_of_nonneg_right h1.le (abs_nonneg x)
    rw [← abs_mul] at hh
    exact (abs_le.mp hh).1
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg x)
  have he : aeval x lowMixedCentered=aeval z lowPM := by simp [lowMixedCentered,x]
  rw [he] at hb
  nlinarith [sq_nonneg (|x|-(19/40)/(2*(187/25))),sq_abs x]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_SH_identity :
    lowSHCentered=C (lowSHCentered.coeff 0)+tail lowSHCentered 1 34 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_SH_reserve : (9/50:ℚ)<lowSHCentered.coeff 0-
    PowerTailBounds.norm lowSHCentered 1 34 (1/12) := by decide

theorem lowPSH_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPSH := by
  have hx : |z-1/12|≤(1/12:ℝ) := abs_le.mpr
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower low_SH_identity hx
  have hr : (9/50:ℝ)<(lowSHCentered.coeff 0:ℝ)-
      (PowerTailBounds.norm lowSHCentered 1 34 (1/12):ℝ) := by exact_mod_cast low_SH_reserve
  have he : aeval (z-1/12) lowSHCentered=aeval z lowPSH := by simp [lowSHCentered]
  rw [he] at hb
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_chord_identity : lowPSG=lowChord+X*(C L-X)*lowChordQuotient := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_quotient_identity :
    lowQuotientCentered=C (lowQuotientCentered.coeff 0)+tail lowQuotientCentered 1 34 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_chord_reserves :
    (451/10000:ℚ)<lowPSG.eval 0 ∧ (3963/10000:ℚ)<lowPSG.eval L ∧
      (44/5:ℚ)<lowQuotientCentered.coeff 0-
        PowerTailBounds.norm lowQuotientCentered 1 34 (1/12) := by decide

theorem lowPSG_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPSG := by
  have hx : |z-1/12|≤(1/12:ℝ) := abs_le.mpr
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower low_quotient_identity hx
  have hr : (44/5:ℝ)<(lowQuotientCentered.coeff 0:ℝ)-
      (PowerTailBounds.norm lowQuotientCentered 1 34 (1/12):ℝ) := by
    exact_mod_cast low_chord_reserves.2.2
  have he : aeval (z-1/12) lowQuotientCentered=aeval z lowChordQuotient := by
    simp [lowQuotientCentered]
  rw [he] at hb
  have hQ : 0≤aeval z lowChordQuotient := by linarith
  have hzero : (451/10000:ℝ)≤(lowPSG.eval 0:ℝ) := by
    exact_mod_cast low_chord_reserves.1.le
  have hend : (451/10000:ℝ)≤(lowPSG.eval L:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (451/10000:ℚ)<3963/10000)
      low_chord_reserves.2.1).le
  have hfirst := mul_le_mul_of_nonneg_left hzero
    (show 0≤1-6*z by linarith [hz.2])
  have hlast := mul_le_mul_of_nonneg_left hend (show 0≤6*z by positivity)
  have hT : (451/10000:ℝ)≤aeval z lowChord := by
    simp only [lowChord,map_add,map_sub,map_mul,map_one,aeval_C,aeval_X]
    norm_num [L]
    linarith
  have hprod := mul_nonneg (mul_nonneg hz.1 (show 0≤1/6-z by linarith [hz.2])) hQ
  have hid := congrArg (fun f : ℚ[X] => aeval z f) low_chord_identity
  simp only [map_add,map_mul,map_sub,aeval_X,aeval_C] at hid
  norm_num [L] at hid
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Certificate
