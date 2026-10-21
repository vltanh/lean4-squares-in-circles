module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositivePolynomialData
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDLowPolynomial

/-!
# Four complete low-angle A-endpoint polynomial bounds

The single-negative numerator retains its right-endpoint value.
The mixed numerator uses one completed Chebyshev square; the two
separated alternatives use centered coefficient norms.  These are
exact rational statements on the whole interval [0,1/6].
Uncompiled source draft; the kernel reductions have not been run.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate

open Polynomial WholeIntervalPolynomial
open PositiveTD.Certificate (L)

def lowMixedCoefficients : ℕ→ℚ := coefficient 24 (centered 0 L lowPM)
def lowSHCentered : ℚ[X] := DirectedPowerBounds.shift (1/12) lowPSH
def lowSGCentered : ℚ[X] := DirectedPowerBounds.shift (1/12) lowPSG

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_quotient_identity :
    lowP=C (lowP.eval L)+(C L-X)*lowQuotient := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_quotient_expansion :
    centered 0 L lowQuotient=expansion 21 (centered 0 L lowQuotient) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_quotient_reserve :
    (127/10000:ℚ)<lowP.eval L ∧ (21/25:ℚ)<lowerOn 21 0 L lowQuotient := by decide

theorem lowP_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowP := by
  have hq := positive_on_interval (by norm_num [L] : (0:ℚ)<L)
    low_quotient_expansion low_quotient_reserve.2 hz
  have hc : (127/10000:ℝ)<(lowP.eval L:ℝ) := by exact_mod_cast low_quotient_reserve.1
  have he := congrArg (fun f : ℚ[X] => aeval z f) low_quotient_identity
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X] at he
  have hp : 0≤((L:ℝ)-z)*aeval z lowQuotient :=
    mul_nonneg (by norm_num [L]; linarith [hz.2]) (by norm_num at hq; linarith)
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_mixed_identity :
    centered 0 L lowPM=C (lowMixedCoefficients 0-lowMixedCoefficients 2)+
      C (lowMixedCoefficients 1)*X+C (2*lowMixedCoefficients 2)*X^2+
        ChebyshevLeadingBounds.tail lowMixedCoefficients 3 22 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_mixed_reserve :
    0<lowMixedCoefficients 2 ∧
      (93/1000:ℚ)<ChebyshevLeadingBounds.quadraticReserve lowMixedCoefficients 22 := by decide

theorem lowPM_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPM := by
  have hh := ChebyshevLeadingBounds.quadratic_on_interval
    (by norm_num [L] : (0:ℚ)<L) low_mixed_identity low_mixed_reserve.1 hz
  have hr : (93/1000:ℝ)<
      (ChebyshevLeadingBounds.quadraticReserve lowMixedCoefficients 22:ℝ) := by
    exact_mod_cast low_mixed_reserve.2
  linarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_separated_identities :
    lowSHCentered=C (lowSHCentered.coeff 0)+PowerTailBounds.tail lowSHCentered 1 19 ∧
    lowSGCentered=C (lowSGCentered.coeff 0)+PowerTailBounds.tail lowSGCentered 1 21 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_separated_reserves :
    (9/50:ℚ)<lowSHCentered.coeff 0-PowerTailBounds.norm lowSHCentered 1 19 (1/12) ∧
    (43/1000:ℚ)<lowSGCentered.coeff 0-PowerTailBounds.norm lowSGCentered 1 21 (1/12) := by decide

theorem lowPSH_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPSH := by
  have hx : |z-1/12|≤(1/12:ℝ) := abs_le.mpr
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hh := DirectedPowerBounds.constant_lower low_separated_identities.1 hx
  have hr : (9/50:ℝ)<(lowSHCentered.coeff 0:ℝ)-
      (PowerTailBounds.norm lowSHCentered 1 19 (1/12):ℝ) := by
    exact_mod_cast low_separated_reserves.1
  have he : aeval (z-1/12) lowSHCentered=aeval z lowPSH := by simp [lowSHCentered]
  rw [he] at hh
  linarith

theorem lowPSG_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPSG := by
  have hx : |z-1/12|≤(1/12:ℝ) := abs_le.mpr
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hh := DirectedPowerBounds.constant_lower low_separated_identities.2 hx
  have hr : (43/1000:ℝ)<(lowSGCentered.coeff 0:ℝ)-
      (PowerTailBounds.norm lowSGCentered 1 21 (1/12):ℝ) := by
    exact_mod_cast low_separated_reserves.2
  have he : aeval (z-1/12) lowSGCentered=aeval z lowPSG := by simp [lowSGCentered]
  rw [he] at hh
  linarith

theorem low_masses_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowRH ∧ 0<aeval z lowRG ∧ 0<aeval z lowRB := by
  have hh := PositiveTD.Certificate.low_masses_positive hz
  have hd := PositiveTD.Explicit.low_domain hz
  have hC : 0<aeval z PositiveTD.Certificate.lowC := by
    rw [PositiveTD.Certificate.lowC_eval]
    linarith [hd.1.1,hd.2.2.1.1]
  have hL : 0<aeval z PositiveTD.Certificate.lowL := by
    rw [PositiveTD.Certificate.lowL_eval]
    linarith [hd.1.1,hd.2.1.1]
  refine ⟨?_,?_,?_⟩
  · simpa only [lowRH,PositiveTD.Certificate.lowRH] using hh.1
  · simpa only [lowRG,PositiveTD.Certificate.lowRG] using hh.2.1
  · simp only [lowRB,map_add,map_mul,aeval_C]
    norm_num
    positivity

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate
