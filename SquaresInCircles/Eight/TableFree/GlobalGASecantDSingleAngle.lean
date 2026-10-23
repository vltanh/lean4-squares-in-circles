module

public import SquaresInCircles.Eight.TableFree.GlobalGASecantDSingleMonotone

/-!
# The complete signed single-angle secant-D estimate

Uncompiled completion of Section 1 of
`HAND_G3_SECANT_D_SINGLE_ANGLE_COMPARISON.md`. The negative branch first
uses the proved monotonicity in the actual secant coefficient, then
compares the full and diagonal supports at coefficient one. The final
export evaluates the force at the original sorted contained point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.SecantD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3
open OrdinaryNegativeSlope

theorem full_increment_negative {c n : ℝ} (hn : n∈Icc 0 frameCap) :
    c*(edgeWidth (-n)-1)+fullSupport 1 c-
      fullSupport (1-c*Real.sin n) (c*Real.cos n)=
        c*(Real.cos n-1)-R*(pairNorm c 1 (-n)-pairNorm c 1 0) := by
  have hnorm := force_norm 1 c (-n)
  simp only [Real.sin_neg,Real.cos_neg,mul_neg,add_neg_eq_sub] at hnorm
  have hzero : Real.sqrt ((1:ℝ)^2+c^2)=pairNorm c 1 0 := by
    simp [pairNorm,pairEnergy,pairProduct,add_comm]
  rw [edgeWidth_negative_formula hn]
  dsimp [fullSupport]
  rw [hnorm,hzero]
  ring

theorem negative_unit_below {k c n : ℝ}
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hc : c∈Icc cLower cUpper)
    (hkc : k≤c) (hc1 : c≤1) (hn : n∈Icc 0 frameCap) :
    V R k 1 n≤increment 1 c (-n) := by
  have h1 : (1:ℝ)∈Icc 1 qUpper := by norm_num [qUpper]
  have hs := sortedSupport_le_full (f:=1-c*Real.sin n) (g:=c*Real.cos n)
  have he := full_increment_negative (c:=c) hn
  have hcost := mul_nonneg (sub_nonneg.mpr hc1)
    (sub_nonneg.mpr (Real.cos_le_one n))
  have hV := OrdinaryNegativeEnvelope.V_monotone_smaller (Real.sqrt_nonneg qCap)
    (q:=1) (by norm_num) hn
    (show k∈Icc ((1:ℝ)/2) 1 by constructor <;> linarith [hk.1,hk.2])
    (show c∈Icc ((1:ℝ)/2) 1 by exact ⟨hk.1.trans hkc,hc1⟩) hkc
  dsimp [increment,V]
  simp only [Real.sin_neg,Real.cos_neg,mul_neg,add_neg_eq_sub]
  rw [baseline_full h1 hc hc1]
  dsimp [V] at hV
  linarith

theorem negative_unit_above {k c n : ℝ}
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hc : c∈Icc cLower cUpper)
    (h1c : 1≤c) (hn : n∈Icc 0 frameCap) :
    V R k 1 n≤increment 1 c (-n) := by
  have hc0 : 0≤c := by linarith
  have hphi := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.one_le_phi hn) hc0
  have hfg : 1-c*Real.sin n≤c*Real.cos n := by dsimp [phi] at hphi; linarith
  have hid : increment 1 c (-n)=c*((diagonal+1/2)*Real.sin n+
      (diagonal-1/2)*(1-Real.cos n)) := by
    dsimp [increment]
    simp only [Real.sin_neg,Real.cos_neg,mul_neg,add_neg_eq_sub]
    rw [sortedSupport_diagonal h1c,sortedSupport_diagonal hfg,edgeWidth_negative_formula hn]
    dsimp [diagonalSupport]
    ring
  have hD := mul_le_mul_of_nonneg_left (diagonal_negative_growth hn) hc0
  have hV := V_tangent_zero
    (show 0<k by linarith [hk.1]) (show k≤1 by linarith [hk.2])
    (show 1≤2*k by linarith [hk.1]) hn
  have hV0 := mul_le_mul_of_nonneg_right (PositiveTD.reference_slope_zero hk).le hn.1
  have hscale := mul_nonneg (sub_nonneg.mpr h1c) hn.1
  rw [hid]
  nlinarith

theorem negative_lower {q k c n : ℝ} (hq : q∈Icc 1 qUpper)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hc : c∈Icc cLower cUpper)
    (hkc : k≤c) (hn : n∈Icc 0 frameCap) :
    V R k 1 n≤increment q c (-n) := by
  have hunit : V R k 1 n≤increment 1 c (-n) := by
    by_cases hc1 : c≤1
    · exact negative_unit_below hk hc hkc hc1 hn
    · exact negative_unit_above hk hc (lt_of_not_ge hc1).le hn
  exact hunit.trans (negative_coefficient_lower hq hc hn)

/-- Uniform signed inequality for the one remaining original D angle. -/
theorem lower {q k c t : ℝ} (hq : q∈Icc 1 qUpper)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hc : c∈Icc cLower cUpper)
    (hkc : k≤c) (ht : |t|≤frameCap) :
    -slope*max q c*positivePart t+V R k 1 (negativePart t)≤increment q c t := by
  by_cases ht0 : 0≤t
  · have h := positive_lower hq hc ⟨ht0,(le_abs_self t).trans ht⟩
    simpa [positivePart,negativePart,max_eq_left ht0,
      max_eq_right (show -t≤0 by linarith)] using h
  · have hn : -t∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs t).trans ht⟩
    have h := negative_lower hq hk hc hkc hn
    simpa [positivePart,negativePart,max_eq_right (le_of_not_ge ht0),
      max_eq_left (show 0≤ -t by linarith)] using h

theorem actual_support {Q q c t : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : P.y≤0) (hP : P.Contained Q) (hQ : Q≤qCap)
    (hq : q∈Icc 1 qUpper) (hc : c∈Icc cLower cUpper) (ht : |t|≤frameCap) :
    (q+c*Real.sin t)*P.a+(c*Real.cos t)*(-P.y)≤
      sortedSupport (q+c*Real.sin t) (c*Real.cos t) := by
  have hf := forces_positive hq hc ht
  exact actual_sorted_support hs hy hP hQ hf.1.le hf.2.le

/-- The minorant at the unchanged original sorted outer D point. -/
theorem actual_minorant {Q q k c t : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : P.y≤0) (hP : P.Contained Q) (hQ : Q≤qCap)
    (hq : q∈Icc 1 qUpper) (hk : k∈Icc (1/2:ℝ) (17/20))
    (hc : c∈Icc cLower cUpper) (hkc : k≤c) (ht : |t|≤frameCap) :
    -slope*max q c*positivePart t+V R k 1 (negativePart t)≤
      actualIncrement q c t P := by
  have hminor := lower hq hk hc hkc ht
  have hsupp := actual_support hs hy hP hQ hq hc ht
  dsimp [increment,actualIncrement] at *
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.SecantD
