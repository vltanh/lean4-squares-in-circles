module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2CutNorms

/-!
# All fourteen negative-flat-A / nonnegative-TD2 scalar endpoints

Uncompiled transcription of equations (8), (9), and (9a) in the complete
scalar companion. Every endpoint below uses the explicit prescribed
weights and the actual trigonometric norms. No scalar positivity remains
as a premise of these statements.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity Explicit
open PositiveTD.Certificate (h)

theorem cut_endpoint (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    0<baseline (cutAtG e) (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z)
      (cutAngle e:ℝ) z+cutV e z := by
  have hn := cut_norm_bounds e hz
  have hr := cut_masses_positive e hz
  have hnonneg := cut_norms_nonnegative e hz
  have hp := PositiveTD.Certificate.num4_transfer (hr 0) (hr 1) (hr 2) (hr 3)
    (hnonneg 0) (hnonneg 1) (hnonneg 2) (hnonneg 3)
    (hn 0) (hn 1) (hn 2) (hn 3) (cut_elementary_lower e hz)
    (show 0<aeval z (PositiveTD.Certificate.num4 _ _ _ _ _ _ _ _ _) from
      cut_numerator_positive e hz)
  have he := cut_scaled_identity e hz
  have hprod : 0<Real.cos (cutAngle e:ℝ)*
      (reducedBaseline .high (cutAtG e) (cutAngle e:ℝ) z+cutV e z) := by
    simpa only [he,normSum,↓reduceIte] using hp
  have hc : 0<Real.cos (cutAngle e:ℝ) := by
    linarith [(transport_trig (cut_domain e)).1]
  have hh := (mul_pos_iff_of_pos_left hc).mp hprod
  have hl := reduced_le_baseline .high (cutAtG e) (cutAngle e:ℝ) z
  linarith

theorem low_endpoints {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z+
      V R (Explicit.k .low z) 1 z ∧
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z+
      mixedG (Explicit.k .low z) (Explicit.l .low z) z ∧
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+V R (Explicit.k .low z) 1 frameCap ∧
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+
        V R (Explicit.k .low z) (Explicit.l .low z) frameCap ∧
    0<baseline true (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z z :=
  ⟨low_H_endpoint hz,low_M_endpoint hz,low_SH_endpoint hz,low_SG_endpoint hz,
    equal_GA_endpoint .low hz⟩

theorem high_endpoints {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (Explicit.k .high z) 1 z ∧
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (Explicit.k .high z) (Explicit.l .high z) z ∧
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (min (Explicit.l .high z) (Explicit.m .high z))
        (max (Explicit.l .high z) (Explicit.m .high z)) z ∧
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z z ∧
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z z :=
  ⟨high_H_endpoint hz,high_G_endpoint hz,high_B_endpoint hz,
    equal_GA_endpoint .high hz,equal_AB_endpoint hz⟩

theorem GA_cut_endpoints {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) (1/4) z+
      V R (Explicit.k .high z) 1 (z-1/4) ∧
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) (1/4) z+
      V R (Explicit.m .high z) (Explicit.l .high z) (z-1/4) := by
  have hH := cut_endpoint .gaH hz
  have hB := cut_endpoint .gaB hz
  constructor
  · simpa [cutAtG,cutAngle,cutV,cutCostCoefficient,cutRole,cutPCoefficient,cutQCoefficient,V] using hH
  · simpa [cutAtG,cutAngle,cutV,cutCostCoefficient,cutRole,cutPCoefficient,cutQCoefficient,V,
      pairNorm_symm (Explicit.m .high z) (Explicit.l .high z)] using hB

theorem AB_cut_endpoints {z : ℝ} (hz : z∈Icc (19/50:ℝ) (7/10:ℝ)) :
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) (19/50) z+
      V R (Explicit.k .high z) (Explicit.l .high z) (z-19/50) ∧
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) (19/50) z+
      V R (Explicit.k .high z) 1 (z-19/50) := by
  have hG := cut_endpoint .abG hz
  have hH := cut_endpoint .abH hz
  constructor
  · simpa [cutAtG,cutAngle,cutV,cutCostCoefficient,cutRole,cutPCoefficient,cutQCoefficient,V] using hG
  · simpa [cutAtG,cutAngle,cutV,cutCostCoefficient,cutRole,cutPCoefficient,cutQCoefficient,V] using hH

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
