module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDScalarBounds
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDUpperPolynomial
public import SquaresInCircles.Eight.TableFree.GlobalGATD2UpperEnvelope

/-!
# The two upper TD2 scalar inequalities at the explicit weights

Uncompiled source.  Both coefficient regimes and the crossing of the
tilted B coefficient through one are included.  Replacing the sorted D
support by its larger full-circle support is an inequality proved for
the original support; no anchor or frame is changed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Certificate
open Polynomial Explicit Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem upper_nonradical_lower (a : Upper) {z : ℝ}
    (hz : z∈Icc (left a:ℝ) (right a:ℝ)) :
    aeval z (upperA a)≤upperNonradical (Explicit.upperK a z) (Explicit.upperC a z) z := by
  have hr := Explicit.upper_ranges a hz
  have hc : 0<Explicit.upperC a z := by
    dsimp [Explicit.cap] at hr
    linarith [hr.2.2.2.2.1]
  have ht := taylor_bounds hr.1
  have hm := tilted_polynomial_bounds (c:=upperC a) hr.1 (by simpa using hc)
  simp only [upperC_eval] at hm
  have hs := sigma_sine_upper hr.1 hc.le
  have hW0 := mul_le_mul_of_nonneg_left
    (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
  have hW : Explicit.upperC a z/2*(1+aeval z C10+aeval z S11)≤
      Explicit.upperC a z*edgeWidth z := by
    rw [edgeWidth_positive_formula hr.1]
    nlinarith only [hW0]
  norm_num only [upperA,map_add,map_sub,map_mul,map_one,aeval_C,upperK_eval,upperC_eval]
  dsimp [upperNonradical]
  nlinarith only [hm.2.1,ht.2.2.2.2.1,hs,hW]

theorem upper_norm_bounds (a : Upper) {z : ℝ}
    (hz : z∈Icc (left a:ℝ) (right a:ℝ)) :
    (pairNorm (Explicit.upperK a z) 1 0)^2≤aeval z (upperPk a) ∧
    (pairNorm (tilted (Explicit.upperC a z) z) 1 0)^2≤aeval z (upperPm a) ∧
    (pairNorm (Explicit.upperC a z) 1 0)^2≤aeval z (upperPc a) ∧
    (pairNorm (Explicit.upperK a z) 1 (-z))^2≤aeval z (upperPHminus a) ∧
    (pairNorm (tilted (Explicit.upperC a z) z) 1 (-z))^2≤aeval z (upperPBminus a) := by
  have hr := Explicit.upper_ranges a hz
  have hk : 0<Explicit.upperK a z := by linarith [hr.2.1]
  have hc : 0<Explicit.upperC a z := hk.trans_le hr.2.2.2.1
  have hm := tilted_polynomial_bounds (c:=upperC a) hr.1 (by simpa using hc)
  simp only [upperC_eval] at hm
  have hm0 : 0<tilted (Explicit.upperC a z) z := tilted_pos hc hr.1
  have hm2 : (tilted (Explicit.upperC a z) z)^2≤(aeval z (mPlus (upperC a)))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm.2.2)
      (show 0≤aeval z (mPlus (upperC a))+tilted (Explicit.upperC a z) z by
        linarith [hm.2.2])]
  have ht := taylor_bounds hr.1
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [zero_norm_sq]
    simp [upperPk,add_comm]
  · rw [zero_norm_sq]
    simp only [upperPm,map_add,map_pow,map_one]
    norm_num
    linarith only [hm2]
  · rw [zero_norm_sq]
    simp [upperPc,add_comm]
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) hr.1 ht.2.1
    norm_num only [upperPHminus,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,upperK_eval]
    nlinarith only [hh]
  · have hh := negative_norm_sq_le (q:=1) hm0 (by norm_num) hr.1 ht.2.1
    have hs := mul_le_mul_of_nonneg_right hm.2.1 ht.1
    norm_num only [upperPBminus,map_add,map_sub,map_mul,map_pow,map_one,aeval_C]
    nlinarith only [hh,hs,hm2]

theorem upper_H_positive (a : Upper) {z : ℝ}
    (hz : z∈Icc (left a:ℝ) (right a:ℝ)) :
    0<baseline (Explicit.upperK a z) 1 (Explicit.upperC a z) z+
      V R (Explicit.upperK a z) 1 z := by
  have hr := upper_masses_positive a hz
  have hn := upper_norm_bounds a hz
  have hp := num4_transfer hr.1 hr.2.1 hr.2.2.2.1 hr.2.2.1
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.2.1 hn.2.2.1 (upper_nonradical_lower a hz) (upperPH_positive a hz)
  exact hp.trans_le (upper_H_lower _ _ _)

theorem upper_B_positive (a : Upper) {z : ℝ}
    (hz : z∈Icc (left a:ℝ) (right a:ℝ)) :
    0<baseline (Explicit.upperK a z) 1 (Explicit.upperC a z) z+
      V R (tilted (Explicit.upperC a z) z) 1 z := by
  have hr := upper_masses_positive a hz
  have hn := upper_norm_bounds a hz
  have hp := num4_transfer hr.1 hr.1 hr.2.2.2.2 hr.2.2.1
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.1 hn.2.2.2.2 hn.2.2.1 (upper_nonradical_lower a hz) (upperPB_positive a hz)
  exact hp.trans_le (upper_B_lower _ _ _)

/-- Concrete positivity for every intrinsic alternative in each upper
coefficient regime.  The scalar statements have no unproved premises. -/
theorem upper_endpoint_positive (a : Upper) {z : ℝ}
    (hz : z∈Icc (left a:ℝ) (right a:ℝ)) (i j : Fin 4) :
    0<baseline (Explicit.upperK a z) 1 (Explicit.upperC a z) z+
      endpoint (Explicit.upperK a z) 1 (Explicit.upperC a z) z i j := by
  have hr := Explicit.upper_ranges a hz
  have hm := Explicit.upper_tilted a hz
  have hk : Explicit.upperK a z∈Icc (2/3:ℝ) (17/20) := by
    dsimp [Explicit.cap] at hr
    exact ⟨hr.2.1.le,by linarith [hr.2.2.1]⟩
  exact upper_scalars_positive hk ⟨hm.1.le,hm.2.1.le⟩ hm.2.2.le hr.1
    (upper_H_positive a hz) (upper_B_positive a hz) i j

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD.Certificate
