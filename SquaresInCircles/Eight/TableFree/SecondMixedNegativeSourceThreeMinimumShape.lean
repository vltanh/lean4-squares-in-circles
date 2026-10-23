module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeSourceThreeMinimumPolynomials

/-!
# Concave first derivatives on both complete minimum intervals

The positive denominator difference puts the phase's third derivative
below one. The positive stationary numerator subtracts another positive
quantity. The literal L label has third derivative above one, proving
strict negativity on each complete target interval. Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratioD ratioDD)

lemma first_slope : g∈slopes := by norm_num [slopes,g,EdgeThreeAligned.gn]
lemma second_slope : (39/40:ℝ)∈slopes := by norm_num [slopes,g,EdgeThreeAligned.gn]

lemma label_third_large {B : ℝ} (hB : B∈targets) : (1:ℝ)<LLabel.d3 B := by
  have hu := U_positive (outer_domain (target_domain hB))
  have hcube := pow_le_pow_left₀ hu.le (show U B≤2 by linarith [(U_bounds hB).2]) 3
  have hr : (1/4:ℝ)<ratioD B := by
    change (1/4:ℝ)<Q0/(U B)^3
    apply (lt_div_iff₀ (pow_pos hu 3)).2
    norm_num [Q0] at *
    linarith
  have hrd := ratioDD_positive (target_domain hB)
  have hp := mul_nonneg hB.1 hrd.le
  dsimp [RoleLabel.d3,LLabel]
  nlinarith

lemma phase_third_upper {B : ℝ} (hB : B∈targets) : betaDDD B<1 := by
  have hu := U_positive (outer_domain (target_domain hB))
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hp := Polynomials.D0_positive ⟨(U_bounds hB).1.le,(U_bounds hB).2.le⟩
  dsimp [betaDDD]
  apply (div_lt_one (mul_pos (pow_pos hu 5) (pow_pos ht 3))).2
  dsimp [D0,T] at *
  linarith

lemma stationary_third_positive {h B : ℝ} (hh : h∈slopes) (hB : B∈targets)
    (hpoly : 0<Ch h (U B)) : 0<RDD h B := by
  rw [RDD_identity hh hB]
  have hu := U_positive (outer_domain (target_domain hB))
  have ht : 0<T B := by linarith [(T_bounds hB).1]
  have hs := S_positive hh hB
  have hv : 0<V B := by dsimp [V]; linarith [hB.1]
  positivity

lemma first_third_negative {B : ℝ} (hB : B∈targets) : E3 g B<0 := by
  have hpoly := Polynomials.Ch_first_positive ⟨(U_bounds hB).1.le,(U_bounds hB).2.le⟩
  have hr := stationary_third_positive first_slope hB hpoly
  dsimp [E3]
  linarith [phase_third_upper hB,label_third_large hB]

lemma second_height {B : ℝ} (hB : B∈Icc (9/20:ℝ) (27/50)) : U B∈Icc (42/25:ℝ) (87/50) := by
  have hd : B∈targets := ⟨by linarith [hB.1],hB.2⟩
  have hu := U_bounds hd
  have hq := UW_circle (outer_domain (target_domain hd))
  have hv2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤19/20)
    (show (19/20:ℝ)≤B+1/2 by linarith [hB.1]) 2
  refine ⟨hu.1.le,?_⟩
  dsimp [W] at hq
  norm_num [Q0] at hq
  nlinarith

lemma second_third_negative {B : ℝ} (hB : B∈Icc (9/20:ℝ) (27/50)) : E3 (39/40) B<0 := by
  have hd : B∈targets := ⟨by linarith [hB.1],hB.2⟩
  have hpoly := Polynomials.Ch_second_positive (second_height hB)
  have hr := stationary_third_positive second_slope hd hpoly
  dsimp [E3]
  linarith [phase_third_upper hd,label_third_large hd]

lemma first_second_antitone : AntitoneOn (E2 g) targets :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (E2_hasDerivAt first_slope hB).continuousAt.continuousWithinAt)
    (fun B hB => E2_hasDerivAt first_slope (Ioo_subset_Icc_self hB))
    (fun B hB => (first_third_negative (Ioo_subset_Icc_self hB)).le)

lemma first_first_concave : ConcaveOn ℝ targets (E1 g) :=
  concave_of_deriv2 (fun B hB => E1_hasDerivAt first_slope hB)
    (fun B hB => E2_hasDerivAt first_slope hB) (fun B hB => (first_third_negative hB).le)

lemma second_second_antitone : AntitoneOn (E2 (39/40)) (Icc (9/20:ℝ) (27/50)) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (E2_hasDerivAt second_slope (show B∈targets from ⟨by linarith [hB.1],hB.2⟩)).continuousAt.continuousWithinAt)
    (fun B hB => E2_hasDerivAt second_slope (show B∈targets from ⟨by linarith [hB.1],hB.2.le⟩))
    (fun B hB => (second_third_negative (Ioo_subset_Icc_self hB)).le)

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum
