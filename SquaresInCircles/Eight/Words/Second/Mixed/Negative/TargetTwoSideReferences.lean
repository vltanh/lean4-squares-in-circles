module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoSideDiscriminant

/-!
# Eight squares: fixed scalar references for the complete side discriminant

Every trigonometric reference is bounded by exact Taylor polynomials.
The two pi-dependent coefficients have rational cages already proved
from the common pi enclosure.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
open CommonQuarter CorePairGeometry Arithmetic

private lemma shift_product {x y l u : ℝ} (hx : 0≤x) (hl : 0≤l) (hy : l≤y ∧ y≤u) :
    (-(25539083129/200000000000:ℝ)-q*x)*u≤(C-q*x)*y ∧
    (C-q*x)*y≤(-(31923853911/250000000000:ℝ)-q*x)*l := by
  have hy0 := hl.trans hy.1
  have hlo : -(25539083129/200000000000:ℝ)-q*x≤0 := by dsimp [q]; linarith
  have hhi : -(31923853911/250000000000:ℝ)-q*x≤0 := by dsimp [q]; linarith
  constructor
  · exact (mul_le_mul_of_nonpos_left hy.2 hlo).trans
      (mul_le_mul_of_nonneg_right (by linarith [C_bounds.1] :
        -(25539083129/200000000000:ℝ)-q*x≤C-q*x) hy0)
  · exact (mul_le_mul_of_nonneg_right (by linarith [C_bounds.2] :
        C-q*x≤ -(31923853911/250000000000:ℝ)-q*x) hy0).trans
      (mul_le_mul_of_nonpos_left hy.1 hhi)

local macro "discriminant_reference" x:term : tactic => `(tactic|
  (have hsL := HighOrderTaylor.S15_le_sin (x := $x) (by norm_num)
   have hsU := HighOrderTaylor.sin_le_S13 (x := $x) (by norm_num)
   have hcL := HighOrderTaylor.C14_le_cos (x := $x) (by norm_num)
   have hcU := HighOrderTaylor.cos_le_C12 (x := $x) (by norm_num)
   have hs2L := HighOrderTaylor.S15_le_sin (x := 2*$x) (by norm_num)
   have hs2U := HighOrderTaylor.sin_le_S13 (x := 2*$x) (by norm_num)
   have hc2L := HighOrderTaylor.C14_le_cos (x := 2*$x) (by norm_num)
   have hc2U := HighOrderTaylor.cos_le_C12 (x := 2*$x) (by norm_num)
   have hpC := shift_product (x := $x) (by norm_num)
     (show 0≤HighOrderTaylor.C14 (2*$x) by
       norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8]) ⟨hc2L,hc2U⟩
   have hpS := shift_product (x := $x) (by norm_num)
     (show 0≤HighOrderTaylor.S15 (2*$x) by
       norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7]) ⟨hs2L,hs2U⟩
   norm_num [q,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
     HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8]
     at hsL hsU hcL hcU hs2L hs2U hc2L hc2U hpC hpS
   norm_num [E,E1,E2,E3,A,B,H,J,q]
   repeat' constructor
   all_goals nlinarith [C_bounds.1,C_bounds.2,Z_bounds.1,Z_bounds.2]))

lemma zero_value : (177/1000000:ℝ)<E 0 := by
  norm_num [E,A,B,H,J,q]
  linarith [C_bounds.1,Z_bounds.1]

lemma left_reference : (339/100000:ℝ)<E (3/10) ∧ (7/5:ℝ)<E3 (3/10) ∧
    E1 (3/10)< -(13/1000:ℝ) ∧ (47/1000:ℝ)<E2 (3/10) := by
  discriminant_reference (3/10:ℝ)

lemma right_reference : (279/100000:ℝ)<E (1/2) ∧ E3 (1/2)< -(11/10:ℝ) ∧
    (43/5000:ℝ)<E1 (1/2) ∧ (11/125:ℝ)<E2 (1/2) := by
  discriminant_reference (1/2:ℝ)

lemma terminal_value : (389/100000:ℝ)<E (7/10) := by
  discriminant_reference (7/10:ℝ)

lemma middle_reference : (61/25000:ℝ)<E (213/500) ∧
    -(1/25000:ℝ)<E1 (213/500) ∧ E1 (213/500)<(1/25000:ℝ) := by
  discriminant_reference (213/500:ℝ)

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
