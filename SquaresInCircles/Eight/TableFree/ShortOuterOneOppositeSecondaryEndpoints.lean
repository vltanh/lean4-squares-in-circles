module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeSecondaryPositive

/-!
# The fixed opposite-secondary endpoint arithmetic

Uncompiled transcription of Section 4 of
`HAND_SHORT_WORD_OPPOSITE_SECONDARY_FAMILIES_WITHOUT_TABLES.md`.
The six source bounds and the two six-entry norm bounds are the exact
rationals displayed in the hand proof. Every norm bound is derived
from its actual squared norm; only the two scalar endpoints occur.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeSecondary.Endpoint
open CommonQuarter CorePairGeometry Arithmetic

def sourceLower : Row→ℝ :=
  ![129190084/1000000000,-729270342/1000000000,273508205/1000000000,0,263139366/1000000000,0]
def initialNormUpper : Row→ℝ :=
  ![1880509701/1000000000,1350400957/1000000000,1332148407/1000000000,
    1176679496/1000000000,1452999491/1000000000,1241873719/1000000000]
def finalNormUpper : Row→ℝ :=
  ![1366936046/1000000000,778595795/1000000000,802609647/1000000000,
    640396588/1000000000,875421590/1000000000,681426094/1000000000]
def initialLower : Row→ℝ :=
  ![89758/100000,89835/100000,89810/100000,89811/100000,89813/100000,92987/100000]

lemma source_lower (r : Row) : sourceLower r≤ sourceBound r := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  have haxial : sourceLower r≤p r*outerAxial := by
    fin_cases r <;> norm_num [sourceLower,p] <;> linarith
  have hd' : (899214065/1000000000:ℝ)<outerDiagonal := by
    rw [outerDiagonal,lt_sub_iff_add_lt,Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  have hdiagonal : r≠1→sourceLower r≤(p r+weight r-q r)*outerDiagonal := by
    intro hr
    fin_cases r <;> first | exact absurd rfl hr | (norm_num [sourceLower,p,q,weight] <;> linarith)
  by_cases hr : r=1
  · simpa [sourceBound,hr] using haxial
  · rw [sourceBound]
    simp only [hr,↓reduceIte]
    exact le_min haxial (hdiagonal hr)

lemma initial_norm (r : Row) (high : Bool) : N r high 0< initialNormUpper r := by
  have hn := norm_initial r high
  have hp := norm_positive r high (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  fin_cases r <;> norm_num [initialNormUpper,P,t,weight] at hn ⊢ <;> nlinarith

lemma final_norm (r : Row) : N r false (7/10)<finalNormUpper r := by
  have hn := norm_sq r false (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hp := norm_positive r false (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have ht := RoleFour.fine_cap_trig
  fin_cases r <;> norm_num [finalNormUpper,P,t,weight,Unit.direction] at hn ⊢ <;>
    nlinarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

lemma initial_product (r : Row) (high : Bool) :
    radius*N r high 0<radiusUpper*initialNormUpper r := by
  have hR : radius≤radiusUpper := by
    have h := RoleFour.radius_upper
    rw [show radiusUpper=(1978788/1000000:ℝ) by norm_num [radiusUpper]]
    exact h.le
  exact (mul_le_mul_of_nonneg_right hR
    (norm_positive r high (show (0:ℝ)∈Icc 0 (7/10) by norm_num)).le).trans_lt
      (mul_lt_mul_of_pos_left (initial_norm r high) (by norm_num [radiusUpper] : (0:ℝ)<radiusUpper))

lemma final_product (r : Row) : radius*N r false (7/10)<radiusUpper*finalNormUpper r := by
  have hR : radius≤radiusUpper := by
    have h := RoleFour.radius_upper
    rw [show radiusUpper=(1978788/1000000:ℝ) by norm_num [radiusUpper]]
    exact h.le
  exact (mul_le_mul_of_nonneg_right hR
    (norm_positive r false (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)).le).trans_lt
      (mul_lt_mul_of_pos_left (final_norm r) (by norm_num [radiusUpper] : (0:ℝ)<radiusUpper))

lemma initial_value (r : Row) (high : Bool) : initialLower r<value r high 0 := by
  have hs := source_lower r
  have hn := initial_product r high
  have hp := pi_hand_enclosure.1
  fin_cases r <;> norm_num [value,c,P,t,weight,sourceLower,initialNormUpper,
    initialLower,radiusUpper] at hs hn ⊢ <;> linarith

lemma initial_threshold (r : Row) (high : Bool) : threshold r<value r high 0 := by
  have hh := initial_value r high
  have hle : threshold r≤ initialLower r := by fin_cases r <;> norm_num [threshold,initialLower]
  exact hle.trans_lt hh

lemma final_value (r : Row) : (497/500:ℝ)<value r false (7/10) := by
  have hs := source_lower r
  have hn := final_product r
  have hp := pi_hand_enclosure.1
  have hc := RoleFour.fine_cap_trig.2.2.1
  fin_cases r <;> norm_num [value,c,P,t,weight,Unit.direction,sourceLower,
    finalNormUpper,radiusUpper] at hs hn ⊢ <;> linarith

lemma initial_curvature_reserve (r : Row) : (11/1000:ℝ)<4*weight r-radius*N r false 0 := by
  have hh := initial_product r false
  have hrat : (11/1000:ℝ)<4*weight r-radiusUpper*initialNormUpper r := by
    fin_cases r <;> norm_num [weight,radiusUpper,initialNormUpper]
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeSecondary.Endpoint
