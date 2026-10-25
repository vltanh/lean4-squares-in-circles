module

public import SquaresInCircles.Eight.Words.Second.Outer.KReference
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeCapCalculus
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeCapReferences

/-!
# Eight squares: exact reserves at the named angle-cap references

The label bounds are direct substitutions into the proved physical
reference cages.  They give positive curvature through `.4`, the
near-stationary tangent reference, and a separate strict bound at the
actual diagonal-target endpoint.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.Cap

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo.CapCurve (height k k1 Domain target_mem)

lemma four_labels :
    TLabel.d1 (2/5)<(6761/10000:ℝ) ∧ TLabel.d2 (2/5)< -2913/5000 ∧
      (7137/10000:ℝ)<KLabel.d1 (height (2/5)) ∧
        (-339/500:ℝ)<KLabel.d2 (height (2/5)) := by
  have hs := FixedReference.target four_mem ⟨le_rfl,le_rfl⟩ four_radical
    (by norm_num) (by norm_num)
  have ht := KReference.target (target_mem four_domain) four_cage.1 four_target_radical
    (by norm_num) (by norm_num)
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,
    KReference.valueLo,KReference.valueHi,KReference.firstLo,KReference.firstHi,
    KReference.secondLo,KReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma reference_labels :
    T reference<(132951199/500000000:ℝ) ∧
      TLabel.d1 reference∈Icc (765874501/1000000000) (382937251/500000000) ∧
      (292887549/1000000000:ℝ)<K (height reference) ∧
      KLabel.d1 (height reference)∈Icc (789727136/1000000000) (789727137/1000000000) := by
  have hs := FixedReference.target reference_mem ⟨le_rfl,le_rfl⟩ reference_radical
    (by norm_num [reference]) (by norm_num)
  have ht := KReference.target (target_mem reference_domain) reference_cage.1
    reference_target_radical (by norm_num) (by norm_num)
  rw [show reference=(137517/500000:ℝ) from rfl] at hs ht ⊢
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,
    KReference.valueLo,KReference.valueHi,KReference.firstLo,KReference.firstHi,
    KReference.secondLo,KReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,⟨by linarith,by linarith⟩,by linarith,⟨by linarith,by linarith⟩⟩

lemma four_first : (3/50:ℝ)<first (2/5) := by
  have hp := mul_lt_mul four_labels.2.2.1 four_cage.2.1.le
    (by norm_num : (0:ℝ)<2587/2500)
    (by linarith [four_labels.2.2.1] : 0≤KLabel.d1 (height (2/5)))
  dsimp only [first]
  norm_num at hp
  linarith [four_labels.1]

lemma four_second : (6/25:ℝ)<second (2/5) := by
  have hk := NegativeTwo.CapCurve.k_bounds four_mem
  have hk0 : 0<k (2/5) := by linarith [hk.1]
  have hk2 := pow_lt_pow_left₀ four_cage.2.2.1 hk0.le (by norm_num : (2:ℕ)≠0)
  have hnegative := mul_lt_mul_of_pos_right four_labels.2.2.2 (pow_pos hk0 2)
  have hpositive := mul_lt_mul four_labels.2.2.1 four_cage.2.2.2.le
    (by norm_num : (0:ℝ)<342/625)
    (by linarith [four_labels.2.2.1] : 0≤KLabel.d1 (height (2/5)))
  dsimp only [second]
  norm_num at hpositive hk2
  linarith [four_labels.2.1]

lemma reference_value : (4488907/5000000:ℝ)<cost reference := by
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1,reference_labels.1,reference_labels.2.2.1]

lemma reference_first : |first reference|<(1/1000000:ℝ) := by
  have hK := reference_labels.2.2.2
  have hk := reference_cage.2
  have hlo := mul_le_mul hK.1 hk.1 (by norm_num : (0:ℝ)≤1212245417/1250000000)
    (by linarith [hK.1] : 0≤KLabel.d1 (height reference))
  have hhi := mul_le_mul hK.2 hk.2 (by linarith [hk.1] : 0≤k reference)
    (by norm_num : (0:ℝ)≤789727137/1000000000)
  dsimp [first]
  rw [abs_lt]
  norm_num at hlo hhi
  constructor <;> linarith [reference_labels.2.1.1,reference_labels.2.1.2]

lemma endpoint_source_value : T endpointUpper<(1441430267/2500000000:ℝ) := by
  have hh := FixedReference.target endpointUpper_mem ⟨le_rfl,le_rfl⟩ endpointUpper_radical
    (by norm_num [endpointUpper]) (by norm_num)
  rw [show endpointUpper=(375927951/500000000:ℝ) from rfl] at hh ⊢
  norm_num [FixedReference.valueLo,FixedReference.valueHi,
    FixedReference.firstLo,FixedReference.firstHi,FixedReference.secondLo,
    FixedReference.secondHi,Q0] at hh
  linarith

lemma endpoint_target_value : (1207117807/2000000000:ℝ)<K outerDiagonal := by
  have hd := diagonal_fine
  have hsq := pow_lt_pow_left₀ hd.1
    (by norm_num : (0:ℝ)≤89921406510940/100000000000000)
    (by norm_num : (2:ℕ)≠0)
  rw [K_diagonal]
  norm_num at hsq
  linarith

lemma endpoint_value {e : ℝ} (he : e∈Icc (2/5) endpointUpper)
    (hc : height e=outerDiagonal) : (8977831/10000000:ℝ)<cost e := by
  have hed := endpoint_domain he hc
  have hm := T_monotone hed.1 endpointUpper_mem he.2
  dsimp [cost,value]
  rw [hc]
  linarith [pi_hand_enclosure.1,endpoint_source_value,endpoint_target_value]

lemma zero_value : (9/10:ℝ)<cost 0 := by
  have hb := target_mem NegativeTwo.CapCurve.zero_domain
  have hk := K_chord hb
  dsimp [cost,value]
  rw [T_zero]
  linarith [pi_hand_enclosure.1,K_zero_bounds.1,NegativeTwo.CapCurve.zero_cage.1.1]

end SquaresInCircles.Eight.SecondWord.NegativeThree.Cap
