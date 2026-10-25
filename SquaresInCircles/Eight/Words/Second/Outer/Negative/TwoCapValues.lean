module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoCapReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoContactBoundary
public import SquaresInCircles.Eight.Words.Second.Outer.SourceReference

/-!
# Eight squares: strict reference reserves for the endpoint-angle minimum

The values below are obtained from the named physical circle cages.
They establish the initial concavity, the later increasing curvature,
and the final tangent-parabola reserve.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve

open CommonQuarter CorePairGeometry Arithmetic

lemma zero_labels : (21/200:ℝ)<PLabel.d2 0 ∧
    TLabel.d1 (height 0)<9173/10000 ∧ TLabel.d2 (height 0)< -113/100 := by
  have hs := SourceReference.source outer_zero_mem zero_radical (by norm_num)
  have ht := FixedReference.target (target_mem zero_domain) zero_cage.1 zero_target_radical
    (by norm_num) (by norm_num)
  norm_num [SourceReference.valueLo,SourceReference.valueHi,SourceReference.firstLo,
    SourceReference.firstHi,SourceReference.secondLo,SourceReference.secondHi,
    FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,by linarith,by linarith⟩

lemma two_labels : (289/2000:ℝ)<PLabel.d2 (1/5) ∧ PLabel.d3 (1/5)<533/2500 ∧
    (7451/10000:ℝ)<TLabel.d1 (height (1/5)) ∧ TLabel.d1 (height (1/5))<1863/2500 ∧
    (-7981/10000:ℝ)<TLabel.d2 (height (1/5)) ∧ TLabel.d2 (height (1/5))< -399/500 ∧
    (509/250:ℝ)<TLabel.d3 (height (1/5)) := by
  have hs := SourceReference.source two_mem two_radical (by norm_num)
  have ht := FixedReference.target (target_mem two_domain) two_cage.1 two_target_radical
    (by norm_num) (by norm_num)
  have hp3 := SourceReference.source_third_upper two_mem
    (ul := (185083764820148/100000000000000:ℝ)) (upper := (533/2500:ℝ))
    (by norm_num) two_radical.1 (by norm_num) (by norm_num [Q0])
  have hthree : (3/10:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hUthree := shifted_chart_reference (outer_domain hthree)
    (l := (9049/5000:ℝ)) (u := (18099/10000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have ht3 := SourceReference.target_third_lower hthree hUthree.2.le
    (lower := (509/250:ℝ)) (by norm_num) (by norm_num [Q0])
  have hm := T_third_monotone hthree (target_mem two_domain)
    (by linarith [two_cage.1.1])
  norm_num [SourceReference.valueLo,SourceReference.valueHi,SourceReference.firstLo,
    SourceReference.firstHi,SourceReference.secondLo,SourceReference.secondHi,
    FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,hp3,by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma six_labels : P (3/5)<6443/12500 ∧ (87629/100000:ℝ)<PLabel.d1 (3/5) ∧
    PLabel.d2 (3/5)<6337/25000 ∧ (6918/12500:ℝ)<T (height (3/5)) ∧
    (627189/1000000:ℝ)<TLabel.d1 (height (3/5)) ∧
    TLabel.d1 (height (3/5))<784/1250 ∧
    (18027/50000:ℝ)<TLabel.d2 (height (3/5)) := by
  have hs := SourceReference.source six_mem six_radical (by norm_num)
  have ht := FixedReference.target (target_mem six_domain) six_cage.1 six_target_radical
    (by norm_num) (by norm_num)
  norm_num [SourceReference.valueLo,SourceReference.valueHi,SourceReference.firstLo,
    SourceReference.firstHi,SourceReference.secondLo,SourceReference.secondHi,
    FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma reference_labels : P (14473/20000)<7823141206/12500000000 ∧
    PLabel.d1 (14473/20000)∈Icc (91065969/100000000) (91065971/100000000) ∧
    (326420021/500000000:ℝ)<T (height (14473/20000)) ∧
    TLabel.d1 (height (14473/20000))∈Icc (7308367/10000000) (9135459/12500000) := by
  have hs := SourceReference.source reference_mem reference_radical (by norm_num)
  have ht := FixedReference.target (target_mem reference_domain) reference_cage_fine.1
    reference_target_radical (by norm_num) (by norm_num)
  norm_num [SourceReference.valueLo,SourceReference.valueHi,SourceReference.firstLo,
    SourceReference.firstHi,SourceReference.secondLo,SourceReference.secondHi,
    FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hs ht
  exact ⟨by linarith,⟨by linarith,by linarith⟩,by linarith,⟨by linarith,by linarith⟩⟩

lemma zero_second : second 0<(-51/100:ℝ) := by
  have hk := k_bounds outer_zero_mem
  have hk0 : 0<k 0 := by linarith [hk.1]
  have hk2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8439/10000) zero_cage.2.1.le 2
  have hnegative := mul_lt_mul_of_pos_right zero_labels.2.2 (pow_pos hk0 2)
  have hpositive := mul_lt_mul zero_labels.2.1 zero_cage.2.2.le hk.2.1
    (by norm_num : (0:ℝ)≤9173/10000)
  dsimp only [second]
  norm_num at hpositive hk2
  linarith [zero_labels.1]

lemma two_second : second (1/5)<(-12/25:ℝ) := by
  have hk := k_bounds two_mem
  have hk0 : 0<k (1/5) := by linarith [hk.1]
  have hk2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4667/5000) two_cage.2.1.le 2
  have hnegative := mul_lt_mul_of_pos_right two_labels.2.2.2.2.2.1 (pow_pos hk0 2)
  have hpositive := mul_lt_mul two_labels.2.2.2.1 two_cage.2.2.2.1.le hk.2.1
    (by norm_num : (0:ℝ)≤1863/2500)
  dsimp only [second]
  norm_num at hpositive hk2
  linarith [two_labels.1]

lemma two_third : (3/5:ℝ)<third (1/5) := by
  have hk := k_bounds two_mem
  have hk0 : 0<k (1/5) := by linarith [hk.1]
  have hk3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4667/5000) two_cage.2.1.le 3
  have hlead := mul_lt_mul two_labels.2.2.2.2.2.2 hk3
    (by norm_num : (0:ℝ)<(4667/5000)^3)
    (by linarith [two_labels.2.2.2.2.2.2] : 0≤TLabel.d3 (height (1/5)))
  have hkk1 := mul_lt_mul two_cage.2.2.1 two_cage.2.2.2.1.le hk.2.1
    (by norm_num : (0:ℝ)≤1867/2000)
  have hprod := mul_pos (show 0<TLabel.d2 (height (1/5))+7981/10000 by
    linarith [two_labels.2.2.2.2.1]) (mul_pos hk0 hk.2.1)
  have hlast := mul_lt_mul two_labels.2.2.1 two_cage.2.2.2.2.le
    (by norm_num : (0:ℝ)<579/2000)
    (by linarith [two_labels.2.2.1] : 0≤TLabel.d1 (height (1/5)))
  dsimp only [third]
  norm_num at hlead hkk1 hlast
  nlinarith [two_labels.2.1]

lemma zero_value : (9/10:ℝ)<cost 0 :=
  axial_contact_lower (target_mem zero_domain) (by norm_num) rfl

lemma two_value : (9/10:ℝ)<cost (1/5) := by
  have hs := SourceReference.source two_mem two_radical (by norm_num)
  have ht := FixedReference.target (target_mem two_domain) two_cage.1 two_target_radical
    (by norm_num) (by norm_num)
  norm_num [SourceReference.valueLo,SourceReference.valueHi,SourceReference.firstLo,
    SourceReference.firstHi,SourceReference.secondLo,SourceReference.secondHi,
    FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hs ht
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1]

lemma six_value : (453/500:ℝ)<cost (3/5) := by
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1,six_labels.1,six_labels.2.2.2.1]

lemma six_first : first (3/5)<0 := by
  have hk := k_bounds six_mem
  have hh := mul_lt_mul six_labels.2.2.2.2.2.1 six_cage.2.2.1.le
    (by linarith [hk.1] : 0<k (3/5)) (by norm_num : (0:ℝ)≤784/1250)
  dsimp only [first]
  norm_num at hh
  linarith [six_labels.2.1]

lemma six_second : (13/20:ℝ)<second (3/5) := by
  have hk2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤577851/500000) six_cage.2.1.le 2
  have hlead := mul_lt_mul six_labels.2.2.2.2.2.2 hk2
    (by norm_num : (0:ℝ)<(577851/500000)^2)
    (by linarith [six_labels.2.2.2.2.2.2] : 0≤TLabel.d2 (height (3/5)))
  have hlast := mul_lt_mul six_labels.2.2.2.2.1 six_cage.2.2.2.le
    (by norm_num : (0:ℝ)<672937/1000000)
    (by linarith [six_labels.2.2.2.2.1] : 0≤TLabel.d1 (height (3/5)))
  dsimp only [second]
  norm_num at hlead hlast
  linarith [six_labels.2.2.1]

lemma reference_value : (89778507/100000000:ℝ)<cost (14473/20000) := by
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1,reference_labels.1,reference_labels.2.2.1]

lemma reference_first : |first (14473/20000)|<(1/1000000:ℝ) := by
  have ht := reference_labels.2.2.2
  have hk := reference_cage_fine.2
  have hlo := mul_le_mul ht.1 hk.1 (by norm_num : (0:ℝ)≤124605027/100000000)
    (by linarith [ht.1] : 0≤TLabel.d1 (height (14473/20000)))
  have hhi := mul_le_mul ht.2 hk.2 (by linarith [hk.1] : 0≤k (14473/20000))
    (by norm_num : (0:ℝ)≤9135459/12500000)
  rw [abs_lt]
  dsimp [first]
  norm_num at hlo hhi
  constructor <;> linarith [reference_labels.2.1.1,reference_labels.2.1.2]

end SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve
