module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeLowerFourth

/-!
# Eight squares: whole-angle decrease of the single early-contact minorant

The fifth derivative is below six on the entire early interval.  One
quadratic Taylor bound at `1.085` makes the third derivative negative;
one square completion at `1.257` then makes the first derivative
negative everywhere.  The value at `1.3` supplies the global reserve.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic

lemma end_mem : (13/10:ℝ)∈Icc lowerAngle (13/10) := by
  constructor
  · dsimp [lowerAngle]
    linarith [pi_hand_enclosure.2]
  · rfl

lemma first_harmonic_upper {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    a1*Real.cos φ+b1*Real.sin φ<(-11/10:ℝ) := by
  have ht := lower_trig (early_lower hφ)
  have hc := end_cos_lower.trans_le
    (lower_cos_antitone (early_lower hφ) (early_lower end_mem) hφ.2)
  have ha := mul_nonneg
    (show 0≤-(11/20:ℝ)-a1 by linarith [a1_bounds.2]) ht.2.2.1
  have hb := mul_nonneg
    (show 0≤-(33/25:ℝ)-b1 by linarith [b1_bounds.2])
    (show 0≤Real.sin φ by linarith [ht.1])
  nlinarith [ht.1]

lemma harmonic_norm : a2^2+b2^2<(11/25:ℝ)^2 := by
  have ha : 0<a2 ∧ a2<153/500 := by
    constructor <;> linarith [a2_bounds.1,a2_bounds.2]
  have hb : (-63/200:ℝ)<b2 ∧ b2<0 := by
    constructor <;> linarith [b2_bounds.1,b2_bounds.2]
  have hsa := mul_pos (show 0<(153/500:ℝ)-a2 by linarith)
    (show 0<(153/500:ℝ)+a2 by linarith)
  have hsb := mul_pos (show 0<(63/200:ℝ)-b2 by linarith)
    (show 0<(63/200:ℝ)+b2 by linarith)
  nlinarith

lemma second_harmonic_upper (φ : ℝ) :
    a2*Real.sin (2*φ)+b2*Real.cos (2*φ)<(11/25:ℝ) := by
  have he : (a2*Real.sin (2*φ)+b2*Real.cos (2*φ))^2+
      (a2*Real.cos (2*φ)-b2*Real.sin (2*φ))^2=a2^2+b2^2 := by
    linear_combination (a2^2+b2^2)*(Real.sin_sq_add_cos_sq (2*φ))
  by_contra hh
  have hlo : (11/25:ℝ)≤a2*Real.sin (2*φ)+b2*Real.cos (2*φ) := by linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤11/25) hlo 2
  nlinarith [harmonic_norm,sq_nonneg (a2*Real.cos (2*φ)-b2*Real.sin (2*φ))]

lemma fifth_upper {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) : fifth φ<6 := by
  have h1 := first_harmonic_upper hφ
  have h2 := second_harmonic_upper φ
  dsimp [fifth]
  linarith

lemma third_reference_mem : (217/200:ℝ)∈Icc lowerAngle (13/10) := by
  constructor
  · dsimp [lowerAngle]
    linarith [pi_hand_enclosure.2]
  · norm_num

lemma first_reference_mem : (1257/1000:ℝ)∈Icc lowerAngle (13/10) := by
  constructor
  · dsimp [lowerAngle]
    linarith [pi_hand_enclosure.2]
  · norm_num

lemma third_upper {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    third φ<(-2/125:ℝ) := by
  have hh := curvature_tangent (f := fun t => -third t)
    (d := fun t => -fourth t) (dd := fun t => -fifth t) (κ := (-6:ℝ))
    hφ third_reference_mem
    (fun t _ => (third_hasDerivAt t).neg)
    (fun t _ => (fourth_hasDerivAt t).neg)
    (fun t ht => by linarith [fifth_upper ht])
  have hdist : |φ-217/200|≤(43/200:ℝ) := by
    rw [abs_le]
    dsimp [lowerAngle] at hφ
    constructor <;> linarith [hφ.1,hφ.2,pi_hand_enclosure.1]
  have hproduct : fourth (217/200)*(φ-217/200)≤(29/50:ℝ)*(43/200) := by
    calc
      _≤|fourth (217/200)*(φ-217/200)| := le_abs_self _
      _=|fourth (217/200)| *|φ-217/200| := abs_mul _ _
      _≤(29/50:ℝ)*(43/200) := mul_le_mul third_reference.2.le hdist
        (abs_nonneg _) (by norm_num)
  have hd := abs_le.mp hdist
  have hs := mul_nonneg (show 0≤43/200-(φ-217/200) by linarith [hd.2])
    (show 0≤43/200+(φ-217/200) by linarith [hd.1])
  nlinarith [third_reference.1]

lemma first_negative {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) : first φ<0 := by
  have hh := curvature_tangent (f := fun t => -first t)
    (d := fun t => -second t) (dd := fun t => -third t) (κ := (2/125:ℝ))
    hφ first_reference_mem
    (fun t _ => (first_hasDerivAt t).neg)
    (fun t _ => (second_hasDerivAt t).neg)
    (fun t ht => by linarith [third_upper ht])
  have hd := abs_lt.mp first_reference.2
  have hs : (second (1257/1000))^2<(1/1000:ℝ)^2 := by nlinarith
  nlinarith [first_reference.1,
    sq_nonneg ((2/125)*(φ-1257/1000)-second (1257/1000))]

lemma minorant_antitone : AntitoneOn minorant (Icc lowerAngle (13/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun t _ => (minorant_hasDerivAt t).continuousAt.continuousWithinAt)
    (fun t _ => minorant_hasDerivAt t)
    (fun t ht => (first_negative (Ioo_subset_Icc_self ht)).le)

theorem minorant_lower {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    (451/500:ℝ)< minorant φ :=
  minorant_end.trans_le (minorant_antitone hφ end_mem hφ.2)

end SquaresInCircles.Eight.SecondWord.PositiveThree.Early
