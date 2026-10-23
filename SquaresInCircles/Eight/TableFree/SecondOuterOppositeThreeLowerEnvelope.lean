module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerEnvelopeBounds

/-!
# The three uniform envelope derivative estimates

The positive relation `D > 3 S / 2` preserves the stationary equation's
dependence and proves the third derivative sign on the full target
interval.  No source partition enters the argument.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerEnvelope
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)

lemma envelope_first_negative {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : g₁ B<0 := by
  have hh : 0<h B := by linarith [(product_bounds hB).1]
  have hs := S_positive (mem_outer hB)
  dsimp [g₁]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) (by positivity)

lemma envelope_second_upper {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    (S B)^2*g₂ B<(63/200:ℝ) := by
  have hs := S_positive (mem_outer hB)
  have hd := D_positive (mem_short hB)
  have hlarge := D_large hB
  have hh := (product_bounds hB).2
  have hj := (product_first_bounds hB).1
  have he : 4*D B*((S B)^2*g₂ B)=2*D B*h B-h₁ B*S B := by
    dsimp [g₂]
    field_simp [hs.ne',hd.ne']
    ring
  have hp := mul_lt_mul_of_pos_left hh (show 0<2*D B by positivity)
  have hq := mul_lt_mul_of_pos_right hj hs
  have hpay : 4*D B*((S B)^2*g₂ B)<4*D B*(63/200) := by
    nlinarith
  exact (mul_lt_mul_left (show 0<4*D B by positivity)).mp hpay

lemma envelope_third_negative {B : ℝ} (hB : B∈Icc (3/100) (3/20)) : g₃ B<0 := by
  have hs := S_positive (mem_outer hB)
  have hd := D_positive (mem_short hB)
  have hlarge := D_large hB
  have hdlo : (159/100:ℝ)<D B := by linarith [(S_bounds hB).1]
  have hv : S B/D B∈Icc (0:ℝ) (2/3) := by
    constructor
    · exact (div_pos hs hd).le
    · apply (div_le_iff₀ hd).2
      linarith
  have hi : 1/D B∈Icc (0:ℝ) (100/159) := by
    constructor
    · positivity
    · apply (div_le_iff₀ hd).2
      linarith
  let V : Interval (S B/D B) := Interval.of_bounds hv
  let I : Interval (1/D B) := Interval.of_bounds hi
  let H : Interval (h B) := Interval.of_bounds ⟨(product_bounds hB).1.le,(product_bounds hB).2.le⟩
  let J : Interval (h₁ B) := Interval.of_bounds
    ⟨(product_first_bounds hB).1.le,(product_first_bounds hB).2.le⟩
  let K : Interval (h₂ B) := Interval.of_bounds
    ⟨(product_second_bounds hB).1.le,(product_second_bounds hB).2.le⟩
  let E : Interval (D₁ B) := Interval.of_bounds ⟨(D_first_bounds hB).1.le,(D_first_bounds hB).2.le⟩
  let Z₀ := ((((Interval.point (-1/8)).mul K).mul V.square).
    add (((Interval.point (1/2)).mul J).mul V)).
      add (((((Interval.point (1/8)).mul J).mul E).mul I).mul V.square)
  let Z := Z₀.sub H
  have hz : Z.hi<0 := by
    norm_num [Z,Z₀,V,I,H,J,K,E,Interval.point,Interval.of_bounds,Interval.mul,
      Interval.square,Interval.add,Interval.sub]
  have he : (S B)^3*g₃ B=
      (-1/8)*h₂ B*(S B/D B)^2+(1/2)*h₁ B*(S B/D B)+
        (1/8)*h₁ B*D₁ B*(1/D B)*(S B/D B)^2-h B := by
    dsimp [g₃]
    field_simp [hs.ne',hd.ne']
    ring
  have hnegative : (S B)^3*g₃ B<0 := by rw [he]; exact Z.mem.2.trans_lt hz
  by_contra hn
  have hp := mul_nonneg (pow_nonneg hs.le 3) (le_of_not_gt hn)
  linarith

theorem derivative_bounds {B : ℝ} (hB : B∈Icc (3/100) (3/20)) :
    g₁ B<0 ∧ (S B)^2*g₂ B<(63/200:ℝ) ∧ g₃ B<0 :=
  ⟨envelope_first_negative hB,envelope_second_upper hB,envelope_third_negative hB⟩

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerEnvelope
