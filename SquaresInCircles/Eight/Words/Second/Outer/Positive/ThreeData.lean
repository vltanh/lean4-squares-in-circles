module

public import SquaresInCircles.Eight.Words.Second.Outer.LBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoData
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds

/-!
# Eight squares: original positive edge-three cost and its four actual weak axes

The role-three positive source label is `V` and its positive target
label is `L`.  Every projection below is an algebraic rearrangement of
the same original separator on the original common circle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def value (b B φ : ℝ) : ℝ := φ+V b-L B
def lowerAngle : ℝ := Real.pi/2-7/10
def Lower (φ : ℝ) : Prop := φ∈Icc lowerAngle (Real.pi/2)

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 3 .outer .outer true true a b A B φ=value b B φ := by
  unfold value
  rw [show V b=VLabel.eval a b from VLabel.outer_actual hs,
    show L B=LLabel.eval A B from LLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,QuarterWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,VLabel,LLabel,RoleLabel.eval]

lemma lower_deviation {φ : ℝ} (hφ : Lower φ) :
    Real.pi/2-φ∈Icc 0 (7/10) := by
  dsimp [Lower,lowerAngle] at hφ
  constructor <;> linarith [hφ.1,hφ.2]

lemma lower_trig {φ : ℝ} (hφ : Lower φ) :
    (19121/25000:ℝ)<Real.sin φ ∧ Real.sin φ≤1 ∧
      0≤Real.cos φ ∧ Real.cos φ<16106/25000 ∧
      1≤Real.sin φ+Real.cos φ := by
  have hh := positive_trig (lower_deviation hφ)
  simp only [Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,sub_zero,zero_add] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,by linarith [hh.2.2.2.2.2]⟩

lemma lower_width {φ : ℝ} (hφ : Lower φ) :
    pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
  have hh := NegativeTwo.lower_width (lower_deviation hφ)
  have he : Real.pi/2-(Real.pi/2-φ)=φ := by ring
  rw [he] at hh
  simpa only [Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,sub_zero,zero_add] using hh

lemma lower_source_secondary_cut {a b A B φ : ℝ} (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ := by
  norm_num [Eight.forwardMargin,lower_width hφ] at hm
  linarith

lemma lower_target_secondary_cut {a b A B φ : ℝ} (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 1 φ) :
    B≤a*Real.sin φ+b*Real.cos φ-(1+Real.sin φ+Real.cos φ)/2 := by
  norm_num [Eight.forwardMargin,lower_width hφ] at hm
  linarith

lemma lower_source_primary_cut {a b A B φ : ℝ} (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 φ) :
    A*Real.cos φ+B*Real.sin φ≤a-(1+Real.sin φ+Real.cos φ)/2 := by
  norm_num [Eight.forwardMargin,lower_width hφ] at hm
  linarith

lemma upper_source_secondary_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 (Real.pi/2+x)) :
    1/2-(A-1/2)*Real.cos x-(B-1/2)*Real.sin x≤b := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  linarith

lemma upper_target_primary_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B 1 1 (Real.pi/2+x)) :
    1/2≤A+(a-1/2)*Real.sin x+(b-1/2)*Real.cos x := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  linarith

lemma upper_target_secondary_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 1 (Real.pi/2+x)) :
    B≤(a-1/2)*Real.cos x-(b+1/2)*Real.sin x-1/2 := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  linarith

lemma upper_source_primary_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 (Real.pi/2+x)) :
    (B+1/2)*Real.cos x≤a-1/2+(A-1/2)*Real.sin x := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  linarith

lemma late_angle {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : (419/250:ℝ)≤φ) : (8979/10000:ℝ)<value b B φ := by
  have hv := V_lower (NegativeTwo.source_mem hs)
  have hL := L_upper (NegativeTwo.source_mem ht)
  dsimp [value]
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree
