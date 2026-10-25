module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeDiagonalContact
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyCutReferences

/-!
# Eight squares: original endpoint reserves for the positive diagonal boundaries

The close endpoint is the source diagonal at `pi/2-0.7`.  Its target
is computed by the exact circle rotation, then the literal target
label is bounded at that actual point.  The reserve is strictly
above `0.89778`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalContact

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

lemma lower_angle_mem : Lower lowerAngle := by
  constructor
  · rfl
  · dsimp [lowerAngle]
    linarith

lemma left_domain : SourceCurve.Domain parameter lowerAngle :=
  ⟨parameter_mem,lower_angle_mem⟩

lemma left_z : z parameter lowerAngle∈Icc (36562811/10^8:ℝ) (36562813/10^8) := by
  dsimp [z,parameter]
  exact ⟨by linarith [EarlyCut.left_trig.1.1,diagonal_fine.2],
    by linarith [EarlyCut.left_trig.1.2,diagonal_fine.1]⟩

lemma left_radical :
    y parameter lowerAngle∈Icc (194471489/10^8:ℝ) (194471493/10^8) := by
  have hh := y_data left_domain
  have hz := left_z
  have hz0 : 0≤z parameter lowerAngle := by linarith [hz.1]
  have hzl2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤36562811/10^8) hz.1 2
  have hzh2 := pow_le_pow_left₀ hz0 hz.2 2
  norm_num [Q0] at hh
  constructor <;> nlinarith

lemma left_rotation :
    u parameter lowerAngle∈Icc (15324675/10^7:ℝ) (15324676/10^7) ∧
      w parameter lowerAngle∈Icc (12518558/10^7:ℝ) (12518560/10^7) := by
  have hz := left_z
  have hy := left_radical
  have hs := EarlyCut.left_trig.1
  have hc := EarlyCut.left_trig.2
  have hz0 : 0≤z parameter lowerAngle := by linarith [hz.1]
  have hy0 : 0≤y parameter lowerAngle := by linarith [hy.1]
  have hs0 : 0≤Real.sin lowerAngle := by linarith [hs.1]
  have hc0 : 0≤Real.cos lowerAngle := by linarith [hc.1]
  have hzslo := mul_le_mul hz.1 hs.1 (by norm_num) hz0
  have hzshi := mul_le_mul hz.2 hs.2 hs0 (by norm_num)
  have hyclo := mul_le_mul hy.1 hc.1 (by norm_num) hy0
  have hychi := mul_le_mul hy.2 hc.2 hc0 (by norm_num)
  have hyslo := mul_le_mul hy.1 hs.1 (by norm_num) hy0
  have hyshi := mul_le_mul hy.2 hs.2 hs0 (by norm_num)
  have hzclo := mul_le_mul hz.1 hc.1 (by norm_num) hz0
  have hzchi := mul_le_mul hz.2 hc.2 hc0 (by norm_num)
  dsimp [u,w]
  exact ⟨⟨by norm_num at hzslo hyclo; linarith,
    by norm_num at hzshi hychi; linarith⟩,
    ⟨by norm_num at hyslo hzchi; linarith,
    by norm_num at hyshi hzclo; linarith⟩⟩

lemma left_target : target parameter lowerAngle∈Icc (3/4:ℝ) outerDiagonal := by
  have hw := left_rotation.2
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2,fine_outer_endpoint_bounds.2]

lemma left_target_mem : target parameter lowerAngle∈Icc 0 outerDiagonal :=
  ⟨by linarith [left_target.1],left_target.2⟩

lemma diagonal_V_lower : (1620101/2500000:ℝ)<V outerDiagonal := by
  have hd := diagonal_fine
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤89921406510940/100000000000000) hd.1.le 2
  rw [V_diagonal]
  nlinarith

lemma left_value :
    (44889/50000:ℝ)<value outerDiagonal (target parameter lowerAngle) lowerAngle := by
  have hw := left_rotation.2
  have hB : target parameter lowerAngle∈Icc
      (7518558/10^7:ℝ) (7518560/10^7) := by
    dsimp [target]
    constructor <;> linarith [hw.1,hw.2]
  have hU : U (target parameter lowerAngle)∈Icc
      (15324675/10^7:ℝ) (15324676/10^7) := by
    rw [target_U left_domain left_target_mem]
    exact left_rotation.1
  have hL := LReference.target left_target_mem hB hU (by norm_num) (by norm_num)
  have hLhi := hL.2.1
  norm_num [LReference.valueHi] at hLhi
  have hA : lowerAngle=Real.pi/2-7/10 := rfl
  dsimp only [value]
  linarith [diagonal_V_lower,pi_hand_enclosure.1]

lemma upper_join_trig : Real.sin (203/200)<(17/20:ℝ) ∧
    (527/1000:ℝ)<Real.cos (203/200) := by
  have ht := PointProducts.trig (show (0:ℝ)≤203/200 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  exact ⟨by linarith [ht.1.2],by linarith [ht.2.1]⟩

lemma lower_join_sine : (106/125:ℝ)<Real.sin (507/500) := by
  have ht := PointProducts.trig (show (0:ℝ)≤507/500 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  linarith [ht.1.1]

lemma target_three_quarters_mem : (3/4:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma target_three_quarters_curvature : (8/5:ℝ)<LLabel.d2 (3/4) := by
  have hU := shifted_chart_reference (outer_domain target_three_quarters_mem)
    (l := (76699/50000:ℝ)) (u := (767/500:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0,W]) (by norm_num [Q0,W])
  have hL := LReference.target target_three_quarters_mem
    (show (3/4:ℝ)∈Icc (3/4) (3/4) from ⟨le_rfl,le_rfl⟩)
    ⟨hU.1.le,hU.2.le⟩ (by norm_num) (by norm_num)
  have hlo := hL.2.2.2.2.1
  norm_num [LReference.secondLo,Q0] at hlo
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.DiagonalContact
