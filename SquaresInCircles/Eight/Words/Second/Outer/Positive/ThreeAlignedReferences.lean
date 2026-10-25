module

public import SquaresInCircles.Eight.Words.Second.Outer.LReference
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeData

/-!
# Eight squares: the two original aligned endpoints for positive edge three

The zero-source target has primary coordinate one.  The other endpoint
is the target diagonal with source coordinate `1-d`.  Their actual
circle radicals are enclosed by integer-square comparisons; both
endpoint costs strictly exceed the final threshold.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def zeroTarget : ℝ := arc 1
def alignedSource : ℝ := 1-outerDiagonal

lemma zeroTarget_state : OuterState 1 zeroTarget :=
  ShortOuterOne.SameContact.primary_state primary_one_mem

lemma zeroTarget_mem : zeroTarget∈Icc 0 outerDiagonal :=
  NegativeTwo.source_mem zeroTarget_state

lemma zeroTarget_arc : arc zeroTarget=1 :=
  (ShortOuterOne.SameContact.actual_arc zeroTarget_state).1

lemma zeroTarget_U : U zeroTarget=(3/2:ℝ) := by
  dsimp [U]
  rw [zeroTarget_arc]
  norm_num

lemma zeroTarget_bounds :
    (79058126439213/100000000000000:ℝ)<zeroTarget ∧
      zeroTarget<79058126439214/100000000000000 := by
  have hc := zeroTarget_state.2.2
  have hb := zeroTarget_mem.1
  norm_num [Q0] at hc
  constructor <;> nlinarith

lemma zeroTarget_labels :
    L zeroTarget<(65379/100000:ℝ) ∧ LLabel.d1 zeroTarget<89/100 ∧
      (2:ℝ)<LLabel.d2 zeroTarget := by
  have hh := LReference.target zeroTarget_mem
    ⟨zeroTarget_bounds.1.le,zeroTarget_bounds.2.le⟩
    (show U zeroTarget∈Icc (3/2) (3/2) by rw [zeroTarget_U]; exact ⟨le_rfl,le_rfl⟩)
    (by norm_num) (by norm_num)
  norm_num [LReference.valueLo,LReference.valueHi,LReference.firstLo,
    LReference.firstHi,LReference.secondLo,LReference.secondHi,Q0] at hh
  exact ⟨by linarith,by linarith,by linarith⟩

lemma zeroTarget_ratio : (43/50:ℝ)<ratio zeroTarget := by
  change (43/50:ℝ)<W zeroTarget/U zeroTarget
  rw [zeroTarget_U]
  dsimp [W]
  linarith [zeroTarget_bounds.1]

lemma zero_aligned_value : (361/400:ℝ)<value 0 zeroTarget (Real.pi/2) := by
  dsimp [value]
  linarith [pi_hand_enclosure.1,V_zero_bounds.1,zeroTarget_labels.1]

lemma alignedSource_mem : alignedSource∈Icc 0 outerDiagonal := by
  dsimp [alignedSource]
  constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]

lemma alignedSource_bounds :
    (10078593489059/100000000000000:ℝ)<alignedSource ∧
      alignedSource<10078593489060/100000000000000 := by
  dsimp [alignedSource]
  constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]

lemma alignedSource_U_bounds :
    (188537960645532/100000000000000:ℝ)<U alignedSource ∧
      U alignedSource<188537960645533/100000000000000 := by
  have hc := UW_circle (outer_domain alignedSource_mem)
  have hp := U_positive (outer_domain alignedSource_mem)
  have hb := alignedSource_bounds
  have hslo : (60078593489059/100000000000000:ℝ)^2<(W alignedSource)^2 := by
    dsimp [W]
    nlinarith [hb.1]
  have hshi : (W alignedSource)^2<(60078593489060/100000000000000:ℝ)^2 := by
    dsimp [W]
    nlinarith [hb.1,hb.2]
  norm_num [Q0] at hc
  constructor <;> nlinarith

lemma alignedSource_value : (452799/5000000:ℝ)<V alignedSource := by
  have hb := alignedSource_bounds
  have hu := alignedSource_U_bounds
  have hp := mul_le_mul
    (show (138537960645532/100000000000000:ℝ)≤U alignedSource-1/2 by linarith)
    hb.1.le (by norm_num : (0:ℝ)≤10078593489059/100000000000000)
    (by linarith : 0≤U alignedSource-1/2)
  have he : V alignedSource= -(41/4000)*(U alignedSource-1/2)+
      (16031/100000)*alignedSource+
        (63457/100000)*(U alignedSource-1/2)*alignedSource := by
    dsimp [V,RoleLabel.outer,RoleLabel.eval,VLabel,U]
    ring
  rw [he]
  nlinarith [hb.1,hu.2]

lemma diagonal_aligned_value :
    (44889/50000:ℝ)<value alignedSource outerDiagonal (Real.pi/2) := by
  dsimp [value]
  linarith [pi_hand_enclosure.1,alignedSource_value,L_diagonal_upper]

end SquaresInCircles.Eight.SecondWord.PositiveThree
