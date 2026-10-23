module

public import SquaresInCircles.Eight.TableFree.SecondMixedLPrimaryZeroCost
public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeThreeLabels

/-!
# The two remaining aligned mixed costs in height coordinates

The positive-core cost is concave between the outer diagonal and height
1.5. For the negative-core cost, a convex derivative settles the lower
height interval; one strong-convexity reference at height 1.64 settles
the entire remaining interval. Both estimates use the actual L label.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.EdgeThreeAligned
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

def threshold : ℝ := 17953/20000
def gp : ℝ := 1303/1250
def ep : ℝ := 1449/100000
def gn : ℝ := 98439/100000
def zn : ℝ := 2667/50000
abbrev en := LPrimaryZero.e

def positiveHeight (u : ℝ) : ℝ := Real.pi/2-ep+gp*(3/2-u)+LHeight.eval u
def positiveHeightD (u : ℝ) : ℝ := LHeight.d1 u-gp
def negativeHeight (u : ℝ) : ℝ :=
  Real.pi/2-en-gn*(u-3/2)+zn*(u-3/2)^2+LHeight.eval u
def negativeHeightD (u : ℝ) : ℝ := LHeight.d1 u-gn+2*zn*(u-3/2)
def negativeHeightDD (u : ℝ) : ℝ := LHeight.d2 u+2*zn

lemma positiveHeight_hasDerivAt {u : ℝ} (hu : u∈LHeightBounds.heights) :
    HasDerivAt positiveHeight (positiveHeightD u) u := by
  convert ((((hasDerivAt_id u).const_sub (3/2)).const_mul gp).const_add
    (Real.pi/2-ep)).add (LHeight.eval_hasDerivAt (LHeightBounds.domain hu)) using 1 <;>
    dsimp [positiveHeight,positiveHeightD] <;> ring

lemma positiveHeightD_hasDerivAt {u : ℝ} (hu : u∈LHeightBounds.heights) :
    HasDerivAt positiveHeightD (LHeight.d2 u) u :=
  (LHeight.d1_hasDerivAt (LHeightBounds.domain hu)).sub_const gp

lemma negativeHeight_hasDerivAt {u : ℝ} (hu : u∈LHeightBounds.heights) :
    HasDerivAt negativeHeight (negativeHeightD u) u := by
  convert (((((hasDerivAt_id u).sub_const (3/2)).const_mul gn).const_sub
    (Real.pi/2-en)).add ((((hasDerivAt_id u).sub_const (3/2)).pow 2).const_mul zn)).add
      (LHeight.eval_hasDerivAt (LHeightBounds.domain hu)) using 1 <;>
    dsimp [negativeHeight,negativeHeightD] <;> ring

lemma negativeHeightD_hasDerivAt {u : ℝ} (hu : u∈LHeightBounds.heights) :
    HasDerivAt negativeHeightD (negativeHeightDD u) u := by
  convert ((LHeight.d1_hasDerivAt (LHeightBounds.domain hu)).sub_const gn).add
    (((hasDerivAt_id u).sub_const (3/2)).const_mul (2*zn)) using 1 <;>
    dsimp [negativeHeightD,negativeHeightDD] <;> ring

lemma negativeHeightDD_hasDerivAt {u : ℝ} (hu : u∈LHeightBounds.heights) :
    HasDerivAt negativeHeightDD (LHeight.d3 u) u :=
  (LHeight.d2_hasDerivAt (LHeightBounds.domain hu)).add_const (2*zn)

lemma positive_zero : (361/400:ℝ)<positiveHeight (3/2) := by
  norm_num [positiveHeight,gp,ep]
  linarith [LPrimaryZero.aligned_height_value,pi_hand_enclosure.1]

lemma negative_zero : (4489/5000:ℝ)<negativeHeight (3/2) := by
  simpa [negativeHeight,LPrimaryZero.K,en,LPrimaryZero.U,PrimaryZero.U,PrimaryZero.m]
    using LPrimaryZero.aligned_cost

lemma diagonal_state : OuterState outerDiagonal outerDiagonal := by
  have hd : outerDiagonal∈Icc (0:ℝ) outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  simpa [ShortOuterOne.SameContact.arc_diagonal] using ShortOuterOne.SameContact.arc_state hd

lemma positive_diagonal : (89779/100000:ℝ)<positiveHeight (outerDiagonal+1/2) := by
  have hM := LHeight_actual diagonal_state
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤449607/500000) hd.1.le 2
  dsimp [positiveHeight]
  rw [hM]
  norm_num [gp,ep,L,RoleLabel.outer,RoleLabel.eval,LLabel,ShortOuterOne.SameContact.arc_diagonal]
  nlinarith [pi_hand_enclosure.1]

theorem positive_height_lower {u : ℝ} (hu : u∈Icc (outerDiagonal+1/2) (3/2)) :
    (89779/100000:ℝ)<positiveHeight u := by
  have hdom : ∀z∈Icc (outerDiagonal+1/2) (3/2),z∈LHeightBounds.heights := by
    intro z hz
    exact ⟨by linarith [hz.1,outer_endpoint_bounds.2.2.1],by linarith [hz.2]⟩
  have hc : ConcaveOn ℝ (Icc (outerDiagonal+1/2) (3/2)) positiveHeight :=
    concave_of_deriv2 (fun z hz => positiveHeight_hasDerivAt (hdom z hz))
      (fun z hz => positiveHeightD_hasDerivAt (hdom z hz))
      (fun z hz => (LHeightBounds.second_negative_below (hdom z hz) (by linarith [hz.2])).le)
  exact concave_gt_of_endpoints hc hu positive_diagonal (by linarith [positive_zero])

lemma negative_join_value : (89793/100000:ℝ)<negativeHeight (81/50) := by
  have hr := root_cage (u := (81/50:ℝ))
    (l := (1136309816907/1000000000000:ℝ))
    (r := (284077454227/250000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  norm_num [negativeHeight,en,LPrimaryZero.e,gn,zn,LHeight,HeightLabel.eval,Q0]
  nlinarith [hr.2,pi_hand_enclosure.1]

lemma negative_join_derivatives :
    negativeHeightD (81/50)<0 ∧ (33/100:ℝ)<negativeHeightDD (81/50) := by
  have hu : (81/50:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
  have hr := root_cage (u := (81/50:ℝ))
    (l := (1136309816907/1000000000000:ℝ))
    (r := (284077454227/250000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  have hp := root_pos (LHeightBounds.domain hu)
  have h1 := LHeight.d1_mul (LHeightBounds.domain hu)
  have h2 := LHeight.d2_mul (LHeightBounds.domain hu)
  have h3l := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1136309816907/1000000000000) hr.1.le 3
  have h3u := pow_le_pow_left₀ hp.le hr.2.le 3
  norm_num [LHeight,Q0] at h1 h2
  constructor
  · have hh : LHeight.d1 (81/50)<(24/25:ℝ) := by
      apply (mul_lt_mul_right hp).mp
      nlinarith [hr.1,hr.2]
    dsimp [negativeHeightD,gn,zn]
    linarith
  · have hh : (9/40:ℝ)<LHeight.d2 (81/50) := by
      apply (mul_lt_mul_right (pow_pos hp 3)).mp
      nlinarith
    dsimp [negativeHeightDD,zn]
    linarith

lemma negative_reference :
    (89779/100000:ℝ)<negativeHeight (41/25) ∧
    |negativeHeightD (41/25)|<1/625 := by
  have hu : (41/25:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
  have hr := root_cage (u := (41/25:ℝ))
    (l := (1107248842853/1000000000000:ℝ))
    (r := (553624421427/500000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  have hp := root_pos (LHeightBounds.domain hu)
  have h1 := LHeight.d1_mul (LHeightBounds.domain hu)
  norm_num [LHeight,Q0] at h1
  constructor
  · norm_num [negativeHeight,en,LPrimaryZero.e,gn,zn,LHeight,HeightLabel.eval,Q0]
    nlinarith [hr.2,pi_hand_enclosure.1]
  · have hl : (48393/50000:ℝ)<LHeight.d1 (41/25) := by
      apply (mul_lt_mul_right hp).mp
      nlinarith [hr.1,hr.2]
    have hh : LHeight.d1 (41/25)<(24197/25000:ℝ) := by
      apply (mul_lt_mul_right hp).mp
      nlinarith [hr.1,hr.2]
    rw [abs_lt]
    dsimp [negativeHeightD,gn,zn]
    constructor <;> linarith

lemma negative_lower_piece {u : ℝ} (hu : u∈Icc (3/2) (81/50)) :
    (4489/5000:ℝ)<negativeHeight u := by
  have hdom : ∀z∈Icc (3/2) (81/50),z∈LHeightBounds.heights :=
    fun z hz => ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hc : ConcaveOn ℝ (Icc (3/2) (81/50)) (fun z => -negativeHeightD z) :=
    concave_of_deriv2 (fun z hz => (negativeHeightD_hasDerivAt (hdom z hz)).neg)
      (fun z hz => (negativeHeightDD_hasDerivAt (hdom z hz)).neg)
      (fun z hz => neg_nonpos.mpr (LHeightBounds.third_positive (hdom z hz)).le)
  have hm := Asymmetric.endpoint_minimum_of_convex_derivative hu
    (fun z hz => negativeHeight_hasDerivAt (hdom z hz)) hc negative_join_derivatives.1.le
  exact (lt_min negative_zero (by linarith [negative_join_value])).trans_le hm

lemma negative_upper_piece {u : ℝ} (hu : u∈Icc (81/50) (383/200)) :
    (44889/50000:ℝ)<negativeHeight u := by
  have hdom : ∀z∈Icc (81/50) (383/200),z∈LHeightBounds.heights :=
    fun z hz => ⟨by linarith [hz.1],hz.2⟩
  have hc : ∀z∈Icc (81/50) (383/200),(33/100:ℝ)≤negativeHeightDD z := by
    intro z hz
    have hm := LHeightBounds.second_monotone
      (show (81/50:ℝ)∈LHeightBounds.heights by norm_num [LHeightBounds.heights])
      (hdom z hz) hz.1
    dsimp [negativeHeightDD] at *
    linarith [negative_join_derivatives.2]
  have ht := curvature_tangent (f := negativeHeight) (d := negativeHeightD) (dd := negativeHeightDD)
    (κ := (33/100:ℝ)) hu (show (41/25:ℝ)∈Icc (81/50) (383/200) by norm_num)
    (fun z hz => negativeHeight_hasDerivAt (hdom z hz))
    (fun z hz => negativeHeightD_hasDerivAt (hdom z hz)) hc
  have hd := abs_lt.mp negative_reference.2
  have hp := mul_pos (show 0<negativeHeightD (41/25)+1/625 by linarith [hd.1])
    (show 0<(1/625:ℝ)-negativeHeightD (41/25) by linarith [hd.2])
  have hs := sq_nonneg ((33/100)*(u-41/25)+negativeHeightD (41/25))
  nlinarith [negative_reference.1]

theorem negative_height_lower {u : ℝ} (hu : u∈Icc (3/2) (383/200)) :
    (44889/50000:ℝ)<negativeHeight u := by
  by_cases he : u≤81/50
  · linarith [negative_lower_piece (show u∈Icc (3/2) (81/50) from ⟨hu.1,he⟩)]
  · exact negative_upper_piece ⟨by linarith,hu.2⟩

end SquaresInCircles.Eight.TableFree.SecondWord.EdgeThreeAligned
