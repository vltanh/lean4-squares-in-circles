module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.ReferenceTrig

/-!
# Eight squares: A whole-angle proof for the fourth lower original owner

The actual weak projection forces an angle above `1.2`.  Its necessary
target cap gives a single decreasing scalar on the entire remaining
interval, whose quarter-turn value has a strict reserve above `1.02`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig

lemma lower_cos_antitone : AntitoneOn Real.cos (Icc lowerAngle (Real.pi/2)) :=
  antiOn_of_hasDeriv_nonpos
    (fun t _ => (Real.hasDerivAt_cos t).continuousAt.continuousWithinAt)
    (fun t _ => Real.hasDerivAt_cos t)
    (fun t ht => by linarith [(lower_trig (Ioo_subset_Icc_self ht)).1])

lemma lower_sin_monotone : MonotoneOn Real.sin (Icc lowerAngle (Real.pi/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun t _ => (Real.hasDerivAt_sin t).continuousAt.continuousWithinAt)
    (fun t _ => Real.hasDerivAt_sin t)
    (fun t ht => (lower_trig (Ioo_subset_Icc_self ht)).2.2.1)

lemma six_fifths_lower : Lower (6/5) := by
  refine ⟨?_,?_⟩
  · dsimp [lowerAngle]
    linarith [pi_hand_enclosure.2]
  · linarith [pi_hand_enclosure.1]

lemma six_fifths_trig :
    (233/250:ℝ)<Real.sin (6/5) ∧ (7247/20000:ℝ)<Real.cos (6/5) ∧
      Real.cos (6/5)<363/1000 := by
  have hs := sin11_le_sin (show (0:ℝ)≤6/5 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤6/5 by norm_num)
  have hcu := cos_le_cos12 (show (0:ℝ)≤6/5 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hc hcu
  exact ⟨by linarith,by linarith,by linarith⟩

def fourthNecessary (φ : ℝ) : ℝ :=
  outerAxial-1/2-(1/2)*Real.sin φ-(outerDiagonal+1/2)*Real.cos φ

lemma fourthNecessary_hasDerivAt (φ : ℝ) :
    HasDerivAt fourthNecessary
      ((outerDiagonal+1/2)*Real.sin φ-(1/2)*Real.cos φ) φ := by
  convert (((Real.hasDerivAt_sin φ).const_mul (1/2)).const_sub
    (outerAxial-1/2)).sub ((Real.hasDerivAt_cos φ).const_mul (outerDiagonal+1/2))
    using 1
  · funext t
    simp only [fourthNecessary,Pi.sub_apply]
  · ring

lemma fourthNecessary_monotone : MonotoneOn fourthNecessary
    (Icc lowerAngle (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun t _ => (fourthNecessary_hasDerivAt t).continuousAt.continuousWithinAt)
    (fun t _ => fourthNecessary_hasDerivAt t)
  intro t ht
  have hh := lower_trig (Ioo_subset_Icc_self ht)
  have hp := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
    hh.1.le (by norm_num : (0:ℝ)≤19121/25000)
    (by linarith [fine_outer_endpoint_bounds.2] : 0≤outerDiagonal+1/2)
  norm_num at hp
  linarith [hh.2.2.2.1]

lemma fourthNecessary_negative : fourthNecessary (6/5)<0 := by
  have ht := six_fifths_trig
  have hp := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
    ht.2.1.le (by norm_num : (0:ℝ)≤7247/20000)
    (by linarith [fine_outer_endpoint_bounds.2] : 0≤outerDiagonal+1/2)
  dsimp [fourthNecessary]
  nlinarith [ht.1,ShortOuterZero.fine_axial_bounds.2]

lemma fourth_angle_lower {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 φ) : (6/5:ℝ)<φ := by
  have hcut := lower_source_primary_cut hφ hm
  have htr := lower_trig hφ
  have hA := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem ht).1 htr.2.2.1
  have hB := mul_nonneg ht.1 (by linarith [htr.1] : 0≤Real.sin φ)
  have hn : 0≤fourthNecessary φ := by
    dsimp [fourthNecessary]
    linarith [(NegativeTwo.primary_mem hs).2]
  by_contra hh
  have hle : φ≤6/5 := by linarith
  have hd := fourthNecessary_monotone hφ six_fifths_lower hle
  linarith [fourthNecessary_negative]

def fourthCap (φ : ℝ) : ℝ :=
  ((outerAxial-1/2)-(outerDiagonal+1/2)*Real.cos φ)/Real.sin φ-1/2
def fourthCapFirst (φ : ℝ) : ℝ :=
  ((outerDiagonal+1/2)-(outerAxial-1/2)*Real.cos φ)/(Real.sin φ)^2
def fourthScalar (φ : ℝ) : ℝ := φ+V 0-793/20000-(147/125)*fourthCap φ

lemma fourthCap_hasDerivAt {φ : ℝ} (hφ : Lower φ) :
    HasDerivAt fourthCap (fourthCapFirst φ) φ := by
  have hp : Real.sin φ≠0 := by linarith [(lower_trig hφ).1]
  have hd := ((((Real.hasDerivAt_cos φ).const_mul (outerDiagonal+1/2)).const_sub
    (outerAxial-1/2)).div (Real.hasDerivAt_sin φ) hp).sub_const (1/2)
  convert hd using 1
  · rfl
  · dsimp only [fourthCapFirst]
    congr 1
    linear_combination -(outerDiagonal+1/2)*(Real.sin_sq_add_cos_sq φ)

lemma fourth_target_cap {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 φ) : B≤fourthCap φ := by
  have hcut := lower_source_primary_cut hφ hm
  have htr := lower_trig hφ
  have hp : 0<Real.sin φ := by linarith [htr.1]
  have hA := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem ht).1 htr.2.2.1
  have hline : (B+1/2)*Real.sin φ≤
      (outerAxial-1/2)-(outerDiagonal+1/2)*Real.cos φ := by
    linarith [(NegativeTwo.primary_mem hs).2]
  have hh := (le_div_iff₀ hp).2 hline
  dsimp [fourthCap]
  linarith

lemma fourth_late_lower {φ : ℝ} (hφ : φ∈Icc (6/5) (Real.pi/2)) : Lower φ :=
  ⟨six_fifths_lower.1.trans hφ.1,hφ.2⟩

lemma fourthCapFirst_lower {φ : ℝ} (hφ : φ∈Icc (6/5) (Real.pi/2)) :
    1<fourthCapFirst φ := by
  have hlo := fourth_late_lower hφ
  have ht := lower_trig hlo
  have hc := (lower_cos_antitone six_fifths_lower hlo hφ.1).trans_lt six_fifths_trig.2.2
  have ha : outerAxial-1/2<(183/200:ℝ) := by linarith [outer_endpoint_bounds.2.1]
  have hprod := mul_le_mul ha.le hc.le ht.2.2.1 (by norm_num : (0:ℝ)≤183/200)
  have hs : 0<Real.sin φ := by linarith [ht.1]
  have hsq : (Real.sin φ)^2≤1 := by nlinarith [ht.2.1]
  dsimp [fourthCapFirst]
  apply (lt_div_iff₀ (sq_pos_of_pos hs)).2
  nlinarith [fine_outer_endpoint_bounds.2]

lemma fourthScalar_antitone : AntitoneOn fourthScalar (Icc (6/5) (Real.pi/2)) := by
  have hd {φ : ℝ} (hφ : φ∈Icc (6/5) (Real.pi/2)) :
      HasDerivAt fourthScalar (1-(147/125)*fourthCapFirst φ) φ := by
    convert (((hasDerivAt_id' φ).add_const (V 0)).sub_const (793/20000)).sub
      ((fourthCap_hasDerivAt (fourth_late_lower hφ)).const_mul (147/125)) using 1
    funext t
    simp only [fourthScalar,Pi.sub_apply]
  exact antiOn_of_hasDeriv_nonpos
    (fun _ ht => (hd ht).continuousAt.continuousWithinAt)
    (fun _ ht => hd (Ioo_subset_Icc_self ht))
    (fun _ ht => by linarith [fourthCapFirst_lower (Ioo_subset_Icc_self ht)])

lemma fourthScalar_quarter : (51/50:ℝ)<fourthScalar (Real.pi/2) := by
  simp only [fourthScalar,fourthCap,Real.cos_pi_div_two,Real.sin_pi_div_two,
    mul_zero,sub_zero,div_one]
  linarith [pi_hand_enclosure.1,V_zero_bounds.1,outer_endpoint_bounds.2.1]

theorem original_lower_source_primary {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 3 a b A B 1 1 φ) :
    (51/50:ℝ)<value b B φ := by
  have hangle := fourth_angle_lower hs ht hφ hm
  have hcap := fourth_target_cap hs ht hφ hm
  have hL := L_axial_line (NegativeTwo.source_mem ht)
  have hV := V_monotone outer_zero_mem (NegativeTwo.source_mem hs) hs.1
  have hstep := fourthScalar_antitone ⟨hangle.le,hφ.2⟩
    (show Real.pi/2∈Icc (6/5) (Real.pi/2) from ⟨six_fifths_lower.2,le_rfl⟩) hφ.2
  have hbase := fourthScalar_quarter.trans_le hstep
  dsimp [fourthScalar,value] at *
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree
