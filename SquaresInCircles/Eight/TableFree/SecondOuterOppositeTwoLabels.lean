module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoData
public import SquaresInCircles.Eight.TableFree.SecondOuterLabelBounds
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoContactCap

/-!
# The fixed circle references used by opposite edge two

The coordinate with primary height one is an actual circle point.
All reference derivative bounds and both axial aligned costs are
obtained from integer-square bounds and the literal labels.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def bOne : ℝ := arc 1

lemma bOne_mem : bOne∈Icc 0 outerDiagonal := primary_secondary_mem primary_one_mem

lemma bOne_arc : arc bOne=1 :=
  (ShortOuterOne.SameContact.actual_arc (primary_state primary_one_mem)).1

lemma bOne_bounds :
    (79058126439213/100000000000000:ℝ)<bOne ∧
      bOne<39529063219607/50000000000000 := by
  have hc := UW_circle (primary_domain primary_one_mem)
  have hp : 0<bOne+1/2 := by linarith [bOne_mem.1]
  norm_num [U,W,Q0] at hc
  change (bOne+1/2)^2+9/4=9789/2500 at hc
  constructor <;> nlinarith

lemma two_radical : (185083/100000:ℝ)<U (1/5) ∧
    U (1/5)<46271/25000 :=
  Asymmetric.shifted_reference NegativeTwo.TargetContact.Cap.two_mem
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma two_ratio : (1891/5000:ℝ)<ratio (1/5) ∧ ratio (1/5)<3783/10000 := by
  have hu := U_positive (outer_domain NegativeTwo.TargetContact.Cap.two_mem)
  change (1891/5000:ℝ)<W (1/5)/U (1/5) ∧
    W (1/5)/U (1/5)<3783/10000
  constructor
  · apply (lt_div_iff₀ hu).2
    norm_num [W]
    linarith [two_radical.2]
  · apply (div_lt_iff₀ hu).2
    norm_num [W]
    linarith [two_radical.1]

lemma two_ratioD : (247/400:ℝ)<ratioD (1/5) := by
  have hu := U_positive (outer_domain NegativeTwo.TargetContact.Cap.two_mem)
  have hcube := pow_le_pow_left₀ hu.le two_radical.2.le 3
  change (247/400:ℝ)<Q0/(U (1/5))^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0]
  nlinarith

lemma V_first_two : (973/1000:ℝ)<VLabel.d1 (1/5) := by
  have hu := two_radical.1
  have hr := two_ratio.2
  have he : VLabel.d1 (1/5)=16031/100000+
      (63457/100000)*(U (1/5)-1/2)-(14583/125000)*ratio (1/5) := by
    simp only [RoleLabel.d1,VLabel,U]
    ring
  rw [he]
  linarith

lemma V_second_two : VLabel.d2 (1/5)< -(69/125:ℝ) := by
  have hr := two_ratio.1
  have hd := two_ratioD
  norm_num [RoleLabel.d2,VLabel]
  linarith

lemma P_second_reference : PLabel.d2 (83/200)<197/1000 := by
  have hb : (83/200:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hu := Asymmetric.shifted_reference (l := (3509/2000:ℝ))
    (u := (8773/5000:ℝ)) hb (by norm_num) (by norm_num)
    (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hp := U_positive (outer_domain hb)
  have hr : ratio (83/200)<261/500 := by
    change W (83/200)/U (83/200)<261/500
    apply (div_lt_iff₀ hp).2
    norm_num [W]
    linarith
  have hd : ratioD (83/200)<363/500 := by
    have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3509/2000) hu.1.le 3
    change Q0/(U (83/200))^3<363/500
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    norm_num [Q0]
    nlinarith
  norm_num [RoleLabel.d2,PLabel]
  linarith

lemma P_second_small {b : ℝ} (hb : b∈Icc 0 (83/200)) :
    PLabel.d2 b<197/1000 := by
  have hr : (83/200:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  exact (P_second_monotone ⟨hb.1,hb.2.trans hr.2⟩ hr hb.2).trans_lt P_second_reference

lemma P_second_bOne : PLabel.d2 bOne<69/200 := by
  have hr : ratio bOne<861/1000 := by
    norm_num [ratio,bOne_arc]
    linarith [bOne_bounds.2]
  have hd : ratioD bOne=9789/2500/(3/2:ℝ)^3 := by
    norm_num [ratioD,bOne_arc,Q0]
  have hmul := mul_le_mul_of_nonneg_right bOne_bounds.2.le
    (show 0≤ratioD bOne by rw [hd]; norm_num)
  norm_num [RoleLabel.d2,PLabel,hd]
  norm_num [hd] at hmul
  nlinarith

lemma aligned_axial_value :
    (44889/50000:ℝ)<Real.pi/2-P bOne-V 0 := by
  have hb := bOne_bounds
  have hb2 := pow_le_pow_left₀ bOne_mem.1 hb.2.le 2
  have ha := ShortOuterZero.fine_axial_bounds.1
  have hpi := pi_hand_enclosure.1
  norm_num [P,V,RoleLabel.outer,RoleLabel.eval,PLabel,VLabel,bOne_arc,
    ShortOuterOne.SameContact.arc_zero]
  nlinarith

lemma reverse_aligned_axial_value :
    (4639/5000:ℝ)<Real.pi/2-P 0-V bOne := by
  have hb := bOne_bounds.2
  have hpi := pi_hand_enclosure.1
  norm_num [P,V,RoleLabel.outer,RoleLabel.eval,PLabel,VLabel,bOne_arc]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo
