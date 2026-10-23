module

public import SquaresInCircles.Eight.TableFree.SecondOuterLabelCalculus

/-!
# Whole-arc derivative bounds for the edge-two outer labels

The source label is convex and has increasing curvature.  The target
label is increasing and strictly concave, with decreasing curvature.
Every bound follows on the entire physical outer arc from its circle
equation and the two circle endpoints.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma ratioDD_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : 0<ratioDD b := by
  have hu := U_positive (outer_domain hb)
  change 0<3*Q0*W b/(U b)^5
  exact div_pos (mul_pos (by norm_num [Q0])
    (by dsimp [W]; linarith [hb.1])) (pow_pos hu 5)

lemma ratioDD_formula {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    ratioDD b=(3*W b/(U b)^2)*ratioD b := by
  have hu := U_positive (outer_domain hb)
  dsimp [ratioDD,ratioD,U,W]
  field_simp [hu.ne']
  ring

lemma ratioDD_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    ratioDD b<3*ratioD b := by
  have hu := U_positive (outer_domain hb)
  have hd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hbounds := UW_bounds hb
  have hquot : 3*W b/(U b)^2<3 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hu)).2
    nlinarith [hbounds.1,hbounds.2.2.2]
  rw [ratioDD_formula hb]
  exact mul_lt_mul_of_pos_right hquot hd

lemma P_second_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<PLabel.d2 b := by
  have hr := ShortOuterOne.SameContact.ratio_pos (outer_domain hb)
  have hd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hm := mul_nonneg hb.1 hd.le
  norm_num [RoleLabel.d2,PLabel]
  nlinarith

lemma P_third_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<PLabel.d3 b := by
  have hd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hh := ratioDD_positive hb
  have hm := mul_nonneg hb.1 hh.le
  norm_num [RoleLabel.d3,PLabel]
  nlinarith

lemma P_second_monotone : MonotoneOn PLabel.d2 (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (PLabel.d2_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => PLabel.d2_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => (P_third_positive (Ioo_subset_Icc_self hb)).le)

lemma P_first_monotone : MonotoneOn PLabel.d1 (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (PLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => PLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => (P_second_positive (Ioo_subset_Icc_self hb)).le)

lemma P_first_zero_bounds : (773/1000:ℝ)<PLabel.d1 0 ∧ PLabel.d1 0<387/500 := by
  norm_num [RoleLabel.d1,PLabel,ShortOuterOne.SameContact.arc_zero]
  constructor <;> linarith [outer_endpoint_bounds.2.1,ShortOuterZero.fine_axial_bounds.1]

lemma ratio_diagonal : ratio outerDiagonal=1 := by
  have hp : outerDiagonal+1/2≠0 := by linarith [outer_endpoint_bounds.2.2.1]
  simp [ratio,ShortOuterOne.SameContact.arc_diagonal,hp]

lemma P_first_diagonal : PLabel.d1 outerDiagonal=
    18603/20000+(2363/50000)*outerDiagonal := by
  norm_num [RoleLabel.d1,PLabel,ShortOuterOne.SameContact.arc_diagonal,ratio_diagonal]
  ring

lemma P_first_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (773/1000:ℝ)<PLabel.d1 b ∧ PLabel.d1 b<973/1000 := by
  have hlo := P_first_monotone outer_zero_mem hb hb.1
  have hhi := P_first_monotone hb
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩) hb.2
  rw [P_first_diagonal] at hhi
  exact ⟨P_first_zero_bounds.1.trans_le hlo,
    by linarith [hhi,outer_endpoint_bounds.2.2.2]⟩

lemma P_monotone : MonotoneOn P (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (PLabel.outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => PLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [(P_first_bounds (Ioo_subset_Icc_self hb)).1])

lemma V_third_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    VLabel.d3 b<0 := by
  have hd := ShortOuterOne.SameContact.ratioD_pos (outer_domain hb)
  have hp := ratioDD_positive hb
  have hu := ratioDD_upper hb
  have hm := mul_nonneg hb.1 hp.le
  norm_num [RoleLabel.d3,VLabel]
  nlinarith

lemma V_second_antitone : AntitoneOn VLabel.d2 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (VLabel.d2_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => VLabel.d2_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => (V_third_negative (Ioo_subset_Icc_self hb)).le)

lemma zero_ratio_upper : ratio 0<131/500 := by
  have hu := U_positive (outer_domain outer_zero_mem)
  change (1/2:ℝ)/U 0<131/500
  apply (div_lt_iff₀ hu).2
  norm_num [U,ShortOuterOne.SameContact.arc_zero]
  linarith [ShortOuterZero.fine_axial_bounds.1]

lemma zero_ratioD_upper : ratioD 0<14/25 := by
  have hu := U_positive (outer_domain outer_zero_mem)
  have hlo : (1914/1000:ℝ)<U 0 := by
    norm_num [U,ShortOuterOne.SameContact.arc_zero]
    linarith [ShortOuterZero.fine_axial_bounds.1]
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1914/1000) hlo.le 3
  change Q0/(U 0)^3<14/25
  apply (div_lt_iff₀ (pow_pos hu 3)).2
  norm_num [Q0]
  nlinarith

lemma V_second_zero : VLabel.d2 0< -(13/40:ℝ) := by
  have hr := (outer_ratio_bounds outer_zero_mem).1
  have hd := zero_ratioD_upper
  norm_num [RoleLabel.d2,VLabel]
  linarith

lemma V_second_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    VLabel.d2 b< -(13/40:ℝ) :=
  (V_second_antitone outer_zero_mem hb hb.1).trans_lt V_second_zero

lemma V_first_antitone : AntitoneOn VLabel.d1 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (VLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => VLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [V_second_upper (Ioo_subset_Icc_self hb)])

lemma V_first_diagonal : VLabel.d1 outerDiagonal=(1066/6250:ℝ) := by
  norm_num [RoleLabel.d1,VLabel,ShortOuterOne.SameContact.arc_diagonal,ratio_diagonal]
  ring

lemma V_first_zero : VLabel.d1 0<1061/1000 := by
  have ha := outer_endpoint_bounds.2.1
  have hr := zero_ratio_upper
  norm_num [RoleLabel.d1,VLabel,ShortOuterOne.SameContact.arc_zero]
  linarith

lemma V_first_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (1066/6250:ℝ)≤VLabel.d1 b ∧ VLabel.d1 b<1061/1000 := by
  have hlo := V_first_antitone hb
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩) hb.2
  rw [V_first_diagonal] at hlo
  exact ⟨hlo,(V_first_antitone outer_zero_mem hb hb.1).trans_lt V_first_zero⟩

lemma V_first_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    VLabel.d1 b<1061/1000 := (V_first_bounds hb).2

lemma V_monotone : MonotoneOn V (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (VLabel.outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => VLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [(V_first_bounds (Ioo_subset_Icc_self hb)).1])

end SquaresInCircles.Eight.TableFree.SecondWord
