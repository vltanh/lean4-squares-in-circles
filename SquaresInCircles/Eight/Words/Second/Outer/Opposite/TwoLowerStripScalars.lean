module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoContactInverse
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoInverseBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoUpperTargetPrimary

/-!
# Eight squares: scalar bounds for the original lower target-secondary short strip

The two rational source references are .415 and .775.  Actual
circle squares give the required first-derivative bounds.  On the
zero-target boundary the inverse angular derivative is paid with
a strict reserve, so that boundary decreases to the aligned state.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerStrip

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def earlyTarget : Set ℝ := Icc 0 (83/200)
def sourceBand : Set ℝ := Icc (31/40) bOne
def axisValue (b : ℝ) : ℝ :=
  Real.pi/2-NegativeTwo.ContactInverse.angle (-(1/2)) b-P b-V 0
def axisFirst (b : ℝ) : ℝ :=
  Inverse.factor (U b)-ratio b/
    (2*Inverse.q (U b)*NegativeTwo.ContactInverse.speed (-(1/2)) b)-PLabel.d1 b

lemma early_mem {b : ℝ} (hb : b∈earlyTarget) : b∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem ⟨hb.1,by linarith [hb.2]⟩

lemma band_mem {b : ℝ} (hb : b∈sourceBand) : b∈Icc 0 outerDiagonal :=
  ⟨by linarith [hb.1],hb.2.trans bOne_mem.2⟩

lemma target_reference_mem : (83/200:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma source_reference_mem : (31/40:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma source_reference_radical :
    (75663/50000:ℝ)<U (31/40) ∧ U (31/40)<151327/100000 :=
  Asymmetric.shifted_reference source_reference_mem
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma source_reference_ratio : (42127/50000:ℝ)<ratio (31/40) := by
  have hp := U_positive (outer_domain source_reference_mem)
  change (42127/50000:ℝ)<W (31/40)/U (31/40)
  apply (lt_div_iff₀ hp).2
  norm_num [W]
  nlinarith [source_reference_radical.2]

lemma source_reference_first : (9269/10000:ℝ)<PLabel.d1 (31/40) := by
  have hu := source_reference_radical
  have hr := source_reference_ratio
  have he : PLabel.d1 (31/40)=93015/100000+(2363/50000)*(31/40)-
      (2211/20000)*(U (31/40)-1/2)+(2211/20000)*(31/40)*ratio (31/40) := by
    simp only [RoleLabel.d1,PLabel,U]
    ring
  rw [he]
  linarith

lemma source_first_lower {b : ℝ} (hb : b∈sourceBand) :
    (9269/10000:ℝ)<PLabel.d1 b := by
  have hm := P_first_increasing source_reference_mem (band_mem hb) hb.1
  linarith [source_reference_first]

lemma target_reference_radical :
    (3509/2000:ℝ)<U (83/200) ∧ U (83/200)<8773/5000 :=
  Asymmetric.shifted_reference target_reference_mem
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma target_reference_ratio : ratio (83/200)<261/500 := by
  have hp := U_positive (outer_domain target_reference_mem)
  change W (83/200)/U (83/200)<261/500
  apply (div_lt_iff₀ hp).2
  norm_num [W]
  nlinarith [target_reference_radical.1]

lemma target_reference_first : (41/50:ℝ)<VLabel.d1 (83/200) := by
  have hu := target_reference_radical
  have hr := target_reference_ratio
  have he : VLabel.d1 (83/200)=16031/100000+(63457/100000)*(U (83/200)-1/2)-
      (-(41/4000)+(63457/100000)*(83/200))*ratio (83/200) := by
    simp only [RoleLabel.d1,VLabel,U]
    ring
  rw [he]
  linarith

lemma target_first_antitone : AntitoneOn VLabel.d1 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (VLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => VLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [V_second_upper (Ioo_subset_Icc_self hb)])

lemma target_first_lower {b : ℝ} (hb : b∈earlyTarget) :
    (41/50:ℝ)<VLabel.d1 b := by
  have hm := target_first_antitone (early_mem hb) target_reference_mem hb.2
  linarith [target_reference_first]

lemma target_monotone : MonotoneOn V earlyTarget :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (VLabel.outer_hasDerivAt (outer_domain (early_mem hb))).continuousAt.continuousWithinAt)
    (fun b hb => VLabel.outer_hasDerivAt (outer_domain (early_mem (Ioo_subset_Icc_self hb))))
    (fun b hb => by linarith [target_first_lower (Ioo_subset_Icc_self hb)])

lemma source_second_upper {b : ℝ} (hb : b∈Icc 0 bOne) :
    PLabel.d2 b<69/200 := by
  have hm := P_second_monotone ⟨hb.1,hb.2.trans bOne_mem.2⟩ bOne_mem hb.2
  exact hm.trans_lt P_second_bOne

lemma source_ratioD_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (557/1000:ℝ)<ratioD b := by
  have hp := U_positive (outer_domain hb)
  have hU := (UW_bounds hb).2.1
  have hcube := pow_le_pow_left₀ hp.le hU.le 3
  change (557/1000:ℝ)<Q0/(U b)^3
  apply (lt_div_iff₀ (pow_pos hp 3)).2
  norm_num [Q0]
  nlinarith

lemma source_ratio_upper {b : ℝ} (hb : b∈Icc 0 bOne) :
    ratio b<861/1000 := by
  have hB : b∈Icc 0 outerDiagonal := ⟨hb.1,hb.2.trans bOne_mem.2⟩
  have hp := U_positive (outer_domain hB)
  have ha := ShortOuterOne.SameContact.arc_antitone
    (outer_domain hB) (outer_domain bOne_mem) hb.2
  rw [bOne_arc] at ha
  change W b/U b<861/1000
  apply (div_lt_iff₀ hp).2
  dsimp [W,U]
  linarith [bOne_bounds.2,hb.2]

lemma band_ratio_lower {b : ℝ} (hb : b∈sourceBand) :
    (133/200:ℝ)<ratio b := by
  have hp := U_positive (outer_domain (band_mem hb))
  have hU := (UW_bounds (band_mem hb)).2.1
  change (133/200:ℝ)<W b/U b
  apply (lt_div_iff₀ hp).2
  dsimp [W]
  nlinarith [hb.1]

lemma band_q_upper {b : ℝ} (hb : b∈sourceBand) :
    Inverse.q (U b)≤4789/2500 := by
  have ha := ShortOuterOne.SameContact.arc_antitone
    (outer_domain (band_mem hb)) (outer_domain bOne_mem) hb.2
  rw [bOne_arc] at ha
  norm_num [Inverse.q,NegativeTwo.Inverse.q,Q0,U]
  linarith

lemma band_speed_upper {b : ℝ} (hb : b∈sourceBand) :
    NegativeTwo.ContactInverse.speed (-(1/2)) b<1291/1000 := by
  have hd := NegativeTwo.ContactInverse.data (band_mem hb)
    (show (-(1/2:ℝ))∈Icc (-(1/2)) (2/5) by norm_num)
  have hq := band_q_upper hb
  nlinarith [hd.2.2.2.2.1,hd.2.2.2.2.2]

lemma band_correction_lower {b : ℝ} (hb : b∈sourceBand) :
    (13/100:ℝ)<ratio b/
      (2*Inverse.q (U b)*NegativeTwo.ContactInverse.speed (-(1/2)) b) := by
  have hB := band_mem hb
  have hd := NegativeTwo.ContactInverse.data hB
    (show (-(1/2:ℝ))∈Icc (-(1/2)) (2/5) by norm_num)
  have hI : U b∈Inverse.interval := ⟨(UW_bounds hB).1.le,(UW_bounds hB).2.1.le⟩
  have hq0 : 0<Inverse.q (U b) := by linarith [(Inverse.range_data hI).2]
  have hv := hd.2.2.2.2.1
  have hden := mul_le_mul (band_q_upper hb) (band_speed_upper hb).le
    hv.le (by norm_num : (0:ℝ)≤4789/2500)
  apply (lt_div_iff₀ (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hq0) hv)).2
  nlinarith [band_ratio_lower hb]

lemma axis_hasDerivAt {b : ℝ} (hb : b∈sourceBand) :
    HasDerivAt axisValue (axisFirst b) b := by
  have hangle := NegativeTwo.ContactInverse.angle_hasDerivAt (band_mem hb)
    (show (-(1/2:ℝ))∈Icc (-(1/2)) (2/5) by norm_num)
  exact (((hangle.const_sub (Real.pi/2)).sub
    (PLabel.outer_hasDerivAt (outer_domain (band_mem hb)))).sub_const (V 0)).congr_deriv
    (by dsimp only [axisFirst,NegativeTwo.ContactInverse.first]; ring)

lemma axis_first_negative {b : ℝ} (hb : b∈sourceBand) : axisFirst b<0 := by
  have hB := band_mem hb
  have hf := Inverse.factor_upper
    (show U b∈Inverse.interval from ⟨(UW_bounds hB).1.le,(UW_bounds hB).2.1.le⟩)
  have hc := band_correction_lower hb
  have hP := source_first_lower hb
  dsimp [axisFirst]
  linarith

lemma axis_antitone : AntitoneOn axisValue sourceBand :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hb => (axis_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun _ hb => axis_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun _ hb => (axis_first_negative (Ioo_subset_Icc_self hb)).le)

lemma axis_aligned :
    axisValue bOne=Real.pi/2-P bOne-V 0 := by
  have hzero : NegativeTwo.TargetContact.B bOne 0=0 := by
    rw [NegativeTwo.TargetContact.B_zero,bOne_arc]
    norm_num
  have hd : NegativeTwo.TargetContact.Domain bOne 0 :=
    ⟨bOne_mem,by norm_num,by rw [hzero]; exact outer_zero_mem⟩
  have he := NegativeTwo.ContactInverse.original_angle hd
  rw [hzero] at he
  norm_num at he
  unfold axisValue
  rw [he,sub_zero]

theorem axis_lower {b : ℝ} (hb : b∈sourceBand) :
    (44889/50000:ℝ)<axisValue b := by
  have hb1 : bOne∈sourceBand := ⟨by linarith [bOne_bounds.1],le_rfl⟩
  have hm := axis_antitone hb hb1 hb.2
  rw [axis_aligned] at hm
  linarith [aligned_axial_value]

end SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerStrip

