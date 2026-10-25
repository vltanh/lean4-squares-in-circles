module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeAligned
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeNegativeGeometry

/-!
# Eight squares: interior geometry for the positive opposite-sign contact

The lower endpoint is either the original target axis or the original
source diagonal. Every intermediate target remains on the same contact
surface. The derivative continuity facts are local facts on that actual
surface, needed for the written stationary-point tests.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open SecondWord (outer_domain outer_zero_mem)

lemma lower_entry {B x : ℝ} (hd : PlusDomain B x) :
    ∃a, a∈Icc 0 B ∧ PlusDomain a x ∧ (a=0 ∨ plus a x=outerDiagonal) ∧
      ∀C∈Icc a B, PlusDomain C x := by
  have hinterval {a : ℝ} (ha : PlusDomain a x) (haB : a≤B) :
      ∀C∈Icc a B, PlusDomain C x := by
    intro C hC
    have hCi : C∈Icc 0 outerDiagonal := ⟨ha.1.1.trans hC.1,hC.2.trans hd.1.2⟩
    have hlo := SecondWord.OppositeZero.plus_target_antitone hd.2.1 hCi hd.1 hC.2
    have hhi := SecondWord.OppositeZero.plus_target_antitone hd.2.1 ha.1 hCi hC.1
    exact ⟨hCi,hd.2.1,⟨hd.2.2.1.trans hlo,hhi.trans ha.2.2.2⟩⟩
  by_cases hzero : plus 0 x≤outerDiagonal
  · have hsource := SecondWord.OppositeZero.plus_target_antitone hd.2.1 outer_zero_mem hd.1 hd.1.1
    have hz : PlusDomain 0 x := ⟨outer_zero_mem,hd.2.1,⟨hd.2.2.1.trans hsource,hzero⟩⟩
    exact ⟨0,⟨le_rfl,hd.1.1⟩,hz,Or.inl rfl,hinterval hz hd.1.1⟩
  · have hc : Continuous (fun C => plus C x) := by dsimp [plus,SecondWord.OppositeZero.plus,arc]; fun_prop
    obtain ⟨a,ha,he⟩ := intermediate_value_Icc hd.1.1 hc.neg.continuousOn
      (show -outerDiagonal∈Icc (-plus 0 x) (-plus B x) from
        ⟨by linarith,by linarith [hd.2.2.2]⟩)
    have heq : plus a x=outerDiagonal := by simpa using he
    have had : PlusDomain a x :=
      ⟨⟨ha.1,ha.2.trans hd.1.2⟩,hd.2.1,by show plus a x∈_; rw [heq]; exact Negative.diagonal_mem⟩
    exact ⟨a,ha,had,Or.inr heq,hinterval had ha.2⟩

lemma initial_target_coordinate {B x : ℝ} (hd : PlusDomain B x)
    (hentry : B=0 ∨ plus B x=outerDiagonal) : B≤low := by
  rcases hentry with rfl | hdiag
  · exact low_mem.1
  · have hh := SecondWord.OppositeZero.plus_angle_antitone hd.1
      (by norm_num) hd.2.1 hd.2.1.1
    rw [show SecondWord.OppositeZero.plus B x=outerDiagonal from hdiag] at hh
    norm_num [plus,SecondWord.OppositeZero.plus] at hh
    dsimp [low]
    linarith

lemma ratio_monotone : MonotoneOn ratio (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => (ShortOuterOne.SameContact.ratioD_pos (outer_domain (Ioo_subset_Icc_self hB))).le)

lemma ratioD_monotone : MonotoneOn ratioD (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).continuousAt.continuousWithinAt)
    (fun B hB => ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain (Ioo_subset_Icc_self hB)))
    (fun B hB => by
      have hu := SecondWord.U_positive (outer_domain (Ioo_subset_Icc_self hB))
      change 0≤3*Q0*(B+1/2)/(SecondWord.U B)^5
      exact div_nonneg (mul_nonneg (by norm_num [Q0]) (by linarith [hB.1])) (pow_pos hu 5).le)

lemma target_projection_upper {B x : ℝ} (hd : PlusDomain B x) : plusK B x≤1 := by
  have tr := positive_trig hd.2.1
  have hr := ShortOuterOne.SameContact.ratio_pos (outer_domain hd.1)
  have hp := mul_nonneg hr.le tr.2.2.1
  dsimp [plusK,SecondWord.OppositeZero.plusK]
  linarith [tr.2.1]

lemma plusTargetCurvature_continuousAt (r : Row) {B x : ℝ} (hd : PlusDomain B x) :
    ContinuousAt (fun C => plusTargetCurvature r C x) B := by
  have hb := (SecondWord.OppositeZero.plus_target_hasDerivAt hd.1 x).continuousAt
  have hD := (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hd.2.2)).continuousAt.comp
    (x := B) hb
  have hL := (l_hasDerivAt r hd.2.2).continuousAt.comp (x := B) hb
  have hR := (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hd.1)).continuousAt
  have hDt := (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hd.1)).continuousAt
  have hK : ContinuousAt (fun C => plusK C x) B :=
    continuousAt_const.sub (hR.mul continuousAt_const)
  exact ((continuousAt_const.mul hD).mul (hK.pow 2)).add
    (((hL.mul continuousAt_const).sub continuousAt_const).mul hDt)

/-- The affine-source row cannot have a target local minimum in the interior. -/
lemma row_zero_stationary_curvature {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusTarget 0 B x=0) : plusTargetCurvature 0 B x<0 := by
  have tr := positive_trig hd.2.1
  have hr := ShortOuterOne.SameContact.ratio_pos (outer_domain hd.1)
  have hD := ShortOuterOne.SameContact.ratioD_pos (outer_domain hd.1)
  have hid : plusTarget 0 B x=t 0-q 0*Real.cos x+
      (q 0*Real.sin x-v 0)*ratio B := by
    norm_num [plusTarget,h,l,p,plusK,SecondWord.OppositeZero.plusK]
    ring
  have hpositive : 0<t 0-q 0*Real.cos x := by norm_num [t,q]; linarith [tr.2.1]
  have hnegative : q 0*Real.sin x-v 0<0 := by
    rw [hid] at hstat
    by_contra! hn
    have hp := mul_nonneg hn hr.le
    linarith
  have hprod := mul_neg_of_neg_of_pos hnegative hD
  simpa [plusTargetCurvature,l,p] using hprod

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive
