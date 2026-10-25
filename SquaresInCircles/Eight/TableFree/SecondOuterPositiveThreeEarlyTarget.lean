module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeEarlyMinorant

/-!
# The early support on the entire physical target arc

The target support has curvature at least `1.29` up to `0.34`.
Beyond that coordinate its first derivative is positive: angle
monotonicity reduces to `1.3`, and concavity reduces the remaining
target interval to its two endpoints.  Thus the one quadratic
minorant controls every original target, including weak contacts.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio ratioD)

def cut : ℝ := 17/50

lemma cut_mem : cut∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [cut])

lemma cut_references :
    (11721/25000:ℝ)<ratio cut ∧ (68083/100000:ℝ)<ratioD cut ∧
      LLabel.d1 cut<17297/25000 ∧ LLabel.d2 cut< -(39003/50000:ℝ) := by
  have hU := shifted_chart_reference (outer_domain cut_mem)
    (l := (179164728671689/10^14:ℝ)) (u := (179164728671690/10^14:ℝ))
    (by norm_num) (by norm_num)
    (by norm_num [cut,W,Q0]) (by norm_num [cut,W,Q0])
  have hr := FixedReference.ratios cut_mem
    (show cut∈Icc cut cut from ⟨le_rfl,le_rfl⟩)
    ⟨hU.1.le,hU.2.le⟩ cut_mem.1 (by norm_num)
  have hL := LReference.target cut_mem
    (show cut∈Icc cut cut from ⟨le_rfl,le_rfl⟩)
    ⟨hU.1.le,hU.2.le⟩ cut_mem.1 (by norm_num)
  have hr1 := hr.1
  have hr2 := hr.2.2.1
  have hL1 := hL.2.2.2.1
  have hL2 := hL.2.2.2.2.2
  norm_num [cut,Q0] at hr1 hr2
  norm_num [LReference.firstHi,LReference.secondHi,cut,Q0] at hL1 hL2
  dsimp only [cut]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma end_trig :
    (19271/20000:ℝ)<Real.sin (13/10) ∧
      (26749/100000:ℝ)<Real.cos (13/10) := by
  have ht := PointProducts.trig (show (0:ℝ)≤13/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  constructor <;> linarith [ht.1.1,ht.2.1]

lemma cut_second {φ : ℝ} (hφ : Lower φ) : m<targetSecond cut φ := by
  have ht := lower_trig hφ
  have hr := cut_references
  have hprod := mul_lt_mul'' hr.2.1 ht.1
    (by norm_num : (0:ℝ)≤68083/100000) (by norm_num : (0:ℝ)≤19121/25000)
  dsimp [targetSecond,g,m]
  linarith [hr.2.2.2]

lemma targetSecond_antitone {φ : ℝ} (hφ : Lower φ) :
    AntitoneOn (fun B => targetSecond B φ) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (targetSecond_hasDerivAt hB φ).continuousAt.continuousWithinAt)
    (fun B hB => targetSecond_hasDerivAt (Ioo_subset_Icc_self hB) φ)
    (fun B hB => (targetThird_negative (Ioo_subset_Icc_self hB) hφ).le)

lemma targetSecond_lower {B φ : ℝ} (hB : B∈Icc 0 cut) (hφ : Lower φ) :
    m≤targetSecond B φ := by
  have hBout : B∈Icc 0 outerDiagonal := ⟨hB.1,hB.2.trans cut_mem.2⟩
  exact (cut_second hφ).le.trans (targetSecond_antitone hφ hBout cut_mem hB.2)

lemma minorant_le_before_cut {B φ : ℝ} (hB : B∈Icc 0 cut) (hφ : Lower φ) :
    minorant φ≤ support B φ := by
  have hstar : star∈Icc 0 cut := by norm_num [star,cut]
  have hh := curvature_tangent (f := fun t => support t φ)
    (d := fun t => targetFirst t φ) (dd := fun t => targetSecond t φ)
    (κ := m) hB hstar
    (fun t ht => support_hasDerivAt ⟨ht.1,ht.2.trans cut_mem.2⟩ φ)
    (fun t ht => targetFirst_hasDerivAt ⟨ht.1,ht.2.trans cut_mem.2⟩ φ)
    (fun t ht => targetSecond_lower ht hφ)
  have h2 : (targetFirst star φ)^2/(2*m)=50/129*(targetFirst star φ)^2 := by
    simp only [m]
    ring
  simp only [m] at hh
  dsimp only [minorant]
  rw [h2]
  nlinarith [sq_nonneg ((129/100)*(B-star)+targetFirst star φ)]

lemma targetFirst_angle_general (B φ : ℝ) :
    HasDerivAt (targetFirst B)
      (g*(ratio B*Real.cos φ-Real.sin φ)) φ := by
  have hd := ((((Real.hasDerivAt_sin φ).const_mul (ratio B)).add
    (Real.hasDerivAt_cos φ)).const_mul g).sub_const (LLabel.d1 B)
  convert hd using 1
  funext t
  simp only [targetFirst,Pi.add_apply]

lemma targetFirst_angle_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (targetFirst B) (Icc lowerAngle (13/10)) := by
  refine antiOn_of_hasDeriv_nonpos
    (fun φ _ => (targetFirst_angle_general B φ).continuousAt.continuousWithinAt)
    (fun φ _ => targetFirst_angle_general B φ) ?_
  intro φ hφ
  have ht := lower_trig (early_lower (Ioo_subset_Icc_self hφ))
  have hr := (outer_ratio_bounds hB).2.1
  have hm := mul_le_mul_of_nonneg_right hr ht.2.2.1
  dsimp [g]
  nlinarith [ht.1,ht.2.2.2.1]

lemma cut_first_end : (1/100:ℝ)<targetFirst cut (13/10) := by
  have hr := cut_references
  have ht := end_trig
  have hm := mul_lt_mul'' hr.1 ht.1
    (by norm_num : (0:ℝ)≤11721/25000) (by norm_num : (0:ℝ)≤19271/20000)
  dsimp [targetFirst,g]
  linarith [hr.2.2.1,ht.2]

lemma diagonal_first_end : (1/50:ℝ)<targetFirst outerDiagonal (13/10) := by
  have hL := L_first_upper
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩)
  rw [targetFirst,ratio_diagonal]
  dsimp [g]
  nlinarith [end_trig.1,end_trig.2]

lemma targetFirst_end_positive {B : ℝ} (hB : B∈Icc cut outerDiagonal) :
    0<targetFirst B (13/10) := by
  have hc : ConcaveOn ℝ (Icc cut outerDiagonal)
      (fun t => targetFirst t (13/10)) :=
    concave_of_deriv2
      (fun t ht => targetFirst_hasDerivAt ⟨cut_mem.1.trans ht.1,ht.2⟩ (13/10))
      (fun t ht => targetSecond_hasDerivAt ⟨cut_mem.1.trans ht.1,ht.2⟩ (13/10))
      (fun t ht => (targetThird_negative ⟨cut_mem.1.trans ht.1,ht.2⟩
        (early_lower end_mem)).le)
  have hh := hc.min_le_of_mem_Icc
    (show cut∈Icc cut outerDiagonal from ⟨le_rfl,cut_mem.2⟩)
    (show outerDiagonal∈Icc cut outerDiagonal from ⟨cut_mem.2,le_rfl⟩) hB
  exact (lt_min (by linarith [cut_first_end])
    (by linarith [diagonal_first_end])).trans_le hh

lemma targetFirst_positive {B φ : ℝ} (hB : B∈Icc cut outerDiagonal)
    (hφ : φ∈Icc lowerAngle (13/10)) : 0<targetFirst B φ := by
  have hBout : B∈Icc 0 outerDiagonal := ⟨cut_mem.1.trans hB.1,hB.2⟩
  exact (targetFirst_end_positive hB).trans_le
    (targetFirst_angle_antitone hBout hφ end_mem hφ.2)

lemma support_monotone_after_cut {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    MonotoneOn (fun B => support B φ) (Icc cut outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (support_hasDerivAt ⟨cut_mem.1.trans hB.1,hB.2⟩ φ).continuousAt.continuousWithinAt)
    (fun _ hB => support_hasDerivAt
      ⟨cut_mem.1.trans hB.1.le,hB.2.le⟩ φ)
    (fun _ hB => (targetFirst_positive (Ioo_subset_Icc_self hB) hφ).le)

theorem minorant_le_support {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hφ : φ∈Icc lowerAngle (13/10)) : minorant φ≤ support B φ := by
  by_cases hc : B≤cut
  · exact minorant_le_before_cut ⟨hB.1,hc⟩ (early_lower hφ)
  · have hcut : cut∈Icc 0 cut := ⟨cut_mem.1,le_rfl⟩
    exact (minorant_le_before_cut hcut (early_lower hφ)).trans
      (support_monotone_after_cut hφ ⟨le_rfl,cut_mem.2⟩
        ⟨le_of_not_ge hc,hB.2⟩ (le_of_not_ge hc))

theorem original_short {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : φ∈Icc lowerAngle (13/10)) (hb : b≤7/20)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (451/500:ℝ)<value b B φ :=
  (minorant_lower hφ).trans_le (minorant_le_support (NegativeTwo.source_mem ht) hφ)
    |>.trans (original_short_support hs ht (early_lower hφ) hb hm)

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.Early
