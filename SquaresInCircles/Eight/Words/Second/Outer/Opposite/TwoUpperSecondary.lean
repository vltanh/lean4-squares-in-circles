module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoUpperTargetPrimary

/-!
# Eight squares: both original upper secondary owners by finite circle comparison

Each original weak secondary separator allows at most `.4*x` of
coordinate displacement from alignment.  Uniform derivative bounds
pay this displacement directly.  If the original primary coordinate
is below one, the primary-label tangent pays its simultaneous loss.
No zero-exit curve or contact minimizer is assumed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma upper_secondary_displacement {a b x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) : upperCut a b x+1-a≤(2/5)*x := by
  have ht := positive_trig hx
  have hprimary : 0≤a-1/2 := by linarith [(outer_bounds hs).1,fine_outer_endpoint_bounds.2]
  have hcos := mul_nonneg hprimary (sub_nonneg.mpr ht.2.1)
  have hsin := mul_nonneg
    (show 0≤2/5-(b-1/2) by linarith [(outer_bounds hs).2.2,outer_endpoint_bounds.2.2.2])
    ht.2.2.1
  have hangle := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 (by norm_num : (0:ℝ)≤2/5)
  dsimp [upperCut]
  nlinarith

lemma P_upper_increment {l b : ℝ} (hl : l∈Icc 0 outerDiagonal)
    (hb : b∈Icc 0 outerDiagonal) (hlb : l≤b) :
    P b-P l≤(973/1000)*(b-l) := by
  have hh := P_chord_at hl hb hlb
  have hm := mul_le_mul_of_nonneg_right (P_first_bounds hb).2.le (sub_nonneg.mpr hlb)
  linarith

lemma V_upper_increment {l B : ℝ} (hl : l∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hlB : l≤B) :
    V B-V l≤(1061/1000)*(B-l) := by
  have hm : MonotoneOn (fun t => (1061/1000)*t-V t) (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (VLabel.affine_difference_hasDerivAt (1061/1000)
        (outer_domain ht)).continuousAt.continuousWithinAt)
      (fun t ht => VLabel.affine_difference_hasDerivAt (1061/1000)
        (outer_domain (Ioo_subset_Icc_self ht)))
      (fun t ht => by linarith [V_first_upper (Ioo_subset_Icc_self ht)])
  have hh := hm hl hB hlB
  linarith

lemma source_primary_loss_below_one {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    PPrimaryLabel.outer 1-PPrimaryLabel.outer a≤(271/250)*(1-a) := by
  have hdom {t : ℝ} (ht : t∈Icc a 1) : t∈Icc outerDiagonal outerAxial :=
    ⟨ha.1.trans ht.1,ht.2.trans primary_one_mem.2⟩
  have hm : MonotoneOn (fun t => (271/250)*t-PPrimaryLabel.outer t) (Icc a 1) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (PPrimaryLabel.affine_difference_hasDerivAt (271/250)
        (primary_domain (hdom ht))).continuousAt.continuousWithinAt)
      (fun t ht => PPrimaryLabel.affine_difference_hasDerivAt (271/250)
        (primary_domain (hdom (Ioo_subset_Icc_self ht))))
      (fun t ht => by
        have hh := M_first_monotone (hdom (Ioo_subset_Icc_self ht)) primary_one_mem ht.2.le
        linarith [M_one_first.2])
  have hh := hm ⟨le_rfl,ha.2⟩ ⟨ha.2,le_rfl⟩ ha.2
  linarith

theorem original_upper_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 0 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hcut : b≤upperCut A B x := by
    have hw := upper_width hx
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
    dsimp [upperCut]
    linarith
  have hdisp : b+1-A≤(2/5)*x := by
    linarith [upper_secondary_displacement ht hx]
  have hb := source_mem hs
  by_cases hA : 1≤A
  · have hl : A-1∈Icc 0 outerDiagonal := by
      constructor
      · linarith
      · linarith [(outer_bounds ht).2.1,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]
    have hbase := aligned_left_original (ShortOuterOne.SameContact.arc_state hl) ht
      (show 1+(A-1)≤A by linarith)
    by_cases hbl : b≤A-1
    · have hP := P_monotone hb hl hbl
      dsimp [value] at *
      linarith [hx.1]
    · have hP := P_upper_increment hl hb (by linarith)
      dsimp [value] at *
      nlinarith [hx.1]
  · have ha : A∈Icc outerDiagonal 1 := ⟨(outer_bounds ht).1,by linarith⟩
    have htarget := target_primary_loss_below_one ha
    have hactual : VPrimaryLabel.outer A= -V B := VLabel.primary_actual ht
    have hone : VPrimaryLabel.outer 1= -V bOne := VLabel.primary_actual (primary_state primary_one_mem)
    rw [hactual,hone] at htarget
    have hsource := P_upper_increment outer_zero_mem hb hb.1
    have hgap := mul_nonneg (show 0≤1-A by linarith)
      (show (0:ℝ)≤973/1000-11/25 by norm_num)
    have hbase := reverse_aligned_axial_value
    dsimp [value]
    nlinarith [hx.1]

theorem original_upper_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 2 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hcut : B≤upperCut a b x := by
    have hw := upper_width hx
    norm_num [forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
    dsimp [upperCut]
    linarith
  have hdisp : B+1-a≤(2/5)*x := by
    linarith [upper_secondary_displacement hs hx]
  have hB := source_mem ht
  by_cases ha : 1≤a
  · have hl : a-1∈Icc 0 outerDiagonal := by
      constructor
      · linarith
      · linarith [(outer_bounds hs).2.1,outer_endpoint_bounds.2.1,fine_outer_endpoint_bounds.2]
    have hbase := aligned_right_original hs (ShortOuterOne.SameContact.arc_state hl)
      (show 1+(a-1)≤a by linarith)
    by_cases hBl : B≤a-1
    · have hV := V_monotone hB hl hBl
      dsimp [value] at *
      linarith [hx.1]
    · have hV := V_upper_increment hl hB (by linarith)
      dsimp [value] at *
      nlinarith [hx.1]
  · have hA : a∈Icc outerDiagonal 1 := ⟨(outer_bounds hs).1,by linarith⟩
    have hsource := source_primary_loss_below_one hA
    have hactual : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
    have hone : PPrimaryLabel.outer 1= -P bOne := PLabel.primary_actual (primary_state primary_one_mem)
    rw [hactual,hone] at hsource
    have htarget := V_upper_increment outer_zero_mem hB hB.1
    have hgap := mul_nonneg hB.1 (show (0:ℝ)≤271/250-1061/1000 by norm_num)
    have hbase := aligned_axial_value
    dsimp [value]
    nlinarith [hx.1]

end SquaresInCircles.Eight.SecondWord.OppositeTwo
