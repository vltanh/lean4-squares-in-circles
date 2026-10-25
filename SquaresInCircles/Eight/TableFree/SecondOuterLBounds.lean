module

public import SquaresInCircles.Eight.TableFree.SecondOuterHigherCalculus
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoLabels

/-!
# Whole-arc bounds for the literal positive target label

The first derivative is convex on the entire physical circle arc.  Its
two endpoint values bound it from above.  Its minimum is controlled by
one tangent at `1/2` and the curvature signs at `1/2` and `11/20`.
All reference radicals are proved by exact square comparisons.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma L_third_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<LLabel.d3 b := by
  have hd := (outer_ratio_bounds hb).2.2.1
  have hdd := ratioDD_positive hb
  have hm := mul_nonneg hb.1 hdd.le
  norm_num [RoleLabel.d3,LLabel]
  nlinarith

lemma L_fourth_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<LLabel.d4 b := by
  have he := LLabel.fourth_numerator (outer_domain hb)
  have hp := pow_pos (U_positive (outer_domain hb)) 7
  have hk := fourth_kernel_positive hb
  have hQ : (0:ℝ)<Q0 := by norm_num [Q0]
  have hval : -3*Q0*((LLabel.p-LLabel.s/2)*(Q0+4*(W b)^2)+5*LLabel.s*Q0*W b)=
      3*Q0*(94721/50000)*(5*Q0*W b-Q0/2-2*(W b)^2) := by
    simp only [LLabel]
    ring
  have hpos : 0<LLabel.d4 b*(U b)^7 := by
    rw [he,hval]
    exact mul_pos (by positivity) hk
  exact pos_of_mul_pos_left hpos hp.le

lemma L_second_monotone : MonotoneOn LLabel.d2 (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (LLabel.d2_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => LLabel.d2_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => (L_third_positive (Ioo_subset_Icc_self hb)).le)

lemma L_third_monotone : MonotoneOn LLabel.d3 (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (LLabel.d3_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => LLabel.d3_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => (L_fourth_positive (Ioo_subset_Icc_self hb)).le)

lemma L_half_mem : (1/2:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma L_eleven_twentieths_mem : (11/20:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma L_half_first : (78/125:ℝ)<LLabel.d1 (1/2) := by
  have hh := LLabel.first_chart_reference (outer_domain L_half_mem)
    (l := (170751281107931/100000000000000:ℝ))
    (u := (170751281107932/100000000000000:ℝ))
    (dlo := (78/125:ℝ)) (dhi := (1:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact hh.1

lemma L_half_second : (-4/125:ℝ)<LLabel.d2 (1/2) ∧ LLabel.d2 (1/2)<0 := by
  exact LLabel.second_chart_reference (outer_domain L_half_mem)
    (l := (170751281107931/100000000000000:ℝ))
    (u := (170751281107932/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])

lemma L_eleven_twentieths_second : 0<LLabel.d2 (11/20) := by
  have hh := LLabel.second_chart_reference (outer_domain L_eleven_twentieths_mem)
    (l := (167722985902350/100000000000000:ℝ))
    (u := (167722985902351/100000000000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (1:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [LLabel,W,Q0]) (by norm_num [LLabel,W,Q0])
  exact hh.1

lemma L_second_early {b : ℝ} (hb : b∈Icc 0 (1/2)) : LLabel.d2 b<0 :=
  (L_second_monotone ⟨hb.1,hb.2.trans L_half_mem.2⟩ L_half_mem hb.2).trans_lt
    L_half_second.2

lemma L_second_late {b : ℝ} (hb : b∈Icc (11/20) outerDiagonal) :
    0<LLabel.d2 b :=
  L_eleven_twentieths_second.trans_le
    (L_second_monotone L_eleven_twentieths_mem ⟨by linarith [hb.1],hb.2⟩ hb.1)

lemma L_first_early_antitone : AntitoneOn LLabel.d1 (Icc 0 (1/2)) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (LLabel.d1_hasDerivAt
      (outer_domain ⟨hb.1,hb.2.trans L_half_mem.2⟩)).continuousAt.continuousWithinAt)
    (fun b hb => LLabel.d1_hasDerivAt
      (outer_domain ⟨le_of_lt hb.1,(le_of_lt hb.2).trans L_half_mem.2⟩))
    (fun b hb => (L_second_early (Ioo_subset_Icc_self hb)).le)

lemma L_first_late_monotone : MonotoneOn LLabel.d1 (Icc (11/20) outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (LLabel.d1_hasDerivAt
      (outer_domain ⟨by linarith [hb.1],hb.2⟩)).continuousAt.continuousWithinAt)
    (fun b hb => LLabel.d1_hasDerivAt
      (outer_domain ⟨by linarith [hb.1],le_of_lt hb.2⟩))
    (fun b hb => (L_second_late (Ioo_subset_Icc_self hb)).le)

lemma L_first_middle {b : ℝ} (hb : b∈Icc (1/2) (11/20)) :
    (389/625:ℝ)<LLabel.d1 b := by
  have hdom : Icc (1/2:ℝ) (11/20)⊆Icc 0 outerDiagonal := by
    intro t ht
    exact ⟨by linarith [ht.1],ht.2.trans L_eleven_twentieths_mem.2⟩
  have hh := curvature_tangent (f := LLabel.d1) (d := LLabel.d2)
    (dd := LLabel.d3) (κ := 0) hb
    (show (1/2:ℝ)∈Icc (1/2) (11/20) by norm_num)
    (fun t ht => LLabel.d1_hasDerivAt (outer_domain (hdom ht)))
    (fun t ht => LLabel.d2_hasDerivAt (outer_domain (hdom ht)))
    (fun t ht => (L_third_positive (hdom ht)).le)
  have hp := mul_nonneg (sub_nonneg.mpr L_half_second.1.le)
    (sub_nonneg.mpr hb.1)
  nlinarith [L_half_first,hb.1,hb.2]

lemma L_first_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (311/500:ℝ)<LLabel.d1 b := by
  by_cases he : b≤1/2
  · have hh := L_first_early_antitone ⟨hb.1,he⟩ (by norm_num) he
    linarith [L_half_first]
  · by_cases hm : b≤11/20
    · linarith [L_first_middle ⟨by linarith,hm⟩]
    · have hh := L_first_late_monotone
        (show (11/20:ℝ)∈Icc (11/20) outerDiagonal from
          ⟨le_rfl,L_eleven_twentieths_mem.2⟩)
        ⟨by linarith,hb.2⟩ (by linarith)
      linarith [L_first_middle (show (11/20:ℝ)∈Icc (1/2) (11/20) by norm_num)]

lemma L_first_zero : LLabel.d1 0<(147/125:ℝ) := by
  norm_num [RoleLabel.d1,LLabel,ShortOuterOne.SameContact.arc_zero]
  linarith [fine_outer_endpoint_bounds.1]

lemma L_first_diagonal : LLabel.d1 outerDiagonal=
    38551/10000-(37437/12500)*outerDiagonal := by
  dsimp [RoleLabel.d1,LLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal,ratio_diagonal]
  ring

lemma L_first_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    LLabel.d1 b<(147/125:ℝ) := by
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal) (fun t => -LLabel.d1 t) :=
    concave_of_deriv2
      (fun t ht => (LLabel.d1_hasDerivAt (outer_domain ht)).neg)
      (fun t ht => (LLabel.d2_hasDerivAt (outer_domain ht)).neg)
      (fun t ht => neg_nonpos.mpr (L_third_positive ht).le)
  have hdiag : LLabel.d1 outerDiagonal<(147/125:ℝ) := by
    rw [L_first_diagonal]
    linarith [fine_outer_endpoint_bounds.2]
  have hh := hc.min_le_of_mem_Icc outer_zero_mem
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩) hb
  have hlo : -(147/125:ℝ)< min (-LLabel.d1 0) (-LLabel.d1 outerDiagonal) :=
    lt_min (by linarith [L_first_zero]) (by linarith)
  linarith

lemma L_first_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (311/500:ℝ)<LLabel.d1 b ∧ LLabel.d1 b<147/125 :=
  ⟨L_first_lower hb,L_first_upper hb⟩

lemma L_monotone : MonotoneOn L (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (LLabel.outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => LLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [L_first_lower (Ioo_subset_Icc_self hb)])

lemma L_zero : L 0=(793/20000:ℝ) := by
  norm_num [L,RoleLabel.outer,RoleLabel.eval,LLabel]

lemma L_diagonal : L outerDiagonal=(793/20000:ℝ)+
    (38551/10000)*outerDiagonal-(33919/10000)*outerDiagonal^2 := by
  dsimp [L,RoleLabel.outer,RoleLabel.eval,LLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  ring

lemma L_diagonal_upper : L outerDiagonal<(95446/125000:ℝ) := by
  rw [L_diagonal]
  have hh := diagonal_fine
  have hs : (89921406510940/100000000000000:ℝ)^2<outerDiagonal^2 := by
    nlinarith [hh.1]
  nlinarith [hh.2]

lemma L_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    L b<(95446/125000:ℝ) :=
  (L_monotone hb ⟨outer_zero_mem.2,le_rfl⟩ hb.2).trans_lt L_diagonal_upper

lemma L_increment_upper {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (h : b≤B) :
    L B-L b≤(147/125)*(B-b) := by
  have hm : AntitoneOn (fun t => L t-(147/125)*t) (Icc 0 outerDiagonal) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => ((LLabel.outer_hasDerivAt (outer_domain ht)).sub
        ((hasDerivAt_id t).const_mul (147/125))).continuousAt.continuousWithinAt)
      (fun t ht => (LLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self ht))).sub
        ((hasDerivAt_id t).const_mul (147/125)))
      (fun t ht => by linarith [L_first_upper (Ioo_subset_Icc_self ht)])
  have hh := hm hb hB h
  linarith

lemma L_axial_line {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    L b≤(793/20000:ℝ)+(147/125)*b := by
  have hh := L_increment_upper outer_zero_mem hb hb.1
  rw [L_zero] at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord
