module

public import SquaresInCircles.Eight.TableFree.SecondOuterHigherCalculus
public import SquaresInCircles.Eight.TableFree.SecondOuterFixedReference
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoContactCap

/-!
# Full-circle bounds for the second-word target label `K`

The third and fourth derivative signs follow from their exact circle
numerators.  They give the global slope bounds, strict concavity and
the chord used by the original negative edge-three owners.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic

lemma K_third_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : KLabel.d3 b<0 := by
  have he := KLabel.third_numerator (outer_domain hb)
  have hu := pow_pos (U_positive (outer_domain hb)) 5
  have hw := (UW_bounds hb).2.2
  norm_num [KLabel,Q0] at he
  nlinarith

lemma K_fourth_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : KLabel.d4 b<0 := by
  have he := KLabel.fourth_numerator (outer_domain hb)
  have hu := pow_pos (U_positive (outer_domain hb)) 7
  have hw := (UW_bounds hb).2.2
  have hs : (W b)^2<(7/5:ℝ)^2 := by nlinarith
  norm_num [KLabel,Q0] at he
  nlinarith

lemma K_second_antitone : AntitoneOn KLabel.d2 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (KLabel.d2_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => KLabel.d2_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => (K_third_negative (Ioo_subset_Icc_self hb)).le)

lemma K_third_antitone : AntitoneOn KLabel.d3 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (KLabel.d3_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => KLabel.d3_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => (K_fourth_negative (Ioo_subset_Icc_self hb)).le)

lemma K_zero_second : KLabel.d2 0<(-221/1000:ℝ) := by
  have hh := KLabel.second_chart_reference (outer_domain outer_zero_mem)
    (l := (191457567100389/100000000000000:ℝ))
    (u := (191457567100390/100000000000000:ℝ))
    (dlo := (-1:ℝ)) (dhi := (-221/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [KLabel,W,Q0]) (by norm_num [KLabel,W,Q0])
  exact hh.2

lemma K_second_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    KLabel.d2 b<(-221/1000:ℝ) :=
  (K_second_antitone outer_zero_mem hb hb.1).trans_lt K_zero_second

lemma K_zero_third : KLabel.d3 0<(-371/500:ℝ) := by
  have hu := NegativeTwo.TargetContact.Cap.zero_source_fine
  have hp := U_positive (outer_domain outer_zero_mem)
  have he := KLabel.third_numerator (outer_domain outer_zero_mem)
  have hh := pow_le_pow_left₀ hp.le hu.2.le 5
  have hpos := pow_pos hp 5
  norm_num [KLabel,W,Q0] at he hh
  nlinarith

lemma K_third_upper {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    KLabel.d3 b<(-371/500:ℝ) :=
  (K_third_antitone outer_zero_mem hb hb.1).trans_lt K_zero_third

lemma K_first_antitone : AntitoneOn KLabel.d1 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (KLabel.d1_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => KLabel.d1_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [K_second_upper (Ioo_subset_Icc_self hb)])

lemma K_zero_first : KLabel.d1 0<(116/125:ℝ) := by
  have hh := KLabel.first_chart_reference (outer_domain outer_zero_mem)
    (l := (191457567100389/100000000000000:ℝ))
    (u := (191457567100390/100000000000000:ℝ))
    (dlo := (0:ℝ)) (dhi := (116/125:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [KLabel,W,Q0]) (by norm_num [KLabel,W,Q0])
  exact hh.2

lemma K_first_diagonal : KLabel.d1 outerDiagonal=(15601/50000:ℝ) := by
  dsimp [RoleLabel.d1,KLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal,ratio_diagonal]
  ring

lemma K_first_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (31/100:ℝ)<KLabel.d1 b ∧ KLabel.d1 b<116/125 := by
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hlo := K_first_antitone hb hd hb.2
  rw [K_first_diagonal] at hlo
  exact ⟨by linarith,(K_first_antitone outer_zero_mem hb hb.1).trans_lt K_zero_first⟩

lemma K_monotone : MonotoneOn K (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (KLabel.outer_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun b hb => KLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun b hb => by linarith [(K_first_bounds (Ioo_subset_Icc_self hb)).1])

lemma K_zero : K 0= -(66/3125)*outerAxial := by
  norm_num [K,RoleLabel.outer,RoleLabel.eval,KLabel,ShortOuterOne.SameContact.arc_zero]

lemma K_zero_bounds : (-2989/100000:ℝ)<K 0 ∧ K 0< -2987/100000 := by
  rw [K_zero]
  constructor <;> linarith [fine_outer_endpoint_bounds.1,outer_endpoint_bounds.2.1]

lemma K_diagonal : K outerDiagonal=(13489/50000)*outerDiagonal+
    (22321/50000)*outerDiagonal^2 := by
  dsimp [K,RoleLabel.outer,RoleLabel.eval,KLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  ring

lemma K_diagonal_lower : (603/1000:ℝ)<K outerDiagonal := by
  rw [K_diagonal]
  have hd := fine_outer_endpoint_bounds.2
  have hs : (899/1000:ℝ)^2<outerDiagonal^2 := by nlinarith
  nlinarith

lemma K_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : K 0≤K b :=
  K_monotone outer_zero_mem hb hb.1

lemma K_concave : ConcaveOn ℝ (Icc 0 outerDiagonal) K :=
  concave_of_deriv2
    (fun b hb => KLabel.outer_hasDerivAt (outer_domain hb))
    (fun b hb => KLabel.d1_hasDerivAt (outer_domain hb))
    (fun b hb => by linarith [K_second_upper hb])

lemma K_chord {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    K 0+(7/10)*b≤K b := by
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal) (fun t => K t-K 0-(7/10)*t) :=
    concave_of_deriv2
      (fun t ht => ((KLabel.outer_hasDerivAt (outer_domain ht)).sub_const (K 0)).sub
        ((hasDerivAt_id t).const_mul (7/10)))
      (fun t ht => (KLabel.d1_hasDerivAt (outer_domain ht)).sub_const (7/10))
      (fun t ht => by linarith [K_second_upper ht])
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hright : 0<K outerDiagonal-K 0-(7/10)*outerDiagonal := by
    linarith [K_diagonal_lower,K_zero_bounds.2,outer_endpoint_bounds.2.2.2]
  have hm := hc.min_le_of_mem_Icc outer_zero_mem hd hb
  have hleft : K 0-K 0-(7/10)*0=0 := by ring
  rw [hleft,min_eq_left hright.le] at hm
  linarith

lemma K_increment_upper {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (h : b≤B) :
    K B-K b≤(116/125)*(B-b) := by
  have hm : AntitoneOn (fun t => K t-(116/125)*t) (Icc 0 outerDiagonal) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => ((KLabel.outer_hasDerivAt (outer_domain ht)).sub
        ((hasDerivAt_id t).const_mul (116/125))).continuousAt.continuousWithinAt)
      (fun t ht => (KLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self ht))).sub
        ((hasDerivAt_id t).const_mul (116/125)))
      (fun t ht => by linarith [(K_first_bounds (Ioo_subset_Icc_self ht)).2])
  have hh := hm hb hB h
  linarith

lemma K_first_small {b : ℝ} (hb : b∈Icc 0 (101/1000)) :
    (901/1000:ℝ)<KLabel.d1 b := by
  have href : (101/1000:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hh := KLabel.first_chart_reference (outer_domain href)
    (l := (18853/10000:ℝ)) (u := (9427/5000:ℝ))
    (dlo := (901/1000:ℝ)) (dhi := (1:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [KLabel,W,Q0]) (by norm_num [KLabel,W,Q0])
  exact hh.1.trans_le (K_first_antitone ⟨hb.1,hb.2.trans href.2⟩ href hb.2)

lemma T_six_value : T (3/5)<(1/2:ℝ) := by
  have hu := shifted_chart_reference (outer_domain T_six_mem)
    (l := (1028/625:ℝ)) (u := (16449/10000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := FixedReference.target T_six_mem ⟨le_rfl,le_rfl⟩ ⟨hu.1.le,hu.2.le⟩
    (by norm_num) (by norm_num)
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord
