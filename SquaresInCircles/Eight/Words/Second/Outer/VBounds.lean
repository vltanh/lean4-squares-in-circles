module

public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoContactCap
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners

/-!
# Eight squares: source chords and strict circle derivatives for positive edge three

Both chords follow from strict concavity and their two actual endpoint
values.  The additional derivative references are single rational
coordinates with radicals enclosed by exact integer squares.
-/

section
/-!
## Full-circle bounds for the second-word target label `K`

The third and fourth derivative signs follow from their exact circle
numerators.  They give the global slope bounds, strict concavity and
the chord used by the original negative edge-three owners.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

open CommonQuarter CorePairGeometry Arithmetic

lemma K_third_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : KLabel.d3 b<0 := by
  have he := KLabel.third_numerator (outer_domain hb)
  have hu := pow_pos (U_positive (outer_domain hb)) 5
  have hw := (UW_bounds hb).2.2
  have hneg : KLabel.d3 b*(U b)^5<0 := by
    rw [he]
    simp only [KLabel]
    norm_num [Q0]
    linarith [hw.2]
  exact neg_of_mul_neg_left hneg hu.le

lemma K_fourth_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : KLabel.d4 b<0 := by
  have he := KLabel.fourth_numerator (outer_domain hb)
  have hu := pow_pos (U_positive (outer_domain hb)) 7
  have hw := (UW_bounds hb).2.2
  have hs : (W b)^2<(7/5:ℝ)^2 := by nlinarith
  have hneg : KLabel.d4 b*(U b)^7<0 := by
    rw [he]
    simp only [KLabel]
    norm_num [Q0] at hs ⊢
    linarith [hw.1]
  exact neg_of_mul_neg_left hneg hu.le

lemma K_second_antitone : AntitoneOn KLabel.d2 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hb => (KLabel.d2_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun _ hb => KLabel.d2_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun _ hb => (K_third_negative (Ioo_subset_Icc_self hb)).le)

lemma K_third_antitone : AntitoneOn KLabel.d3 (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hb => (KLabel.d3_hasDerivAt (outer_domain hb)).continuousAt.continuousWithinAt)
    (fun _ hb => KLabel.d3_hasDerivAt (outer_domain (Ioo_subset_Icc_self hb)))
    (fun _ hb => (K_fourth_negative (Ioo_subset_Icc_self hb)).le)

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
  have hU : U 0<(19147/10000:ℝ) := by linarith [hu.2]
  have hh := pow_le_pow_left₀ hp.le hU.le 5
  have hpos := pow_pos hp 5
  have hneg : KLabel.d3 0*(U 0)^5< -(371/500)*(19147/10000:ℝ)^5 := by
    rw [he]
    simp only [KLabel,W]
    norm_num [Q0]
  by_contra hcon
  have h1 := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hpos.le
  have h2 := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤371/500)
  linarith

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

lemma K_chord {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    K 0+(7/10)*b≤K b := by
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal) (fun t => K t-K 0-(7/10)*t) :=
    concave_of_deriv2 (f' := fun t => KLabel.d1 t-7/10) (f'' := KLabel.d2)
      (fun t ht => (((KLabel.outer_hasDerivAt (outer_domain ht)).sub_const (K 0)).sub
        ((hasDerivAt_id' t).const_mul (7/10))).congr_deriv (by ring))
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

end SquaresInCircles.Eight.SecondWord
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

lemma V_zero : V 0= -(41/4000)*outerAxial := by
  norm_num [V,RoleLabel.outer,RoleLabel.eval,VLabel,ShortOuterOne.SameContact.arc_zero]

lemma V_zero_bounds : (-29/2000:ℝ)<V 0 ∧ V 0< -1449/100000 := by
  rw [V_zero]
  constructor <;> linarith [ShortOuterZero.fine_axial_bounds.1,
    ShortOuterZero.fine_axial_bounds.2]

lemma V_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (-29/2000:ℝ)<V b :=
  V_zero_bounds.1.trans_le (V_monotone outer_zero_mem hb hb.1)

lemma V_concave : ConcaveOn ℝ (Icc 0 outerDiagonal) V :=
  concave_of_deriv2
    (fun b hb => VLabel.outer_hasDerivAt (outer_domain hb))
    (fun b hb => VLabel.d1_hasDerivAt (outer_domain hb))
    (fun b hb => by linarith [V_second_upper hb])

lemma V_diagonal : V outerDiagonal=(7503/50000)*outerDiagonal+
    (63457/100000)*outerDiagonal^2 := by
  dsimp [V,RoleLabel.outer,RoleLabel.eval,VLabel]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  ring

lemma V_diagonal_bounds : (648/1000:ℝ)<V outerDiagonal ∧
    V outerDiagonal<6481/10000 := by
  rw [V_diagonal]
  have hh := diagonal_fine
  have hlo : (89921406510940/100000000000000:ℝ)^2<outerDiagonal^2 := by
    nlinarith [hh.1]
  have hhi : outerDiagonal^2<(89921406510941/100000000000000:ℝ)^2 := by
    nlinarith [hh.1,hh.2]
  constructor <;> nlinarith [hh.1,hh.2]

lemma V_chord {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    V 0+(92/125)*b≤V b := by
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal)
      (fun t => V t-V 0-(92/125)*t) :=
    concave_of_deriv2 (f' := fun t => VLabel.d1 t-92/125)
      (fun t ht => (((VLabel.outer_hasDerivAt (outer_domain ht)).sub_const (V 0)).sub
        ((hasDerivAt_id' t).const_mul (92/125))).congr_deriv (by ring))
      (fun t ht => (VLabel.d1_hasDerivAt (outer_domain ht)).sub_const (92/125))
      (fun t ht => by linarith [V_second_upper ht])
  have hr : 0<V outerDiagonal-V 0-(92/125)*outerDiagonal := by
    linarith [V_diagonal_bounds.1,V_zero_bounds.2,diagonal_fine.2]
  have hh := hc.min_le_of_mem_Icc outer_zero_mem
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩) hb
  have hz : V 0-V 0-(92/125)*0=0 := by ring
  rw [hz,min_eq_left hr.le] at hh
  linarith

lemma V_short_mem : (7/20:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma V_short_chord_end : V 0+(49/50)*(7/20)<V (7/20) := by
  have hu := shifted_chart_reference (outer_domain V_short_mem)
    (l := (178692473260627/100000000000000:ℝ))
    (u := (178692473260628/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have he : V (7/20)= -(41/4000)*(U (7/20)-1/2)+
      (16031/100000)*(7/20)+(63457/100000)*(U (7/20)-1/2)*(7/20) := by
    dsimp [V,RoleLabel.outer,RoleLabel.eval,VLabel,U]
    ring
  rw [he]
  linarith [hu.1,V_zero_bounds.2]

lemma V_chord_short {b : ℝ} (hb : b∈Icc 0 (7/20)) :
    V 0+(49/50)*b≤V b := by
  have hdom : Icc (0:ℝ) (7/20)⊆Icc 0 outerDiagonal := by
    intro t ht
    exact ⟨ht.1,ht.2.trans V_short_mem.2⟩
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (7/20))
      (fun t => V t-V 0-(49/50)*t) :=
    concave_of_deriv2 (f' := fun t => VLabel.d1 t-49/50)
      (fun t ht => (((VLabel.outer_hasDerivAt (outer_domain (hdom ht))).sub_const (V 0)).sub
        ((hasDerivAt_id' t).const_mul (49/50))).congr_deriv (by ring))
      (fun t ht => (VLabel.d1_hasDerivAt (outer_domain (hdom ht))).sub_const (49/50))
      (fun t ht => by linarith [V_second_upper (hdom ht)])
  have hh := hc.min_le_of_mem_Icc (by norm_num) (by norm_num) hb
  have hz : V 0-V 0-(49/50)*0=0 := by ring
  have hr : 0<V (7/20)-V 0-(49/50)*(7/20) := by linarith [V_short_chord_end]
  rw [hz,min_eq_left hr.le] at hh
  linarith

lemma V_zero_first_lower : (1303/1250:ℝ)<VLabel.d1 0 := by
  have hr := (outer_ratio_bounds outer_zero_mem).1
  norm_num [RoleLabel.d1,VLabel,ShortOuterOne.SameContact.arc_zero]
  linarith [fine_outer_endpoint_bounds.1]

lemma V_tenth_second_upper : VLabel.d2 (1/10)<(-217/500:ℝ) := by
  have hh := VLabel.second_chart_reference
    (outer_domain (Asymmetric.rational_outer_mem (show (1/10:ℝ)∈Icc 0 (899/1000) by norm_num)))
    (l := (188562986824031/100000000000000:ℝ))
    (u := (188562986824032/100000000000000:ℝ))
    (dlo := (-1:ℝ)) (dhi := (-217/500:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [VLabel,W,Q0]) (by norm_num [VLabel,W,Q0])
  exact hh.2

lemma V_second_late {b : ℝ} (hb : b∈Icc (1/10) outerDiagonal) :
    VLabel.d2 b<(-217/500:ℝ) :=
  (V_second_antitone
    (Asymmetric.rational_outer_mem (show (1/10:ℝ)∈Icc 0 (899/1000) by norm_num))
    ⟨by linarith [hb.1],hb.2⟩ hb.1).trans_lt V_tenth_second_upper

lemma outer_ratioDD_comparison {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    ratioDD b<(43/20)*ratioD b := by
  have hu := U_positive (outer_domain hb)
  have hd := (outer_ratio_bounds hb).2.2.1
  have hh := UW_bounds hb
  have hquot : 3*W b/(U b)^2<(43/20:ℝ) := by
    apply (div_lt_iff₀ (sq_pos_of_pos hu)).2
    have hsq : (1399/1000:ℝ)^2<(U b)^2 := by nlinarith [hh.1]
    nlinarith [hh.2.2.2]
  rw [ratioDD_formula hb]
  exact mul_lt_mul_of_pos_right hquot hd

end SquaresInCircles.Eight.SecondWord
end
end
end
