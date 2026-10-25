module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroContactGeometry

/-!
# Strict decrease of the last mixed negative contact

The exact contact's third derivative is below `-1/2`. At the single
reference angle `.14`, its first derivative is below `-.0055` and its
second derivative has absolute value below `.005`. Strong concavity
therefore makes the first derivative negative everywhere. One final
contact value supplies the original strict `.898` cost bound.

The original separator pays the actual target-core slack during the
comparison to the contact, so neither square is silently replaced.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero.SmallContact

open CommonQuarter CorePairGeometry Arithmetic

def reference : ℝ := 7/50

lemma reference_trig :
    (1395431146/10000000000:ℝ)<Real.sin reference ∧
      Real.sin reference<1395431150/10000000000 ∧
      (9902159962/10000000000:ℝ)<Real.cos reference ∧
      Real.cos reference<9902159963/10000000000 := by
  have hs := sin_lower_seven (x := reference) (by norm_num [reference])
  have hsU := sin_upper_five (x := reference) (by norm_num [reference])
  have hc := cos_lower_six (x := reference) (by norm_num [reference])
  have hcU := cos_le_cos8 (x := reference) (by norm_num [reference])
  simp only [reference] at hs hsU hc hcU ⊢
  norm_num [cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma reference_coordinates :
    (5894167/10000000:ℝ)<b reference ∧ b reference<5894168/10000000 ∧
      (10567876/10000000:ℝ)<bd reference ∧ bd reference<10567878/10000000 := by
  have ht := reference_trig
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hu : 0≤1/2+CoreAngleEndpoint.diagonal := by linarith [hd.1]
  have hv : 0≤CoreAngleEndpoint.diagonal-1/2 := by linarith [hd.1]
  have hsL := mul_le_mul_of_nonneg_left ht.1.le hu
  have hsU := mul_le_mul_of_nonneg_left ht.2.1.le hu
  have hcL := mul_le_mul_of_nonneg_left ht.2.2.1.le hv
  have hcU := mul_le_mul_of_nonneg_left ht.2.2.2.le hv
  have hcL' := mul_le_mul_of_nonneg_left ht.2.2.1.le hu
  have hcU' := mul_le_mul_of_nonneg_left ht.2.2.2.le hu
  have hsL' := mul_le_mul_of_nonneg_left ht.1.le hv
  have hsU' := mul_le_mul_of_nonneg_left ht.2.1.le hv
  dsimp [b,bd]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [hd.1,hd.2]

lemma reference_root : (16518992/10000000:ℝ)<Y (b reference) ∧
    Y (b reference)<16518994/10000000 := by
  have hr : reference∈Icc 0 smallCap := by norm_num [reference,smallCap]
  have hp := Y_pos (curve_domain hr)
  have hs := Y_sq (curve_domain hr)
  have hb := reference_coordinates
  have hbL := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5894167/10000000+1/2)
    (show (5894167/10000000:ℝ)+1/2≤b reference+1/2 by linarith [hb.1]) 2
  have hbU := pow_le_pow_left₀ (show 0≤b reference+1/2 by linarith [hb.1])
    (show b reference+1/2≤(5894168/10000000:ℝ)+1/2 by linarith [hb.2.1]) 2
  norm_num [Q0] at hs
  constructor <;> nlinarith

lemma reference_radial_derivatives :
    (9409714/10000000:ℝ)<fd (b reference) ∧ fd (b reference)<9409717/10000000 ∧
      (793342/10000000:ℝ)<fdd (b reference) ∧ fdd (b reference)<793345/10000000 := by
  have hb := reference_coordinates
  have hy := reference_root
  have hypos : 0<Y (b reference) := by linarith [hy.1]
  have hy3L := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤16518992/10000000) hy.1.le 3
  have hy3U := pow_le_pow_left₀ hypos.le hy.2.le 3
  refine ⟨?_,?_,?_,?_⟩
  · have hh : (9409714/10000000:ℝ)-88074/100000<e*(b reference+1/2)/Y (b reference) := by
      apply (lt_div_iff₀ hypos).2
      norm_num [e]
      nlinarith [hb.1,hy.2]
    dsimp [fd]
    linarith
  · have hh : e*(b reference+1/2)/Y (b reference)<(9409717/10000000:ℝ)-88074/100000 := by
      apply (div_lt_iff₀ hypos).2
      norm_num [e]
      nlinarith [hb.2.1,hy.1]
    dsimp [fd]
    linarith
  · rw [fdd,lt_div_iff₀ (pow_pos hypos 3)]
    norm_num [e,Q0] at hy3U ⊢
    nlinarith
  · rw [fdd,div_lt_iff₀ (pow_pos hypos 3)]
    norm_num [e,Q0] at hy3L ⊢
    nlinarith

lemma reference_derivatives : Hd reference< -(11/2000:ℝ) ∧ |Hdd reference|<(1/200:ℝ) := by
  have hb := reference_coordinates
  have hf := reference_radial_derivatives
  have hbd0 : 0≤bd reference := by linarith [hb.2.2.1]
  have hfd0 : 0≤fd (b reference) := by linarith [hf.1]
  have hfdd0 : 0≤fdd (b reference) := by linarith [hf.2.2.1]
  have hprod := mul_le_mul hf.2.1.le hb.2.2.2.le hbd0 (by norm_num)
  have hsqL := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10567876/10000000) hb.2.2.1.le 2
  have hsqU := pow_le_pow_left₀ hbd0 hb.2.2.2.le 2
  have hposL := mul_le_mul hf.2.2.1.le hsqL (by positivity) hfdd0
  have hposU := mul_le_mul hf.2.2.2.le hsqU (sq_nonneg (bd reference)) (by norm_num)
  have hbL : (5894167/10000000:ℝ)-1/2≤b reference-1/2 := by linarith [hb.1]
  have hbU : b reference-1/2≤(5894168/10000000:ℝ)-1/2 := by linarith [hb.2.1]
  have hnegL := mul_le_mul hf.1.le hbL (by norm_num) hfd0
  have hnegU := mul_le_mul hf.2.1.le hbU (by linarith [hb.1]) (by norm_num)
  constructor
  · dsimp [Hd]
    nlinarith
  · rw [abs_lt]
    dsimp [Hdd,bdd]
    constructor <;> nlinarith

/-- One reference point and the proved negative third derivative make
the exact first derivative strictly negative on the whole contact. -/
lemma Hd_negative {x : ℝ} (hx : x∈Icc 0 smallCap) : Hd x<0 := by
  have hr : reference∈Icc 0 smallCap := by norm_num [reference,smallCap]
  have hder := reference_derivatives
  have hval : (-Hdd reference)^2<2*(1/2:ℝ)*(-Hd reference) := by
    have hab := abs_lt.mp hder.2
    have hs : (Hdd reference)^2<(1/200:ℝ)^2 := by nlinarith [hab.1,hab.2]
    nlinarith [hder.1]
  have hh := positive_of_curvature (κ := (1/2:ℝ)) (by norm_num) hx hr
    (f := fun z => -Hd z) (d := fun z => -Hdd z) (dd := fun z => -Hddd z)
    (fun z hz => (Hd_hasDerivAt hz).neg)
    (fun z hz => (Hdd_hasDerivAt hz).neg)
    (fun z hz => by linarith [Hddd_negative hz]) hval
  linarith

lemma H_antitone : AntitoneOn H (Icc 0 smallCap) :=
  antiOn_of_hasDeriv_nonpos (fun x hx => (H_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun x hx => H_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun x hx => (Hd_negative (Ioo_subset_Icc_self hx)).le)

lemma endpoint_root_upper : Y (b smallCap)<(69961/50000:ℝ) := by
  have hx : smallCap∈Icc 0 smallCap := by norm_num [smallCap]
  have hp := Y_pos (curve_domain hx)
  have hs := Y_sq (curve_domain hx)
  have hb := endpoint_b.1
  have hb2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤449609/500000+1/2)
    (show (449609/500000:ℝ)+1/2≤b smallCap+1/2 by linarith) 2
  norm_num [Q0] at hs
  nlinarith

lemma H_endpoint : (449/500:ℝ)<H smallCap := by
  have hy := endpoint_root_upper
  have hb := endpoint_b.1
  have hc := CoreAngleEndpoint.diagonal_bounds.1
  have hsc : smallCap=5519/12500 := rfl
  have hH : H smallCap=-smallCap+28271/100000+
      (-(9133/100000)*(Y (b smallCap)-1/2)+(88074/100000)*b smallCap)+
        (62095/100000)*CoreAngleEndpoint.diagonal := rfl
  rw [hH]
  linarith

lemma H_lower {x : ℝ} (hx : x∈Icc 0 smallCap) : (449/500:ℝ)<H x :=
  H_endpoint.trans_le (H_antitone hx (by norm_num [smallCap]) hx.2)

/-- The actual separator pays the original target-core slack while the
source outer circle supplies its exact diagonal-contact value. -/
theorem original_cost_lower {a z A B x : ℝ} (hs : OuterState a z)
    (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤z-A*Real.sin x+B*Real.cos x) :
    H x≤-x+28271/100000-e*a+(88074/100000)*z+(62095/100000)*B := by
  have hcut := negative_angle_cut hs ht hx hm
  have hxc : x∈Icc 0 smallCap := ⟨hx.1,hcut.le⟩
  have htr := positive_trig hx
  have hA := core_primary_lower ht
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.2.2
  have hprim := mul_le_mul_of_nonneg_right hA htr.2.2.1
  have hslack : b x+(CoreAngleEndpoint.diagonal-B)*Real.cos x≤z := by
    dsimp [b]
    linarith
  have hextra := mul_nonneg (sub_nonneg.mpr hB) (show 0≤Real.cos x by linarith [htr.1])
  have hbz : b x≤z := by linarith
  have hcoord := curve_domain hxc
  have hy := Y_pos hcoord
  have hy2 := Y_sq hcoord
  have hroot : a≤Y (b x)-1/2 := by
    have hb2 := pow_le_pow_left₀ (show 0≤b x+1/2 by linarith [hcoord.1])
      (show b x+1/2≤z+1/2 by linarith) 2
    have ha : 0≤a+1/2 := by linarith [hs.1,hs.2.1]
    nlinarith [hs.2.2]
  have hcoef : (62095/100000:ℝ)≤(88074/100000)*Real.cos x := by linarith [htr.1]
  have hpaid := mul_nonneg (sub_nonneg.mpr hcoef) (sub_nonneg.mpr hB)
  have hmargin := mul_le_mul_of_nonneg_left hslack (by norm_num : (0:ℝ)≤88074/100000)
  have hsource := mul_le_mul_of_nonneg_left hroot (show 0≤e by norm_num [e])
  dsimp [H,radial]
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortMixedZero.SmallContact

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero

open CommonQuarter CorePairGeometry

theorem opposite_outer_negative_third {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)< -x+c 3-p 3*a+q 3*b+g 3*B := by
  have hcut := negative_angle_cut hs ht hx hm
  have hh := (SmallContact.H_lower ⟨hx.1,hcut.le⟩).trans_le
    (SmallContact.original_cost_lower hs ht hx hm)
  simpa [c,p,q,g,SmallContact.e] using hh

/-- All six outer-source opposite-sign negative-angle families, each
proved from the complete original core and outer geometry. -/
theorem opposite_outer_negative (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)< -x+c r-p r*a+q r*b+g r*B := by
  by_cases h0 : r=0
  · subst r
    exact opposite_outer_negative_first hs ht hx hm
  by_cases h3 : r=3
  · subst r
    exact opposite_outer_negative_third hs ht hx hm
  exact opposite_outer_negative_secant r h0 h3 hs ht hx hm

end SquaresInCircles.Eight.TableFree.ShortMixedZero
