module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroReferences

/-!
# The positive-contact speed estimates in the written proof

Uncompiled source draft.  The sum a(B)+B is monotone, so the exact
circle identity gives the stated whole-range speed bounds.  The P
angular derivative is positive throughout its two analytic ranges;
the first J range is controlled by its target or source coordinate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.PositivePJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma mass_monotone : MonotoneOn (fun B => arc B+B) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add
      (hasDerivAt_id B)).continuousAt.continuousWithinAt)
    (fun B hB => (ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain (Ioo_subset_Icc_self hB))).add
      (hasDerivAt_id B))
    (fun B hB => by linarith [(outer_ratio_bounds (Ioo_subset_Icc_self hB)).2.1])

lemma speed_bound {B x t M : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10))
    (ht : t∈Icc 0 outerDiagonal) (hBt : t≤B) (hM : 0<M)
    (hm : Q0-2*(arc t+t)<M^2) : plusSpeed B x<M := by
  have hh := mass_monotone ht hB hBt
  have hn := plus_norm hB x
  nlinarith [sq_nonneg (plus B x-1/2)]
lemma speed_upper {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    plusSpeed B x<(1043/1000:ℝ) :=
  speed_bound hB hx outer_zero_mem hB.1 (by norm_num)
    (by simpa using Reference.mass_references.1)
lemma speed_fifth {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10))
    (hBt : 1/5≤B) : plusSpeed B x<(903/1000:ℝ) :=
  speed_bound hB hx (Asymmetric.rational_outer_mem (by norm_num)) hBt (by norm_num)
    Reference.mass_references.2.1

lemma P_early {B x : ℝ} (hd : PlusDomain B x) (hx : x≤3/10) : 0<plusFirst PLabel B x := by
  let f : ℝ→ℝ := fun t => (183/200)*Real.cos t+(1/2)*Real.sin t
  have hm : MonotoneOn f (Icc 0 (3/10)) :=
    monoOn_of_hasDeriv_nonneg
      (by dsimp [f]; fun_prop)
      (fun t _ => by
        convert ((Real.hasDerivAt_cos t).const_mul (183/200)).add
          ((Real.hasDerivAt_sin t).const_mul (1/2)) using 1 <;> dsimp [f] <;> ring)
      (fun t ht => by
        have hs := Real.sin_le_self ht.1.le
        have hc := cos_lower_two ht.1.le
        nlinarith [ht.2])
  have hspeed : plusSpeed B x≤f x := by
    have ha := outer_bounds (ShortOuterOne.SameContact.arc_state hd.1)
    have ht := positive_trig hd.2.1
    have h1 := mul_le_mul_of_nonneg_right
      (show arc B-1/2≤(183/200:ℝ) by linarith [ha.2.1,fine_outer_endpoint_bounds.1])
        (by linarith [ht.1] : 0≤Real.cos x)
    have h2 := mul_le_mul_of_nonneg_right
      (show -(B-1/2)≤(1/2:ℝ) by linarith [hd.1.1]) ht.2.2.1
    dsimp [plusSpeed,f]
    linarith
  have hupper := hspeed.trans (hm ⟨hd.2.1.1,hx⟩ (by norm_num) hx)
  have hp := (P_first_bounds hd.2.2).2
  have hpos := (positive_data hd.1 hd.2.1).1
  have hprod := mul_lt_mul_of_pos_right hp hpos
  have hmul := mul_le_mul_of_nonneg_left hupper (by norm_num : (0:ℝ)≤973/1000)
  have href := Reference.zero_speed_references.1
  dsimp [f] at hmul
  dsimp [plusFirst]
  linarith

lemma P_late {B x : ℝ} (hd : PlusDomain B x) (hx : 3/10≤x) : 0<plusFirst PLabel B x := by
  have h1 := plus_target_antitone hd.2.1 outer_zero_mem hd.1 hd.1.1
  have h2 := plus_angle_antitone outer_zero_mem
    (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num) hd.2.1 hx
  have hb : plus B x<177/250 := by linarith [Reference.plus_references.1]
  have hP := P_first_monotone hd.2.2 (Asymmetric.rational_outer_mem (by norm_num)) hb.le
  have hp : PLabel.d1 (plus B x)<907/1000 := hP.trans_lt Reference.P_708
  have hv := speed_upper hd.1 hd.2.1
  have hh := mul_lt_mul hp hv (positive_data hd.1 hd.2.1).1 (by norm_num)
  dsimp [plusFirst]
  norm_num at hh
  linarith

theorem P_positive {B x : ℝ} (hd : PlusDomain B x) : 0<plusFirst PLabel B x := by
  rcases le_total x (3/10) with hx | hx
  · exact P_early hd hx
  · exact P_late hd hx

lemma J_early {B x : ℝ} (hd : PlusDomain B x) (hx : x≤1/2) : 0<plusFirst JLabel B x := by
  by_cases hB : 1/5≤B
  · have hJ := (J_first_bounds hd.2.2).2
    have hv := speed_fifth hd.1 hd.2.1 hB
    have hh := mul_lt_mul hJ hv (positive_data hd.1 hd.2.1).1 (by norm_num)
    norm_num at hh
    dsimp [plusFirst]
    linarith
  · have hB' : B≤1/5 := le_of_not_ge hB
    have h1 := plus_target_antitone hd.2.1 hd.1
      (Asymmetric.rational_outer_mem (by norm_num : (1/5:ℝ)∈Icc 0 (899/1000))) hB'
    have h2 := plus_angle_antitone
      (Asymmetric.rational_outer_mem (by norm_num : (1/5:ℝ)∈Icc 0 (899/1000)))
      hd.2.1 (by norm_num : (1/2:ℝ)∈Icc 0 (7/10)) hx
    have hb : 7/20<plus B x := by linarith [Reference.plus_references.2.1]
    have hJ := (J_first_antitone (Asymmetric.rational_outer_mem (by norm_num)) hd.2.2 hb.le).
      trans_lt Reference.J_35
    have hh := mul_lt_mul hJ (speed_upper hd.1 hd.2.1) (positive_data hd.1 hd.2.1).1 (by norm_num)
    norm_num at hh
    dsimp [plusFirst]
    linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.PositivePJ
