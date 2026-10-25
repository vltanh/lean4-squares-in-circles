module

public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoAxialCalculus

/-!
# Eight squares: the actual target label in primary coordinates

The transformed target label is increasing and convex.  Its derivative
relative to the physical circle speed has a uniform positive reserve.
These whole-primary-interval bounds supply the lower-primary contact
curvature as well as the upper-primary finite comparison.
-/

section
/-!
## The source label in the original primary coordinate

The primary label is the exact circle transform of the source label.
Its increasing curvature and derivative are proved on the complete
physical primary interval, with one rational reference at height one.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma primary_diagonal_mem : outerDiagonal∈Icc outerDiagonal outerAxial :=
  ⟨le_rfl,ShortOuterOne.SameContact.diagonal_le_axial⟩

lemma M_third_positive {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<PPrimaryLabel.d3 a := by
  have hu := U_positive (primary_domain ha)
  have he := PPrimaryLabel.third_numerator (primary_domain ha)
  have hW : (1399/1000:ℝ)<W a := by dsimp [W]; linarith [ha.1,fine_outer_endpoint_bounds.2]
  norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,Q0] at he ⊢
  have hp := pow_pos hu 5
  nlinarith

lemma M_second_monotone :
    MonotoneOn PPrimaryLabel.d2 (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (PPrimaryLabel.d2_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun _ ha => PPrimaryLabel.d2_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun _ ha => (M_third_positive (Ioo_subset_Icc_self ha)).le)

lemma primary_diagonal_ratioD : (71/50:ℝ)<ratioD outerDiagonal := by
  have hu := U_positive (primary_domain primary_diagonal_mem)
  have hU : U outerDiagonal<7/5 := by
    rw [U,ShortOuterOne.SameContact.arc_diagonal]
    linarith [outer_endpoint_bounds.2.2.2]
  have hc := pow_le_pow_left₀ hu.le hU.le 3
  change (71/50:ℝ)<Q0/(U outerDiagonal)^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0]
  nlinarith

lemma M_second_diagonal : (9/10:ℝ)<PPrimaryLabel.d2 outerDiagonal := by
  have hc : (807/1000:ℝ)<22663/25000-(2211/20000)*outerDiagonal := by
    linarith [outer_endpoint_bounds.2.2.2]
  have hm := mul_lt_mul hc primary_diagonal_ratioD.le (by norm_num)
    (by linarith : 0≤22663/25000-(2211/20000)*outerDiagonal)
  norm_num [RoleLabel.d2,PPrimaryLabel,RoleLabel.primary,PLabel,ratio_diagonal]
  nlinarith

lemma M_second_positive {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<PPrimaryLabel.d2 a := by
  have hh := M_second_monotone primary_diagonal_mem ha ha.1
  linarith [M_second_diagonal]

lemma M_first_monotone : MonotoneOn PPrimaryLabel.d1 (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (PPrimaryLabel.d1_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun _ ha => PPrimaryLabel.d1_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun _ ha => (M_second_positive (Ioo_subset_Icc_self ha)).le)

lemma M_first_diagonal : (243/250:ℝ)<PPrimaryLabel.d1 outerDiagonal := by
  norm_num [RoleLabel.d1,PPrimaryLabel,RoleLabel.primary,PLabel,ratio_diagonal,
    ShortOuterOne.SameContact.arc_diagonal]
  linarith [fine_outer_endpoint_bounds.2]

lemma M_first_lower {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (243/250:ℝ)<PPrimaryLabel.d1 a :=
  M_first_diagonal.trans_le (M_first_monotone primary_diagonal_mem ha ha.1)

lemma M_one_first : (1083/1000:ℝ)<PPrimaryLabel.d1 1 ∧
    PPrimaryLabel.d1 1<271/250 := by
  exact PPrimaryLabel.first_chart_reference
    (l := (129058126439213/100000000000000:ℝ))
    (u := (64529063219607/50000000000000:ℝ))
    (dlo := (1083/1000:ℝ)) (dhi := (271/250:ℝ)) (primary_domain primary_one_mem)
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])
    (by norm_num [PPrimaryLabel,RoleLabel.primary,PLabel,W,Q0])

lemma M_first_above_one {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    (1083/1000:ℝ)<PPrimaryLabel.d1 a :=
  M_one_first.1.trans_le (M_first_monotone primary_one_mem
    ⟨primary_one_mem.1.trans ha.1,ha.2⟩ ha.1)

lemma M_monotone : MonotoneOn PPrimaryLabel.outer (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (PPrimaryLabel.outer_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun _ ha => PPrimaryLabel.outer_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun _ ha => by linarith [M_first_lower (Ioo_subset_Icc_self ha)])

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def VPrimaryLabel : RoleLabel := VLabel.primary
def primarySpeed (a : ℝ) : ℝ := Real.sqrt (Q0-(a-1/2)^2)
def targetProduct (a : ℝ) : ℝ := VPrimaryLabel.d1 a*primarySpeed a

lemma V_primary_second_positive {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<VPrimaryLabel.d2 a := by
  have hr := ShortOuterOne.SameContact.ratio_pos (primary_domain ha)
  have hd := ShortOuterOne.SameContact.ratioD_pos (primary_domain ha)
  have ha0 : 0≤a := by linarith [ha.1,outer_endpoint_bounds.2.2.1]
  have hm := mul_nonneg ha0 hd.le
  norm_num [VPrimaryLabel,RoleLabel.primary,VLabel,RoleLabel.d2]
  nlinarith

lemma V_primary_first_monotone :
    MonotoneOn VPrimaryLabel.d1 (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (VPrimaryLabel.d1_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun _ ha => VPrimaryLabel.d1_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun _ ha => (V_primary_second_positive (Ioo_subset_Icc_self ha)).le)

lemma V_primary_first_diagonal : VPrimaryLabel.d1 outerDiagonal=(1066/6250:ℝ) := by
  norm_num [VPrimaryLabel,RoleLabel.primary,VLabel,RoleLabel.d1,ratio_diagonal,
    ShortOuterOne.SameContact.arc_diagonal]

lemma V_primary_first_positive {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<VPrimaryLabel.d1 a := by
  have hh := V_primary_first_monotone primary_diagonal_mem ha ha.1
  rw [V_primary_first_diagonal] at hh
  linarith

lemma V_primary_monotone : MonotoneOn VPrimaryLabel.outer (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ha => (VPrimaryLabel.outer_hasDerivAt (primary_domain ha)).continuousAt.continuousWithinAt)
    (fun _ ha => VPrimaryLabel.outer_hasDerivAt (primary_domain (Ioo_subset_Icc_self ha)))
    (fun _ ha => (V_primary_first_positive (Ioo_subset_Icc_self ha)).le)

lemma V_primary_one_first : (54/125:ℝ)<VPrimaryLabel.d1 1 ∧
    VPrimaryLabel.d1 1<11/25 := by
  exact VPrimaryLabel.first_chart_reference
    (l := (129058126439213/100000000000000:ℝ))
    (u := (64529063219607/50000000000000:ℝ))
    (dlo := (54/125:ℝ)) (dhi := (11/25:ℝ)) (primary_domain primary_one_mem)
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [VPrimaryLabel,RoleLabel.primary,VLabel,W,Q0])
    (by norm_num [VPrimaryLabel,RoleLabel.primary,VLabel,W,Q0])

lemma target_primary_domain {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    a∈Icc outerDiagonal outerAxial := ⟨primary_one_mem.1.trans ha.1,ha.2⟩

lemma V_primary_first_above_one {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    (54/125:ℝ)<VPrimaryLabel.d1 a :=
  V_primary_one_first.1.trans_le
    (V_primary_first_monotone primary_one_mem (target_primary_domain ha) ha.1)

lemma primary_ratioD_over_ratio {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    (61/50)*ratio a<ratioD a := by
  have hu := U_positive (primary_domain (target_primary_domain ha))
  have harc := ShortOuterOne.SameContact.arc_antitone (primary_domain primary_one_mem)
    (primary_domain (target_primary_domain ha)) ha.1
  have hU : U a<1291/1000 := by
    have h1 : arc a≤bOne := harc
    dsimp only [U]
    linarith [bOne_bounds.2]
  have hW : 0≤W a ∧ W a<383/200 := by
    dsimp [W]
    exact ⟨by linarith [ha.1],by linarith [ha.2,outer_endpoint_bounds.2.1]⟩
  have hU2 := pow_le_pow_left₀ hu.le hU.le 2
  have hm := mul_le_mul hW.2.le hU2 (sq_nonneg (U a)) (by norm_num)
  have hnum : (61/50)*W a*(U a)^2<Q0 := by norm_num [Q0]; nlinarith
  have he : ratioD a-(61/50)*ratio a=
      (Q0-(61/50)*W a*(U a)^2)/(U a)^3 := by
    dsimp [ratioD,ratio,U,W]
    field_simp [hu.ne']
  have hp := div_pos (sub_pos.mpr hnum) (pow_pos hu 3)
  rw [←he] at hp
  linarith

lemma V_primary_second_ratio {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    (23/10)*VPrimaryLabel.d1 a<VPrimaryLabel.d2 a := by
  have hr := primary_ratio_one (target_primary_domain ha)
  have hb := primary_secondary_mem (target_primary_domain ha)
  have hc : 0<16031/100000+(63457/100000)*a ∧
      16031/100000+(63457/100000)*a<1059/1000 := by
    constructor <;> linarith [ha.1,ha.2,outer_endpoint_bounds.2.1]
  have hmain := mul_lt_mul_of_pos_left (primary_ratioD_over_ratio ha) hc.1
  have hcoef := mul_lt_mul_of_pos_right hc.2 (by linarith : 0<ratio a)
  norm_num [VPrimaryLabel,RoleLabel.primary,VLabel,RoleLabel.d1,RoleLabel.d2]
  nlinarith [hb.1]

lemma primarySpeed_data {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    (7/4:ℝ)<primarySpeed a ∧
      (a-1/2)^2+(primarySpeed a)^2=Q0 ∧
      (1539/500:ℝ)<(primarySpeed a)^2 := by
  have hh : 0≤a-1/2 ∧ a-1/2<183/200 := by
    constructor <;> linarith [ha.1,ha.2,outer_endpoint_bounds.2.1]
  have hsq := pow_le_pow_left₀ hh.1 hh.2.le 2
  have hrad : 0<Q0-(a-1/2)^2 := by norm_num [Q0]; nlinarith
  have hp := Real.sqrt_pos.mpr hrad
  have hc := Real.sq_sqrt hrad.le
  dsimp [primarySpeed]
  refine ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num [Q0]; linarith),by linarith,?_⟩
  rw [hc]
  norm_num [Q0]
  linarith

lemma primarySpeed_hasDerivAt {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    HasDerivAt primarySpeed (-(a-1/2)/primarySpeed a) a := by
  have hd := primarySpeed_data ha
  have hrad : Q0-(a-1/2)^2≠0 := by nlinarith [hd.2.1,hd.2.2]
  have hin : HasDerivAt (fun y => Q0-(y-1/2)^2) (-(2*(a-1/2))) a :=
    ((((hasDerivAt_id a).sub_const (1/2)).pow 2).const_sub Q0).congr_deriv (by simp)
  have hv : primarySpeed a=Real.sqrt (Q0-(a-1/2)^2) := rfl
  have hp : 0<primarySpeed a := by linarith [hd.1]
  refine (hin.sqrt hrad).congr_deriv ?_
  rw [← hv]
  field_simp [hp.ne']

lemma target_curvature_lower {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    (5/2:ℝ)<VPrimaryLabel.d2 a*(primarySpeed a)^2-
      VPrimaryLabel.d1 a*(a-1/2) := by
  have hd := primarySpeed_data ha
  have hN := V_primary_first_above_one ha
  have hN0 : 0<VPrimaryLabel.d1 a := by linarith
  have hmain := mul_lt_mul_of_pos_right (V_primary_second_ratio ha)
    (by linarith [hd.2.2] : 0<(primarySpeed a)^2)
  have hsq := mul_lt_mul_of_pos_left hd.2.2 hN0
  have hlast := mul_le_mul_of_nonneg_left
    (show a-1/2≤183/200 by linarith [ha.2,outer_endpoint_bounds.2.1]) hN0.le
  nlinarith

lemma targetProduct_hasDerivAt {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    HasDerivAt targetProduct
      (VPrimaryLabel.d2 a*primarySpeed a-
        VPrimaryLabel.d1 a*(a-1/2)/primarySpeed a) a := by
  exact ((VPrimaryLabel.d1_hasDerivAt (primary_domain (target_primary_domain ha))).mul
    (primarySpeed_hasDerivAt ha)).congr_deriv (by ring)

lemma targetProduct_monotone : MonotoneOn targetProduct (Icc 1 outerAxial) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun _ ha => (targetProduct_hasDerivAt ha).continuousAt.continuousWithinAt
  · exact fun _ ha => targetProduct_hasDerivAt (Ioo_subset_Icc_self ha)
  · intro a ha
    have hA := Ioo_subset_Icc_self ha
    have hp : 0<primarySpeed a := by linarith [(primarySpeed_data hA).1]
    have he : (VPrimaryLabel.d2 a*primarySpeed a-
        VPrimaryLabel.d1 a*(a-1/2)/primarySpeed a)*primarySpeed a=
      VPrimaryLabel.d2 a*(primarySpeed a)^2-VPrimaryLabel.d1 a*(a-1/2) := by
      field_simp [hp.ne']
    have hh := target_curvature_lower hA
    by_contra! hn
    have hm := mul_neg_of_neg_of_pos hn hp
    linarith

lemma targetProduct_lower {a : ℝ} (ha : a∈Icc 1 outerAxial) :
    (41/50:ℝ)<targetProduct a := by
  have hspeed : primarySpeed 1=outerAxial+1/2 := by
    have hd := primarySpeed_data ⟨le_rfl,primary_one_mem.2⟩
    have hp : 0<outerAxial+1/2 := by linarith [outer_endpoint_bounds.1]
    nlinarith [axial_circle]
  have hp := mul_lt_mul V_primary_one_first.1
    (show (1914/1000:ℝ)<primarySpeed 1 by
      rw [hspeed]; linarith [ShortOuterZero.fine_axial_bounds.1]).le
    (by norm_num) (by linarith [V_primary_one_first.1] : 0≤VPrimaryLabel.d1 1)
  have hz : (41/50:ℝ)<targetProduct 1 := by dsimp [targetProduct]; nlinarith
  exact hz.trans_le (targetProduct_monotone ⟨le_rfl,primary_one_mem.2⟩ ha ha.1)

end SquaresInCircles.Eight.SecondWord.OppositeTwo
end
end
end
