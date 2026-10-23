module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreePrimary
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoLowerSource
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoUpperSource

/-!
# One strongly convex primary speed product

The transformed source label and the original target-circle speed give
a product with second derivative greater than `.3` on its full primary
interval.  Its one-point reserve at primary coordinate one proves the
actual lower contact-speed inequality everywhere.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic

lemma primary_growth_one {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<TPrimaryLabel.d3 a-2*TPrimaryLabel.d2 a := by
  have hm : MonotoneOn (fun t => TPrimaryLabel.d3 t-2*TPrimaryLabel.d2 t)
      (Icc outerDiagonal outerAxial) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun t ht => ((TPrimaryLabel.d3_hasDerivAt (primary_domain ht)).sub
        ((TPrimaryLabel.d2_hasDerivAt (primary_domain ht)).const_mul 2)).continuousAt.continuousWithinAt)
      (fun t ht => (TPrimaryLabel.d3_hasDerivAt (primary_domain (Ioo_subset_Icc_self ht))).sub
        ((TPrimaryLabel.d2_hasDerivAt (primary_domain (Ioo_subset_Icc_self ht))).const_mul 2))
    intro t ht
    have h := Ioo_subset_Icc_self ht
    linarith [primary_fourth_growth h,primary_third_positive h]
  have hh := hm primary_diagonal_mem ha ha.1
  linarith [primary_diagonal_third,primary_diagonal_second]

lemma primary_growth_two {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<TPrimaryLabel.d3 a-2*TPrimaryLabel.d1 a := by
  have hm : MonotoneOn (fun t => TPrimaryLabel.d3 t-2*TPrimaryLabel.d1 t)
      (Icc outerDiagonal outerAxial) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun t ht => ((TPrimaryLabel.d3_hasDerivAt (primary_domain ht)).sub
        ((TPrimaryLabel.d1_hasDerivAt (primary_domain ht)).const_mul 2)).continuousAt.continuousWithinAt)
      (fun t ht => (TPrimaryLabel.d3_hasDerivAt (primary_domain (Ioo_subset_Icc_self ht))).sub
        ((TPrimaryLabel.d1_hasDerivAt (primary_domain (Ioo_subset_Icc_self ht))).const_mul 2))
    intro t ht
    have h := Ioo_subset_Icc_self ht
    linarith [primary_fourth_growth h,primary_third_positive h,primary_growth_one h]
  have hh := hm primary_diagonal_mem ha ha.1
  linarith [primary_diagonal_third,primary_diagonal_first]

lemma primary_growth_three {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<TPrimaryLabel.d3 a-2*TPrimaryLabel.d2 a-2*TPrimaryLabel.d1 a := by
  have hm : MonotoneOn
      (fun t => TPrimaryLabel.d3 t-2*TPrimaryLabel.d2 t-2*TPrimaryLabel.d1 t)
      (Icc outerDiagonal outerAxial) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun t ht => (((TPrimaryLabel.d3_hasDerivAt (primary_domain ht)).sub
        ((TPrimaryLabel.d2_hasDerivAt (primary_domain ht)).const_mul 2)).sub
          ((TPrimaryLabel.d1_hasDerivAt (primary_domain ht)).const_mul 2)).continuousAt.continuousWithinAt)
      (fun t ht => ((TPrimaryLabel.d3_hasDerivAt (primary_domain (Ioo_subset_Icc_self ht))).sub
        ((TPrimaryLabel.d2_hasDerivAt (primary_domain (Ioo_subset_Icc_self ht))).const_mul 2)).sub
          ((TPrimaryLabel.d1_hasDerivAt (primary_domain (Ioo_subset_Icc_self ht))).const_mul 2))
    intro t ht
    have h := Ioo_subset_Icc_self ht
    linarith [primary_fourth_growth h,primary_third_positive h,primary_growth_one h]
  have hh := hm primary_diagonal_mem ha ha.1
  linarith [primary_diagonal_third,primary_diagonal_first,primary_diagonal_second]

namespace PrimarySpeed

def mass : ℝ := Q0-9/5
def speed (a : ℝ) : ℝ := Real.sqrt (mass-(a-1/2)^2)
def product (a : ℝ) : ℝ := TPrimaryLabel.d1 a*speed a
def first (a : ℝ) : ℝ :=
  TPrimaryLabel.d2 a*speed a-TPrimaryLabel.d1 a*(a-1/2)/speed a
def second (a : ℝ) : ℝ :=
  TPrimaryLabel.d3 a*speed a-2*TPrimaryLabel.d2 a*(a-1/2)/speed a-
    TPrimaryLabel.d1 a*mass/(speed a)^3

lemma data {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<speed a ∧ (speed a)^2=mass-(a-1/2)^2 ∧
      (639/500:ℝ)<(speed a)^2 ∧ (speed a)^2<49/25 ∧
      0<(speed a)^2-(a-1/2) ∧ (23/20:ℝ)<2*(speed a)^4-mass := by
  have hz : (399/1000:ℝ)<a-1/2 ∧ a-1/2<183/200 := by
    constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.1]
  have hrad : 0<mass-(a-1/2)^2 := by norm_num [mass,Q0]; nlinarith
  have hp : 0<speed a := Real.sqrt_pos.2 hrad
  have he : (speed a)^2=mass-(a-1/2)^2 := Real.sq_sqrt hrad.le
  have hlo : (639/500:ℝ)<(speed a)^2 := by norm_num [mass,Q0] at he; nlinarith
  have hhi : (speed a)^2<(49/25:ℝ) := by norm_num [mass,Q0] at he; nlinarith
  refine ⟨hp,he,hlo,hhi,by linarith,?_⟩
  have hsq : (639/500:ℝ)^2<(speed a)^4 := by nlinarith [sq_nonneg ((speed a)^2-639/500)]
  norm_num [mass,Q0]
  nlinarith

lemma speed_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt speed (-(a-1/2)/speed a) a := by
  have hh := data ha
  have hrad : mass-(a-1/2)^2≠0 := by nlinarith [hh.1,hh.2.1]
  have hd := ((((hasDerivAt_id a).sub_const (1/2)).pow 2).const_sub mass).sqrt hrad
  convert hd using 1 <;> dsimp [speed] <;>
    field_simp [show Real.sqrt (mass-(a-1/2)^2)≠0 from hh.1.ne'] <;> ring

lemma product_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt product (first a) a := by
  convert (TPrimaryLabel.d1_hasDerivAt (primary_domain ha)).mul (speed_hasDerivAt ha)
    using 1 <;> dsimp [product,first] <;> ring

lemma first_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt first (second a) a := by
  have hh := data ha
  have hd := ((TPrimaryLabel.d2_hasDerivAt (primary_domain ha)).mul (speed_hasDerivAt ha)).sub
    ((((TPrimaryLabel.d1_hasDerivAt (primary_domain ha)).mul
      ((hasDerivAt_id a).sub_const (1/2))).div (speed_hasDerivAt ha) hh.1.ne')
  convert hd using 1
  · rfl
  · dsimp [first,second]
    field_simp [hh.1.ne']
    nlinarith [hh.2.1]

lemma second_positive {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (3/10:ℝ)<second a := by
  have hv := data ha
  have hm := primary_first_lower ha
  have hv3 := pow_pos hv.1 3
  have hv4 := pow_pos hv.1 4
  have he : second a*(speed a)^3=
      TPrimaryLabel.d3 a*(speed a)^4-
        2*TPrimaryLabel.d2 a*(a-1/2)*(speed a)^2-TPrimaryLabel.d1 a*mass := by
    dsimp [second]
    field_simp [hv.1.ne']
    ring
  have hbase := mul_lt_mul hm hv.2.2.2.2.2
    (by norm_num : (0:ℝ)<23/20) (by linarith [hm] : 0≤TPrimaryLabel.d1 a)
  have hmain : (19/25:ℝ)*(23/20)<second a*(speed a)^3 := by
    by_cases hdd : 0≤TPrimaryLabel.d2 a
    · have hg := primary_growth_three ha
      have hp := mul_pos hg hv4
      have hreserve := mul_nonneg hdd
        (mul_nonneg (sq_nonneg (speed a)) hv.2.2.2.2.1.le)
      nlinarith
    · have hg := primary_growth_two ha
      have hp := mul_pos hg hv4
      have hz : 0<a-1/2 := by linarith [ha.1,fine_outer_endpoint_bounds.2]
      have hterm := mul_neg_of_neg_of_pos (lt_of_not_ge hdd)
        (mul_pos hz (pow_pos hv.1 2))
      nlinarith
  have hspeed : speed a<(7/5:ℝ) := by nlinarith [hv.2.2.2.1]
  have hcube := pow_lt_pow_left₀ hv.1.le hspeed (by norm_num : (3:ℕ)≠0)
  norm_num at hmain hcube
  nlinarith

lemma one_speed : speed 1∈Icc (68293/50000) (136587/100000) := by
  have hv := data primary_one_mem
  norm_num [mass,Q0] at hv
  constructor <;> nlinarith [hv.1,hv.2.1]

lemma one_references : (1057/1000:ℝ)<product 1 ∧ |first 1|<1/10 := by
  have hv := one_speed
  have hm := primary_one_references
  have hp := (data primary_one_mem).1
  have hprod := mul_lt_mul hm.1 hv.1 (by norm_num : (0:ℝ)<68293/50000)
    (by linarith [hm.1] : 0≤TPrimaryLabel.d1 1)
  have hfirstlo : (3819/10000:ℝ)<TPrimaryLabel.d2 1*speed 1 := by
    have hh := mul_lt_mul hm.2.2.1 hv.1 (by norm_num : (0:ℝ)<68293/50000)
      (by linarith [hm.2.2.1] : 0≤TPrimaryLabel.d2 1)
    norm_num at hh
    linarith
  have hfirsthi : TPrimaryLabel.d2 1*speed 1<(191/500:ℝ) := by
    have hh := mul_lt_mul hm.2.2.2 hv.2 hp (by norm_num : (0:ℝ)≤5593/20000)
    norm_num at hh
    linarith
  have hquotlo : (1417/5000:ℝ)<TPrimaryLabel.d1 1*(1/2)/speed 1 := by
    apply (lt_div_iff₀ hp).2
    nlinarith [hv.2,hm.1]
  have hquothi : TPrimaryLabel.d1 1*(1/2)/speed 1<(709/2500:ℝ) := by
    apply (div_lt_iff₀ hp).2
    nlinarith [hv.1,hm.2.1]
  constructor
  · dsimp [product]
    norm_num at hprod
    linarith
  · rw [abs_lt]
    norm_num [first]
    exact ⟨by linarith,by linarith⟩

theorem product_lower {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (26/25:ℝ)<product a := by
  have ht := curvature_tangent (κ := (3/10:ℝ)) ha primary_one_mem
    (fun t ht => product_hasDerivAt ht) (fun t ht => first_hasDerivAt ht)
    (fun t ht => (second_positive ht).le)
  have hs := abs_lt.mp one_references.2
  have hsq : (first 1)^2<(1/100:ℝ) := by nlinarith
  nlinarith [one_references.1,sq_nonneg ((3/10)*(a-1)+first 1)]

end PrimarySpeed

theorem lower_active_speed {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (ha : NegativeTwo.lowerSource A B x∈Icc outerDiagonal outerAxial) :
    1<TPrimaryLabel.d1 (NegativeTwo.lowerSource A B x)*NegativeTwo.lowerSpeed A B x := by
  have hactual := NegativeTwo.lowerSource_norm ht x
  have hv := PrimarySpeed.data ha
  have hp := NegativeTwo.lowerSpeed_positive ht hx
  have hB : B<(9/10:ℝ) := (NegativeTwo.source_mem ht).2.trans_lt outer_endpoint_bounds.2.2.2
  have hs : PrimarySpeed.speed (NegativeTwo.lowerSource A B x)<NegativeTwo.lowerSpeed A B x := by
    dsimp [PrimarySpeed.mass] at hv
    nlinarith [hv.1,hv.2.1]
  have hM : 0<TPrimaryLabel.d1 (NegativeTwo.lowerSource A B x) := by
    linarith [primary_first_lower ha]
  have hh := mul_lt_mul_of_pos_left hs hM
  have hbase := PrimarySpeed.product_lower ha
  dsimp [PrimarySpeed.product] at hbase
  linarith

theorem upper_active_speed {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (ha : NegativeTwo.upperSource A B x∈Icc outerDiagonal 1) :
    TPrimaryLabel.d1 (NegativeTwo.upperSource A B x)*NegativeTwo.upperSpeed A B x<1 := by
  have hv := NegativeTwo.upperSpeed_positive ht hx
  have hn := NegativeTwo.upperSource_norm ht x
  have hsum := NegativeTwo.outer_sum_lower ht
  have hs : NegativeTwo.upperSpeed A B x<(11/10:ℝ) := by
    norm_num [Q0] at hn
    nlinarith [fine_outer_endpoint_bounds.1,sq_nonneg (NegativeTwo.upperSource A B x-1/2)]
  have hM := primary_first_small ha
  have hh := mul_lt_mul hM hs hv (by norm_num : (0:ℝ)≤9/10)
  norm_num at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree
