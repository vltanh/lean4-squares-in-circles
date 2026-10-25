module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoAligned

/-!
# Eight squares: the original upper source-primary owner

The original target circle bounds the source-contact speed by a radical
depending only on its physical primary coordinate.  The product of that
radical and the source-label slope increases up to height one, where it
is strictly less than one.  An intermediate-value contact connects the
original weak separator to alignment while retaining the actual target.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def upperSpeed (A B x : ℝ) : ℝ :=
  (1/2-B)*Real.sin x+(A-1/2)*Real.cos x
def upperMass : ℝ := Q0-2*outerAxial
def primarySpeed (a : ℝ) : ℝ := Real.sqrt (upperMass-(a-1/2)^2)
def primaryProduct (a : ℝ) : ℝ := PPrimaryLabel.d1 a*primarySpeed a

lemma outer_sum_lower {A B : ℝ} (ht : OuterState A B) : outerAxial≤A+B := by
  have hz := (ShortOuterOne.SameContact.arc_state outer_zero_mem).2.2
  rw [ShortOuterOne.SameContact.arc_zero] at hz
  have hA0 : 0≤A := ht.1.trans ht.2.1
  have hAB := mul_nonneg hA0 ht.1
  have hs : 0≤A+B := by linarith [ht.1]
  have hax : 0≤outerAxial := by linarith [outer_endpoint_bounds.1]
  by_contra hh
  have hsum : A+B<outerAxial := lt_of_not_ge hh
  have hsq : (A+B)^2<outerAxial^2 := by nlinarith
  nlinarith [ht.2.2]

lemma upperSource_zero (A B : ℝ) : upperSource A B 0=1-B := by
  norm_num [upperSource]
  ring

lemma upperSource_hasDerivAt (A B x : ℝ) :
    HasDerivAt (upperSource A B) (-upperSpeed A B x) x := by
  have hd := (((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).fun_sub
    ((Real.hasDerivAt_sin x).const_mul (A-1/2))
  exact hd.congr_deriv (by dsimp [upperSpeed]; ring)

lemma upperSpeed_positive {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) : 0<upperSpeed A B x := by
  have hh := positive_trig hx
  have hcos0 : 0≤Real.cos x := by linarith [hh.1]
  have hfirst := mul_nonneg
    (show 0≤A-1/2-399/1000 by linarith [(primary_mem ht).1,fine_outer_endpoint_bounds.2]) hcos0
  have hsecond := mul_nonneg
    (show 0≤1/2-B+2/5 by linarith [(source_mem ht).2,outer_endpoint_bounds.2.2.2])
    hh.2.2.1
  dsimp [upperSpeed]
  nlinarith [hh.1,hh.2.2.2.1]

lemma upperSource_antitone {A B : ℝ} (ht : OuterState A B) :
    AntitoneOn (upperSource A B) (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x _ => (upperSource_hasDerivAt A B x).continuousAt.continuousWithinAt)
    (fun x _ => upperSource_hasDerivAt A B x)
    (fun x hx => neg_nonpos.mpr (upperSpeed_positive ht (Ioo_subset_Icc_self hx)).le)

lemma upperSource_norm {A B : ℝ} (ht : OuterState A B) (x : ℝ) :
    (upperSource A B x-1/2)^2+(upperSpeed A B x)^2=Q0-2*(A+B) := by
  dsimp [upperSource,upperSpeed]
  linear_combination ht.2.2+
    ((1/2-B)^2+(A-1/2)^2)*(Real.sin_sq_add_cos_sq x)

lemma primarySpeed_data {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    0<primarySpeed a ∧ (primarySpeed a)^2=upperMass-(a-1/2)^2 ∧
      (2089/2500:ℝ)<(primarySpeed a)^2 := by
  have hcenter : 0≤a-1/2 ∧ a-1/2≤1/2 := by
    constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2]
  have hs : (a-1/2)^2≤(1/2:ℝ)^2 := by nlinarith
  have hm : (1357/1250:ℝ)<upperMass := by
    dsimp [upperMass]
    norm_num [Q0]
    linarith [outer_endpoint_bounds.2.1]
  have hpos : 0<upperMass-(a-1/2)^2 := by nlinarith
  have hp : 0<primarySpeed a := Real.sqrt_pos.2 hpos
  have he : (primarySpeed a)^2=upperMass-(a-1/2)^2 := Real.sq_sqrt hpos.le
  exact ⟨hp,he,by nlinarith⟩

lemma primarySpeed_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    HasDerivAt primarySpeed (-(a-1/2)/primarySpeed a) a := by
  have hp := primarySpeed_data ha
  have hrad : upperMass-(a-1/2)^2≠0 := by rw [← hp.2.1]; exact (pow_pos hp.1 2).ne'
  have hd := ((((hasDerivAt_id' a).sub_const (1/2)).fun_pow 2).const_sub upperMass).sqrt hrad
  show HasDerivAt (fun y => Real.sqrt (upperMass-(y-1/2)^2)) _ a
  refine hd.congr_deriv ?_
  have hYx : Real.sqrt (upperMass-(a-1/2)^2)=primarySpeed a := rfl
  rw [hYx]
  field_simp
  norm_num
  ring

lemma primaryProduct_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    HasDerivAt primaryProduct
      (PPrimaryLabel.d2 a*primarySpeed a-
        PPrimaryLabel.d1 a*(a-1/2)/primarySpeed a) a := by
  have hd := (PPrimaryLabel.d1_hasDerivAt (primary_domain (aligned_domain ha).1)).fun_mul
    (primarySpeed_hasDerivAt ha)
  exact hd.congr_deriv (by ring)

lemma primaryProduct_increases {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    0<PPrimaryLabel.d2 a*primarySpeed a-
      PPrimaryLabel.d1 a*(a-1/2)/primarySpeed a := by
  have hs := primarySpeed_data ha
  have hM := OppositeTwo.M_second_monotone OppositeTwo.primary_diagonal_mem
    (aligned_domain ha).1 ha.1
  have hMlower : (9/10:ℝ)<PPrimaryLabel.d2 a :=
    OppositeTwo.M_second_diagonal.trans_le hM
  have hfirst := OppositeTwo.M_first_monotone (aligned_domain ha).1 primary_one_mem ha.2
  have hfirstupper : PPrimaryLabel.d1 a<(271/250:ℝ) :=
    hfirst.trans_lt OppositeTwo.M_one_first.2
  have hfirstpos : 0<PPrimaryLabel.d1 a := by
    linarith [OppositeTwo.M_first_lower (aligned_domain ha).1]
  have hcenter : 0≤a-1/2 ∧ a-1/2≤1/2 := by
    constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2]
  have hbig := mul_lt_mul hMlower hs.2.2.le (by norm_num : (0:ℝ)<2089/2500)
    (by linarith : 0≤PPrimaryLabel.d2 a)
  have hsmall := mul_le_mul hfirstupper.le hcenter.2 hcenter.1 (by norm_num : (0:ℝ)≤271/250)
  have he : (PPrimaryLabel.d2 a*(primarySpeed a)^2-
      PPrimaryLabel.d1 a*(a-1/2))/primarySpeed a=
      PPrimaryLabel.d2 a*primarySpeed a-
        PPrimaryLabel.d1 a*(a-1/2)/primarySpeed a := by
    field_simp [hs.1.ne']
  rw [←he]
  exact div_pos (by linarith) hs.1

lemma primaryProduct_monotone : MonotoneOn primaryProduct (Icc outerDiagonal 1) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (primaryProduct_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun a ha => primaryProduct_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun a ha => (primaryProduct_increases (Ioo_subset_Icc_self ha)).le)

lemma primarySpeed_one : primarySpeed 1=outerAxial-1/2 := by
  have hs := primarySpeed_data (show (1:ℝ)∈Icc outerDiagonal 1 from ⟨primary_one_mem.1,le_rfl⟩)
  have hz := (ShortOuterOne.SameContact.arc_state outer_zero_mem).2.2
  rw [ShortOuterOne.SameContact.arc_zero] at hz
  norm_num [upperMass] at hs
  nlinarith [outer_endpoint_bounds.1]

lemma primaryProduct_one : primaryProduct 1<1 := by
  have hs : 0≤outerAxial-1/2 := by linarith [outer_endpoint_bounds.1]
  have hh := mul_le_mul OppositeTwo.M_one_first.2.le
    (show outerAxial-1/2≤(183/200:ℝ) by linarith [outer_endpoint_bounds.2.1])
    hs (by norm_num : (0:ℝ)≤271/250)
  dsimp [primaryProduct]
  rw [primarySpeed_one]
  norm_num at hh
  linarith

lemma upper_source_speed_paid {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (ha : upperSource A B x∈Icc outerDiagonal 1) :
    PPrimaryLabel.d1 (upperSource A B x)*upperSpeed A B x<1 := by
  have hv := upperSpeed_positive ht hx
  have hs := primarySpeed_data ha
  have hn := upperSource_norm ht x
  have hsum := outer_sum_lower ht
  have hspeed : upperSpeed A B x≤primarySpeed (upperSource A B x) := by
    dsimp [upperMass] at hs
    nlinarith
  have hM : 0≤PPrimaryLabel.d1 (upperSource A B x) := by
    linarith [OppositeTwo.M_first_lower (aligned_domain ha).1]
  have hprod := mul_le_mul_of_nonneg_left hspeed hM
  have hmono := primaryProduct_monotone ha ⟨primary_one_mem.1,le_rfl⟩ ha.2
  have hend := primaryProduct_one
  dsimp [primaryProduct] at hmono hend
  linarith

theorem original_upper_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    (8977827/10000000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases halign : 1≤a+B
  · have hh := original_aligned hs ht halign
    dsimp [value] at *
    linarith [hx.1]
  · have hcut := upper_source_cut hx hm
    have hc : Continuous (fun t => -upperSource A B t) :=
      continuous_iff_continuousAt.2 fun t => (upperSource_hasDerivAt A B t).neg.continuousAt
    obtain ⟨y,hy,hycontact⟩ := intermediate_value_Icc hx.1 hc.continuousOn
      (show -a∈Icc (-upperSource A B 0) (-upperSource A B x) by
        rw [upperSource_zero]
        constructor <;> linarith)
    have he : upperSource A B y=a := by linarith
    have hycap : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hx.2⟩
    have hstart : 1-B∈Icc outerDiagonal 1 := by
      constructor <;> linarith [(primary_mem hs).1,ht.1]
    have hdom {t : ℝ} (htime : t∈Icc 0 y) :
        t∈Icc 0 (7/10) ∧ upperSource A B t∈Icc outerDiagonal 1 := by
      have htcap : t∈Icc 0 (7/10) := ⟨htime.1,htime.2.trans hycap.2⟩
      have hlo := upperSource_antitone ht htcap hycap htime.2
      have hhi := upperSource_antitone ht (by norm_num) htcap htime.1
      rw [he] at hlo
      rw [upperSource_zero] at hhi
      exact ⟨htcap,⟨(primary_mem hs).1.trans hlo,hhi.trans hstart.2⟩⟩
    have hd {t : ℝ} (htime : t∈Icc 0 y) :
        HasDerivAt (fun s => s+PPrimaryLabel.outer (upperSource A B s))
          (1-PPrimaryLabel.d1 (upperSource A B t)*upperSpeed A B t) t := by
      have hh := (PPrimaryLabel.outer_hasDerivAt
        (primary_domain (aligned_domain (hdom htime).2).1)).comp t
          (upperSource_hasDerivAt A B t)
      exact ((hasDerivAt_id' t).fun_add hh).congr_deriv (by ring)
    have hmono : MonotoneOn (fun s => s+PPrimaryLabel.outer (upperSource A B s))
        (Icc 0 y) := monoOn_of_hasDeriv_nonneg
      (fun t ht' => (hd ht').continuousAt.continuousWithinAt)
      (fun t ht' => hd (Ioo_subset_Icc_self ht'))
      (fun t ht' => by
        have hh := hdom (Ioo_subset_Icc_self ht')
        linarith [upper_source_speed_paid ht hh.1 hh.2])
    have hstep := hmono ⟨le_rfl,hy.1⟩ ⟨hy.1,le_rfl⟩ hy.1
    dsimp only at hstep
    rw [upperSource_zero,he] at hstep
    have hbase := aligned_lower hstart
    have hactual : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
    dsimp [aligned,value] at *
    rw [hactual] at hstep
    have harg : 1-(1-B)=B := by ring
    rw [harg] at hbase
    linarith [hy.2]

end SquaresInCircles.Eight.SecondWord.NegativeTwo
