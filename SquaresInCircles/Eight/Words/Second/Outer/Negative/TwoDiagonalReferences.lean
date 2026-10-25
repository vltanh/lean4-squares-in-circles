module

public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners

/-!
# Eight squares: two fixed references on the original diagonal-source contact

All reference enclosures are consequences of rational Taylor polynomials
and the same physical circle equation.  The points `2/5` and `1/2` supply
the slope, curvature and tangent-value reserves for the complete arc.
-/

section
/-!
## The original lower source-primary weak owner

The source contact increases. Its active cost increases because the original target circle gives
a strict speed reserve. An exact intermediate-value contact therefore compares the original pair
to alignment or to the physical diagonal boundary (`original_lower_source_primary`). The original
target and its common circle are kept throughout.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic

def lowerSpeed (A B x : ℝ) : ℝ :=
  (B-1/2)*Real.sin x+(A+1/2)*Real.cos x

lemma lowerSource_zero (A B : ℝ) : lowerSource A B 0=1-B := by
  norm_num [lowerSource]
  ring

lemma lowerSource_hasDerivAt (A B x : ℝ) :
    HasDerivAt (lowerSource A B) (lowerSpeed A B x) x := by
  have h := (((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (A+1/2))
  show HasDerivAt (fun y => 1/2+(1/2-B)*Real.cos y+(A+1/2)*Real.sin y)
    (lowerSpeed A B x) x
  exact h.congr_deriv (by dsimp [lowerSpeed]; ring)

lemma lowerSpeed_positive {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) : 0<lowerSpeed A B x := by
  have hh := positive_trig hx
  have hmain := mul_nonneg
    (show 0≤A+1/2-1399/1000 by
      linarith [(primary_mem ht).1,fine_outer_endpoint_bounds.2])
    (show 0≤Real.cos x by linarith [hh.1])
  have hsmall := mul_nonneg ht.1 hh.2.2.1
  dsimp [lowerSpeed]
  nlinarith [hh.1,hh.2.2.2.1]

lemma lowerSource_monotone {A B : ℝ} (ht : OuterState A B) :
    MonotoneOn (lowerSource A B) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (lowerSource_hasDerivAt A B x).continuousAt.continuousWithinAt)
    (fun x _ => lowerSource_hasDerivAt A B x)
    (fun _ hx => (lowerSpeed_positive ht (Ioo_subset_Icc_self hx)).le)

lemma lowerSource_norm {A B : ℝ} (ht : OuterState A B) (x : ℝ) :
    (lowerSource A B x-1/2)^2+(lowerSpeed A B x)^2=Q0-2*B := by
  dsimp [lowerSource,lowerSpeed]
  linear_combination ht.2.2+
    ((B-1/2)^2+(A+1/2)^2)*(Real.sin_sq_add_cos_sq x)

lemma lower_active_speed {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (ha : lowerSource A B x∈Icc outerDiagonal outerAxial) :
    1<PPrimaryLabel.d1 (lowerSource A B x)*lowerSpeed A B x := by
  have hv := lowerSpeed_positive ht hx
  have hn := lowerSource_norm ht x
  have hcenter : 0≤lowerSource A B x-1/2 ∧ lowerSource A B x-1/2<183/200 := by
    constructor <;> linarith [ha.1,ha.2,fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.1]
  have hB : B<(9/10:ℝ) := (source_mem ht).2.trans_lt outer_endpoint_bounds.2.2.2
  have hspeed : (11/10:ℝ)<lowerSpeed A B x := by
    norm_num [Q0] at hn
    nlinarith
  have hM := OppositeTwo.M_first_lower ha
  have hh := mul_lt_mul hM hspeed.le (by norm_num : (0:ℝ)<11/10)
    (by linarith [hM] : 0≤PPrimaryLabel.d1 (lowerSource A B x))
  norm_num at hh
  linarith

lemma lowerSource_cap {A B : ℝ} (ht : OuterState A B) :
    outerDiagonal<lowerSource A B (7/10) := by
  have htr := CommonQuarter.cap_trig
  have hcos0 : 0≤Real.cos (7/10:ℝ) := by linarith [htr.2.2.1]
  have hsin0 : 0≤Real.sin (7/10:ℝ) := by linarith [htr.1]
  have hlow := mul_nonneg
    (show 0≤1/2-B+2/5 by linarith [(source_mem ht).2,outer_endpoint_bounds.2.2.2]) hcos0
  have hhigh := mul_nonneg
    (show 0≤A+1/2-1399/1000 by linarith [(primary_mem ht).1,fine_outer_endpoint_bounds.2]) hsin0
  dsimp [lowerSource]
  nlinarith [htr.2.2.2,htr.1,outer_endpoint_bounds.2.2.2]

lemma lower_active_monotone {A B l u : ℝ} (ht : OuterState A B)
    (hl : l∈Icc 0 (7/10)) (hu : u∈Icc 0 (7/10)) (_hlu : l≤u)
    (hleft : outerDiagonal≤lowerSource A B l)
    (hright : lowerSource A B u≤outerAxial) :
    MonotoneOn (fun t => -t+PPrimaryLabel.outer (lowerSource A B t)) (Icc l u) := by
  have hdom (t : ℝ) (htime : t∈Icc l u) :
      t∈Icc 0 (7/10) ∧ lowerSource A B t∈Icc outerDiagonal outerAxial := by
    have htf : t∈Icc 0 (7/10) := ⟨hl.1.trans htime.1,htime.2.trans hu.2⟩
    exact ⟨htf,⟨hleft.trans (lowerSource_monotone ht hl htf htime.1),
      (lowerSource_monotone ht htf hu htime.2).trans hright⟩⟩
  have hd (t : ℝ) (htime : t∈Icc l u) :
      HasDerivAt (fun z => -z+PPrimaryLabel.outer (lowerSource A B z))
        (-1+PPrimaryLabel.d1 (lowerSource A B t)*lowerSpeed A B t) t := by
    have hc := (PPrimaryLabel.outer_hasDerivAt
      (primary_domain (hdom t htime).2)).comp t (lowerSource_hasDerivAt A B t)
    exact (hasDerivAt_id' t).neg.add hc
  exact monoOn_of_hasDeriv_nonneg
    (fun t htime => (hd t htime).continuousAt.continuousWithinAt)
    (fun t htime => hd t (Ioo_subset_Icc_self htime))
    (fun t htime => by
      have h := hdom t (Ioo_subset_Icc_self htime)
      linarith [lower_active_speed ht h.1 h.2])

theorem original_lower_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2-x)) :
    (8977827/10000000:ℝ)<value b B (Real.pi/2-x) := by
  have hcut := lower_source_cut hx hm
  have ha := primary_mem hs
  have hactual : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
  by_cases hstart : outerDiagonal≤1-B
  · have hzero : outerDiagonal≤lowerSource A B 0 := by simpa only [lowerSource_zero] using hstart
    have hmono := lower_active_monotone ht (by norm_num) hx hx.1 hzero (hcut.trans ha.2)
    have hstep := hmono (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hx.1⟩)
      (show x∈Icc 0 x from ⟨hx.1,le_rfl⟩) hx.1
    have hxdom : lowerSource A B x∈Icc outerDiagonal outerAxial :=
      ⟨hzero.trans (lowerSource_monotone ht (by norm_num) hx hx.1),hcut.trans ha.2⟩
    have hM := OppositeTwo.M_monotone hxdom ha hcut
    rw [hactual] at hM
    dsimp only at hstep
    rw [lowerSource_zero] at hstep
    have hbase := aligned_lower (show 1-B∈Icc outerDiagonal 1 from ⟨hstart,by linarith [ht.1]⟩)
    have harg : 1-(1-B)=B := by ring
    dsimp [aligned] at hbase
    rw [harg] at hbase
    dsimp [value]
    linarith
  · have hcont : Continuous (lowerSource A B) :=
      continuous_iff_continuousAt.2 fun y => (lowerSource_hasDerivAt A B y).continuousAt
    obtain ⟨y,hy,hycontact⟩ := intermediate_value_Icc
      (show (0:ℝ)≤7/10 by norm_num) hcont.continuousOn
      (show outerDiagonal∈Icc (lowerSource A B 0) (lowerSource A B (7/10)) by
        rw [lowerSource_zero]
        exact ⟨by linarith,(lowerSource_cap ht).le⟩)
    have hdiag := PrimaryDiagonal.original_contact ht hy hycontact
    rcases le_total x y with hxy | hyx
    · have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
      have hP := P_monotone (source_mem hs) hd (source_mem hs).2
      dsimp [value] at *
      linarith
    · have hmono := lower_active_monotone ht hy hx hyx (by rw [hycontact]) (hcut.trans ha.2)
      have hstep := hmono (show y∈Icc y x from ⟨le_rfl,hyx⟩)
        (show x∈Icc y x from ⟨hyx,le_rfl⟩) hyx
      dsimp only at hstep
      rw [hycontact] at hstep
      have hxdom : lowerSource A B x∈Icc outerDiagonal outerAxial := by
        have hh := lowerSource_monotone ht hy hx hyx
        rw [hycontact] at hh
        exact ⟨hh,hcut.trans ha.2⟩
      have hM := OppositeTwo.M_monotone hxdom ha hcut
      rw [hactual] at hM
      have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
      have hD : PPrimaryLabel.outer outerDiagonal= -P outerDiagonal := by
        have hh := PLabel.primary_actual (ShortOuterOne.SameContact.arc_state hd)
        rw [ShortOuterOne.SameContact.arc_diagonal] at hh
        exact hh
      rw [hD] at hstep
      dsimp [value] at *
      linarith

end SquaresInCircles.Eight.SecondWord.NegativeTwo
end
end
end

section
/-!
## One strongly convex primary speed product

The transformed source label and the original target-circle speed give
a product with second derivative greater than `.3` on its full primary
interval.  Its one-point reserve at primary coordinate one proves the
actual lower contact-speed inequality everywhere.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree

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
  have hrad : 0< mass-(a-1/2)^2 := by norm_num [mass,Q0]; nlinarith
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
  have hin : HasDerivAt (fun t => mass-(t-1/2)^2) (-(2*(a-1/2))) a := by
    convert (((hasDerivAt_id' a).sub_const (1/2)).pow 2).const_sub mass using 1
    norm_num
  have hd := hin.sqrt hrad
  show HasDerivAt (fun t => Real.sqrt (mass-(t-1/2)^2))
    (-(a-1/2)/Real.sqrt (mass-(a-1/2)^2)) a
  convert hd using 1
  rw [neg_div,neg_div,mul_div_mul_left _ _ (two_ne_zero)]

lemma product_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt product (first a) a := by
  have h := (TPrimaryLabel.d1_hasDerivAt (primary_domain ha)).mul (speed_hasDerivAt ha)
  have he : first a=TPrimaryLabel.d2 a*speed a+TPrimaryLabel.d1 a*(-(a-1/2)/speed a) := by
    simp only [first]
    ring
  rw [he]
  exact h

lemma first_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt first (second a) a := by
  have hh := data ha
  have h1 : HasDerivAt (fun t => TPrimaryLabel.d1 t*(t-1/2))
      (TPrimaryLabel.d2 a*(a-1/2)+TPrimaryLabel.d1 a*1) a :=
    (TPrimaryLabel.d1_hasDerivAt (primary_domain ha)).mul ((hasDerivAt_id' a).sub_const (1/2))
  have h2 := h1.div (speed_hasDerivAt ha) hh.1.ne'
  have h3 := ((TPrimaryLabel.d2_hasDerivAt (primary_domain ha)).mul (speed_hasDerivAt ha)).sub h2
  have hmass : mass=(speed a)^2+(a-1/2)^2 := by linarith [hh.2.1]
  show HasDerivAt (fun t => TPrimaryLabel.d2 t*speed t-TPrimaryLabel.d1 t*(t-1/2)/speed t)
    (second a) a
  convert h3 using 1
  simp only [second]
  rw [hmass]
  field_simp [hh.1.ne']
  ring

lemma second_positive {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (3/10:ℝ)<second a := by
  have hv := data ha
  have hm := primary_first_lower ha
  have hv3 := pow_pos hv.1 3
  have hv4 := pow_pos hv.1 4
  have he : second a*(speed a)^3=
      TPrimaryLabel.d3 a*(speed a)^4-
        2*TPrimaryLabel.d2 a*(a-1/2)*(speed a)^2-TPrimaryLabel.d1 a*mass := by
    simp only [second]
    field_simp [hv.1.ne']
  have hbase := mul_lt_mul hm hv.2.2.2.2.2.le
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
  have hcube := pow_lt_pow_left₀ hspeed hv.1.le (by norm_num : (3:ℕ)≠0)
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
  have hh := mul_lt_mul hM hs.le hv (by norm_num : (0:ℝ)≤9/10)
  norm_num at hh
  linarith

end SquaresInCircles.Eight.SecondWord.NegativeThree
end
end
end

section
/-!
## The original upper target-secondary owner by finite coordinate comparison

Its original weak separator permits at most `.4*x` of target-coordinate loss from alignment. The
target slope costs less than `1.069` per unit of that coordinate, while the original angle
contributes the full `x`. The aligned bound therefore applies to the original squares themselves
(`original_upper_target_secondary`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma upper_target_displacement {a b x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10)) :
    1-a-upperTarget a b x≤(2/5)*x := by
  have ht := positive_trig hx
  have hc := mul_nonneg
    (show 0≤a-1/2 by linarith [(primary_mem hs).1,fine_outer_endpoint_bounds.2])
    (sub_nonneg.mpr ht.2.1)
  have hsine := mul_le_mul_of_nonneg_right
    (show b-1/2≤(2/5:ℝ) by linarith [(source_mem hs).2,outer_endpoint_bounds.2.2.2])
    ht.2.2.1
  have hxsin := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 (by norm_num : (0:ℝ)≤2/5)
  dsimp [upperTarget]
  nlinarith

theorem original_upper_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2+x)) :
    (8977827/10000000:ℝ)<value b B (Real.pi/2+x) := by
  have hcut := upper_target_cut hx hm
  have hdisp : 1-a-B≤(2/5)*x := by
    linarith [upper_target_displacement hs hx]
  by_cases ha : 1≤a
  · have hbase := original_aligned hs ht (by linarith [ht.1])
    dsimp [value] at *
    linarith [hx.1]
  · have hdom := aligned_domain ⟨(primary_mem hs).1,by linarith⟩
    have hs0 := ShortOuterOne.SameContact.arc_state hdom.2.1
    have hbase := original_aligned hs hs0 (show 1≤a+(1-a) by linarith)
    by_cases hB : 1-a≤B
    · have hT := T_monotone hdom.2.1 (source_mem ht) hB
      dsimp [value] at *
      linarith [hx.1]
    · have hT := T_increment_upper (source_mem ht) hdom.2.1 (by linarith)
      dsimp [value] at *
      nlinarith [hx.1]

end SquaresInCircles.Eight.SecondWord.NegativeTwo
end
end
end

section
/-!
## Both original upper primary/secondary owners for negative edge three

The target-secondary separator loses at most `.4*x` of its aligned
target coordinate.  The target-label increment is less than `.928`
times that loss.  For the source-primary separator the actual target
circle gives a contact-speed product below one; the first contact with
the original source therefore compares directly with alignment.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

theorem original_upper_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2+x)) :
    (93/100:ℝ)<value b B (Real.pi/2+x) := by
  have hcut := NegativeTwo.upper_target_cut hx hm
  have hdisp : 1-a-B≤(2/5)*x := by
    linarith [NegativeTwo.upper_target_displacement hs hx]
  by_cases ha : 1≤a
  · have hbase := original_aligned hs ht (by linarith [ht.1])
    dsimp [value] at *
    linarith [hx.1]
  · have hdom := NegativeTwo.aligned_domain
      (show a∈Icc outerDiagonal 1 from ⟨(NegativeTwo.primary_mem hs).1,by linarith⟩)
    have hs0 := ShortOuterOne.SameContact.arc_state hdom.2.1
    have hbase := original_aligned hs hs0 (show 1≤a+(1-a) by linarith)
    by_cases hB : 1-a≤B
    · have hK := K_monotone hdom.2.1 (NegativeTwo.source_mem ht) hB
      dsimp [value] at *
      linarith [hx.1]
    · have hK := K_increment_upper (NegativeTwo.source_mem ht) hdom.2.1 (by linarith)
      dsimp [value] at *
      nlinarith [hx.1]

theorem original_upper_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    (93/100:ℝ)<value b B (Real.pi/2+x) := by
  by_cases halign : 1≤a+B
  · have hh := original_aligned hs ht halign
    dsimp only [value] at hh ⊢
    linarith [hx.1]
  · have hcut := NegativeTwo.upper_source_cut hx hm
    have hc : Continuous (fun t => -NegativeTwo.upperSource A B t) := by
      dsimp [NegativeTwo.upperSource]
      fun_prop
    obtain ⟨y,hy,hycontact⟩ := intermediate_value_Icc hx.1 hc.continuousOn
      (show -a∈Icc (-NegativeTwo.upperSource A B 0) (-NegativeTwo.upperSource A B x) by
        rw [NegativeTwo.upperSource_zero]
        constructor <;> linarith)
    have he : NegativeTwo.upperSource A B y=a := by linarith
    have hycap : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hx.2⟩
    have hstart : 1-B∈Icc outerDiagonal 1 := by
      constructor <;> linarith [(NegativeTwo.primary_mem hs).1,ht.1]
    have hdom {t : ℝ} (htime : t∈Icc 0 y) :
        t∈Icc 0 (7/10) ∧ NegativeTwo.upperSource A B t∈Icc outerDiagonal 1 := by
      have htcap : t∈Icc 0 (7/10) := ⟨htime.1,htime.2.trans hycap.2⟩
      have hlo := NegativeTwo.upperSource_antitone ht htcap hycap htime.2
      have hhi := NegativeTwo.upperSource_antitone ht (by norm_num) htcap htime.1
      rw [he] at hlo
      rw [NegativeTwo.upperSource_zero] at hhi
      exact ⟨htcap,⟨(NegativeTwo.primary_mem hs).1.trans hlo,hhi.trans hstart.2⟩⟩
    have hd {t : ℝ} (htime : t∈Icc 0 y) :
        HasDerivAt (fun s => s+TPrimaryLabel.outer (NegativeTwo.upperSource A B s))
          (1-TPrimaryLabel.d1 (NegativeTwo.upperSource A B t)*
            NegativeTwo.upperSpeed A B t) t := by
      have hh := (TPrimaryLabel.outer_hasDerivAt
        (primary_domain (NegativeTwo.aligned_domain (hdom htime).2).1)).comp t
          (NegativeTwo.upperSource_hasDerivAt A B t)
      exact ((hasDerivAt_id' t).add hh).congr_deriv (by ring)
    have hmono : MonotoneOn
        (fun s => s+TPrimaryLabel.outer (NegativeTwo.upperSource A B s)) (Icc 0 y) :=
      monoOn_of_hasDeriv_nonneg
        (fun t ht' => (hd ht').continuousAt.continuousWithinAt)
        (fun t ht' => hd (Ioo_subset_Icc_self ht'))
        (fun t ht' => by
          have hh := hdom (Ioo_subset_Icc_self ht')
          linarith [upper_active_speed ht hh.1 hh.2])
    have hstep := hmono ⟨le_rfl,hy.1⟩ ⟨hy.1,le_rfl⟩ hy.1
    dsimp only at hstep
    rw [NegativeTwo.upperSource_zero,he] at hstep
    have hbase := aligned_lower hstart
    have hactual := primary_actual hs
    dsimp only [aligned] at hbase
    dsimp only [value]
    rw [hactual] at hstep
    have harg : 1-(1-B)=B := by ring
    rw [harg] at hbase
    linarith [hy.2]

end SquaresInCircles.Eight.SecondWord.NegativeThree
end
end
end

section
/-!
## The actual diagonal-source contact and its derivative shape

The global target-curvature bound `|T''|<1.335`, together with `T'''>1.6`,
already makes the contact cost's third derivative positive on its
entire physical arc.  No target-sign split or contact curvature rows
are required.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

lemma T_second_abs {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    |TLabel.d2 b|<(267/200:ℝ) := by
  have hz := T_second_monotone outer_zero_mem hb hb.1
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hh := T_second_monotone hb hd hb.2
  have hzero : -(267/200:ℝ)<TLabel.d2 0 := by
    have hr := (outer_ratio_bounds outer_zero_mem).1
    norm_num [RoleLabel.d2,TLabel]
    linarith
  have hdiag : TLabel.d2 outerDiagonal<(267/200:ℝ) := by
    have hD := (outer_ratio_bounds hd).2.2
    have hp := mul_le_mul outer_endpoint_bounds.2.2.2.le hD.2.le hD.1.le (by norm_num)
    norm_num [RoleLabel.d2,TLabel,ratio_diagonal]
    nlinarith
  rw [abs_lt]
  constructor <;> linarith

namespace NegativeTwo.DiagonalSource

def height (x : ℝ) : ℝ := TargetContact.B outerDiagonal x
def speed (x : ℝ) : ℝ := TargetContact.v outerDiagonal x
def cost (x : ℝ) : ℝ := value outerDiagonal (height x) (Real.pi/2-x)
def first (x : ℝ) : ℝ := -1+TLabel.d1 (height x)*speed x
def second (x : ℝ) : ℝ :=
  TLabel.d2 (height x)*(speed x)^2-TLabel.d1 (height x)*(height x-1/2)
def third (x : ℝ) : ℝ := speed x*(TLabel.d3 (height x)*(speed x)^2-
  3*TLabel.d2 (height x)*(height x-1/2)-TLabel.d1 (height x))

def Domain (x : ℝ) : Prop := x∈Icc 0 (7/10) ∧ height x≤outerDiagonal

lemma diagonal_mem : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩

lemma height_zero : height 0=1-outerDiagonal := by
  rw [height,TargetContact.B_zero,ShortOuterOne.SameContact.arc_diagonal]

lemma height_monotone : MonotoneOn height (Icc 0 (7/10)) :=
  TargetContact.B_angle_monotone diagonal_mem

lemma height_hasDerivAt (x : ℝ) : HasDerivAt height (speed x) x :=
  TargetContact.B_angle_hasDerivAt outerDiagonal x

lemma speed_hasDerivAt (x : ℝ) : HasDerivAt speed (1/2-height x) x :=
  TargetContact.v_angle_hasDerivAt outerDiagonal x

lemma domain_data {x : ℝ} (hx : Domain x) :
    height x∈Icc 0 outerDiagonal ∧ 0<speed x ∧ |height x-1/2|<2/5 ∧
      (4889/2500:ℝ)<(speed x)^2 := by
  have hlo := height_monotone (by norm_num) hx.1 hx.1.1
  rw [height_zero] at hlo
  have hheight : height x∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.2],hx.2⟩
  have hv := TargetContact.v_positive diagonal_mem hx.1
  have hz : |height x-1/2|<2/5 := by
    rw [abs_lt]
    constructor <;> linarith [hlo,hx.2,outer_endpoint_bounds.2.2.2]
  have hn : (height x-1/2)^2+(speed x)^2=Q0-2*outerDiagonal := by
    have hh := TargetContact.norm_identity diagonal_mem x
    norm_num [U,ShortOuterOne.SameContact.arc_diagonal,Inverse.q] at hh
    dsimp [height,speed]
    linarith
  have hz2 : (height x-1/2)^2<(4/25:ℝ) := by
    nlinarith [(abs_lt.mp hz).1,(abs_lt.mp hz).2]
  refine ⟨hheight,hv,hz,?_⟩
  norm_num [Q0] at hn
  nlinarith [outer_endpoint_bounds.2.2.2]

lemma domain_before {x t : ℝ} (hx : Domain x) (ht : t∈Icc 0 x) : Domain t := by
  have htcap : t∈Icc 0 (7/10) := ⟨ht.1,ht.2.trans hx.1.2⟩
  exact ⟨htcap,(height_monotone htcap hx.1 ht.2).trans hx.2⟩

lemma cost_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt cost (first x) x := by
  have hT := (TLabel.outer_hasDerivAt (outer_domain (domain_data hx).1)).comp x
    (height_hasDerivAt x)
  have hd := (((hasDerivAt_id' x).const_sub (Real.pi/2)).sub_const
    (P outerDiagonal)).add hT
  exact hd.congr_deriv (by simp only [first])

lemma first_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt first (second x) x := by
  have hT := (TLabel.d1_hasDerivAt (outer_domain (domain_data hx).1)).comp x
    (height_hasDerivAt x)
  have hd := (hT.mul (speed_hasDerivAt x)).const_add (-1)
  exact hd.congr_deriv (by simp only [second,Function.comp_apply]; ring)

lemma second_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt second (third x) x := by
  have hT := (TLabel.d1_hasDerivAt (outer_domain (domain_data hx).1)).comp x
    (height_hasDerivAt x)
  have hTT := (TLabel.d2_hasDerivAt (outer_domain (domain_data hx).1)).comp x
    (height_hasDerivAt x)
  have hs2 : HasDerivAt (fun y => (speed y)^2) (2*speed x*(1/2-height x)) x :=
    ((speed_hasDerivAt x).pow 2).congr_deriv (by norm_num)
  have hd := (hTT.mul hs2).sub (hT.mul ((height_hasDerivAt x).sub_const (1/2)))
  exact hd.congr_deriv (by simp only [third,Function.comp_apply]; ring)

lemma third_positive {x : ℝ} (hx : Domain x) : 0<third x := by
  have hd := domain_data hx
  have hT3 := T_third_lower hd.1
  have hT2 := T_second_abs hd.1
  have hT1 := T_first_upper hd.1
  have hprod := mul_le_mul_of_nonneg_left hd.2.2.2.le
    (show 0≤TLabel.d3 (height x) by linarith)
  have hprod' := mul_lt_mul_of_pos_right hT3 (by norm_num : (0:ℝ)<4889/2500)
  have habs : |TLabel.d2 (height x)*(height x-1/2)|<(267/500:ℝ) := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left hd.2.2.1.le (abs_nonneg (TLabel.d2 (height x)))
    nlinarith
  have hcharge := (le_abs_self (TLabel.d2 (height x)*(height x-1/2))).trans_lt habs
  have hinside : 0<TLabel.d3 (height x)*(speed x)^2-
      3*TLabel.d2 (height x)*(height x-1/2)-TLabel.d1 (height x) := by
    nlinarith
  exact mul_pos hd.2.1 hinside

lemma second_monotone {x : ℝ} (hx : Domain x) : MonotoneOn second (Icc 0 x) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ ht => (second_hasDerivAt (domain_before hx ht)).continuousAt.continuousWithinAt)
    (fun _ ht => second_hasDerivAt (domain_before hx (Ioo_subset_Icc_self ht)))
    (fun _ ht => (third_positive (domain_before hx (Ioo_subset_Icc_self ht))).le)

end NegativeTwo.DiagonalSource
end SquaresInCircles.Eight.SecondWord
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.DiagonalSource

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig

def dLo : ℝ := 89921406510940/100000000000000
def dHi : ℝ := 89921406510941/100000000000000

lemma point_cage {x sl sh cl ch : ℝ}
    (hs : Real.sin x∈Icc sl sh) (hc : Real.cos x∈Icc cl ch)
    (hsl : 0≤ sl) (hcl : 0≤cl) :
    1/2-(dHi-1/2)*ch+(dLo+1/2)*sl≤height x ∧
      height x≤1/2-(dLo-1/2)*cl+(dHi+1/2)*sh ∧
      (dLo-1/2)*sl+(dLo+1/2)*cl≤ speed x ∧
      speed x≤(dHi-1/2)*sh+(dHi+1/2)*ch := by
  have hd : dLo≤outerDiagonal ∧ outerDiagonal≤dHi :=
    ⟨diagonal_fine.1.le,diagonal_fine.2.le⟩
  have hslow : 0≤Real.sin x := hsl.trans hs.1
  have hclow : 0≤Real.cos x := hcl.trans hc.1
  have hsm := mul_le_mul (show dLo-1/2≤outerDiagonal-1/2 by linarith) hs.1 hsl
    (by linarith [hd.1,show (1/2:ℝ)<dLo by norm_num [dLo]])
  have hsM := mul_le_mul (show outerDiagonal-1/2≤dHi-1/2 by linarith) hs.2 hslow
    (by norm_num [dHi])
  have hsp := mul_le_mul (show dLo+1/2≤outerDiagonal+1/2 by linarith) hs.1 hsl
    (by linarith [hd.1,show (0:ℝ)<dLo by norm_num [dLo]])
  have hsP := mul_le_mul (show outerDiagonal+1/2≤dHi+1/2 by linarith) hs.2 hslow
    (by norm_num [dHi])
  have hcm := mul_le_mul (show dLo-1/2≤outerDiagonal-1/2 by linarith) hc.1 hcl
    (by linarith [hd.1,show (1/2:ℝ)<dLo by norm_num [dLo]])
  have hcM := mul_le_mul (show outerDiagonal-1/2≤dHi-1/2 by linarith) hc.2 hclow
    (by norm_num [dHi])
  have hcp := mul_le_mul (show dLo+1/2≤outerDiagonal+1/2 by linarith) hc.1 hcl
    (by linarith [hd.1,show (0:ℝ)<dLo by norm_num [dLo]])
  have hcP := mul_le_mul (show outerDiagonal+1/2≤dHi+1/2 by linarith) hc.2 hclow
    (by norm_num [dHi])
  dsimp [height,speed,TargetContact.B,TargetContact.v]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

lemma four_trig :
    Real.sin (2/5:ℝ)∈Icc (97354585577/250000000000) (38941834231/100000000000) ∧
      Real.cos (2/5:ℝ)∈Icc (460530497001/500000000000) (921060994003/1000000000000) := by
  have hs := sin11_le_sin (show (0:ℝ)≤2/5 by norm_num)
  have hS := sin_le_sin9 (show (0:ℝ)≤2/5 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤2/5 by norm_num)
  have hC := cos_le_cos12 (show (0:ℝ)≤2/5 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hS hc hC
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma five_trig :
    Real.sin (1/2:ℝ)∈Icc (119856384651/250000000000) (479425538617/1000000000000) ∧
      Real.cos (1/2:ℝ)∈Icc (877582561889/1000000000000) (877582561891/1000000000000) := by
  have hs := sin11_le_sin (show (0:ℝ)≤1/2 by norm_num)
  have hS := sin_le_sin9 (show (0:ℝ)≤1/2 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤1/2 by norm_num)
  have hC := cos_le_cos12 (show (0:ℝ)≤1/2 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hS hc hC
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma four_cage :
    height (2/5)∈Icc (6771791/10000000) (846474/1250000) ∧
      speed (2/5)∈Icc (14442227/10000000) (14442229/10000000) := by
  have hh := point_cage four_trig.1 four_trig.2 (by norm_num) (by norm_num)
  norm_num [dLo,dHi] at hh
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma five_cage :
    height (1/2)∈Icc (2051189/2500000) (8204757/10000000) ∧
      speed (1/2)∈Icc (1774149/1250000) (7096597/5000000) := by
  have hh := point_cage five_trig.1 five_trig.2 (by norm_num) (by norm_num)
  norm_num [dLo,dHi] at hh
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma four_domain : Domain (2/5) :=
  ⟨by norm_num,by linarith [four_cage.1.2,fine_outer_endpoint_bounds.2]⟩

lemma five_domain : Domain (1/2) :=
  ⟨by norm_num,by linarith [five_cage.1.2,fine_outer_endpoint_bounds.2]⟩

lemma four_radical : U (height (2/5))∈Icc (15905499/10000000) (15905501/10000000) := by
  have hc := UW_circle (outer_domain (domain_data four_domain).1)
  have hp := U_positive (outer_domain (domain_data four_domain).1)
  dsimp [W] at hc
  norm_num [Q0] at hc
  constructor <;> nlinarith [four_cage.1.1,four_cage.1.2]

lemma five_radical : U (height (1/2))∈Icc (3684379/2500000) (7368759/5000000) := by
  have hc := UW_circle (outer_domain (domain_data five_domain).1)
  have hp := U_positive (outer_domain (domain_data five_domain).1)
  dsimp [W] at hc
  norm_num [Q0] at hc
  constructor <;> nlinarith [five_cage.1.1,five_cage.1.2]

lemma four_label :
    (6621/12500:ℝ)<T (height (2/5)) ∧
      (7703/12500:ℝ)<TLabel.d1 (height (2/5)) ∧
      TLabel.d1 (height (2/5))<30813/50000 ∧
      (10689/50000:ℝ)<TLabel.d2 (height (2/5)) := by
  have hh := FixedReference.target (domain_data four_domain).1 four_cage.1 four_radical
    (by norm_num) (by norm_num)
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hh
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma five_label : (12443/20000:ℝ)<T (height (1/2)) ∧
    (68923/100000:ℝ)<TLabel.d1 (height (1/2)) ∧
      TLabel.d1 (height (1/2))<17231/25000 := by
  have hh := FixedReference.target (domain_data five_domain).1 five_cage.1 five_radical
    (by norm_num) (by norm_num)
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hh
  exact ⟨by linarith,by linarith,by linarith⟩

lemma four_value : (1819/2000:ℝ)<cost (2/5) := by
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1,P_diagonal_fine,four_label.1]

lemma four_first : first (2/5)<0 := by
  have hh := mul_le_mul four_label.2.2.1.le four_cage.2.2
    (domain_data four_domain).2.1.le (by norm_num : (0:ℝ)≤30813/50000)
  dsimp [first]
  norm_num at hh
  linarith

lemma four_second : (3/10:ℝ)<second (2/5) := by
  have hspeed : (14442227/10000000:ℝ)^2≤(speed (2/5))^2 :=
    pow_le_pow_left₀ (by norm_num) four_cage.2.1 2
  have hpositive := mul_le_mul four_label.2.2.2.le hspeed
    (by positivity) (by linarith [four_label.2.2.2] : 0≤TLabel.d2 (height (2/5)))
  have hnegative := mul_le_mul four_label.2.2.1.le
    (show height (2/5)-1/2≤846474/1250000-1/2 by linarith [four_cage.1.2])
    (by linarith [four_cage.1.1] : 0≤height (2/5)-1/2)
    (by norm_num : (0:ℝ)≤30813/50000)
  dsimp [second]
  norm_num at hpositive hnegative
  linarith

lemma five_value : (22551/25000:ℝ)<cost (1/2) := by
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1,P_diagonal_fine,five_label.1]

lemma five_first : |first (1/2)|<(11/500:ℝ) := by
  have hlo := mul_le_mul five_label.2.1.le five_cage.2.1
    (by norm_num : (0:ℝ)≤1774149/1250000)
    (by linarith [five_label.2.1] : 0≤TLabel.d1 (height (1/2)))
  have hhi := mul_le_mul five_label.2.2.le five_cage.2.2
    (domain_data five_domain).2.1.le (by norm_num : (0:ℝ)≤17231/25000)
  rw [abs_lt]
  dsimp [first]
  norm_num at hlo hhi
  constructor <;> linarith

end SquaresInCircles.Eight.SecondWord.NegativeTwo.DiagonalSource
end
end
end
