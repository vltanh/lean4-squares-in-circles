module

public import SquaresInCircles.Eight.Words.Second.Mixed.TransverseSupportWide
public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoLower
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoDiagonalReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperDiagonalData
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle

/-!
# Eight squares: the physical-cycle negative-outer mixed row and its reflection

`actual_owner` applies the scalar row to the unchanged points of the boundary cycle and the
selected original weak separating axis. Boolean reflection carries the exact role labels to the
opposite quarter role (`original_role`).
-/

section
/-!
## A convex speed product for the complete mixed core corner

The height label is the already proved primary transform of T.  Its
third derivative dominates three times the positive lower derivatives.
Multiplying its first derivative by either core-endpoint contact speed
gives one strictly convex function on the complete height interval.
Its endpoint bounds keep every endpoint cost increasing.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedOuterNegative
open CommonQuarter CorePairGeometry Arithmetic
open NegativeThree

def primaryRange : Set ℝ := Icc (9/10) (6/5)

lemma primaryRange_subset : primaryRange⊆Icc outerDiagonal outerAxial := by
  intro a ha
  exact ⟨by linarith [ha.1,outer_endpoint_bounds.2.2.2],
    by linarith [ha.2,outer_endpoint_bounds.1]⟩

lemma three_first {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    3*TPrimaryLabel.d1 a<TPrimaryLabel.d3 a := by
  have hd (t : ℝ) (ht : t∈Icc outerDiagonal outerAxial) :
      HasDerivAt (fun x => TPrimaryLabel.d3 x-3*TPrimaryLabel.d1 x)
        (TPrimaryLabel.d4 t-3*TPrimaryLabel.d2 t) t :=
    (TPrimaryLabel.d3_hasDerivAt (primary_domain ht)).sub
      ((TPrimaryLabel.d1_hasDerivAt (primary_domain ht)).const_mul 3)
  have hm : MonotoneOn (fun x => TPrimaryLabel.d3 x-3*TPrimaryLabel.d1 x)
      (Icc outerDiagonal outerAxial) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hd t (Ioo_subset_Icc_self ht))
      (fun t ht => by
        have h := Ioo_subset_Icc_self ht
        linarith [primary_fourth_growth h,primary_growth_one h,primary_third_positive h])
  have hh := hm primary_diagonal_mem ha ha.1
  linarith [primary_diagonal_third,primary_diagonal_first]

lemma three_first_second {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    3*TPrimaryLabel.d1 a+3*TPrimaryLabel.d2 a<TPrimaryLabel.d3 a := by
  have hd (t : ℝ) (ht : t∈Icc outerDiagonal outerAxial) :
      HasDerivAt (fun x => TPrimaryLabel.d3 x-3*TPrimaryLabel.d1 x-3*TPrimaryLabel.d2 x)
        (TPrimaryLabel.d4 t-3*TPrimaryLabel.d2 t-3*TPrimaryLabel.d3 t) t :=
    ((TPrimaryLabel.d3_hasDerivAt (primary_domain ht)).sub
      ((TPrimaryLabel.d1_hasDerivAt (primary_domain ht)).const_mul 3)).sub
        ((TPrimaryLabel.d2_hasDerivAt (primary_domain ht)).const_mul 3)
  have hm : MonotoneOn (fun x => TPrimaryLabel.d3 x-3*TPrimaryLabel.d1 x-3*TPrimaryLabel.d2 x)
      (Icc outerDiagonal outerAxial) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hd t (Ioo_subset_Icc_self ht))
      (fun t ht => by
        have h := Ioo_subset_Icc_self ht
        linarith [primary_fourth_growth h,primary_growth_one h])
  have hh := hm primary_diagonal_mem ha ha.1
  linarith [primary_diagonal_third,primary_diagonal_first,primary_diagonal_second]

def coreSpeed (K a : ℝ) : ℝ := Real.sqrt (K-(a-1/2)^2)
def speedProduct (K a : ℝ) : ℝ := TPrimaryLabel.d1 a*coreSpeed K a
def speedProductD (K a : ℝ) : ℝ :=
  TPrimaryLabel.d2 a*coreSpeed K a-TPrimaryLabel.d1 a*(a-1/2)/coreSpeed K a
def speedProductDD (K a : ℝ) : ℝ :=
  TPrimaryLabel.d3 a*coreSpeed K a-2*TPrimaryLabel.d2 a*(a-1/2)/coreSpeed K a-
    TPrimaryLabel.d1 a*K/(coreSpeed K a)^3

lemma speed_data {K a : ℝ} (hK : K∈Icc (112479/100000:ℝ) (169/144))
    (ha : a∈primaryRange) :
    0<coreSpeed K a ∧ (coreSpeed K a)^2=K-(a-1/2)^2 ∧
      (63479/100000:ℝ)≤(coreSpeed K a)^2 ∧
      0<3*(coreSpeed K a)^2-2*(a-1/2) ∧ 0<3*(coreSpeed K a)^4-K := by
  have hz : (2/5:ℝ)≤a-1/2 ∧ a-1/2≤7/10 :=
    ⟨by linarith [ha.1],by linarith [ha.2]⟩
  have hsq := pow_le_pow_left₀ (by linarith [hz.1] : 0≤a-1/2) hz.2 2
  have hr : 0<K-(a-1/2)^2 := by linarith [hK.1]
  have hp : 0<coreSpeed K a := Real.sqrt_pos.mpr hr
  have he : (coreSpeed K a)^2=K-(a-1/2)^2 := Real.sq_sqrt hr.le
  have hlo : (63479/100000:ℝ)≤(coreSpeed K a)^2 := by linarith [hK.1]
  have hfour := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤63479/100000) hlo 2
  refine ⟨hp,he,hlo,by linarith [hz.2],?_⟩
  nlinarith [hK.2]

lemma coreSpeed_hasDerivAt {K a : ℝ} (hK : K∈Icc (112479/100000:ℝ) (169/144))
    (ha : a∈primaryRange) : HasDerivAt (coreSpeed K) (-(a-1/2)/coreSpeed K a) a := by
  have hs := speed_data hK ha
  have hr : K-(a-1/2)^2≠0 := by nlinarith [hs.1,hs.2.1]
  have hd := ((((hasDerivAt_id' (x := a)).sub_const (1/2)).fun_pow 2).const_sub K).sqrt hr
  refine hd.congr_deriv ?_
  have hc : Real.sqrt (K-(a-1/2)^2)=coreSpeed K a := rfl
  rw [hc]
  field_simp
  ring

lemma speedProduct_hasDerivAt {K a : ℝ} (hK : K∈Icc (112479/100000:ℝ) (169/144))
    (ha : a∈primaryRange) : HasDerivAt (speedProduct K) (speedProductD K a) a := by
  have hd := (TPrimaryLabel.d1_hasDerivAt (primary_domain (primaryRange_subset ha))).fun_mul
    (coreSpeed_hasDerivAt hK ha)
  refine hd.congr_deriv ?_
  simp only [speedProductD]
  ring

lemma speedProductD_hasDerivAt {K a : ℝ} (hK : K∈Icc (112479/100000:ℝ) (169/144))
    (ha : a∈primaryRange) : HasDerivAt (speedProductD K) (speedProductDD K a) a := by
  have hs := speed_data hK ha
  have hD := primary_domain (primaryRange_subset ha)
  have hd := ((TPrimaryLabel.d2_hasDerivAt hD).fun_mul (coreSpeed_hasDerivAt hK ha)).fun_sub
    (((TPrimaryLabel.d1_hasDerivAt hD).fun_mul ((hasDerivAt_id' (x := a)).sub_const (1/2))).fun_div
      (coreSpeed_hasDerivAt hK ha) hs.1.ne')
  refine hd.congr_deriv ?_
  have hc := hs.1.ne'
  have h2 := hs.2.1
  simp only [speedProductDD]
  generalize coreSpeed K a = c at hc h2 ⊢
  have hK' : K = c^2+(a-1/2)^2 := by linarith
  subst hK'
  field_simp
  ring

lemma speedProductDD_positive {K a : ℝ} (hK : K∈Icc (112479/100000:ℝ) (169/144))
    (ha : a∈primaryRange) : 0<speedProductDD K a := by
  have hs := speed_data hK ha
  have hfull := primaryRange_subset ha
  have hm : 0<TPrimaryLabel.d1 a := by linarith [primary_first_lower hfull]
  have he : speedProductDD K a*(coreSpeed K a)^3=
      TPrimaryLabel.d3 a*(coreSpeed K a)^4-
        2*TPrimaryLabel.d2 a*(a-1/2)*(coreSpeed K a)^2-TPrimaryLabel.d1 a*K := by
    have hc := hs.1.ne'
    simp only [speedProductDD]
    field_simp
  have hbase := mul_pos hm hs.2.2.2.2
  have hp : 0<speedProductDD K a*(coreSpeed K a)^3 := by
    by_cases hsecond : 0≤TPrimaryLabel.d2 a
    · have hg := mul_lt_mul_of_pos_right (three_first_second hfull) (pow_pos hs.1 4)
      have hpay := mul_nonneg hsecond
        (mul_nonneg (sq_nonneg (coreSpeed K a)) hs.2.2.2.1.le)
      nlinarith
    · have hg := mul_lt_mul_of_pos_right (three_first hfull) (pow_pos hs.1 4)
      have hterm := mul_neg_of_neg_of_pos (lt_of_not_ge hsecond)
        (mul_pos (show 0<a-1/2 by linarith [ha.1]) (pow_pos hs.1 2))
      nlinarith
  by_contra hn
  have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (pow_pos hs.1 3).le
  linarith

lemma speedProduct_endpoints {K : ℝ} (hK : K∈Icc (112479/100000:ℝ) (169/144)) :
    speedProduct K (9/10)<(869/1000:ℝ) ∧ speedProduct K (6/5)<(869/1000:ℝ) := by
  have hl := speed_data hK (show (9/10:ℝ)∈primaryRange by norm_num [primaryRange])
  have hr := speed_data hK (show (6/5:ℝ)∈primaryRange by norm_num [primaryRange])
  have hvL : coreSpeed K (9/10)<(1007/1000:ℝ) := by nlinarith [hK.2,hl.2.1]
  have hvR : coreSpeed K (6/5)<(82681/100000:ℝ) := by nlinarith [hK.2,hr.2.1]
  have hdL := OppositeThree.primary_first_eleven
    (show (9/10:ℝ)∈Icc outerDiagonal (11/10) from
      ⟨by linarith [outer_endpoint_bounds.2.2.2],by norm_num⟩)
  have hdR := OppositeThree.primary_six_fifths_first
  have hpL := (mul_lt_mul_of_pos_right hdL hl.1).trans
    (mul_lt_mul_of_pos_left hvL (by norm_num : (0:ℝ)<17/20))
  have hpR := (mul_lt_mul_of_pos_right hdR hr.1).trans
    (mul_lt_mul_of_pos_left hvR (by norm_num : (0:ℝ)<1051/1000))
  dsimp [speedProduct]
  constructor <;> nlinarith

theorem speedProduct_upper {K a : ℝ} (hK : K∈Icc (112479/100000:ℝ) (169/144))
    (ha : a∈primaryRange) : speedProduct K a<(869/1000:ℝ) := by
  have hc : ConcaveOn ℝ primaryRange (fun x => -speedProduct K x) :=
    concave_of_deriv2
      (fun x hx => (speedProduct_hasDerivAt hK hx).neg)
      (fun x hx => (speedProductD_hasDerivAt hK hx).neg)
      (fun x hx => neg_nonpos.mpr (speedProductDD_positive hK hx).le)
  have he := speedProduct_endpoints hK
  have hh := concave_gt_of_endpoints hc ha
    (show -(869/1000:ℝ)< -speedProduct K (9/10) by linarith [he.1])
    (show -(869/1000:ℝ)< -speedProduct K (6/5) by linarith [he.2])
  linarith

end SquaresInCircles.Eight.SecondWord.MixedOuterNegative
end
end
end

section
/-!
## The complete negative-outer mixed corner contact

The primary separator gives a lower bound on the original outer
height.  The resulting contact cost is concave across the complete
core corner and increases in the complete early angle range.  Two
initial endpoint references therefore bound the whole rectangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedOuterNegative
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig)
open NegativeThree

def earlyAngles : Set ℝ := Icc lowerAngle (549/500)
def contactPrimary (B φ : ℝ) : ℝ :=
  1/2+(MixedCorner.a B+1/2)*Real.cos φ-(B-1/2)*Real.sin φ
def contactTangent (B φ : ℝ) : ℝ := MixedCorner.w B*Real.cos φ+Real.sin φ
def contactSpeed (B φ : ℝ) : ℝ :=
  (MixedCorner.a B+1/2)*Real.sin φ+(B-1/2)*Real.cos φ
def cornerCost (B φ : ℝ) : ℝ := φ+TPrimaryLabel.outer (contactPrimary B φ)+c₀+g*B
def cornerD (B φ : ℝ) : ℝ := -TPrimaryLabel.d1 (contactPrimary B φ)*contactTangent B φ+g
def cornerDD (B φ : ℝ) : ℝ :=
  TPrimaryLabel.d2 (contactPrimary B φ)*(contactTangent B φ)^2-
    TPrimaryLabel.d1 (contactPrimary B φ)*Real.cos φ*(1+(MixedCorner.w B)^2)/MixedCorner.z B

lemma early_subset : earlyAngles⊆Icc lowerAngle (Real.pi/2) :=
  fun φ hφ => ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma early_cosine {φ : ℝ} (hφ : φ∈earlyAngles) : (91/200:ℝ)<Real.cos φ := by
  have hm : AntitoneOn Real.cos (Icc lowerAngle (Real.pi/2)) :=
    antiOn_of_hasDeriv_nonpos
      (fun x _ => Real.continuous_cos.continuousAt.continuousWithinAt)
      (fun x _ => Real.hasDerivAt_cos x)
      (fun x hx => by linarith [(lower_trig (Ioo_subset_Icc_self hx)).1])
  have hh := hm (early_subset hφ)
    (early_subset (show (549/500:ℝ)∈earlyAngles by
      constructor
      · dsimp [lowerAngle]; linarith [pi_hand_enclosure.2]
      · exact le_rfl)) hφ.2
  have hc := HighOrderTaylor.C14_le_cos (x := (549/500:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8] at hc
  linarith

lemma contact_range {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    contactPrimary B φ∈primaryRange := by
  have htr := lower_trig (early_subset hφ)
  have hcos := early_cosine hφ
  have hb := MixedCorner.chart_bounds hB
  have haL : (279/500:ℝ)<MixedCorner.a B := by
    dsimp [MixedCorner.a]
    linarith [hb.1,CoreAngleEndpoint.diagonal_bounds.1]
  have haU : MixedCorner.a B≤(7/12:ℝ) := by dsimp [MixedCorner.a]; linarith [hb.2.1]
  have hAcL := mul_nonneg (show 0≤MixedCorner.a B+1/2-529/500 by linarith) htr.2.2.1
  have hAcU := mul_nonneg (sub_nonneg.mpr haU) htr.2.2.1
  have hBs := mul_nonneg (sub_nonneg.mpr hB.1) (show 0≤Real.sin φ by linarith [htr.1])
  have hBsU := mul_le_mul_of_nonneg_left (Real.sin_le_one φ) (sub_nonneg.mpr hB.1)
  have hBhi : B-1/2<(59/1000:ℝ) := by linarith [hB.2,CoreAngleEndpoint.diagonal_bounds.2]
  dsimp [primaryRange,contactPrimary]
  constructor <;> nlinarith [htr.2.2.2.1]

lemma primary_second_reference : TPrimaryLabel.d2 (6/5)<(803/250:ℝ) := by
  have hh := TPrimaryLabel.second_chart_reference
    (primary_domain OppositeThree.primary_six_fifths_mem)
    (l := (101271911/100000000:ℝ)) (u := (25317978/25000000:ℝ))
    (dlo := (3:ℝ)) (dhi := (803/250:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
    (by norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,W,Q0])
  exact hh.2

lemma primary_second_upper {a : ℝ} (ha : a∈primaryRange) : TPrimaryLabel.d2 a<(803/250:ℝ) := by
  have hm : MonotoneOn TPrimaryLabel.d2 primaryRange :=
    monoOn_of_hasDeriv_nonneg
      (fun x hx => (TPrimaryLabel.d2_hasDerivAt (primary_domain (primaryRange_subset hx))).continuousAt.continuousWithinAt)
      (fun x hx => TPrimaryLabel.d2_hasDerivAt (primary_domain (primaryRange_subset (Ioo_subset_Icc_self hx))))
      (fun x hx => (primary_third_positive (primaryRange_subset (Ioo_subset_Icc_self hx))).le)
  exact (hm ha (by norm_num [primaryRange]) ha.2).trans_lt primary_second_reference

lemma contactPrimary_hasDerivAt_B {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun t => contactPrimary t φ) (-contactTangent B φ) B := by
  refine ((((MixedCorner.a_hasDerivAt hB).add_const (1/2)).mul_const (Real.cos φ)).const_add
    (1/2)).sub (((hasDerivAt_id B).sub_const (1/2)).mul_const (Real.sin φ)) |>.congr_deriv ?_
  simp only [contactTangent]
  ring


lemma contactTangent_hasDerivAt_B {B φ : ℝ} (hB : B∈MixedCorner.domain) :
    HasDerivAt (fun t => contactTangent t φ)
      ((1+(MixedCorner.w B)^2)*Real.cos φ/MixedCorner.z B) B := by
  refine ((MixedCorner.w_hasDerivAt hB).mul_const (Real.cos φ)).add_const (Real.sin φ)
    |>.congr_deriv ?_
  ring


lemma cornerCost_hasDerivAt_B {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    HasDerivAt (fun t => cornerCost t φ) (cornerD B φ) B := by
  refine ((((TPrimaryLabel.outer_hasDerivAt
    (primary_domain (primaryRange_subset (contact_range hB hφ)))).comp B
      (contactPrimary_hasDerivAt_B hB)).const_add φ).add_const c₀).add
        ((hasDerivAt_id B).const_mul g) |>.congr_deriv ?_
  simp only [cornerD]
  ring


lemma cornerD_hasDerivAt_B {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    HasDerivAt (fun t => cornerD t φ) (cornerDD B φ) B := by
  refine ((((TPrimaryLabel.d1_hasDerivAt
    (primary_domain (primaryRange_subset (contact_range hB hφ)))).comp B
      (contactPrimary_hasDerivAt_B hB)).neg.mul (contactTangent_hasDerivAt_B hB)).add_const g)
    |>.congr_deriv ?_
  simp only [cornerDD,Pi.neg_apply,Function.comp_apply]
  ring


lemma cornerDD_negative {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    cornerDD B φ<0 := by
  have ha := contact_range hB hφ
  have hm := primary_first_lower (primaryRange_subset ha)
  have hsecond := primary_second_upper ha
  have hc := early_cosine hφ
  have hz := MixedCorner.z_positive hB
  have hzU := (MixedCorner.chart_bounds hB).2.1
  have hnorm : (contactTangent B φ)^2≤1+(MixedCorner.w B)^2 := by
    have he : (contactTangent B φ)^2+
        (Real.cos φ-MixedCorner.w B*Real.sin φ)^2=1+(MixedCorner.w B)^2 := by
      dsimp [contactTangent]
      linear_combination (1+(MixedCorner.w B)^2)*(Real.sin_sq_add_cos_sq φ)
    nlinarith [sq_nonneg (Real.cos φ-MixedCorner.w B*Real.sin φ)]
  have hprod := (mul_lt_mul_of_pos_left hc (by norm_num : (0:ℝ)<19/25)).trans
    (mul_lt_mul_of_pos_right hm (by linarith [hc] : 0<Real.cos φ))
  have hpay : (803/250:ℝ)<TPrimaryLabel.d1 (contactPrimary B φ)*Real.cos φ/MixedCorner.z B := by
    apply (lt_div_iff₀ hz).2
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hsecond.le (sq_nonneg (contactTangent B φ))
  have hnext := mul_le_mul_of_nonneg_left hnorm (by norm_num : (0:ℝ)≤803/250)
  have hstrict := mul_lt_mul_of_pos_right hpay
    (show 0<1+(MixedCorner.w B)^2 by positivity)
  have heq : TPrimaryLabel.d1 (contactPrimary B φ)*Real.cos φ/MixedCorner.z B*
      (1+(MixedCorner.w B)^2)=TPrimaryLabel.d1 (contactPrimary B φ)*Real.cos φ*
      (1+(MixedCorner.w B)^2)/MixedCorner.z B := by ring
  dsimp only [cornerDD]
  linarith


lemma contactPrimary_hasDerivAt_φ (B φ : ℝ) :
    HasDerivAt (contactPrimary B) (-contactSpeed B φ) φ := by
  refine (((Real.hasDerivAt_cos φ).const_mul (MixedCorner.a B+1/2)).const_add (1/2)).sub
    ((Real.hasDerivAt_sin φ).const_mul (B-1/2)) |>.congr_deriv ?_
  simp only [contactSpeed]
  ring


lemma contactSpeed_eq {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    contactSpeed B φ=coreSpeed ((MixedCorner.a B+1/2)^2+(B-1/2)^2) (contactPrimary B φ) := by
  have ht := lower_trig (early_subset hφ)
  have ha := (CoreAngleEndpoint.state_bounds (MixedCorner.state hB)).1
  have hp : 0<contactSpeed B φ := by
    dsimp [contactSpeed]
    have hfirst := mul_pos (show 0<MixedCorner.a B+1/2 by linarith) (show 0<Real.sin φ by linarith [ht.1])
    have hsecond := mul_nonneg (sub_nonneg.mpr hB.1) ht.2.2.1
    linarith
  have hs := speed_data (MixedCorner.endpoint_mass hB) (contact_range hB hφ)
  have he : (contactSpeed B φ)^2+(contactPrimary B φ-1/2)^2=
      (MixedCorner.a B+1/2)^2+(B-1/2)^2 := by
    dsimp [contactSpeed,contactPrimary]
    linear_combination ((MixedCorner.a B+1/2)^2+(B-1/2)^2)*(Real.sin_sq_add_cos_sq φ)
  nlinarith [hs.1,hs.2.1]

lemma cornerCost_hasDerivAt_φ {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    HasDerivAt (cornerCost B) (1-TPrimaryLabel.d1 (contactPrimary B φ)*contactSpeed B φ) φ := by
  refine (((hasDerivAt_id φ).add
    ((TPrimaryLabel.outer_hasDerivAt (primary_domain (primaryRange_subset (contact_range hB hφ)))).comp φ
      (contactPrimary_hasDerivAt_φ B φ))).add_const c₀).add_const (g*B) |>.congr_deriv ?_
  ring


lemma corner_angle_monotone {B : ℝ} (hB : B∈MixedCorner.domain) :
    MonotoneOn (cornerCost B) earlyAngles := by
  apply monoOn_of_hasDeriv_nonneg
    (fun φ hφ => (cornerCost_hasDerivAt_φ hB hφ).continuousAt.continuousWithinAt)
    (fun φ hφ => cornerCost_hasDerivAt_φ hB (Ioo_subset_Icc_self hφ))
  intro φ hφ
  have h := Ioo_subset_Icc_self hφ
  have hh := speedProduct_upper (MixedCorner.endpoint_mass hB) (contact_range hB h)
  rw [contactSpeed_eq hB h]
  dsimp [speedProduct] at hh
  linarith

lemma initial_value_references :
    (-107733/250000:ℝ)<TPrimaryLabel.outer (119789/100000) ∧
      (-489529/1000000:ℝ)<TPrimaryLabel.outer (11371/10000) := by
  have hjoin : (119789/100000:ℝ)∈Icc outerDiagonal outerAxial :=
    ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith [outer_endpoint_bounds.1]⟩
  have hdiag : (11371/10000:ℝ)∈Icc outerDiagonal outerAxial :=
    ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith [outer_endpoint_bounds.1]⟩
  have hj := shifted_chart_reference (primary_domain hjoin)
    (l := (101625269/100000000:ℝ)) (u := (10162527/10000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hd := shifted_chart_reference (primary_domain hdiag)
    (l := (111153209/100000000:ℝ)) (u := (11115321/10000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  dsimp [U] at hj hd
  norm_num [TPrimaryLabel,RoleLabel.primary,TLabel,RoleLabel.outer,RoleLabel.eval,Q0]
  constructor <;> nlinarith

lemma initial_cost_references :
    (9196/10000:ℝ)<cornerCost (1/2) lowerAngle ∧
      (8977/10000:ℝ)<cornerCost CoreAngleEndpoint.diagonal lowerAngle := by
  have hleft : lowerAngle∈earlyAngles :=
    ⟨le_rfl,by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2]⟩
  have hj : (1/2:ℝ)∈MixedCorner.domain :=
    ⟨le_rfl,by linarith [CoreAngleEndpoint.diagonal_bounds.1]⟩
  have hd : CoreAngleEndpoint.diagonal∈MixedCorner.domain :=
    ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl⟩
  have ht := MixedAffine.left_trig
  have hjcut : (119789/100000:ℝ)≤contactPrimary (1/2) lowerAngle := by
    dsimp [contactPrimary]
    rw [MixedCorner.join]
    nlinarith [ht.2.2.1]
  have hdcut : (11371/10000:ℝ)≤contactPrimary CoreAngleEndpoint.diagonal lowerAngle := by
    have hl := mul_nonneg (show 0≤CoreAngleEndpoint.diagonal-55892556/100000000 by
      linarith [CoreAngleEndpoint.diagonal_bounds.1]) (show 0≤Real.cos lowerAngle by linarith [ht.2.2.1])
    have hu := mul_nonneg (show 0≤55892557/100000000-CoreAngleEndpoint.diagonal by
      linarith [CoreAngleEndpoint.diagonal_bounds.2]) (show 0≤Real.sin lowerAngle by linarith [ht.1])
    dsimp [contactPrimary]
    rw [MixedCorner.diagonal]
    nlinarith [ht.2.2.1,ht.2.1]
  have hmj := primary_monotone
    (show (119789/100000:ℝ)∈Icc outerDiagonal outerAxial from
      ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith [outer_endpoint_bounds.1]⟩)
    (primaryRange_subset (contact_range hj hleft)) hjcut
  have hmd := primary_monotone
    (show (11371/10000:ℝ)∈Icc outerDiagonal outerAxial from
      ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith [outer_endpoint_bounds.1]⟩)
    (primaryRange_subset (contact_range hd hleft)) hdcut
  have hla : lowerAngle=Real.pi/2-7/10 := rfl
  dsimp only [cornerCost,g,c₀]
  constructor <;> linarith [initial_value_references.1,initial_value_references.2,
    CoreAngleEndpoint.diagonal_bounds.1,pi_hand_enclosure.1]


theorem corner_lower {B φ : ℝ} (hB : B∈MixedCorner.domain) (hφ : φ∈earlyAngles) :
    (8977/10000:ℝ)<cornerCost B φ := by
  have hleft : lowerAngle∈earlyAngles :=
    ⟨le_rfl,by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2]⟩
  have hc : ConcaveOn ℝ MixedCorner.domain (fun t => cornerCost t lowerAngle) :=
    concave_of_deriv2
      (fun t ht => cornerCost_hasDerivAt_B ht hleft)
      (fun t ht => cornerD_hasDerivAt_B ht hleft)
      (fun t ht => (cornerDD_negative ht hleft).le)
  have hl := concave_gt_of_endpoints hc hB
    (show (8977/10000:ℝ)<cornerCost (1/2) lowerAngle by linarith [initial_cost_references.1])
    initial_cost_references.2
  exact hl.trans_le (corner_angle_monotone hB hleft hφ hφ.1)

end SquaresInCircles.Eight.SecondWord.MixedOuterNegative
end
end
end

section
/-!
## Every original owner for the negative outer to negative core family

The first two early owners are impossible at the actual core point.
The transverse owner uses the whole-circle support; the primary owner
uses the whole side support or the complete corner contact theorem.
The direct late estimate includes the complete upper quarter half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedOuterNegative
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

lemma late_value {a b B φ : ℝ} (hs : OuterState a b) (hB : 0≤B)
    (hφ : (1409/1000:ℝ)≤φ) : γ<value b B φ := by
  have hT := T_upper (NegativeTwo.source_mem hs)
  have hg := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hB
  dsimp [value,c₀,γ]
  linarith

lemma late_corner_value {a b B φ : ℝ} (hs : OuterState a b) (hB : 1/2≤B)
    (hφ : (549/500:ℝ)≤φ) : γ<value b B φ := by
  have hT := T_upper (NegativeTwo.source_mem hs)
  have hg := mul_le_mul_of_nonneg_left hB (show (0:ℝ)≤g by norm_num [g])
  dsimp [value,c₀,g,γ] at *
  linarith

lemma transverse_original {a b B φ : ℝ} (hs : OuterState a b)
    (hφ : φ∈Icc lowerAngle (1409/1000))
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ+B) :
    γ<value b B φ := by
  have hT := MixedTEnvelope.upper (NegativeTwo.source_mem hs)
  have hsupp := outer_circle_lower (X := -g*Real.sin φ) (Y := g*Real.cos φ-q) hs
  have he : Real.sqrt ((-g*Real.sin φ)^2+(g*Real.cos φ-q)^2)=N φ := by
    dsimp [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination (g^2)*(Real.sin_sq_add_cos_sq φ)
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep (show (0:ℝ)≤g by norm_num [g])
  have hcompare : transverse φ<value b B φ := by
    dsimp [transverse,value]
    nlinarith
  have hlow := transverse_lower hφ
  dsimp [γ]
  linarith

lemma side_original {a b B φ : ℝ} (hs : OuterState a b) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-(7/12)*Real.cos φ+B*Real.sin φ) :
    γ<value b B φ := by
  have ht := lower_trig hφ
  have hsine : 0<Real.sin φ := by linarith [ht.1]
  have hT := mul_lt_mul_of_pos_right (MixedTEnvelope.upper (NegativeTwo.source_mem hs)) hsine
  have hsupp := outer_circle_lower (X := -g) (Y := -q*Real.sin φ) hs
  have he : Real.sqrt ((-g)^2+(-q*Real.sin φ)^2)=Real.sqrt (g^2+q^2*(Real.sin φ)^2) := by
    congr 1
    ring
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep (show (0:ℝ)≤g by norm_num [g])
  have hside := side_positive (lower_deviation hφ)
  have heq : side (Real.pi/2-φ)=
      (φ+c₀-k+(g+q)/2-γ)*Real.sin φ+g*(1+(13/12)*Real.cos φ)-
        CommonQuarter.radius*Real.sqrt (g^2+q^2*(Real.sin φ)^2) := by
    simp only [side,sideK,sideN,Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,
      Real.cos_pi_div_two,zero_mul,one_mul,sub_zero]
    ring
  rw [heq] at hside
  have hpositive : 0<(value b B φ-γ)*Real.sin φ := by
    dsimp [value]
    nlinarith
  by_contra hn
  have hh := mul_nonpos_of_nonpos_of_nonneg (show value b B φ-γ≤0 by linarith) hsine.le
  linarith

lemma corner_original {a b A B φ : ℝ} (hs : OuterState a b)
    (hB : 1/2≤B) (hBA : B≤A) (hc : (A-1/2)^2+(B-1/2)^2=(1/12:ℝ)^2)
    (hφ : φ∈earlyAngles)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) :
    γ<value b B φ := by
  obtain ⟨hdom,hA⟩ := MixedCorner.actual hB hBA hc
  have hcut : contactPrimary B φ≤a := by
    dsimp [contactPrimary]
    rw [←hA]
    nlinarith
  have hm := NegativeThree.primary_monotone
    (primaryRange_subset (contact_range hdom hφ)) (NegativeTwo.primary_mem hs) hcut
  rw [NegativeThree.primary_actual hs] at hm
  have hh := corner_lower hdom hφ
  dsimp [cornerCost,value,γ] at *
  linarith

theorem original {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    γ<value b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds ht
  by_cases hlate : (1409/1000:ℝ)≤φ
  · exact late_value hs hcore.2.2.1 hlate
  have hlow : Lower φ :=
    ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],
      by linarith [pi_hand_enclosure.1]⟩
  have htr := lower_trig hlow
  have hsine : 0≤Real.sin φ := by linarith [htr.1]
  have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
  fin_cases j
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤ -b+A*Real.sin φ+B*Real.cos φ := by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    have he : (A*Real.sin φ+B*Real.cos φ)^2+
        (A*Real.cos φ-B*Real.sin φ)^2=A^2+B^2 := by
      linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
    have hlarge : 1≤A*Real.sin φ+B*Real.cos φ := by linarith [hs.1]
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
    have hrad := core_radius_sq ht
    nlinarith [sq_nonneg (A*Real.cos φ-B*Real.sin φ)]
  · have hac := mul_nonneg (show 0≤a by linarith [hs.1,hs.2.1]) htr.2.2.1
    have hbs := mul_nonneg hs.1 hsine
    norm_num [Eight.forwardMargin,lower_width hlow] at hm
    nlinarith [hcore.2.1]
  · apply transverse_original hs ⟨hlow.1,by linarith⟩
    norm_num [Eight.forwardMargin,lower_width hlow] at hm
    linarith
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ := by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    rcases ht with ⟨rfl,hB,hBu⟩ | ⟨hB,hBA,hcircle⟩
    · exact side_original hs hlow hsep
    · by_cases hlate' : (549/500:ℝ)≤φ
      · exact late_corner_value hs hB hlate'
      · exact corner_original hs hB hBA hcircle ⟨hlow.1,by linarith⟩ hsep

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    SecondWord.threshold 3<cost 3 .outer kind false false a b A B φ := by
  rw [threshold_value,MixedThree.outer_core_negative_negative hk hs]
  have hh := original hs ht hφ j hm
  simpa [γ,value,g,c₀] using hh

end SquaresInCircles.Eight.SecondWord.MixedOuterNegative
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedOuterNegative
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Role (i : Vertex) (source target : RadialKind) (σ τ : Bool) : Prop :=
  (i=3 ∧ source=.outer ∧ target≠.outer ∧ σ=false ∧ τ=false) ∨
  (i=5 ∧ source≠.outer ∧ target=.outer ∧ σ=true ∧ τ=true)

theorem original_role {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hrole : Role i source target σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    SecondWord.threshold i<cost i source target σ τ a b A B φ := by
  rcases hrole with ⟨rfl,rfl,hk,rfl,rfl⟩ | ⟨rfl,hk,rfl,rfl,rfl⟩
  · exact literal hk (by simpa [State] using hs) (by simpa [State,hk] using ht)
      hφ j (by simpa [WordProblems.sign] using hm)
  · have hs' : CoreState a b := by simpa [State,hk] using hs
    have ht' : OuterState A B := by simpa [State] using ht
    have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) (-1) φ := by
      rw [show (-1:ℝ)= -(1:ℝ) by ring,margin_reflection]
      simpa [WordProblems.sign] using hm
    have hh := literal hk ht' hs' hφ (reflectedOwner j) hrev
    have he := cost_reflection (3:Vertex) .outer source false false A B a b φ
    norm_num [reverseEdge] at he
    rw [←he] at hh
    simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  exact original_role hrole (actual_state C i) (actual_state C (next i)) hφ j
    (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole j howner

end SquaresInCircles.Eight.SecondWord.MixedOuterNegative
end
end
end
