module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeSpeed
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreePrimaryBounds

/-!
# A convex speed product for the complete mixed core corner

The height label is the already proved primary transform of T.  Its
third derivative dominates three times the positive lower derivatives.
Multiplying its first derivative by either core-endpoint contact speed
gives one strictly convex function on the complete height interval.
Its endpoint bounds keep every endpoint cost increasing.  Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedOuterNegative
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
  convert ((((hasDerivAt_id a).sub_const (1/2)).pow 2).const_sub K).sqrt hr using 1 <;>
    dsimp [coreSpeed] <;> ring

lemma speedProduct_hasDerivAt {K a : ℝ} (hK : K∈Icc (112479/100000:ℝ) (169/144))
    (ha : a∈primaryRange) : HasDerivAt (speedProduct K) (speedProductD K a) a := by
  convert (TPrimaryLabel.d1_hasDerivAt (primary_domain (primaryRange_subset ha))).mul
    (coreSpeed_hasDerivAt hK ha) using 1 <;> dsimp [speedProduct,speedProductD] <;> ring

lemma speedProductD_hasDerivAt {K a : ℝ} (hK : K∈Icc (112479/100000:ℝ) (169/144))
    (ha : a∈primaryRange) : HasDerivAt (speedProductD K) (speedProductDD K a) a := by
  have hs := speed_data hK ha
  have hd := ((TPrimaryLabel.d2_hasDerivAt (primary_domain (primaryRange_subset ha))).mul
    (coreSpeed_hasDerivAt hK ha)).sub
      ((((TPrimaryLabel.d1_hasDerivAt (primary_domain (primaryRange_subset ha))).mul
        ((hasDerivAt_id a).sub_const (1/2))).div (coreSpeed_hasDerivAt hK ha) hs.1.ne')
  convert hd using 1
  · rfl
  · dsimp [speedProductDD]
    field_simp [hs.1.ne']
    nlinarith [hs.2.1]

lemma speedProductDD_positive {K a : ℝ} (hK : K∈Icc (112479/100000:ℝ) (169/144))
    (ha : a∈primaryRange) : 0<speedProductDD K a := by
  have hs := speed_data hK ha
  have hfull := primaryRange_subset ha
  have hm : 0<TPrimaryLabel.d1 a := by linarith [primary_first_lower hfull]
  have he : speedProductDD K a*(coreSpeed K a)^3=
      TPrimaryLabel.d3 a*(coreSpeed K a)^4-
        2*TPrimaryLabel.d2 a*(a-1/2)*(coreSpeed K a)^2-TPrimaryLabel.d1 a*K := by
    dsimp [speedProductDD]
    field_simp [hs.1.ne']
    ring
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

end SquaresInCircles.Eight.TableFree.SecondWord.MixedOuterNegative
