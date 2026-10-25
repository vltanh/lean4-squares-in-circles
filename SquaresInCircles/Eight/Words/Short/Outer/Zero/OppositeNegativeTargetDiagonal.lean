module

public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeAligned
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeNegativeGeometry

/-!
# Eight squares: the target-diagonal boundary on the negative half

Three
rows increase throughout. The remaining row has concave first derivative
and positive initial derivative, so its minimum is at an endpoint. Both
endpoints are the original aligned and double-diagonal contacts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative.TargetDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open SecondWord (U W outer_domain outer_zero_mem UW_circle U_positive)

abbrev b (x : ℝ) : ℝ := minus outerDiagonal x
abbrev speed (x : ℝ) : ℝ := minusSpeed outerDiagonal x
abbrev value (r : Row) (x : ℝ) : ℝ := minusCost r outerDiagonal x
abbrev first (r : Row) (x : ℝ) : ℝ := minusAngle r outerDiagonal x

def second (r : Row) (x : ℝ) : ℝ :=
  -p r*ratioD (b x)*(speed x)^2-l r (b x)*(b x-1/2)
def third (r : Row) (x : ℝ) : ℝ := speed x*
  (-p r*ratioDD (b x)*(speed x)^2+3*p r*ratioD (b x)*(b x-1/2)-l r (b x))

lemma domain {x : ℝ} (hx : x∈Icc 0 finalAngle) : MinusDomain outerDiagonal x := by
  have hxi : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans final_mem.2⟩
  have hh := SecondWord.OppositeZero.minus_angle_monotone diagonal_mem hxi final_mem hx.2
  rw [show SecondWord.OppositeZero.minus outerDiagonal finalAngle=outerDiagonal
    from double_contact] at hh
  have hl := SecondWord.OppositeZero.minus_aligned_le diagonal_mem hxi
  exact ⟨diagonal_mem,hxi,⟨by linarith [outer_endpoint_bounds.2.2.2],hh⟩⟩

lemma square_lower {x : ℝ} (hx : x∈Icc 0 finalAngle) : Q0/2≤(speed x)^2 := by
  have hd := domain hx
  have hband := (band_coordinates hd).2
  have hn := SecondWord.OppositeZero.minus_norm diagonal_mem x
  have hc := UW_circle (outer_domain diagonal_mem)
  rw [U,ShortOuterOne.SameContact.arc_diagonal] at hc
  dsimp [W] at hc
  have hz : (b x-1/2)^2≤(outerDiagonal-1/2)^2 := by
    dsimp [low] at hband
    nlinarith [hband.1,hband.2,outer_endpoint_bounds.2.2.1]
  nlinarith

lemma value_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    HasDerivAt (value r) (first r x) x := minusCost_angle_hasDerivAt r (domain hx)

lemma first_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    HasDerivAt (first r) (second r x) x := by
  have hd := domain hx
  have hl : HasDerivAt (fun y => l r (minus outerDiagonal y))
      (-p r*ratioD (minus outerDiagonal x)*minusSpeed outerDiagonal x) x :=
    (l_hasDerivAt r hd.2.2).comp x (SecondWord.OppositeZero.minus_hasDerivAt outerDiagonal x)
  have hs := SecondWord.OppositeZero.minusSpeed_hasDerivAt outerDiagonal x
  have h := (hl.fun_mul hs).const_add (-1)
  have he : first r=fun y => -1+l r (minus outerDiagonal y)*minusSpeed outerDiagonal y := rfl
  rw [he]
  convert h using 1
  simp only [second,b,speed]
  ring

lemma second_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    HasDerivAt (second r) (third r x) x := by
  have hb := (domain hx).2.2
  have hs := SecondWord.OppositeZero.minus_hasDerivAt outerDiagonal x
  have hv := SecondWord.OppositeZero.minusSpeed_hasDerivAt outerDiagonal x
  have hD : HasDerivAt (fun y => ratioD (minus outerDiagonal y))
      (ratioDD (minus outerDiagonal x)*minusSpeed outerDiagonal x) x :=
    (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).comp x hs
  have hL : HasDerivAt (fun y => l r (minus outerDiagonal y))
      (-p r*ratioD (minus outerDiagonal x)*minusSpeed outerDiagonal x) x :=
    (l_hasDerivAt r hb).comp x hs
  have h := ((hD.const_mul (-p r)).fun_mul (hv.fun_pow 2)).fun_sub
    (hL.fun_mul (hs.sub_const (1/2)))
  have he : second r=fun y => -p r*ratioD (minus outerDiagonal y)*(minusSpeed outerDiagonal y)^2-
      l r (minus outerDiagonal y)*(minus outerDiagonal y-1/2) := rfl
  rw [he]
  convert h using 1
  simp only [third,b,speed,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  ring

lemma increasing (r : Row) (hr : r=0 ∨ r=1 ∨ r=5) {x : ℝ}
    (hx : x∈Icc 0 finalAngle) : 0<first r x := by
  have hd := domain hx
  have hratio := SecondWord.outer_ratio_bounds hd.2.2
  have hL : (76744/100000:ℝ)≤l r (b x) := by
    rcases hr with rfl | rfl | rfl <;> norm_num [l,p,q] <;> linarith [hratio.1,hratio.2.1]
  have hv := (SecondWord.OppositeZero.positive_data hd.1 hd.2.1).2.1
  have hs : (1399/1000:ℝ)<speed x := by
    have hh := square_lower hx
    norm_num [Q0] at hh
    nlinarith
  have hp := mul_le_mul hL hs.le (by norm_num) (by linarith [hL] : 0≤l r (b x))
  dsimp [first,minusAngle]
  nlinarith

lemma row_four_initial : 0<first 4 0 := by
  have hlow := low_ratio
  have hd := ShortMixedZero.fine_diagonal_bounds.1
  have hL : (1034/1000:ℝ)<l 4 low := by
    norm_num [l,p,q]
    linarith
  have heB : b 0=low := by
    simp only [b,minus,SecondWord.OppositeZero.minus,low,Real.cos_zero,Real.sin_zero]
    ring
  have hev : speed 0=outerDiagonal+1/2 := by
    simp [speed,minusSpeed,SecondWord.OppositeZero.minusSpeed,ShortOuterOne.SameContact.arc_diagonal]
  change 0< -1+l 4 (b 0)*speed 0
  rw [heB,hev]
  have hp := mul_le_mul hL.le
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith) (by norm_num)
    (by linarith : 0≤l 4 low)
  nlinarith

lemma row_four_third_negative {x : ℝ} (hx : x∈Icc 0 finalAngle) : third 4 x<0 := by
  have hd := domain hx
  have hL : 0<l 4 (b x) := by linarith [(slope_bounds 4 hd.2.2).1]
  have hv := (SecondWord.OppositeZero.positive_data hd.1 hd.2.1).2.1
  have hD := ShortOuterOne.SameContact.ratioD_pos (outer_domain hd.2.2)
  have hu := U_positive (outer_domain hd.2.2)
  have hDD : 0<ratioDD (b x) := by
    change 0<3*Q0*(b x+1/2)/(U (b x))^5
    exact div_pos (mul_pos (by norm_num [Q0]) (by linarith [hd.2.2.1])) (pow_pos hu 5)
  have hinner : -p 4*ratioDD (b x)*(speed x)^2+
      3*p 4*ratioD (b x)*(b x-1/2)-l 4 (b x)<0 := by
    by_cases hz : b x≤1/2
    · have h1 := mul_nonneg hDD.le (sq_nonneg (speed x))
      have h2 := mul_nonpos_of_nonneg_of_nonpos hD.le (by linarith : b x-1/2≤0)
      norm_num [p]
      nlinarith
    · have hz0 : 0≤b x-1/2 := by linarith
      have hzU : b x-1/2≤(2/5:ℝ) := by
        linarith [hd.2.2.2,outer_endpoint_bounds.2.2.2]
      have hW : 1≤W (b x) := by dsimp [W]; linarith
      have hc := UW_circle (outer_domain hd.2.2)
      have hu2 : (U (b x))^2≤Q0-1 := by nlinarith
      have hprod1 := mul_le_mul_of_nonneg_left (square_lower hx) (by linarith : (0:ℝ)≤W (b x))
      have hprod2 := mul_le_mul_of_nonneg_right hW (by norm_num [Q0] : (0:ℝ)≤Q0/2)
      have hprod3 := mul_le_mul hzU hu2 (sq_nonneg _) (by norm_num)
      have hdominate : (b x-1/2)*(U (b x))^2<W (b x)*(speed x)^2 := by
        have href : (2/5)*(Q0-1)<Q0/2 := by norm_num [Q0]
        linarith
      have hratio : 3*ratioD (b x)*(b x-1/2)<ratioDD (b x)*(speed x)^2 := by
        change 3*(Q0/(U (b x))^3)*(b x-1/2)<
          (3*Q0*W (b x)/(U (b x))^5)*(speed x)^2
        apply (lt_of_mul_lt_mul_right _ (pow_nonneg hu.le 5))
        field_simp [hu.ne']
        have hh := mul_lt_mul_of_pos_left hdominate (by norm_num [Q0] : 0<3*Q0)
        nlinarith
      norm_num [p]
      nlinarith
  exact mul_neg_of_pos_of_neg hv hinner

private lemma minimum_of_concave_first {f d : ℝ→ℝ} {a u x : ℝ}
    (hf : ∀y∈Icc a u,HasDerivAt f (d y) y)
    (hd : ConcaveOn ℝ (Icc a u) d) (ha : 0≤d a) (hx : x∈Icc a u) :
    min (f a) (f u)≤f x := by
  have hleft : a∈Icc a u := ⟨le_rfl,hx.1.trans hx.2⟩
  by_cases hdx : 0≤d x
  · have hm : MonotoneOn f (Icc a x) :=
      monoOn_of_hasDeriv_nonneg
        (fun y hy => (hf y ⟨hy.1,hy.2.trans hx.2⟩).continuousAt.continuousWithinAt)
        (fun y hy => hf y ⟨hy.1.le,hy.2.le.trans hx.2⟩)
        (fun y hy => (le_min ha hdx).trans
          (hd.min_le_of_mem_Icc hleft hx (Ioo_subset_Icc_self hy)))
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)
  · have hm : AntitoneOn f (Icc x u) := by
      apply antiOn_of_hasDeriv_nonpos
        (fun y hy => (hf y ⟨hx.1.trans hy.1,hy.2⟩).continuousAt.continuousWithinAt)
        (fun y hy => hf y ⟨hx.1.trans hy.1.le,hy.2.le⟩)
      intro y hy
      by_contra! hdy
      have hh := hd.min_le_of_mem_Icc hleft
        (show y∈Icc a u from ⟨hx.1.trans hy.1.le,hy.2.le⟩) ⟨hx.1,hy.1.le⟩
      exact hdx ((le_min ha hdy.le).trans hh)
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)

lemma endpoints (r : Row) : (89809/100000:ℝ)<value r 0 ∧
    (89809/100000:ℝ)<value r finalAngle := by
  have hlow := aligned_original r low_mem diagonal_mem (by dsimp [low]; ring)
  have hfinal := double_value r
  constructor
  · have h0 : minus outerDiagonal 0=low := by
      simp only [minus,SecondWord.OppositeZero.minus,Real.cos_zero,Real.sin_zero,low]
      ring
    show 89809/100000< minusCost r outerDiagonal 0
    rw [minusCost,h0]
    simpa only [neg_zero,zero_add] using hlow
  · dsimp [value,minusCost]
    rw [double_contact]
    simp only [source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
      ShortOuterOne.SameContact.arc_diagonal,add_zero,zero_mul,zero_add]
    linarith

theorem lower (r : Row) (hr : ConcaveRow r) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    (89809/100000:ℝ)<value r x := by
  by_cases hfour : r=4
  · subst r
    have hc : ConcaveOn ℝ (Icc 0 finalAngle) (first 4) :=
      concave_of_deriv2 (fun x hx => first_hasDerivAt 4 hx)
        (fun x hx => second_hasDerivAt 4 hx) (fun x hx => (row_four_third_negative hx).le)
    have hh := minimum_of_concave_first (fun x hx => value_hasDerivAt 4 hx)
      hc row_four_initial.le hx
    exact (lt_min (endpoints 4).1 (endpoints 4).2).trans_le hh
  · have hrows : r=0 ∨ r=1 ∨ r=5 := by
      rcases hr with rfl | rfl | rfl | rfl <;> simp_all
    have hm : MonotoneOn (value r) (Icc 0 finalAngle) :=
      monoOn_of_hasDeriv_nonneg
        (fun x hx => (value_hasDerivAt r hx).continuousAt.continuousWithinAt)
        (fun x hx => value_hasDerivAt r (Ioo_subset_Icc_self hx))
        (fun x hx => (increasing r hrows (Ioo_subset_Icc_self hx)).le)
    exact (endpoints r).1.trans_le (hm ⟨le_rfl,final_bound.1.le⟩ hx hx.1)

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative.TargetDiagonal
