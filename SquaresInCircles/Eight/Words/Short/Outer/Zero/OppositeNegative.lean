module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroNegativePJ
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeNegativeCurvature
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveZeroGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.PositivePrimary

/-!
# Eight squares: all six negative-angle opposite-sign short-word zero contacts

Four target
intervals are concave between their two actual diagonal endpoints;
the two remaining rows use the written constant multiplier. The
original weak separator is restored using the increasing source label.
-/

section
/-!
## The two increasing multiplier envelopes on the negative half

The multiplier is exactly `.9994`. The original source remainder is kept (`source_lower`); the
target is bounded by its axial or diagonal support (`target_lower`). Both resulting scalar
functions `axial` and `diagonal` increase on the whole angle interval (`derivatives_positive`)
and have a positive initial reserve (`initial_values`), which gives `contact_lower`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative.Multiplier
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open WrongWordCircleSupport

abbrev weight : ℝ := 4997/5000
def Rows (r : Row) : Prop := r=2 ∨ r=3
def sourceFloor (r : Row) : ℝ := if r=2 then 0 else (p r+q r-weight)*outerDiagonal

def axial (r : Row) (x : ℝ) : ℝ := -x+c r+sourceFloor r+weight/2+v r*outerAxial+
  (weight/2)*Real.cos x+weight*(1/2+outerAxial)*Real.sin x
def diagonal (r : Row) (x : ℝ) : ℝ := -x+c r+sourceFloor r+weight/2+
  (v r+t r)*outerDiagonal+weight*(1/2-outerDiagonal)*Real.cos x+
    weight*(1/2+outerDiagonal)*Real.sin x

def axialD (x : ℝ) : ℝ := -1-(weight/2)*Real.sin x+
  weight*(1/2+outerAxial)*Real.cos x
def diagonalD (x : ℝ) : ℝ := -1+weight*(outerDiagonal-1/2)*Real.sin x+
  weight*(outerDiagonal+1/2)*Real.cos x

lemma source_lower (r : Row) (hr : Rows r) {a b : ℝ} (hs : OuterState a b) :
    sourceFloor r≤p r*a+(q r-weight)*b := by
  rcases hr with rfl | rfl
  · norm_num [sourceFloor,p,q,weight]
  · have hh := outer_diagonal_lower (X := p 3) (Y := q 3-weight) hs
      (by norm_num [p]) (by norm_num [p,q,weight])
    have he : sourceFloor 3=(p 3+(q 3-weight))*outerDiagonal := by
      simp only [sourceFloor]
      rw [ite_eq_right (by decide)]
      ring
    rw [he]
    exact hh

lemma target_lower (r : Row) (hr : Rows r) {A B x : ℝ}
    (ht : OuterState A B) (hx : x∈Icc 0 (7/10)) :
    min ((v r+weight*Real.sin x)*outerAxial)
      ((v r+t r+weight*(Real.sin x-Real.cos x))*outerDiagonal)≤
        (v r+weight*Real.sin x)*A+(t r-weight*Real.cos x)*B := by
  have tr := positive_trig hx
  by_cases hX : 0≤v r+weight*Real.sin x
  · apply outer_concave_lower ht hX (min_le_left _ _)
    have hh := min_le_right ((v r+weight*Real.sin x)*outerAxial)
      ((v r+t r+weight*(Real.sin x-Real.cos x))*outerDiagonal)
    nlinarith
  · have hder : (t r-weight*Real.cos x)-(v r+weight*Real.sin x)≤0 := by
      rcases hr with rfl | rfl
      · norm_num [v,t,weight]
        linarith [tr.2.2.2.2.2]
      · have hnon : 0≤v 3+weight*Real.sin x := by
          norm_num [v,weight]
          exact tr.2.2.1
        exact (hX hnon).elim
    have hh := outer_diagonal_lower ht (le_of_not_ge hX) hder
    have hm := min_le_right ((v r+weight*Real.sin x)*outerAxial)
      ((v r+t r+weight*(Real.sin x-Real.cos x))*outerDiagonal)
    nlinarith

lemma axial_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (axial r) (axialD x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -y+c r+sourceFloor r+weight/2+v r*outerAxial) (-1) x := by
    simpa using ((((((hasDerivAt_id x).neg).add_const (c r)).add_const (sourceFloor r)).add_const
       (weight/2)).add_const (v r*outerAxial))
  have h2 : HasDerivAt (fun y => (weight/2)*Real.cos y) ((weight/2)*(-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul _
  have h3 : HasDerivAt (fun y => weight*(1/2+outerAxial)*Real.sin y)
      (weight*(1/2+outerAxial)*Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul _
  have h := (h1.fun_add h2).fun_add h3
  have he : axial r=fun y => -y+c r+sourceFloor r+weight/2+v r*outerAxial+
      (weight/2)*Real.cos y+weight*(1/2+outerAxial)*Real.sin y := rfl
  rw [he]
  convert h using 1
  simp only [axialD]
  ring

lemma diagonal_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (diagonal r) (diagonalD x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -y+c r+sourceFloor r+weight/2+(v r+t r)*outerDiagonal)
      (-1) x := by
    simpa using ((((((hasDerivAt_id x).neg).add_const (c r)).add_const (sourceFloor r)).add_const
       (weight/2)).add_const ((v r+t r)*outerDiagonal))
  have h2 : HasDerivAt (fun y => weight*(1/2-outerDiagonal)*Real.cos y)
      (weight*(1/2-outerDiagonal)*(-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul _
  have h3 : HasDerivAt (fun y => weight*(1/2+outerDiagonal)*Real.sin y)
      (weight*(1/2+outerDiagonal)*Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul _
  have h := (h1.fun_add h2).fun_add h3
  have he : diagonal r=fun y => -y+c r+sourceFloor r+weight/2+(v r+t r)*outerDiagonal+
      weight*(1/2-outerDiagonal)*Real.cos y+weight*(1/2+outerDiagonal)*Real.sin y := rfl
  rw [he]
  convert h using 1
  simp only [diagonalD]
  ring

lemma derivatives_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<axialD x ∧ 0<diagonalD x := by
  have tr := positive_trig hx
  have hA := mul_le_mul
    (show (1914/1000:ℝ)≤outerAxial+1/2 by linarith [ShortOuterZero.fine_axial_bounds.1])
    tr.1.le (by norm_num) (by linarith [outer_endpoint_bounds.1])
  have hD := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [ShortMixedZero.fine_diagonal_bounds.1])
    tr.1.le (by norm_num) (by linarith [outer_endpoint_bounds.2.2.1])
  have hsin := mul_nonneg
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1]) tr.2.2.1
  simp only [axialD,diagonalD,weight]
  constructor <;> nlinarith [tr.2.2.2.1]

lemma initial_values (r : Row) (hr : Rows r) :
    (112263/125000:ℝ)<axial r 0 ∧ (112263/125000:ℝ)<diagonal r 0 := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  rcases hr with rfl | rfl <;>
    norm_num [axial,diagonal,sourceFloor,weight,c,p,q,v,t] <;>
    constructor <;> linarith [ha.1,ha.2,hd.1,hd.2]

lemma scalar_lower (r : Row) (hr : Rows r) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (112263/125000:ℝ)< min (axial r x) (diagonal r x) := by
  have ha : MonotoneOn (axial r) (Icc 0 (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (axial_hasDerivAt r x).continuousAt.continuousWithinAt)
      (fun x _ => axial_hasDerivAt r x)
      (fun x hx => (derivatives_positive (Ioo_subset_Icc_self hx)).1.le)
  have hd : MonotoneOn (diagonal r) (Icc 0 (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (diagonal_hasDerivAt r x).continuousAt.continuousWithinAt)
      (fun x _ => diagonal_hasDerivAt r x)
      (fun x hx => (derivatives_positive (Ioo_subset_Icc_self hx)).2.le)
  exact lt_min ((initial_values r hr).1.trans_le (ha (by norm_num) hx hx.1))
    ((initial_values r hr).2.trans_le (hd (by norm_num) hx hx.1))

lemma original_projection (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (112263/125000:ℝ)< -x+c r+p r*a+q r*b+v r*A+t r*B := by
  have hsource := source_lower r hr hs
  have htarget := target_lower r hr ht hx
  have hsep := mul_le_mul_of_nonneg_left hm (by norm_num [weight] : (0:ℝ)≤weight)
  have hvalue := scalar_lower r hr hx
  have he : min (axial r x) (diagonal r x)=
      -x+c r+sourceFloor r+weight*(1+Real.sin x+Real.cos x)/2+
        min ((v r+weight*Real.sin x)*outerAxial)
          ((v r+t r+weight*(Real.sin x-Real.cos x))*outerDiagonal) := by
    rw [add_min]
    congr 1 <;> dsimp [axial,diagonal] <;> ring
  rw [he] at hvalue
  generalize min ((v r+weight*Real.sin x)*outerAxial)
    ((v r+t r+weight*(Real.sin x-Real.cos x))*outerDiagonal) = m at hvalue htarget
  simp only [weight] at hsource htarget hsep hvalue
  linarith only [hsource,htarget,hsep,hvalue]

theorem contact_lower (r : Row) (hr : Rows r) {B x : ℝ} (hd : MinusDomain B x) :
    (89809/100000:ℝ)< minusCost r B x := by
  have hs := ShortOuterOne.SameContact.arc_state hd.2.2
  have ht := ShortOuterOne.SameContact.arc_state hd.1
  have he : (1+Real.sin x+Real.cos x)/2=
      minus B x-arc B*Real.sin x+B*Real.cos x := by
    dsimp [minus,SecondWord.OppositeZero.minus]
    ring
  have hh := original_projection r hr hs ht hd.2.1 he.le
  dsimp [minusCost,source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval]
  linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative.Multiplier
end
end
end

section
/-!
## The target-diagonal boundary on the negative half

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
end
end
end

section
/-!
## The source-diagonal curve on the negative half

The
explicit rotated circle is the unchanged original target. Its factor
has negative derivative; the literal target-label cost is concave.
The initial and final endpoints are aligned and double-diagonal.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative.SourceDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (U W outer_domain outer_zero_mem U_positive UW_circle)

abbrev horizontal := SecondWord.NegativeTwo.PrimaryDiagonal.horizontal
abbrev vertical := SecondWord.NegativeTwo.PrimaryDiagonal.vertical
abbrev height := SecondWord.NegativeTwo.PrimaryDiagonal.height
abbrev factor := SecondWord.NegativeTwo.PrimaryDiagonal.factor
abbrev factorD := SecondWord.NegativeTwo.PrimaryDiagonal.factorD

def value (r : Row) (x : ℝ) : ℝ := -x+c r+(p r+q r)*outerDiagonal+
  v r*(horizontal x-1/2)+t r*(vertical x-1/2)
def first (r : Row) (x : ℝ) : ℝ := -1+(t r*horizontal x-v r*vertical x)*factor x
def second (r : Row) (x : ℝ) : ℝ :=
  -(t r*vertical x+v r*horizontal x)*(factor x)^2+
    (t r*horizontal x-v r*vertical x)*factorD x

lemma angle_mem {x : ℝ} (hx : x∈Icc 0 finalAngle) : x∈Icc 0 (7/10) :=
  ⟨hx.1,hx.2.trans final_mem.2⟩

lemma final_height : height finalAngle=outerDiagonal :=
  SecondWord.OppositeZero.NegativePJ.diagonal_original
    (TargetDiagonal.domain ⟨final_bound.1.le,le_rfl⟩) double_contact

lemma target_band {x : ℝ} (hx : x∈Icc 0 finalAngle) : height x∈Icc low outerDiagonal := by
  have hl := SecondWord.NegativeTwo.PrimaryDiagonal.height_monotone
    (by norm_num) (angle_mem hx) hx.1
  have hu := SecondWord.NegativeTwo.PrimaryDiagonal.height_monotone
    (angle_mem hx) final_mem hx.2
  rw [SecondWord.NegativeTwo.PrimaryDiagonal.height_zero] at hl
  rw [show SecondWord.NegativeTwo.PrimaryDiagonal.height finalAngle=outerDiagonal
    from final_height] at hu
  exact ⟨hl,hu⟩

lemma coordinates {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    U (height x)=horizontal x ∧ W (height x)=vertical x := by
  have hband := target_band hx
  have hmem : height x∈Icc 0 outerDiagonal := ⟨low_mem.1.trans hband.1,hband.2⟩
  have hcircle := SecondWord.NegativeTwo.PrimaryDiagonal.circle (angle_mem hx)
  have hactual := UW_circle (outer_domain hmem)
  have hU := U_positive (outer_domain hmem)
  have hu := (SecondWord.NegativeTwo.PrimaryDiagonal.coordinates_positive (angle_mem hx)).1
  have hW : W (height x)=vertical x := by
    dsimp [W,height,SecondWord.NegativeTwo.PrimaryDiagonal.height]
    ring
  rw [hW] at hactual
  exact ⟨by nlinarith,hW⟩

lemma contact {x : ℝ} (hx : x∈Icc 0 finalAngle) : minus (height x) x=outerDiagonal := by
  have hcoords := coordinates hx
  have he : minus (height x) x=1/2+(1-W (height x))*Real.cos x+U (height x)*Real.sin x := by
    simp only [minus,SecondWord.OppositeZero.minus,U,W]
    ring
  rw [he,hcoords.1,hcoords.2]
  dsimp only [horizontal,vertical,SecondWord.NegativeTwo.PrimaryDiagonal.horizontal,
    SecondWord.NegativeTwo.PrimaryDiagonal.vertical,SecondWord.NegativeTwo.PrimaryDiagonal.Z,
    SecondWord.NegativeTwo.PrimaryDiagonal.offset]
  linear_combination (-(1/2+Real.cos x-outerDiagonal))*Real.sin_sq_add_cos_sq x

lemma physical_domain {x : ℝ} (hx : x∈Icc 0 finalAngle) : MinusDomain (height x) x :=
  ⟨⟨low_mem.1.trans (target_band hx).1,(target_band hx).2⟩,angle_mem hx,
    by show minus (height x) x∈_; rw [contact hx]; exact diagonal_mem⟩

lemma original_coordinates {B x : ℝ} (hd : MinusDomain B x)
    (he : minus B x=outerDiagonal) : x∈Icc 0 finalAngle ∧ height x=B :=
  ⟨⟨hd.2.1.1,original_angle hd⟩,
    SecondWord.OppositeZero.NegativePJ.diagonal_original hd he⟩

lemma value_actual (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    value r x=minusCost r (height x) x := by
  have hcoords := coordinates hx
  rw [minusCost,contact hx]
  simp only [source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval,
    ShortOuterOne.SameContact.arc_diagonal,add_zero,zero_mul,zero_add]
  have hA : arc (height x)=horizontal x-1/2 := by
    have hh := hcoords.1
    dsimp [U] at hh
    linarith
  rw [hA]
  dsimp [value,height,SecondWord.NegativeTwo.PrimaryDiagonal.height]
  ring

lemma value_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    HasDerivAt (value r) (first r x) x := by
  have hU := SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt (angle_mem hx)
  have hV := SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt (angle_mem hx)
  have h1 : HasDerivAt (fun y : ℝ => -y+c r+(p r+q r)*outerDiagonal) (-1) x := by
    simpa using (((hasDerivAt_id x).neg).add_const (c r)).add_const ((p r+q r)*outerDiagonal)
  have h2 : HasDerivAt (fun y => v r*(horizontal y-1/2))
      (v r*(-SecondWord.NegativeTwo.PrimaryDiagonal.vertical x*
        SecondWord.NegativeTwo.PrimaryDiagonal.factor x)) x :=
    (hU.sub_const (1/2)).const_mul (v r)
  have h3 : HasDerivAt (fun y => t r*(vertical y-1/2))
      (t r*SecondWord.NegativeTwo.PrimaryDiagonal.speed x) x :=
    (hV.sub_const (1/2)).const_mul (t r)
  have h := (h1.fun_add h2).fun_add h3
  have he : value r=fun y => -y+c r+(p r+q r)*outerDiagonal+
      v r*(horizontal y-1/2)+t r*(vertical y-1/2) := rfl
  rw [he]
  convert h using 1
  simp only [first,SecondWord.NegativeTwo.PrimaryDiagonal.speed]
  ring

lemma first_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    HasDerivAt (first r) (second r x) x := by
  have hU := SecondWord.NegativeTwo.PrimaryDiagonal.horizontal_hasDerivAt (angle_mem hx)
  have hV := SecondWord.NegativeTwo.PrimaryDiagonal.vertical_hasDerivAt (angle_mem hx)
  have hf := SecondWord.NegativeTwo.PrimaryDiagonal.factor_hasDerivAt (angle_mem hx)
  have h := (((hU.const_mul (t r)).fun_sub (hV.const_mul (v r))).fun_mul hf).const_add (-1)
  have he : first r=fun y => -1+(t r*horizontal y-v r*vertical y)*factor y := rfl
  rw [he]
  convert h using 1
  simp only [second,SecondWord.NegativeTwo.PrimaryDiagonal.speed]
  ring

lemma work_signs (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    0<t r*vertical x+v r*horizontal x ∧ 0<t r*horizontal x-v r*vertical x := by
  have hcoords := coordinates hx
  have hband := target_band hx
  have hu := band_root hband
  have hV : (3/5:ℝ)<vertical x := by
    rw [←hcoords.2]
    dsimp [W,low] at *
    linarith [hband.1,outer_endpoint_bounds.2.2.2]
  have hU : 0<horizontal x ∧ horizontal x<(943/500:ℝ) := by
    rw [←hcoords.1]
    exact ⟨by linarith [hu.1],hu.2⟩
  have hfirst : 0<t r*vertical x+v r*horizontal x := by
    fin_cases r <;> norm_num [v,t] <;> linarith
  have htarget := (slope_bounds r (physical_domain hx).1).2.2
  have hh := mul_pos htarget hU.1
  have he : h r (height x)*horizontal x=t r*horizontal x-v r*vertical x := by
    dsimp [h,ratio]
    change (t r-v r*(W (height x)/U (height x)))*horizontal x=_
    rw [hcoords.1,hcoords.2]
    field_simp [hU.1.ne']
  rw [he] at hh
  exact ⟨hfirst,hh⟩

lemma curvature_negative (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) : second r x<0 := by
  have hwork := work_signs r hx
  have hf := SecondWord.NegativeTwo.PrimaryDiagonal.factor_bounds (angle_mem hx)
  have hfd := SecondWord.NegativeTwo.PrimaryDiagonal.factorD_negative (angle_mem hx)
  have hfirst := mul_pos hwork.1 (sq_pos_of_pos (by linarith [hf.1] : 0<factor x))
  have hsecond := mul_neg_of_pos_of_neg hwork.2 hfd
  dsimp [second]
  linarith

lemma endpoints (r : Row) : (89809/100000:ℝ)<value r 0 ∧
    (89809/100000:ℝ)<value r finalAngle := by
  have hz : (0:ℝ)∈Icc 0 finalAngle := ⟨le_rfl,final_bound.1.le⟩
  have ht : finalAngle∈Icc 0 finalAngle := ⟨final_bound.1.le,le_rfl⟩
  constructor
  · rw [value_actual r hz,minusCost,contact hz,
      show height 0=1-outerDiagonal from SecondWord.NegativeTwo.PrimaryDiagonal.height_zero]
    have hh := aligned_original r diagonal_mem low_mem (by dsimp [low]; ring)
    simpa only [neg_zero,zero_add] using hh
  · rw [value_actual r ht,final_height]
    exact (TargetDiagonal.endpoints r).2

theorem lower (r : Row) {x : ℝ} (hx : x∈Icc 0 finalAngle) :
    (89809/100000:ℝ)<value r x := by
  have hc : ConcaveOn ℝ (Icc 0 finalAngle) (value r) :=
    concave_of_deriv2 (fun x hx => value_hasDerivAt r hx)
      (fun x hx => first_hasDerivAt r hx) (fun x hx => (curvature_negative r hx).le)
  exact concave_gt_of_endpoints hc hx (endpoints r).1 (endpoints r).2

theorem original_lower (r : Row) {B x : ℝ} (hd : MinusDomain B x)
    (he : minus B x=outerDiagonal) : (89809/100000:ℝ)< minusCost r B x := by
  obtain ⟨hx,hB⟩ := original_coordinates hd he
  have hh := lower r hx
  rw [value_actual r hx,hB] at hh
  exact hh

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative.SourceDiagonal
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma concave_contact_lower (r : Row) (hr : ConcaveRow r) {B x : ℝ}
    (hd : MinusDomain B x) : (89809/100000:ℝ)< minusCost r B x := by
  obtain ⟨a,ha,hentry,hdom⟩ := entry hd
  have hleft : MinusDomain a x := hdom a ⟨le_rfl,ha.2.trans hd.1.2⟩
  have hc : ConcaveOn ℝ (Icc a outerDiagonal) (fun C => minusCost r C x) :=
    concave_of_deriv2
      (fun C hC => minusCost_target_hasDerivAt r (hdom C hC))
      (fun C hC => minusTarget_hasDerivAt r (hdom C hC))
      (fun C hC => (target_curvature_negative r hr (hdom C hC)).le)
  apply concave_gt_of_endpoints hc ⟨ha.2,hd.1.2⟩
  · exact SourceDiagonal.original_lower r hleft hentry
  · exact TargetDiagonal.lower r hr ⟨hd.2.1.1,original_angle hd⟩

/-- No row-specific curvature, support or contact-boundary premise remains. -/
theorem contact_lower (r : Row) {B x : ℝ} (hd : MinusDomain B x) :
    (89809/100000:ℝ)< minusCost r B x := by
  by_cases hrows : Multiplier.Rows r
  · exact Multiplier.contact_lower r hrows hd
  · have hconcave : ConcaveRow r := by
      fin_cases r <;> simp_all [Multiplier.Rows,ConcaveRow]
    exact concave_contact_lower r hconcave hd

theorem original (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) (-x)) :
    (89809/100000:ℝ)< -x+c r+p r*a+q r*b+v r*A+t r*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hcut : minus B x≤b := by
    have hw := signed_width (show |-x|≤7/10 by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2)
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin,Real.sin_neg,Real.cos_neg] at hm
    rw [hw] at hm
    dsimp [minus,SecondWord.OppositeZero.minus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hd : MinusDomain B x := ⟨hB,hx,⟨by
    linarith [SecondWord.OppositeZero.minus_aligned_le hB hx,hB.2,outer_endpoint_bounds.2.2.2],
    hcut.trans hb.2⟩⟩
  have hsource := source_monotone r hd.2.2 hb hcut
  rw [(source r).outer_actual hs] at hsource
  have hl := contact_lower r hd
  dsimp [minusCost] at hl
  rw [(target r).outer_actual ht] at hl
  dsimp [source,target,SecondWord.RoleLabel.eval] at *
  linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative
end
end
end
