module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Arithmetic.Taylor
public import SquaresInCircles.Eight.Frames.SeparatingAxis
public import SquaresInCircles.Eight.Words.Common.QuarterState

/-!
# Eight squares: endpoint changes for the common zero-quarter opposite supports

The diagonal support increases away from alignment on both signed halves.
The axial support at multiplier `39/40` does the same. At multiplier
`203/200` a coarse loss of `7/300` still leaves ample reserve. A single
monotone quartic proves the positive-half estimates on the whole interval.
-/

section
/-!
## Whole-angle trigonometric reserves for common quarter-word supports

All inequalities hold on complete closed frame intervals. The only fixed
substitutions are the two geometric endpoints `1/10` and `7/10`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open Arithmetic

theorem tenth_trig :
    9983/100000<Real.sin (1/10:ℝ) ∧ Real.sin (1/10:ℝ)<999/10000 ∧
      199/200≤Real.cos (1/10:ℝ) := by
  have hs := sin_lower_seven (show (0:ℝ)≤1/10 by norm_num)
  have hu := sin_upper_five (show (0:ℝ)≤1/10 by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1/10:ℝ))
  refine ⟨?_,?_,?_⟩
  · have h : (9983/100000:ℝ)<1/10-(1/10)^3/6+(1/10)^5/120-(1/10)^7/5040 := by norm_num
    linarith
  · have h : (1/10:ℝ)-(1/10)^3/6+(1/10)^5/120<999/10000 := by norm_num
    linarith
  · have h : (199/200:ℝ)=1-(1/10)^2/2 := by norm_num
    linarith

theorem cap_trig :
    3221/5000<Real.sin (7/10:ℝ) ∧ Real.sin (7/10:ℝ)<16106/25000 ∧
      19121/25000<Real.cos (7/10:ℝ) ∧ Real.cos (7/10:ℝ)<191211/250000 := by
  have hs := sin_lower_seven (show (0:ℝ)≤7/10 by norm_num)
  have hu := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hcu := cos_le_cos8 (show (0:ℝ)≤7/10 by norm_num)
  norm_num [cos8] at hs hu hc hcu
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem sin_mono {x y : ℝ} (hx : x∈Icc 0 (7/10))
    (hy : y∈Icc 0 (7/10)) (hxy : x≤y) : Real.sin x≤Real.sin y :=
  Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos]) (by linarith [hy.2,Real.pi_gt_three]) hxy

theorem cos_anti {x y : ℝ} (hx : x∈Icc 0 (7/10))
    (hy : y∈Icc 0 (7/10)) (hxy : x≤y) : Real.cos y≤Real.cos x :=
  Real.cos_le_cos_of_nonneg_of_le_pi hx.1
    (by linarith [hy.2,Real.pi_gt_three]) hxy

/-- Uniform signs, rational bounds and the full first-quadrant width. -/
theorem positive_trig {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    19121/25000<Real.cos x ∧ Real.cos x≤1 ∧
      0≤Real.sin x ∧ Real.sin x<16106/25000 ∧
      Real.sin x≤x ∧ 1≤Real.sin x+Real.cos x := by
  have hc := (cap_trig.2.2.1).trans_le
    (cos_anti hx ⟨by norm_num,le_rfl⟩ hx.2)
  have hs0 : 0≤Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_three])
  have hs := (sin_mono hx ⟨by norm_num,le_rfl⟩ hx.2).trans_lt cap_trig.2.1
  have hw := one_le_abs_cos_add_abs_sin x
  rw [abs_of_pos (by linarith : 0<Real.cos x),abs_of_nonneg hs0] at hw
  exact ⟨hc,Real.cos_le_one x,hs0,hs,Real.sin_le hx.1,by linarith⟩

theorem positive_taylor_reserves {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (9/10)*x≤Real.sin x ∧ (47/100)*x^2≤1-Real.cos x ∧
      1-Real.cos x≤x^2/2 := by
  have hs := Real.sin_ge_sub_cube hx.1
  have hc := cos_upper_four hx.1
  have hl := Real.one_sub_sq_div_two_le_cos (x := x)
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hx3 := mul_le_mul_of_nonneg_right hx2 hx.1
  have hx4 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
  exact ⟨by linarith [hx.1],by linarith [sq_nonneg x],by linarith⟩

theorem signed_cos {x : ℝ} (hx : |x|≤7/10) :
    19121/25000<Real.cos x ∧ Real.cos x≤1 := by
  by_cases hp : 0≤x
  · exact ⟨(positive_trig ⟨hp,(abs_le.mp hx).2⟩).1,Real.cos_le_one x⟩
  · have h := positive_trig (x := -x)
      ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    simpa only [Real.cos_neg] using And.intro h.1 h.2.1

theorem signed_sin {x : ℝ} (hx : |x|≤7/10) : |Real.sin x|<16106/25000 := by
  by_cases hp : 0≤x
  · have h := positive_trig ⟨hp,(abs_le.mp hx).2⟩
    simpa only [abs_of_nonneg h.2.2.1] using h.2.2.2.1
  · have h := positive_trig (x := -x)
      ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have hs : Real.sin x≤0 := by simpa only [Real.sin_neg,neg_nonneg] using h.2.2.1
    rw [abs_of_nonpos hs]
    simpa only [Real.sin_neg] using h.2.2.2.1

theorem signed_width {x : ℝ} (hx : |x|≤7/10) :
    pairWidth x=(1+Real.cos x+|Real.sin x|)/2 := by
  have hc : 0<Real.cos x := by linarith [(signed_cos hx).1]
  simp [pairWidth,abs_of_pos hc,add_comm,add_left_comm,add_assoc]

theorem quarter_width {x : ℝ} (hx : |x|≤7/10) :
    pairWidth (Real.pi/2+x)=(1+Real.cos x+|Real.sin x|)/2 := by
  have hc : 0<Real.cos x := by linarith [(signed_cos hx).1]
  simp [pairWidth,Real.sin_add,Real.cos_add,abs_of_pos hc,abs_neg]

/-- A lower harmonic support for all three sine-norm applications. -/
theorem ratio_harmonic {x l : ℝ} (hx : x∈Icc (1/10) (7/10))
    (hl : 1939/2000≤l) :
    (203/200:ℝ)<l*Real.cos x+(3/5)*Real.sin x := by
  have hbase : (203/200:ℝ)<(1939/2000)*Real.cos x+(3/5)*Real.sin x := by
    have hh := harmonic_pos_of_endpoints (K := -(203/200:ℝ))
      (A := (1939/2000:ℝ)) (B := (3/5:ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three]) hx
      (by linarith [tenth_trig.1,tenth_trig.2.2])
      (by linarith [cap_trig.1,cap_trig.2.2.1])
    linarith
  have hc : 0≤Real.cos x := by
    linarith [(positive_trig ⟨by linarith [hx.1],hx.2⟩).1]
  have hm := mul_le_mul_of_nonneg_right hl hc
  linarith

end SquaresInCircles.Eight.CommonQuarter
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

def axialChange (l x : ℝ) : ℝ :=
  x+(l/2)*(Real.cos x-1)+(l/2)*|Real.sin x|-l*outerAxial*Real.sin x

def diagonalChange (l x : ℝ) : ℝ :=
  x+(l/2)*(Real.cos x-1)+(l/2)*|Real.sin x|-
    l*outerDiagonal*(Real.sin x+Real.cos x-1)

def axialPolynomial (l x : ℝ) : ℝ :=
  1-(183/200)*l-(l/4)*x+(61/400)*l*x^2-(61/8000)*l*x^4

theorem axialPolynomial_antitone {l : ℝ} (hl : 0≤l) :
    AntitoneOn (axialPolynomial l) (Icc 0 (7/10)) := by
  have hd (x : ℝ) : HasDerivAt (axialPolynomial l)
      (-l/4+(61/200)*l*x-(61/2000)*l*x^3) x := by
    have h : HasDerivAt (axialPolynomial l)
        (0-l/4*1+(61/400)*l*(((2:ℕ):ℝ)*x^(2-1))-(61/8000)*l*(((4:ℕ):ℝ)*x^(4-1))) x :=
      (((hasDerivAt_const x (1-(183/200)*l)).sub
        ((hasDerivAt_id' x).const_mul (l/4))).add
          ((hasDerivAt_pow 2 x).const_mul ((61/400)*l))).sub
            ((hasDerivAt_pow 4 x).const_mul ((61/8000)*l))
    convert h using 1
    norm_num
    ring
  apply antiOn_of_hasDeriv_nonpos (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => hd x)
  intro x hx
  have hlin := mul_le_mul_of_nonneg_left hx.2.le (show 0≤(61/200)*l by positivity)
  have hcub : 0≤(61/2000)*l*x^3 := by have := hx.1.le; positivity
  nlinarith

theorem axial_change_positive_lower {l x : ℝ} (hl : 0≤l)
    (hx : x∈Icc 0 (7/10)) : x*axialPolynomial l x≤axialChange l x := by
  have ht := positive_trig hx
  have hc := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := x))
    (show 0≤l/2 by positivity)
  have hs := mul_le_mul_of_nonneg_left (sin_upper_five hx.1)
    (show 0≤(183/200)*l by positivity)
  have ha := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.1.le
    (mul_nonneg hl ht.2.2.1)
  dsimp [axialChange,axialPolynomial]
  rw [abs_of_nonneg ht.2.2.1]
  linarith

theorem axial_change_negative_nonneg {l z : ℝ}
    (hl : l∈Icc (39/40) (203/200)) (hz : z∈Icc 0 (7/10)) :
    0≤axialChange l (-z) := by
  have ht := positive_trig hz
  have hr := positive_taylor_reserves hz
  have hl0 : 0≤l := by linarith [hl.1]
  have hz2 := mul_le_mul_of_nonneg_right hz.2 hz.1
  have ha := mul_le_mul_of_nonneg_right outer_endpoint_bounds.1.le
    (mul_nonneg hl0 ht.2.2.1)
  have hs := mul_le_mul_of_nonneg_left hr.1
    (show 0≤(191/100)*l by positivity)
  have hcos := mul_le_mul_of_nonneg_left hr.2.2 (show 0≤l/2 by positivity)
  have hcap := mul_le_mul_of_nonneg_left hz2 (show 0≤l/4 by positivity)
  have hmin := mul_le_mul_of_nonneg_right hl.1 hz.1
  dsimp [axialChange]
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg ht.2.2.1]
  nlinarith

theorem diagonal_change_nonneg {l x : ℝ}
    (hl : l∈Icc (39/40) (203/200)) (hx : |x|≤7/10) :
    0≤diagonalChange l x := by
  have hl0 : 0≤l := by linarith [hl.1]
  have hd0 : 0≤outerDiagonal-1/2 := by linarith [outer_endpoint_bounds.2.2.1]
  by_cases hp : 0≤x
  · have ht := positive_trig ⟨hp,(abs_le.mp hx).2⟩
    have hsum : 0≤Real.sin x+Real.cos x-1 := by linarith [ht.2.2.2.2.2]
    have hupper : Real.sin x+Real.cos x-1≤x := by
      linarith [ht.2.1,ht.2.2.2.2.1]
    have hcoef : l*(outerDiagonal-1/2)<1 := by
      have hh := mul_le_mul_of_nonneg_left outer_endpoint_bounds.2.2.2.le hl0
      have hlh := mul_le_mul_of_nonneg_right hl.2 (show (0:ℝ)≤2/5 by norm_num)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hupper (mul_nonneg hl0 hd0)
    have hmx := mul_le_mul_of_nonneg_right hcoef.le hp
    dsimp [diagonalChange]
    rw [abs_of_nonneg ht.2.2.1]
    nlinarith
  · let z : ℝ := -x
    have hz : z∈Icc 0 (7/10) := ⟨by dsimp [z]; linarith,
      by dsimp [z]; linarith [(abs_le.mp hx).1]⟩
    have ht := positive_trig hz
    have hs := (positive_taylor_reserves hz).1
    have hcoef : (10/9:ℝ)≤l*(outerDiagonal+1/2) := by
      have hh := mul_le_mul_of_nonneg_left outer_endpoint_bounds.2.2.1.le hl0
      have hlh := mul_le_mul_of_nonneg_right hl.1 (show (0:ℝ)≤139/100 by norm_num)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hs
      (show 0≤l*(outerDiagonal+1/2) by positivity)
    have hlow := mul_le_mul_of_nonneg_right hcoef hz.1
    have hcos := mul_nonneg (mul_nonneg hl0 hd0) (by linarith [ht.2.1] : 0≤1-Real.cos z)
    have he : x= -z := by dsimp [z]; ring
    rw [he]
    dsimp [diagonalChange]
    rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg ht.2.2.1]
    nlinarith

/-- The axial support for `39/40` never decreases from alignment. -/
theorem axial_change_39_nonneg {x : ℝ} (hx : |x|≤7/10) :
    0≤axialChange (39/40) x := by
  by_cases hp : 0≤x
  · have hx' : x∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hx).2⟩
    have hpoly := axialPolynomial_antitone (l := (39/40:ℝ)) (by norm_num)
      hx' (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx'.2
    have hcap : 0<axialPolynomial (39/40) (7/10) := by norm_num [axialPolynomial]
    have hm := mul_nonneg hp (by linarith : 0≤axialPolynomial (39/40) x)
    exact hm.trans (axial_change_positive_lower (by norm_num) hx')
  · have hz : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    simpa only [neg_neg] using axial_change_negative_nonneg
      (l := (39/40:ℝ)) (by norm_num) hz

/-- The slightly larger mixed multiplier needs only this small uniform loss. -/
theorem axial_change_203_lower {x : ℝ} (hx : |x|≤7/10) :
    -(7/300:ℝ)≤axialChange (203/200) x := by
  by_cases hp : 0≤x
  · have hx' : x∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hx).2⟩
    have hpoly := axialPolynomial_antitone (l := (203/200:ℝ)) (by norm_num)
      hx' (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx'.2
    have hcap : -(1/30:ℝ)<axialPolynomial (203/200) (7/10) := by
      norm_num [axialPolynomial]
    have hm := mul_le_mul_of_nonneg_right
      (show -(1/30:ℝ)≤axialPolynomial (203/200) x by linarith) hp
    have he := axial_change_positive_lower (l := (203/200:ℝ)) (by norm_num) hx'
    linarith [hx'.2]
  · have hz : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have hh := axial_change_negative_nonneg (l := (203/200:ℝ)) (by norm_num) hz
    simp only [neg_neg] at hh
    linarith

/-- Both actual target endpoints for the opposite outer/outer zero edge. -/
theorem zero_outer_opposite_endpoints {x : ℝ} (hx : |x|≤7/10) :
    (391/400:ℝ)<x+(39/40)*pairWidth x-9/50+(13/200)*outerAxial+
      ((13/200)-(39/40)*Real.sin x)*outerAxial ∧
    (391/400:ℝ)<x+(39/40)*pairWidth x-9/50+(13/200)*outerAxial+
      ((27/25)-(39/40)*(Real.sin x+Real.cos x))*outerDiagonal := by
  have ha := axial_change_39_nonneg hx
  have hd := diagonal_change_nonneg (l := (39/40:ℝ)) (by norm_num) hx
  have hend : (13/200)*outerAxial≤(21/200)*outerDiagonal := by
    linarith [outer_endpoint_bounds.2.1,outer_endpoint_bounds.2.2.1]
  rw [signed_width hx]
  dsimp [axialChange] at ha
  dsimp [diagonalChange] at hd
  constructor <;> nlinarith [outer_endpoint_bounds.1]

/-- Both actual target endpoints for the opposite core/outer zero edge. -/
theorem zero_core_outer_opposite_endpoints {x : ℝ} (hx : |x|≤7/10) :
    (391/400:ℝ)<x+(203/200)*pairWidth x-9/100+
      ((13/200)-(203/200)*Real.sin x)*outerAxial ∧
    (391/400:ℝ)<x+(203/200)*pairWidth x-9/100+
      ((27/25)-(203/200)*(Real.sin x+Real.cos x))*outerDiagonal := by
  have ha := axial_change_203_lower hx
  have hd := diagonal_change_nonneg (l := (203/200:ℝ)) (by norm_num) hx
  rw [signed_width hx]
  dsimp [axialChange] at ha
  dsimp [diagonalChange] at hd
  constructor <;> nlinarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.1]

end SquaresInCircles.Eight.CommonQuarter
end
end
end
