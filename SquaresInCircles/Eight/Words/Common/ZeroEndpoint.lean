module

public import SquaresInCircles.Eight.Words.Common.QuarterState
public import SquaresInCircles.Eight.Words.Common.QuarterTrig

/-!
# Eight squares: endpoint changes for the common zero-quarter opposite supports

The diagonal support increases away from alignment on both signed halves.
The axial support at multiplier `39/40` does the same. At multiplier
`203/200` a coarse loss of `7/300` still leaves ample reserve. A single
monotone quartic proves the positive-half estimates on the whole interval.
-/

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
