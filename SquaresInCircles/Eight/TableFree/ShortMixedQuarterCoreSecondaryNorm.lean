module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterSecondary

/-!
# Whole-half norm comparisons for positive outer secondary targets

Uncompiled transcription of Section 1, equations (2)--(7), of
`HAND_SHORT_WORD_MIXED_QUARTER_CIRCLE_AND_SIDE_CONTACTS_WITHOUT_TABLES.md`.
The two squared comparisons retain the same sine and cosine. They
prove concavity on each entire half before any endpoint is evaluated.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.CoreSecondaryPositive
open CommonQuarter CorePairGeometry Arithmetic

def lambda : Row→ℝ :=
  ![0,251/400,22771/20000,223/200,0,95269/100000,104073/100000,10853/10000,
    0,0,58829/100000,0,0,99173/100000,95269/100000,23831/25000,
    0,0,19839/20000,0,5507/5000,5637/5000,23831/25000,0]
def mass (r : Row) : ℝ := coP r^2+coQ r^2+lambda r^2
def cosineWeight (r : Row) : ℝ := 2*lambda r*coP r
def sineWeight (r : Row) (upper : Bool) : ℝ := 2*direction upper*lambda r*coQ r
def N (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  CircularNorm.norm (mass r) (cosineWeight r) (sineWeight r upper) x
def N0sq (r : Row) : ℝ := (coP r+lambda r)^2+coQ r^2
def N0 (r : Row) : ℝ := Real.sqrt (N0sq r)
def D (r : Row) : ℝ :=
  if 0≤coP r then N0sq r-lambda r*coP r
  else N0sq r+2*lambda r*|coP r|/(441/250)
def F (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+coC r+(lambda r+coP r+coQ r)/2+
    lambda r*(Real.cos x+(if upper then Real.sin x else 0))-radius*N r upper x
def Fd (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  direction upper+lambda r*(-Real.sin x+(if upper then Real.cos x else 0))-
    radius*CircularNorm.d1 (mass r) (cosineWeight r) (sineWeight r upper) x
def Fdd (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  lambda r*(-Real.cos x-(if upper then Real.sin x else 0))-
    radius*CircularNorm.d2 (mass r) (cosineWeight r) (sineWeight r upper) x

theorem fixed_coefficients (r : Row) (hr : targetPositive r=true) :
    0<lambda r ∧ 0≤sourceSign r*(coG r-lambda r) ∧
    19/50<coP r+(191/250)*lambda r ∧ 0<D r ∧
    31/100<2*lambda r*coQ r-(129/200)*D r ∧
    9/100<(191/250)*N0sq r-lambda r*coQ r-
      lambda r*max 0 (-coP r)*(129/200)/(441/250) ∧
    27/100<4*lambda r-radius*N0 r := by
  have hλ : 0<lambda r := by
    fin_cases r <;> norm_num [targetPositive,lambda] at hr ⊢
  have hroot : 0≤N0 r := Real.sqrt_nonneg _
  have hsq : N0 r^2=N0sq r := Real.sq_sqrt (by dsimp [N0sq]; positivity)
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hR2 := radius_sq
  have hs : Q0*N0sq r<(4*lambda r-27/100)^2 ∧ 0<4*lambda r-27/100 := by
    fin_cases r <;> norm_num [targetPositive,lambda,N0sq,coP,coQ,Q0] at hr ⊢
  have hfixed : 0≤sourceSign r*(coG r-lambda r) ∧
      19/50<coP r+(191/250)*lambda r ∧ 0<D r ∧
      31/100<2*lambda r*coQ r-(129/200)*D r ∧
      9/100<(191/250)*N0sq r-lambda r*coQ r-
        lambda r*max 0 (-coP r)*(129/200)/(441/250) := by
    fin_cases r <;>
      norm_num [targetPositive,lambda,sourceSign,sourcePositive,WordProblems.sign,coP,coQ,coG,D,N0sq] at hr ⊢
  refine ⟨hλ,hfixed.1,hfixed.2.1,hfixed.2.2.1,hfixed.2.2.2.1,hfixed.2.2.2.2,?_⟩
  have hprod := mul_nonneg hR.le hroot
  have hid : (radius*N0 r)^2=Q0*N0sq r := by rw [mul_pow,hR2,hsq]
  nlinarith

theorem energy_identity (r : Row) (upper : Bool) (x : ℝ) :
    CircularNorm.energy (mass r) (cosineWeight r) (sineWeight r upper) x=
      (coP r+lambda r*Real.cos x)^2+(coQ r+direction upper*lambda r*Real.sin x)^2 := by
  cases upper <;> dsimp [CircularNorm.energy,mass,cosineWeight,sineWeight,direction] <;>
    linear_combination -(lambda r)^2*(Real.sin_sq_add_cos_sq x)

theorem energy_positive (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<CircularNorm.energy (mass r) (cosineWeight r) (sineWeight r upper) x := by
  have hh := fixed_coefficients r hr
  have ht := positive_trig hx
  have hp := mul_lt_mul_of_pos_left ht.1 hh.1
  have hpos : 0<coP r+lambda r*Real.cos x := by linarith [hh.2.2.1]
  rw [energy_identity]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hpos) (sq_nonneg _)

theorem norm_nonnegative (r : Row) (upper : Bool) (x : ℝ) : 0≤N r upper x := Real.sqrt_nonneg _
theorem norm_square (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    N r upper x^2=mass r+cosineWeight r*Real.cos x+sineWeight r upper*Real.sin x :=
  CircularNorm.norm_sq (energy_positive r hr upper hx).le

theorem lower_norm (r : Row) (hr : targetPositive r=true) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : N r false x≤N0 r*Real.cos x := by
  obtain ⟨hλ,hrem,hprim,hD,hfirst,hthird,hreserve⟩ := fixed_coefficients r hr
  have ht := positive_trig hx
  have hu := Real.sin_sq_add_cos_sq x
  have hcos := Real.cos_le_one x
  have hlow : (Real.sin x)^2/2≤1-Real.cos x := by nlinarith [sq_nonneg (1-Real.cos x)]
  have hhigh : (441/250)*(1-Real.cos x)≤(Real.sin x)^2 := by
    have hm := mul_nonneg (show 0≤Real.cos x-191/250 by linarith [ht.1])
      (show 0≤1-Real.cos x by linarith)
    nlinarith
  have hcomp : N r false x^2-N0sq r*(Real.cos x)^2≤
      Real.sin x*(D r*Real.sin x-2*lambda r*coQ r) := by
    have hN := norm_square r hr false hx
    have hid : N r false x^2-N0sq r*(Real.cos x)^2=
        N0sq r*(Real.sin x)^2-2*lambda r*coP r*(1-Real.cos x)-
          2*lambda r*coQ r*Real.sin x := by
      rw [hN]
      dsimp [N0sq,mass,cosineWeight,sineWeight,direction]
      linear_combination -((coP r+lambda r)^2+coQ r^2)*(Real.sin_sq_add_cos_sq x)
    by_cases hp : 0≤coP r
    · have hm := mul_nonneg (mul_nonneg hλ.le hp) (sub_nonneg.mpr hlow)
      dsimp [D]
      rw [if_pos hp]
      nlinarith [hid]
    · have hmp : 0≤ -coP r := by linarith
      have hm := mul_nonneg (mul_nonneg hλ.le hmp) (sub_nonneg.mpr hhigh)
      dsimp [D]
      rw [if_neg hp,abs_of_neg (lt_of_not_ge hp)]
      nlinarith [hid]
  have hDs := mul_le_mul_of_nonneg_left ht.2.2.2.1.le hD.le
  have hbr : D r*Real.sin x-2*lambda r*coQ r≤0 := by linarith
  have hneg := mul_nonpos_of_nonneg_of_nonpos ht.2.2.1 hbr
  have h0 := Real.sqrt_nonneg (N0sq r)
  have h02 : N0 r^2=N0sq r := Real.sq_sqrt (by dsimp [N0sq]; positivity)
  have hpos := mul_nonneg h0 (show 0≤Real.cos x by linarith [ht.1])
  nlinarith [norm_nonnegative r false x]

theorem upper_norm (r : Row) (hr : targetPositive r=true) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : N r true x≤N0 r*(Real.cos x+Real.sin x) := by
  obtain ⟨hλ,hrem,hprim,hD,hfirst,hthird,hreserve⟩ := fixed_coefficients r hr
  have ht := positive_trig hx
  have hu := Real.sin_sq_add_cos_sq x
  have hcos := Real.cos_le_one x
  have hN := norm_square r hr true hx
  have hid : N r true x^2-N0sq r*(Real.cos x+Real.sin x)^2=
      2*lambda r*coP r*(Real.cos x-1)+2*lambda r*coQ r*Real.sin x-
        2*N0sq r*Real.cos x*Real.sin x := by
    rw [hN]
    dsimp [N0sq,mass,cosineWeight,sineWeight,direction]
    linear_combination -((coP r+lambda r)^2+coQ r^2)*(Real.sin_sq_add_cos_sq x)
  have hhigh : (441/250)*(1-Real.cos x)≤(Real.sin x)^2 := by
    have hm := mul_nonneg (show 0≤Real.cos x-191/250 by linarith [ht.1])
      (show 0≤1-Real.cos x by linarith)
    nlinarith
  have h02 : N0 r^2=N0sq r := Real.sq_sqrt (by dsimp [N0sq]; positivity)
  have h0 : 0≤N0 r := Real.sqrt_nonneg _
  have hmass : 0≤N0sq r := by dsimp [N0sq]; positivity
  have hkc := mul_le_mul_of_nonneg_left (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) hmass
  have hbound : N r true x^2≤N0sq r*(Real.cos x+Real.sin x)^2 := by
    by_cases hp : 0≤coP r
    · have hpterm := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hλ.le hp)
        (sub_nonpos.mpr hcos)
      have hmargin : lambda r*coQ r-N0sq r*Real.cos x≤0 := by
        rw [max_eq_left (by linarith : -coP r≤0)] at hthird
        linarith
      have hs := mul_nonpos_of_nonneg_of_nonpos ht.2.2.1 hmargin
      nlinarith [hid]
    · have hpterm := mul_nonneg (mul_nonneg hλ.le (show 0≤ -coP r by linarith))
        (sub_nonneg.mpr hhigh)
      have hsine := mul_le_mul_of_nonneg_left ht.2.2.2.1.le
        (mul_nonneg hλ.le (show 0≤ -coP r by linarith))
      rw [max_eq_right (by linarith : 0≤ -coP r)] at hthird
      have hmargin : lambda r*(-coP r)*Real.sin x/(441/250)+
          lambda r*coQ r-N0sq r*Real.cos x≤0 := by linarith
      have hs := mul_nonpos_of_nonneg_of_nonpos ht.2.2.1 hmargin
      nlinarith [hid]
  have hpos := mul_nonneg h0 (add_nonneg (show 0≤Real.cos x by linarith [ht.1]) ht.2.2.1)
  nlinarith [norm_nonnegative r true x]

theorem F_hasDerivAt (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt (F r upper) (Fd r upper x) x := by
  have hn := CircularNorm.norm_hasDerivAt (energy_positive r hr upper hx)
  cases upper
  · convert ((((hasDerivAt_id x).neg).const_add
      (Real.pi/2+coC r+(lambda r+coP r+coQ r)/2)).add
        ((Real.hasDerivAt_cos x).const_mul (lambda r))).sub (hn.const_mul radius) using 1 <;>
      dsimp [F,Fd,angle,direction,N] <;> ring
  · convert (((hasDerivAt_id x).add_const
      (Real.pi/2+coC r+(lambda r+coP r+coQ r)/2)).add
        (((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).const_mul (lambda r))).sub
          (hn.const_mul radius) using 1 <;> dsimp [F,Fd,angle,direction,N] <;> ring

theorem Fd_hasDerivAt (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt (Fd r upper) (Fdd r upper x) x := by
  have hn := CircularNorm.d1_hasDerivAt (energy_positive r hr upper hx)
  cases upper
  · convert (((Real.hasDerivAt_sin x).const_mul (-lambda r)).const_add (-1)).sub
      (hn.const_mul radius) using 1 <;> dsimp [Fd,Fdd,direction] <;> ring
  · convert (((((Real.hasDerivAt_sin x).neg).add (Real.hasDerivAt_cos x)).const_mul
      (lambda r)).const_add 1).sub (hn.const_mul radius) using 1 <;>
      dsimp [Fd,Fdd,direction] <;> ring

theorem curvature (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : Fdd r upper x<0 := by
  obtain ⟨hλ,_,_,_,_,_,hreserve⟩ := fixed_coefficients r hr
  have ht := positive_trig hx
  have hR : 0<radius := by linarith [radius_bounds.1]
  have hcoef : cosineWeight r^2+sineWeight r upper^2≤mass r^2 := by
    cases upper <;> dsimp [cosineWeight,sineWeight,direction,mass] <;>
      nlinarith [sq_nonneg (coP r^2+coQ r^2-lambda r^2)]
  have hcurv := CircularNorm.curvature_lower (energy_positive r hr upper hx) hcoef
  have hmul := mul_le_mul_of_nonneg_left hcurv hR.le
  change radius*(-N r upper x/4)≤_ at hmul
  cases upper
  · have hn := mul_le_mul_of_nonneg_left (lower_norm r hr hx) hR.le
    have hp := mul_pos (show 0<4*lambda r-radius*N0 r by linarith)
      (show 0<Real.cos x by linarith [ht.1])
    dsimp [Fdd]
    nlinarith
  · have hn := mul_le_mul_of_nonneg_left (upper_norm r hr hx) hR.le
    have hp := mul_pos (show 0<4*lambda r-radius*N0 r by linarith)
      (show 0<Real.cos x+Real.sin x by linarith [ht.1,ht.2.2.1])
    dsimp [Fdd]
    nlinarith

theorem concave (r : Row) (hr : targetPositive r=true) (upper : Bool) :
    ConcaveOn ℝ (Icc 0 (7/10)) (F r upper) :=
  concave_of_deriv2 (fun x hx => F_hasDerivAt r hr upper hx)
    (fun x hx => Fd_hasDerivAt r hr upper hx)
    (fun x hx => (curvature r hr upper hx).le)

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.CoreSecondaryPositive
