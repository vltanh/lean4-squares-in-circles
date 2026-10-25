module

public import SquaresInCircles.Eight.Owners.CircularNorm
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.PositivePrimary

/-!
# Eight squares: pointwise source-sign dominance for the original primary owners

The primary separating inequality is unchanged when the normalized source sign is negative
(`primary_constraint`). The original signed labels dominate that comparison pointwise on the same
state (`core_cost_reduction`, `outer_cost_reduction`). This is only a pair inequality; the vertex
labels of the cyclic sum stay the same.
-/

section
/-!
## Whole-half norm comparisons for positive outer secondary targets

The two squared comparisons retain the same sine and cosine. They
prove concavity on each entire half before any endpoint is evaluated.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.CoreSecondaryPositive
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
    lambda r*(Real.cos x+(if upper then Real.sin x else 0))-CommonQuarter.radius*N r upper x
def Fd (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  direction upper+lambda r*(-Real.sin x+(if upper then Real.cos x else 0))-
    CommonQuarter.radius*CircularNorm.d1 (mass r) (cosineWeight r) (sineWeight r upper) x
def Fdd (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  lambda r*(-Real.cos x-(if upper then Real.sin x else 0))-
    CommonQuarter.radius*CircularNorm.d2 (mass r) (cosineWeight r) (sineWeight r upper) x

theorem fixed_coefficients (r : Row) (hr : targetPositive r=true) :
    0<lambda r ∧ 0≤ sourceSign r*(coG r-lambda r) ∧
    19/50<coP r+(191/250)*lambda r ∧ 0<D r ∧
    31/100<2*lambda r*coQ r-(129/200)*D r ∧
    9/100<(191/250)*N0sq r-lambda r*coQ r-
      lambda r*max 0 (-coP r)*(129/200)/(441/250) ∧
    27/100<4*lambda r-CommonQuarter.radius*N0 r := by
  have hlam : 0<lambda r := by
    revert hr
    fin_cases r <;> norm_num [targetPositive,lambda]
  have hroot : 0≤N0 r := Real.sqrt_nonneg _
  have hsq : N0 r^2=N0sq r := Real.sq_sqrt (by dsimp [N0sq]; positivity)
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hR2 := radius_sq
  have hs : Q0*N0sq r<(4*lambda r-27/100)^2 ∧ 0<4*lambda r-27/100 := by
    revert hr
    fin_cases r <;> norm_num [targetPositive,lambda,N0sq,coP,coQ,Q0]
  have hfixed : 0≤ sourceSign r*(coG r-lambda r) ∧
      19/50<coP r+(191/250)*lambda r ∧ 0<D r ∧
      31/100<2*lambda r*coQ r-(129/200)*D r ∧
      9/100<(191/250)*N0sq r-lambda r*coQ r-
        lambda r*max 0 (-coP r)*(129/200)/(441/250) := by
    revert hr
    fin_cases r <;>
      norm_num [targetPositive,lambda,sourceSign,sourcePositive,WordProblems.sign,coP,coQ,coG,D,N0sq]
  refine ⟨hlam,hfixed.1,hfixed.2.1,hfixed.2.2.1,hfixed.2.2.2.1,hfixed.2.2.2.2,?_⟩
  have hprod := mul_nonneg hR.le hroot
  have hid : (CommonQuarter.radius*N0 r)^2=Q0*N0sq r := by rw [mul_pow,hR2,hsq]
  have hlt := lt_of_pow_lt_pow_left₀ 2 hs.2.le (by rw [hid]; exact hs.1)
  linarith

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

theorem norm_square (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    N r upper x^2=mass r+cosineWeight r*Real.cos x+sineWeight r upper*Real.sin x :=
  CircularNorm.norm_sq (energy_positive r hr upper hx).le

theorem lower_norm (r : Row) (hr : targetPositive r=true) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : N r false x≤N0 r*Real.cos x := by
  obtain ⟨hlam,hrem,hprim,hD,hfirst,hthird,hreserve⟩ := fixed_coefficients r hr
  have ht := positive_trig hx
  have hu := Real.sin_sq_add_cos_sq x
  have hcos := Real.cos_le_one x
  have hlow : (Real.sin x)^2/2≤1-Real.cos x := by linarith [sq_nonneg (1-Real.cos x)]
  have hhigh : (441/250)*(1-Real.cos x)≤(Real.sin x)^2 := by
    have hm := mul_nonneg (show 0≤Real.cos x-191/250 by linarith [ht.1])
      (show 0≤1-Real.cos x by linarith)
    linarith
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
    · have hm := mul_nonneg (mul_nonneg hlam.le hp) (sub_nonneg.mpr hlow)
      dsimp [D]
      rw [ite_eq_left hp]
      linarith [hid]
    · have hmp : 0≤ -coP r := by linarith
      have hm := mul_nonneg (mul_nonneg hlam.le hmp) (sub_nonneg.mpr hhigh)
      dsimp [D]
      rw [ite_eq_right hp,abs_of_neg (lt_of_not_ge hp)]
      linarith [hid]
  have hDs := mul_le_mul_of_nonneg_left ht.2.2.2.1.le hD.le
  have hbr : D r*Real.sin x-2*lambda r*coQ r≤0 := by linarith
  have hneg := mul_nonpos_of_nonneg_of_nonpos ht.2.2.1 hbr
  have h0 : 0≤N0 r := Real.sqrt_nonneg _
  have h02 : N0 r^2=N0sq r := Real.sq_sqrt (by dsimp [N0sq]; positivity)
  have hpos := mul_nonneg h0 (show 0≤Real.cos x by linarith [ht.1])
  exact le_of_pow_le_pow_left₀ two_ne_zero hpos (by rw [mul_pow,h02]; linarith)

theorem upper_norm (r : Row) (hr : targetPositive r=true) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : N r true x≤N0 r*(Real.cos x+Real.sin x) := by
  obtain ⟨hlam,hrem,hprim,hD,hfirst,hthird,hreserve⟩ := fixed_coefficients r hr
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
    linarith
  have h02 : N0 r^2=N0sq r := Real.sq_sqrt (by dsimp [N0sq]; positivity)
  have h0 : 0≤N0 r := Real.sqrt_nonneg _
  have hmass : 0≤N0sq r := by dsimp [N0sq]; positivity
  have hkc := mul_le_mul_of_nonneg_left (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) hmass
  have hbound : N r true x^2≤N0sq r*(Real.cos x+Real.sin x)^2 := by
    by_cases hp : 0≤coP r
    · have hpterm := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hlam.le hp)
        (sub_nonpos.mpr hcos)
      have hmargin : lambda r*coQ r-N0sq r*Real.cos x≤0 := by
        rw [max_eq_left (by linarith : -coP r≤0)] at hthird
        linarith
      have hs := mul_nonpos_of_nonneg_of_nonpos ht.2.2.1 hmargin
      linarith [hid]
    · have hpterm := mul_nonneg (mul_nonneg hlam.le (show 0≤ -coP r by linarith))
        (sub_nonneg.mpr hhigh)
      have hsine := mul_le_mul_of_nonneg_left ht.2.2.2.1.le
        (mul_nonneg hlam.le (show 0≤ -coP r by linarith))
      rw [max_eq_right (by linarith : 0≤ -coP r)] at hthird
      have e1 : lambda r*(-coP r)*Real.sin x/(441/250)=
          (250/441)*(lambda r*(-coP r)*Real.sin x) := by ring
      have e2 : lambda r*(-coP r)*(129/200)/(441/250)=(250/441)*(129/200)*(lambda r*(-coP r)) := by
        ring
      have hlp : 0≤lambda r*(-coP r) := mul_nonneg hlam.le (by linarith)
      have hmargin : lambda r*(-coP r)*Real.sin x/(441/250)+
          lambda r*coQ r-N0sq r*Real.cos x≤0 := by linarith
      have hs := mul_nonpos_of_nonneg_of_nonpos ht.2.2.1 hmargin
      linarith [hid]
  have hpos := mul_nonneg h0 (add_nonneg (show 0≤Real.cos x by linarith [ht.1]) ht.2.2.1)
  exact le_of_pow_le_pow_left₀ two_ne_zero hpos (by rw [mul_pow,h02]; linarith)

theorem F_hasDerivAt (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt (F r upper) (Fd r upper x) x := by
  have hn := CircularNorm.norm_hasDerivAt (energy_positive r hr upper hx)
  cases upper
  · have h := ((((hasDerivAt_id' x).neg).const_add
      (Real.pi/2+coC r+(lambda r+coP r+coQ r)/2)).add
        ((Real.hasDerivAt_cos x).const_mul (lambda r))).sub (hn.const_mul CommonQuarter.radius)
    have hF : F r false=fun y => Real.pi/2+coC r+(lambda r+coP r+coQ r)/2+-y+
        lambda r*Real.cos y-CommonQuarter.radius*CircularNorm.norm (mass r) (cosineWeight r) (sineWeight r false) y := by
      funext y
      simp only [F,angle,direction,N,Bool.false_eq_true,↓reduceIte]
      ring
    rw [hF]
    convert h using 1
    simp only [Fd,direction,Bool.false_eq_true,↓reduceIte]
    ring
  · have h := (((hasDerivAt_id' x).add_const
      (Real.pi/2+coC r+(lambda r+coP r+coQ r)/2)).add
        (((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).const_mul (lambda r))).sub
          (hn.const_mul CommonQuarter.radius)
    have hF : F r true=fun y => y+(Real.pi/2+coC r+(lambda r+coP r+coQ r)/2)+
        lambda r*(Real.cos y+Real.sin y)-
          CommonQuarter.radius*CircularNorm.norm (mass r) (cosineWeight r) (sineWeight r true) y := by
      funext y
      simp only [F,angle,direction,N,↓reduceIte]
      ring
    rw [hF]
    convert h using 1
    simp only [Fd,direction,↓reduceIte]

theorem Fd_hasDerivAt (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt (Fd r upper) (Fdd r upper x) x := by
  have hn := CircularNorm.d1_hasDerivAt (energy_positive r hr upper hx)
  cases upper
  · have h := (((Real.hasDerivAt_sin x).const_mul (-lambda r)).const_add (-1)).sub
      (hn.const_mul CommonQuarter.radius)
    have hF : Fd r false=fun y => -1+-lambda r*Real.sin y-
        CommonQuarter.radius*CircularNorm.d1 (mass r) (cosineWeight r) (sineWeight r false) y := by
      funext y
      simp only [Fd,direction,Bool.false_eq_true,↓reduceIte]
      ring
    rw [hF]
    convert h using 1
    simp only [Fdd,Bool.false_eq_true,↓reduceIte]
    ring
  · have h := (((((Real.hasDerivAt_sin x).neg).add (Real.hasDerivAt_cos x)).const_mul
      (lambda r)).const_add 1).sub (hn.const_mul CommonQuarter.radius)
    have hF : Fd r true=fun y => 1+lambda r*(-Real.sin y+Real.cos y)-
        CommonQuarter.radius*CircularNorm.d1 (mass r) (cosineWeight r) (sineWeight r true) y := by
      funext y
      simp only [Fd,direction,↓reduceIte]
    rw [hF]
    convert h using 1
    simp only [Fdd,↓reduceIte]
    ring

theorem curvature (r : Row) (hr : targetPositive r=true) (upper : Bool)
    {x : ℝ} (hx : x∈Icc 0 (7/10)) : Fdd r upper x<0 := by
  obtain ⟨hlam,_,_,_,_,_,hreserve⟩ := fixed_coefficients r hr
  have ht := positive_trig hx
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hcoef : cosineWeight r^2+sineWeight r upper^2≤ mass r^2 := by
    cases upper <;> dsimp [cosineWeight,sineWeight,direction,mass] <;>
      nlinarith [sq_nonneg (coP r^2+coQ r^2-lambda r^2)]
  have hcurv := CircularNorm.curvature_lower (energy_positive r hr upper hx) hcoef
  have hmul := mul_le_mul_of_nonneg_left hcurv hR.le
  change CommonQuarter.radius*(-N r upper x/4)≤_ at hmul
  cases upper
  · have hn := mul_le_mul_of_nonneg_left (lower_norm r hr hx) hR.le
    have hp := mul_pos (show 0<4*lambda r-CommonQuarter.radius*N0 r by linarith)
      (show 0<Real.cos x by linarith [ht.1])
    dsimp [Fdd]
    nlinarith
  · have hn := mul_le_mul_of_nonneg_left (upper_norm r hr hx) hR.le
    have hp := mul_pos (show 0<4*lambda r-CommonQuarter.radius*N0 r by linarith)
      (show 0<Real.cos x+Real.sin x by linarith [ht.1,ht.2.2.1])
    dsimp [Fdd]
    nlinarith

theorem concave (r : Row) (hr : targetPositive r=true) (upper : Bool) :
    ConcaveOn ℝ (Icc 0 (7/10)) (F r upper) :=
  concave_of_deriv2 (fun _ hx => F_hasDerivAt r hr upper hx)
    (fun _ hx => Fd_hasDerivAt r hr upper hx)
    (fun _ hx => (curvature r hr upper hx).le)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.CoreSecondaryPositive
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry Arithmetic

def primaryRow : Row→Row :=
  ![0,3,2,3,4,7,6,7,4,11,6,11,12,15,14,15,12,19,14,19,20,21,20,23]

theorem primaryRow_signs (r : Row) :
    sourcePositive (primaryRow r)=false ∧ targetPositive (primaryRow r)=targetPositive r := by
  fin_cases r <;> decide
theorem primaryRow_self (r : Row) (hr : sourcePositive r=false) : primaryRow r=r := by
  fin_cases r <;> simp [sourcePositive,primaryRow] at hr ⊢
theorem primary_constraint (r : Row) (a b A B φ : ℝ) :
    sourcePrimary (primaryRow r) a b A B φ↔sourcePrimary r a b A B φ := by
  simp only [sourcePrimary,targetSign,(primaryRow_signs r).2]

theorem core_cost_reduction (r : Row) {a b A B φ : ℝ} (hs : CoreState a b) :
    coreOuterCost (primaryRow r) a b A B φ≤coreOuterCost r a b A B φ := by
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  fin_cases r <;>
    norm_num [coreOuterCost,primaryRow,sourceSign,targetSign,sourcePositive,targetPositive,
      WordProblems.sign,coC,coP,coQ,coG] <;> linarith

theorem outer_sum_lower {a b : ℝ} (hs : OuterState a b) : outerAxial≤a+b := by
  have ha : 0≤a := hs.1.trans hs.2.1
  have he := hs.2.2
  have hax := axial_circle
  have h0 : 0≤outerAxial := by linarith [outer_endpoint_bounds.1]
  have hQ : (1:ℝ)/2≤Q0 := by norm_num [Q0]
  have hprod : 0≤((b+1/2)^2-1/4)*(Q0-1/4-(b+1/2)^2) := by
    apply mul_nonneg
    · nlinarith [hs.1]
    · nlinarith [hs.1,hs.2.1]
  have hA : (a+1/2)^2=Q0-(b+1/2)^2 := by linarith
  have hsq : ((outerAxial+1/2)/2)^2≤((a+1/2)*(b+1/2))^2 := by
    rw [mul_pow,hA]
    nlinarith [hprod,hax]
  have hP : (outerAxial+1/2)/2≤(a+1/2)*(b+1/2) :=
    le_of_pow_le_pow_left₀ (by norm_num) (by nlinarith [hs.1]) hsq
  have hsq2 : (outerAxial+1)^2≤(a+b+1)^2 := by nlinarith [hP,he,hax]
  have := le_of_pow_le_pow_left₀ (by norm_num) (by linarith [hs.1]) hsq2
  linarith

theorem outer_increasing_label_lower {a b X Y : ℝ} (hs : OuterState a b)
    (hY : |X|≤Y) : X*outerAxial≤X*a+Y*b := by
  have hb := outer_bounds hs
  have hy : 0≤Y := (abs_nonneg X).trans hY
  by_cases hx : 0≤X
  · have hsum := mul_le_mul_of_nonneg_left (outer_sum_lower hs) hx
    have hrem := mul_nonneg (show 0≤Y-X by rw [abs_of_nonneg hx] at hY; linarith) hs.1
    nlinarith
  · exact MixedQuarter.outer_axial_lower hs (le_of_not_ge hx) hy

theorem outer_cost_reduction (r : Row) {a b A B φ : ℝ} (hs : OuterState a b) :
    outerCoreCost (primaryRow r) a b A B φ≤outerCoreCost r a b A B φ := by
  by_cases hr : sourcePositive r=false
  · rw [primaryRow_self r hr]
  have hsigma : sourcePositive r=true := by cases h : sourcePositive r <;> simp_all
  let X := ocP r-ocP (primaryRow r)
  let Y := ocQ r+ocQ (primaryRow r)
  have hXY : |X|≤Y := by
    fin_cases r <;> norm_num [sourcePositive] at hsigma <;>
      norm_num [X,Y,primaryRow,ocP,ocQ]
  have hsource := outer_increasing_label_lower hs hXY
  have hzero : 0<ocC r-ocC (primaryRow r)+X*outerAxial := by
    have ha := ShortOuterZero.fine_axial_bounds
    fin_cases r <;> norm_num [sourcePositive] at hsigma <;>
      norm_num [X,primaryRow,ocC,ocP] <;> linarith [ha.1,ha.2]
  have htarget : ocG (primaryRow r)=ocG r := by
    fin_cases r <;> norm_num [primaryRow,ocG]
  have hsign : sourceSign (primaryRow r)= -1 := by
    simp [sourceSign,WordProblems.sign,(primaryRow_signs r).1]
  have hself : sourceSign r=1 := by simp [sourceSign,WordProblems.sign,hsigma]
  dsimp [outerCoreCost]
  rw [hsign,hself,htarget,show targetSign (primaryRow r)=targetSign r by
    simp [targetSign,(primaryRow_signs r).2]]
  dsimp [X,Y] at hsource hzero
  linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter
end
end
end
