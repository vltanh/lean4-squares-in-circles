module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowNegativeComparison
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowABSlope
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CutData
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Polynomial
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Positive.TDLowTransfer

/-!
# Eight squares: the two exact affected negative curves in the secant coordinate

The larger-secant branch is
affine minus the original rotated norm. The other branch retains its
square root and cosine quotient, including both exact derivatives.
-/

section
/-!
## The affected-pair norm in secant coordinates

Its x derivative is a
normalized coordinate; its z derivative has the factor r+x cos z-sin z.
This gives the exact monotonicity used when z is moved to s in the
positive-surplus argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedNorm
open Candidate Secondary PositiveAngularEnvelope SecantBaseline

def norm (r z x : ℝ) : ℝ := Real.sqrt ((x+r*Real.cos z)^2+(1-r*Real.sin z)^2)
def first (r z x : ℝ) : ℝ := (x+r*Real.cos z)/norm r z x
def second (r z x : ℝ) : ℝ := (1-r*Real.sin z)^2/(norm r z x)^3
def zFirst (r z x : ℝ) : ℝ := -r*(x*Real.sin z+Real.cos z)/norm r z x
def firstZ (r z x : ℝ) : ℝ :=
  r*(1-r*Real.sin z)*(r+x*Real.cos z-Real.sin z)/(norm r z x)^3

theorem norm_sq (r z x : ℝ) :
    (norm r z x)^2=(x+r*Real.cos z)^2+(1-r*Real.sin z)^2 :=
  Real.sq_sqrt (by positivity)

theorem norm_sq_expanded (r z x : ℝ) :
    (norm r z x)^2=1+x^2+r^2+2*r*(x*Real.cos z-Real.sin z) := by
  rw [norm_sq]
  linear_combination r^2*(Real.sin_sq_add_cos_sq z)

theorem second_coordinate_pos {r z : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hz : z∈Icc 0 frameCap) :
    0<1-r*Real.sin z := by
  have ht := transport_trig hz
  have hmul := mul_le_mul hr.2 ht.2.2.2.1.le ht.2.2.1 (by norm_num : (0:ℝ)≤71/50)
  linarith

theorem norm_pos {r z x : ℝ} (hv : 0<1-r*Real.sin z) : 0<norm r z x := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (x+r*Real.cos z)]

theorem norm_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (norm r z) (first r z x) x := by
  have hn := norm_pos (x:=x) hv
  have hr : (x+r*Real.cos z)^2+(1-r*Real.sin z)^2≠0 := by
    nlinarith [norm_sq r z x]
  have hh := ((((hasDerivAt_id x).add_const (r*Real.cos z)).pow 2).add_const
    ((1-r*Real.sin z)^2)).sqrt hr
  convert hh using 1
  · rfl
  · dsimp [first,norm]
    ring

theorem first_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (first r z) (second r z x) x := by
  have hn := norm_pos (x:=x) hv
  have hh := ((hasDerivAt_id x).add_const (r*Real.cos z)).div
    (norm_hasDerivAt hv) hn.ne'
  convert hh using 1
  · rfl
  · dsimp [first,second]
    field_simp [hn.ne']
    nlinarith only [norm_sq r z x]

theorem normZ_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (fun z => norm r z x) (zFirst r z x) z := by
  have hn := norm_pos (x:=x) hv
  have hr : (x+r*Real.cos z)^2+(1-r*Real.sin z)^2≠0 := by
    nlinarith [norm_sq r z x]
  have hu := ((Real.hasDerivAt_cos z).const_mul r).const_add x
  have hv' := ((Real.hasDerivAt_sin z).const_mul r).const_sub 1
  have hh := ((hu.pow 2).add (hv'.pow 2)).sqrt hr
  convert hh using 1
  · rfl
  · dsimp [zFirst,norm]
    ring

theorem firstZ_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (fun z => first r z x) (firstZ r z x) z := by
  have hn := norm_pos (x:=x) hv
  have hh := (((Real.hasDerivAt_cos z).const_mul r).const_add x).div
    (normZ_hasDerivAt hv) hn.ne'
  have he : -r*Real.sin z*(norm r z x)^2+
      r*(x+r*Real.cos z)*(x*Real.sin z+Real.cos z)=
      r*(1-r*Real.sin z)*(r+x*Real.cos z-Real.sin z) := by
    rw [norm_sq]
    linear_combination r^2*(1-r*Real.sin z)*(Real.sin_sq_add_cos_sq z)
  convert hh using 1
  · rfl
  · dsimp [firstZ,first,zFirst]
    field_simp [hn.ne']
    nlinarith only [he]

theorem first_le_one {r z x : ℝ} (hv : 0<1-r*Real.sin z) : first r z x≤1 := by
  have hn := norm_pos (x:=x) hv
  unfold first
  apply (div_le_one hn).2
  nlinarith [norm_sq r z x,sq_nonneg (1-r*Real.sin z)]

theorem tan_identity {s : ℝ} (hc : 0<Real.cos s) :
    Real.tan s*Real.cos s-Real.sin s=0 ∧
    1+Real.tan s^2=(1/Real.cos s)^2 := by
  constructor
  · rw [Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring
  · rw [Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    nlinarith only [Real.sin_sq_add_cos_sq s]

theorem first_z_monotone {r s : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hs : s∈Icc 0 frameCap) :
    MonotoneOn (fun z => first r z (Real.tan s)) (Icc 0 s) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hdomain (z : ℝ) (hz : z∈Icc 0 s) : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans hs.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun z hz => (firstZ_hasDerivAt (x:=Real.tan s)
      (second_coordinate_pos hr (hdomain z hz))).continuousAt.continuousWithinAt)
    (fun z hz => firstZ_hasDerivAt (x:=Real.tan s)
      (second_coordinate_pos hr (hdomain z (Ioo_subset_Icc_self hz))))
  intro z hz
  have hz' := Ioo_subset_Icc_self hz
  have hdiff : s-z∈Icc 0 frameCap :=
    ⟨by linarith [hz'.2],by linarith [hs.2,hz'.1]⟩
  have hsin := (transport_trig hdiff).2.2.1
  have he : Real.tan s*Real.cos z-Real.sin z=Real.sin (s-z)/Real.cos s := by
    rw [Real.tan_eq_sin_div_cos,Real.sin_sub]
    field_simp [hc.ne']
  have hbr : 0≤r+Real.tan s*Real.cos z-Real.sin z := by
    have hn := div_nonneg hsin hc.le
    rw [←he] at hn
    linarith [hr.1]
  unfold firstZ
  exact div_nonneg
    (mul_nonneg (mul_nonneg hr.1 (second_coordinate_pos hr (hdomain z hz')).le) hbr)
    (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem norm_at_equal {r s : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hs : s∈Icc 0 frameCap) :
    norm r s (Real.tan s)=denominator r s/Real.cos s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hn := norm_pos (x:=Real.tan s) (second_coordinate_pos hr hs)
  have hsupp := SecantNormCurvature.norm_pos (a:=r) hc
  have he := norm_sq_expanded r s (Real.tan s)
  rw [(tan_identity hc).1,mul_zero,add_zero] at he
  have he' : (norm r s (Real.tan s))^2=(SecantNormCurvature.supportNorm r s)^2 := by
    rw [SecantNormCurvature.norm_sq]
    dsimp [SecantNormCurvature.secant]
    nlinarith only [he,(tan_identity hc).2]
  have hnorm : norm r s (Real.tan s)=SecantNormCurvature.supportNorm r s := by
    nlinarith
  rw [hnorm,support_norm_identity hc]

theorem first_at_equal {r s : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hs : s∈Icc 0 frameCap) :
    first r s (Real.tan s)=
      (Real.sin s+r*Real.cos s^2)/denominator r s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  unfold first
  rw [norm_at_equal hr hs,Real.tan_eq_sin_div_cos]
  field_simp [hc.ne',(denominator_pos r s).ne']

theorem first_le_equal {r s z : ℝ}
    (hr : r∈Icc (0:ℝ) (71/50:ℝ)) (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 s) :
    first r z (Real.tan s)≤(Real.sin s+r*Real.cos s^2)/denominator r s := by
  have hh := first_z_monotone hr hs hz (show s∈Icc 0 s from ⟨hs.1,le_rfl⟩) hz.2
  simpa only [first_at_equal hr hs] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedNorm
end
end
end

section
/-!
## The secant coordinate of the negative-A angle

The coordinate is `x = tan s`, and its inverse stays in every negative-angle charge
(`charge_arctan`). The derivatives of `base` and of `pure` are computed before any numerical
bound or endpoint reduction is applied.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.SecantCoordinate
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope PairNormCalculus OrdinaryCurvatureBounds

def radical (A x : ℝ) : ℝ := Real.sqrt (A+x^2)
def base (r x : ℝ) : ℝ := radical 1 x+(13/12)*x-R*radical (1+r^2) x
def baseFirst (r x : ℝ) : ℝ :=
  x/radical 1 x+13/12-R*x/radical (1+r^2) x
def baseSecond (r x : ℝ) : ℝ :=
  1/(radical 1 x)^3-R*(1+r^2)/(radical (1+r^2) x)^3
def baseThird (r x : ℝ) : ℝ :=
  3*x*(R*(1+r^2)/(radical (1+r^2) x)^5-1/(radical 1 x)^5)
def ratioDerivative (r x : ℝ) : ℝ :=
  R*r*(1+r^2-2*x^2)/(radical (1+r^2) x)^5

theorem radical_positive {A x : ℝ} (hA : 0<A) : 0<radical A x :=
  Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x])
theorem radical_square {A x : ℝ} (hA : 0<A) : (radical A x)^2=A+x^2 :=
  Real.sq_sqrt (by nlinarith [sq_nonneg x])

theorem radical_hasDerivAt {A x : ℝ} (hA : 0<A) :
    HasDerivAt (radical A) (x/radical A x) x := by
  convert (((hasDerivAt_id x).pow 2).const_add A).sqrt
    (by nlinarith [sq_nonneg x] : A+x^2≠0) using 1
  · rfl
  · dsimp [radical]
    ring

theorem radicalFirst_hasDerivAt {A x : ℝ} (hA : 0<A) :
    HasDerivAt (fun x => x/radical A x) (A/(radical A x)^3) x := by
  have hp := radical_positive (x:=x) hA
  have hs := radical_square (x:=x) hA
  refine ((hasDerivAt_id x).fun_div (radical_hasDerivAt hA) hp.ne').congr_deriv ?_
  simp only [id,one_mul]
  field_simp
  linear_combination hs

theorem base_hasDerivAt (r x : ℝ) : HasDerivAt (base r) (baseFirst r x) x := by
  have hA : 0<1+r^2 := by positivity
  convert ((radical_hasDerivAt (A:=1) (by norm_num)).add
    ((hasDerivAt_id x).const_mul (13/12:ℝ))).sub
    ((radical_hasDerivAt hA).const_mul R) using 1
  · rfl
  · dsimp [baseFirst]
    ring

theorem baseFirst_hasDerivAt (r x : ℝ) :
    HasDerivAt (baseFirst r) (baseSecond r x) x := by
  have hA : 0<1+r^2 := by positivity
  convert ((radicalFirst_hasDerivAt (A:=1) (x:=x) (by norm_num)).add_const
    (13/12:ℝ)).sub ((radicalFirst_hasDerivAt (x:=x) hA).const_mul R) using 1
  · funext y
    dsimp [baseFirst]
    ring
  · dsimp [baseSecond]
    ring

theorem baseSecond_hasDerivAt (r x : ℝ) :
    HasDerivAt (baseSecond r) (baseThird r x) x := by
  have hA : 0<1+r^2 := by positivity
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hN := radical_positive (x:=x) hA
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hN2 := radical_square (x:=x) hA
  have hd := ((hasDerivAt_const x (1:ℝ)).div
    ((radical_hasDerivAt (A:=1) (by norm_num)).pow 3) (pow_ne_zero 3 hW.ne')).sub
    ((hasDerivAt_const x (R*(1+r^2))).div
      ((radical_hasDerivAt hA).pow 3) (pow_ne_zero 3 hN.ne'))
  convert hd using 1
  · rfl
  · dsimp [baseThird]
    field_simp [hW.ne',hN.ne']
    ring

theorem baseSecond_ratio_hasDerivAt (r x : ℝ) :
    HasDerivAt (fun r => baseSecond r x) (ratioDerivative r x) r := by
  have hA : 0<1+r^2 := by positivity
  have hN := radical_positive (x:=x) hA
  have hN2 := radical_square (x:=x) hA
  have hroot : HasDerivAt (fun r => radical (1+r^2) x) (r/radical (1+r^2) x) r := by
    have h0 : HasDerivAt (fun r:ℝ => 1+r^2+x^2) (2*r) r := by
      simpa using (((hasDerivAt_id r).fun_pow 2).const_add (1:ℝ)).add_const (x^2)
    refine (h0.sqrt (by positivity)).congr_deriv ?_
    rw [show Real.sqrt (1+r^2+x^2)=radical (1+r^2) x from rfl]
    field_simp
  have h1 : HasDerivAt (fun r:ℝ => R*(1+r^2)) (R*(2*r)) r := by
    simpa using (((hasDerivAt_id r).fun_pow 2).const_add (1:ℝ)).const_mul R
  have h3 : HasDerivAt (fun r => (radical (1+r^2) x)^3)
      (3*(radical (1+r^2) x)^2*(r/radical (1+r^2) x)) r :=
    (hroot.fun_pow 3).congr_deriv (by norm_num)
  have hd := (h1.fun_div h3 (pow_ne_zero 3 hN.ne')).const_sub (1/(radical 1 x)^3)
  refine hd.congr_deriv ?_
  simp only [ratioDerivative]
  field_simp
  linear_combination (-2*r)*hN2

/-- Enlarging the basic ratio increases `baseSecond r x` when `2 x^2 ≤ 1`. -/
theorem baseSecond_ratio_mono {r r' x : ℝ}
    (hr : 0≤r) (hrr' : r≤r') (hx : 2*x^2≤1) :
    baseSecond r x≤baseSecond r' x := by
  have hm : MonotoneOn (fun r => baseSecond r x) (Icc r r') := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (baseSecond_ratio_hasDerivAt a x).continuousAt.continuousWithinAt)
      (fun a _ => baseSecond_ratio_hasDerivAt a x)
    intro a ha
    have ha0 : 0≤a := hr.trans ha.1.le
    have hfactor : 0≤1+a^2-2*x^2 := by nlinarith [sq_nonneg a]
    exact div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) ha0) hfactor)
      (pow_nonneg (Real.sqrt_nonneg _) 5)
  exact hm ⟨le_rfl,hrr'⟩ ⟨hrr',le_rfl⟩ hrr'

theorem normalized_arctan (r x : ℝ) :
    SecantNormCurvature.normalized R r (Real.arctan x)=base r x-base r 0 := by
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hcos : 1/Real.cos (Real.arctan x)=radical 1 x := by
    rw [Real.cos_arctan]
    simp [radical]
  have hnorm : SecantNormCurvature.supportNorm r (Real.arctan x)=radical (1+r^2) x := by
    dsimp [SecantNormCurvature.supportNorm,SecantNormCurvature.secant]
    rw [hcos,hW2]
    congr 1
    ring
  simp only [SecantNormCurvature.normalized,SecantNormCurvature.secant,
    hcos,hnorm,Real.tan_arctan,base,radical,add_zero,
    mul_zero]
  rw [show r^2+1=1+r^2 by ring]
  ring

theorem charge_arctan {l : ℝ} (hl : 0<l) (a x : ℝ) :
    FlatTStress.secantCharge R l a (Real.arctan x)=
      l*(base (a/l) x-base (a/l) 0) := by
  rw [SecantNormCurvature.charge_scale hl,normalized_arctan]

theorem arctan_tan {s : ℝ} (hs : s∈Icc 0 frameCap) :
    Real.arctan (Real.tan s)=s :=
  Real.arctan_tan (by linarith [hs.1,Real.pi_gt_three])
    (by dsimp [frameCap] at hs; linarith [hs.2,Real.pi_gt_three])

theorem tan_monotone : MonotoneOn Real.tan (Icc (0:ℝ) frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (Real.hasDerivAt_tan
      (show Real.cos s≠0 by linarith [(transport_trig hs).1])).continuousAt.continuousWithinAt)
    (fun s hs => Real.hasDerivAt_tan
      (show Real.cos s≠0 by linarith [(transport_trig (Ioo_subset_Icc_self hs)).1]))
  intro s hs
  positivity

theorem tan_nonnegative {s : ℝ} (hs : s∈Icc 0 frameCap) : 0≤Real.tan s := by
  simpa only [Real.tan_zero] using tan_monotone
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hs hs.1

theorem arctan_interval {a x : ℝ} (ha : a∈Icc 0 frameCap)
    (hx : x∈Icc 0 (Real.tan a)) : Real.arctan x∈Icc 0 a := by
  constructor
  · simpa only [Real.arctan_zero] using Real.arctan_strictMono.monotone hx.1
  · simpa only [arctan_tan ha] using Real.arctan_strictMono.monotone hx.2

def pure (B l r p q z x : ℝ) : ℝ :=
  B+l*(base r x-base r 0)+V R p q (z-Real.arctan x)
def pureFirst (l r p q z x : ℝ) : ℝ :=
  l*baseFirst r x-Vd R p q (z-Real.arctan x)/(1+x^2)
def negativeSecond (p q z x : ℝ) : ℝ :=
  (curvature R p q (-(z-Real.arctan x))-q*Real.cos (z-Real.arctan x)+
    2*x*Vd R p q (z-Real.arctan x))/(1+x^2)^2
def pureSecond (l r p q z x : ℝ) : ℝ := l*baseSecond r x+negativeSecond p q z x

theorem pure_hasDerivAt {B l r p q z x : ℝ}
    (hp : 0<p) (hq : 0<q) (hθ : z-Real.arctan x∈Icc 0 frameCap) :
    HasDerivAt (pure B l r p q z) (pureFirst l r p q z x) x := by
  have hv := (V_hasDerivAt (R:=R) hp hq hθ).comp x ((Real.hasDerivAt_arctan x).const_sub z)
  have hb := (((base_hasDerivAt r x).sub_const (base r 0)).const_mul l).const_add B
  refine (hb.fun_add hv).congr_deriv ?_
  simp only [pureFirst]
  ring

theorem pureFirst_hasDerivAt {l r p q z x : ℝ}
    (hp : 0<p) (hq : 0<q) (hθ : z-Real.arctan x∈Icc 0 frameCap) :
    HasDerivAt (pureFirst l r p q z) (pureSecond l r p q z x) x := by
  have hv := (Vd_hasDerivAt (R:=R) hp hq hθ).comp x ((Real.hasDerivAt_arctan x).const_sub z)
  have hden : 1+x^2≠0 := by positivity
  have h2 : HasDerivAt (fun x:ℝ => 1+x^2) (2*x) x := by
    simpa using ((hasDerivAt_id x).fun_pow 2).const_add (1:ℝ)
  have hd := ((baseFirst_hasDerivAt r x).const_mul l).fun_sub (hv.fun_div h2 hden)
  refine hd.congr_deriv ?_
  simp only [pureSecond,negativeSecond,Function.comp_apply]
  field_simp
  ring

theorem pure_at_original (atG : Bool) {k l c s z p q : ℝ}
    (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    pure (baseline atG k l c 0 z) l (SecantBaseline.basicRatio atG k l c z)
      p q z (Real.tan s)=baseline atG k l c s z+V R p q (z-s) := by
  rw [SecantBaseline.baseline_eq_extension atG k l c z hs]
  have hc := charge_arctan hl (SecantBaseline.affected atG k c z) (Real.tan s)
  rw [arctan_tan hs] at hc
  dsimp [pure,SecantBaseline.angularBaseline,SecantBaseline.basicRatio]
  rw [hc,arctan_tan hs]

theorem pure_concave {B l r p q z a : ℝ}
    (hp : 0<p) (hq : 0<q) (ha : a∈Icc 0 frameCap)
    (haz : a≤z) (hz : z≤frameCap)
    (hcurv : ∀x∈Icc 0 (Real.tan a),pureSecond l r p q z x≤0) :
    ConcaveOn ℝ (Icc 0 (Real.tan a)) (pure B l r p q z) := by
  have hθ (x : ℝ) (hx : x∈Icc 0 (Real.tan a)) :
      z-Real.arctan x∈Icc 0 frameCap := by
    have hs := arctan_interval ha hx
    exact ⟨by linarith [hs.2],by linarith [hs.1]⟩
  exact concave_of_deriv2 (fun x hx => pure_hasDerivAt hp hq (hθ x hx))
    (fun x hx => pureFirst_hasDerivAt hp hq (hθ x hx)) hcurv

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.SecantCoordinate
end
end
end

section
/-!
## Positive tangent denominators for the negative-A scalar endpoints

Each bound holds on the whole coefficient interval. It applies the centered monomial coefficient
norm to the auxiliary polynomial itself (`mass_reserve`, `cut_mass_reserve`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
open Polynomial PowerTailBounds
open PositiveTD.Certificate (C4 h)
open WholeIntervalPolynomial.Certificate (Scaled)
open PositiveTD.Certificate (S5 etaQ)

def mass (f : Family) : Fin 15→ℚ[X] :=
  ![RH f,RG f,RB f,RD f,RHminus f,RGminus f,RBminus f,
    C4*RH f,equalGAR f 1,C4*RB f,C4*RD f,C4*RG f,
    C (4/5)*l f+C (3/5)*mu f*C4,C (77/100),C (77/100)*l f]
def midpoint (f : Family) : ℚ := (left f+right f)/2
def radius (f : Family) : ℚ := (right f-left f)/2
def massCentered (f : Family) (i : Fin 15) : ℚ[X] :=
  DirectedPowerBounds.shift (midpoint f) (mass f i)

/-! ### The auxiliary masses as scaled integer coefficient lists -/

private def r42S5 : Scaled :=
  (Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))
private theorem r42S5_rep : r42S5.Rep S5 :=
  (Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))
private def r42C4 : Scaled :=
  ((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))
private theorem r42C4_rep : r42C4.Rep C4 :=
  (Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))
private def r42t : Family → Scaled
  | .low => (Scaled.const split).sub Scaled.var
  | .high => Scaled.var.sub (Scaled.const split)
private theorem r42t_rep : ∀ f, (r42t f).Rep (t f)
  | .low => (Scaled.rep_const _).sub Scaled.rep_var
  | .high => Scaled.rep_var.sub (Scaled.rep_const _)
private def r42k : Family → Scaled
  | .low => (((Scaled.const (169/250)).sub ((Scaled.const (1/5)).mul (r42t .low))).add
      ((Scaled.const (19/5)).mul ((r42t .low).pow 2))).sub
      ((Scaled.const 5).mul ((r42t .low).pow 3))
  | .high => (((Scaled.const (169/250)).add ((Scaled.const (1/5)).mul (r42t .high))).add
      ((Scaled.const (9/10)).mul ((r42t .high).pow 2))).sub
      ((Scaled.const (13/10)).mul ((r42t .high).pow 3))
private theorem r42k_rep : ∀ f, (r42k f).Rep (k f)
  | .low => (((Scaled.rep_const _).sub ((Scaled.rep_const _).mul (r42t_rep .low))).add
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))).sub
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 3))
  | .high => (((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r42t_rep .high))).add
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))).sub
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 3))
private def r42l : Family → Scaled
  | .low => ((((Scaled.const (41/40)).sub ((Scaled.const (1/4)).mul (r42t .low))).add
      ((Scaled.const (29/2)).mul ((r42t .low).pow 2))).add
      ((Scaled.const (55/4)).mul ((r42t .low).pow 3))).sub
      ((Scaled.const 200).mul ((r42t .low).pow 4))
  | .high => ((Scaled.const (41/40)).add ((Scaled.const (11/50)).mul (r42t .high))).sub
      ((Scaled.const (3/10)).mul ((r42t .high).pow 2))
private theorem r42l_rep : ∀ f, (r42l f).Rep (l f)
  | .low => ((((Scaled.rep_const _).sub ((Scaled.rep_const _).mul (r42t_rep .low))).add
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))).add
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 3))).sub
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 4))
  | .high => ((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r42t_rep .high))).sub
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))
private def r42c : Family → Scaled
  | .low => ((Scaled.ofNat 1).add ((Scaled.const (11/10)).mul (r42t .low))).add
      ((Scaled.const 17).mul ((r42t .low).pow 2))
  | .high => ((Scaled.ofNat 1).sub ((Scaled.const (7/10)).mul (r42t .high))).add
      ((Scaled.const (22/25)).mul ((r42t .high).pow 2))
private theorem r42c_rep : ∀ f, (r42c f).Rep (c f)
  | .low => (Scaled.rep_one.add ((Scaled.rep_const _).mul (r42t_rep .low))).add
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))
  | .high => (Scaled.rep_one.sub ((Scaled.rep_const _).mul (r42t_rep .high))).add
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))
private def r42mu (f : Family) : Scaled := (r42c f).mul (r42C4.add ((Scaled.const etaQ).mul r42S5))
private theorem r42mu_rep (f : Family) : (r42mu f).Rep (mu f) :=
  (r42c_rep f).mul (r42C4_rep.add ((Scaled.rep_const _).mul r42S5_rep))
private def r42RH (f : Family) : Scaled := (Scaled.const (83/100)).add ((Scaled.const (279/500)).mul (r42k f))
private theorem r42RH_rep (f : Family) : (r42RH f).Rep (RH f) :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul (r42k_rep f))
private def r42RG (f : Family) : Scaled :=
  ((Scaled.const (11/20)).mul (r42k f)).add ((Scaled.const (167/200)).mul (r42l f))
private theorem r42RG_rep (f : Family) : (r42RG f).Rep (RG f) :=
  ((Scaled.rep_const _).mul (r42k_rep f)).add ((Scaled.rep_const _).mul (r42l_rep f))
private def r42RB (f : Family) : Scaled :=
  ((Scaled.const (29/40)).mul (r42mu f)).add ((Scaled.const (689/1000)).mul (r42l f))
private theorem r42RB_rep (f : Family) : (r42RB f).Rep (RB f) :=
  ((Scaled.rep_const _).mul (r42mu_rep f)).add ((Scaled.rep_const _).mul (r42l_rep f))
private def r42RD (f : Family) : Scaled := (Scaled.const (7071/10000)).mul ((Scaled.ofNat 1).add (r42c f))
private theorem r42RD_rep (f : Family) : (r42RD f).Rep (RD f) :=
  (Scaled.rep_const _).mul (Scaled.rep_one.add (r42c_rep f))
private def r42RHminus (f : Family) : Scaled :=
  ((Scaled.const (179/200)).mul r42C4).add ((Scaled.const (223/500)).mul ((r42k f).sub r42S5))
private theorem r42RHminus_rep (f : Family) : (r42RHminus f).Rep (RHminus f) :=
  ((Scaled.rep_const _).mul r42C4_rep).add ((Scaled.rep_const _).mul ((r42k_rep f).sub r42S5_rep))
private def r42RGminus (f : Family) : Scaled :=
  (((Scaled.const (9/10)).mul (r42l f)).mul r42C4).add
    ((Scaled.const (109/250)).mul ((r42k f).sub ((r42l f).mul r42S5)))
private theorem r42RGminus_rep (f : Family) : (r42RGminus f).Rep (RGminus f) :=
  (((Scaled.rep_const _).mul (r42l_rep f)).mul r42C4_rep).add
    ((Scaled.rep_const _).mul ((r42k_rep f).sub ((r42l_rep f).mul r42S5_rep)))
private def r42RBminus (f : Family) : Scaled :=
  (((Scaled.const (94/125)).mul (r42l f)).mul r42C4).add
    ((Scaled.const (33/50)).mul ((r42mu f).sub ((r42l f).mul r42S5)))
private theorem r42RBminus_rep (f : Family) : (r42RBminus f).Rep (RBminus f) :=
  (((Scaled.rep_const _).mul (r42l_rep f)).mul r42C4_rep).add
    ((Scaled.rep_const _).mul ((r42mu_rep f).sub ((r42l_rep f).mul r42S5_rep)))
private theorem r42_rep_eval {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) : (S.center num den s 0).Rep (C (p.eval a)) := by
  have hc := hp.centered num den s 0 (a:=a) (b:=a) hden (by rw [← ha]; ring) (by simp)
  have he : WholeIntervalPolynomial.centered a a p=C (p.eval a) := by
    rw [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,sub_self,zero_div,
      map_zero,zero_mul,add_zero,add_self_div_two,comp_C]
  rwa [he] at hc
private theorem r42_rep_Cmul {S T : Scaled} {a b : ℚ} (hS : S.Rep (C a)) (hT : T.Rep (C b)) :
    (S.mul T).Rep (C (a*b)) := by rw [map_mul]; exact hS.mul hT
private def r42head (S : Scaled) : Scaled := ⟨[S.l.getD 0 0],S.s⟩
private theorem r42head_rep {S : Scaled} {c : ℚ} (hS : S.Rep (C c)) : (r42head S).Rep (C c) := by
  unfold Scaled.Rep at *
  have h0 := congrArg (fun q => q.coeff 0) hS
  simp only [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul,coeff_C_zero] at h0
  simp only [r42head,WholeIntervalPolynomial.Certificate.toPoly,mul_zero,add_zero,h0,map_mul]
private def r42ang (e : Cut) (S : Scaled) : Scaled :=
  r42head (if cutAtG e then S.center 1 4 1 0 else S.center 19 50 1 0)
private theorem r42ang_rep (e : Cut) {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r42ang e S).Rep (C (p.eval (cutAngle e))) := by
  apply r42head_rep
  rcases hb : cutAtG e with _|_ <;> simp only [cutAngle,hb,Bool.false_eq_true,↓reduceIte]
  · exact r42_rep_eval hp 19 50 1 (by norm_num) (by norm_num)
  · exact r42_rep_eval hp 1 4 1 (by norm_num) (by norm_num)
private def r42ga (e : Cut) : Scaled := r42ang e r42C4
private def r42ta (e : Cut) : Scaled := r42ang e r42S5
private theorem r42ga_rep (e : Cut) : (r42ga e).Rep (C (gammaApprox e)) := r42ang_rep e r42C4_rep
private theorem r42ta_rep (e : Cut) : (r42ta e).Rep (C (tauApprox e)) := r42ang_rep e r42S5_rep
private def r42cosAp (e : Cut) : Scaled := ((r42ga e).mul r42C4).add ((r42ta e).mul r42S5)
private theorem r42cosAp_rep (e : Cut) : (r42cosAp e).Rep (thetaCosApprox e) :=
  ((r42ga_rep e).mul r42C4_rep).add ((r42ta_rep e).mul r42S5_rep)
private def r42sinAp (e : Cut) : Scaled := ((r42ga e).mul r42S5).sub ((r42ta e).mul r42C4)
private theorem r42sinAp_rep (e : Cut) : (r42sinAp e).Rep (thetaSinApprox e) :=
  ((r42ga_rep e).mul r42S5_rep).sub ((r42ta_rep e).mul r42C4_rep)
private def r42theta (e : Cut) : Scaled := Scaled.var.sub (Scaled.const (cutAngle e))
private theorem r42theta_rep (e : Cut) : (r42theta e).Rep (theta e) :=
  Scaled.rep_var.sub (Scaled.rep_const _)
private def r42cR0 (e : Cut) : Scaled := (r42ga e).mul (r42RH .high)
private theorem r42cR0_rep (e : Cut) : (r42cR0 e).Rep (C (gammaApprox e)*RH .high) :=
  (r42ga_rep e).mul (r42RH_rep .high)
private def r42cR0u (e : Cut) : Scaled :=
  (r42ga e).mul (((Scaled.const (87/100)).mul (r42cosAp e)).add
    ((Scaled.const (493/1000)).mul ((r42k .high).sub (r42sinAp e))))
private theorem r42cR0u_rep (e : Cut) : (r42cR0u e).Rep (C (gammaApprox e)*
    (C (87/100)*thetaCosApprox e+C (493/1000)*(k .high-thetaSinApprox e))) :=
  (r42ga_rep e).mul (((Scaled.rep_const _).mul (r42cosAp_rep e)).add
    ((Scaled.rep_const _).mul ((r42k_rep .high).sub (r42sinAp_rep e))))
private def r42cR1g (e : Cut) : Scaled :=
  ((Scaled.const (21/25)).mul (r42l .high)).add
    (((Scaled.const (543/1000)).mul (r42ga e)).mul (r42k .high))
private theorem r42cR1g_rep (e : Cut) : (r42cR1g e).Rep
    (C (21/25)*l .high+C (543/1000*gammaApprox e)*k .high) :=
  ((Scaled.rep_const _).mul (r42l_rep .high)).add
    ((r42_rep_Cmul (Scaled.rep_const _) (r42ga_rep e)).mul (r42k_rep .high))
private def r42cR1a (e : Cut) : Scaled := (r42ga e).mul (r42RG .high)
private theorem r42cR1a_rep (e : Cut) : (r42cR1a e).Rep (C (gammaApprox e)*RG .high) :=
  (r42ga_rep e).mul (r42RG_rep .high)
private def r42cR1u (e : Cut) : Scaled :=
  (r42ga e).mul ((((Scaled.const (9/10)).mul (r42l .high)).mul (r42cosAp e)).add
    ((Scaled.const (109/250)).mul ((r42k .high).sub ((r42l .high).mul (r42sinAp e)))))
private theorem r42cR1u_rep (e : Cut) : (r42cR1u e).Rep (C (gammaApprox e)*
    (C (9/10)*l .high*thetaCosApprox e+C (109/250)*(k .high-l .high*thetaSinApprox e))) :=
  (r42ga_rep e).mul ((((Scaled.rep_const _).mul (r42l_rep .high)).mul (r42cosAp_rep e)).add
    ((Scaled.rep_const _).mul ((r42k_rep .high).sub ((r42l_rep .high).mul (r42sinAp_rep e)))))
private def r42cR2g (e : Cut) : Scaled := (r42ga e).mul (r42RB .high)
private theorem r42cR2g_rep (e : Cut) : (r42cR2g e).Rep (C (gammaApprox e)*RB .high) :=
  (r42ga_rep e).mul (r42RB_rep .high)
private def r42cR2a (e : Cut) : Scaled :=
  ((Scaled.const (4/5)).mul (r42l .high)).add (((Scaled.const (3/5)).mul (r42ga e)).mul (r42mu .high))
private theorem r42cR2a_rep (e : Cut) : (r42cR2a e).Rep
    (C (4/5)*l .high+C (3/5*gammaApprox e)*mu .high) :=
  ((Scaled.rep_const _).mul (r42l_rep .high)).add
    ((r42_rep_Cmul (Scaled.rep_const _) (r42ga_rep e)).mul (r42mu_rep .high))
private def r42cR2u (e : Cut) : Scaled :=
  (r42ga e).mul (((((Scaled.const (357/500)).add ((Scaled.const (11/20)).mul (r42theta e))).mul
      (r42l .high)).mul (r42cosAp e)).add
    (((Scaled.const (7/10)).sub ((Scaled.const (41/50)).mul (r42theta e))).mul
      ((r42mu .high).sub ((r42l .high).mul (r42sinAp e)))))
private theorem r42cR2u_rep (e : Cut) : (r42cR2u e).Rep (C (gammaApprox e)*
    ((C (357/500)+C (11/20)*theta e)*l .high*thetaCosApprox e+
      (C (7/10)-C (41/50)*theta e)*(mu .high-l .high*thetaSinApprox e))) :=
  (r42ga_rep e).mul (((((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r42theta_rep e))).mul
      (r42l_rep .high)).mul (r42cosAp_rep e)).add
    (((Scaled.rep_const _).sub ((Scaled.rep_const _).mul (r42theta_rep e))).mul
      ((r42mu_rep .high).sub ((r42l_rep .high).mul (r42sinAp_rep e)))))
private def r42cR3 (e : Cut) : Scaled := (r42ga e).mul (r42RD .high)
private theorem r42cR3_rep (e : Cut) : (r42cR3 e).Rep (C (gammaApprox e)*RD .high) :=
  (r42ga_rep e).mul (r42RD_rep .high)

private def r42mass (f : Family) : Fin 15→Scaled :=
  ![r42RH f,r42RG f,r42RB f,r42RD f,r42RHminus f,r42RGminus f,r42RBminus f,
    r42C4.mul (r42RH f),
    ((Scaled.const (21/25)).mul (r42l f)).add (((Scaled.const (543/1000)).mul (r42k f)).mul r42C4),
    r42C4.mul (r42RB f),r42C4.mul (r42RD f),r42C4.mul (r42RG f),
    ((Scaled.const (4/5)).mul (r42l f)).add (((Scaled.const (3/5)).mul (r42mu f)).mul r42C4),
    Scaled.const (77/100),(Scaled.const (77/100)).mul (r42l f)]
private theorem r42mass_rep (f : Family) (i : Fin 15) : (r42mass f i).Rep (mass f i) := by
  fin_cases i
  exacts [r42RH_rep f,r42RG_rep f,r42RB_rep f,r42RD_rep f,r42RHminus_rep f,r42RGminus_rep f,
    r42RBminus_rep f,r42C4_rep.mul (r42RH_rep f),
    ((Scaled.rep_const _).mul (r42l_rep f)).add (((Scaled.rep_const _).mul (r42k_rep f)).mul r42C4_rep),
    r42C4_rep.mul (r42RB_rep f),r42C4_rep.mul (r42RD_rep f),r42C4_rep.mul (r42RG_rep f),
    ((Scaled.rep_const _).mul (r42l_rep f)).add (((Scaled.rep_const _).mul (r42mu_rep f)).mul r42C4_rep),
    Scaled.rep_const _,(Scaled.rep_const _).mul (r42l_rep f)]

private theorem r42_shift_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {m : ℚ} (hden : den≠0) (hm : m=num*s/den) (h1 : (1:ℚ)=num*t/den) :
    (S.center num den s t).Rep (DirectedPowerBounds.shift m p) := by
  have hc := hp.centered num den s t (a:=m-1) (b:=m+1) hden (by rw [← hm]; ring) (by rw [← h1]; ring)
  rwa [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,show (m-1+(m+1))/2=m by ring,
    show (m+1-(m-1))/2=1 by ring,map_one,one_mul] at hc

private def r42mc : Family→Fin 15→Scaled
  | .low,i => (r42mass .low i).center 1 10 1 10
  | .high,i => (r42mass .high i).center 1 20 9 20
private theorem r42mc_rep : ∀ f i,(r42mc f i).Rep (massCentered f i)
  | .low,i => r42_shift_rep (r42mass_rep .low i) 1 10 1 10 (by norm_num)
      (by norm_num [midpoint,left,right,split]) (by norm_num)
  | .high,i => r42_shift_rep (r42mass_rep .high i) 1 20 9 20 (by norm_num)
      (by norm_num [midpoint,left,right,split,h]) (by norm_num)

/-- A polynomial of degree at most `n` is its constant term plus its power tail. -/
private theorem r42_tail_identity {p : ℚ[X]} {n : ℕ} (hp : p.natDegree≤n) :
    p=C (p.coeff 0)+tail p 1 n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n:=n+1) (Nat.lt_succ_of_le hp)]
  rw [Finset.sum_range_succ',tail,← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff (i+1))*X^(i+1)) n,
    pow_zero,mul_one,add_comm]

private theorem r42_reserve_of_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (n : ℕ) (r ρ : ℚ) (h : ρ<(S.l.getD 0 0:ℚ)/S.s-
      ∑ j : Fin n,|(S.l.getD (j.val+1) 0:ℚ)/S.s| *r^(j.val+1)) :
    ρ<p.coeff 0-PowerTailBounds.norm p 1 n r := by
  simp only [PowerTailBounds.norm,hp.coeff hs]
  exact h

theorem mass_identity (f : Family) (i : Fin 15) :
    massCentered f i=C ((massCentered f i).coeff 0)+tail (massCentered f i) 1 11 := by
  cases f <;> fin_cases i <;>
    exact r42_tail_identity (((r42mc_rep _ _).natDegree_le (by decide +kernel)).trans
      (by decide +kernel))

theorem mass_reserve (f : Family) (i : Fin 15) :
    (29/50:ℚ)<(massCentered f i).coeff 0-
      PowerTailBounds.norm (massCentered f i) 1 11 (radius f) := by
  cases f <;> fin_cases i <;>
    exact r42_reserve_of_rep (r42mc_rep _ _) (by decide +kernel) _ _ _ (by decide +kernel)

theorem mass_lower (f : Family) (i : Fin 15) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) :
    (29/50:ℝ)<aeval z (mass f i) := by
  have hx : |z-(midpoint f:ℝ)|≤(radius f:ℝ) := by
    apply abs_le.mpr
    simp only [midpoint,radius]
    push_cast
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower (mass_identity f i) hx
  have hr := (Rat.cast_lt (K:=ℝ)).mpr (mass_reserve f i)
  push_cast at hr
  have he : aeval (z-(midpoint f:ℝ)) (massCentered f i)=aeval z (mass f i) := by
    simp [massCentered]
  rw [he] at hb
  linarith

theorem mass_positive (f : Family) (i : Fin 15) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) : 0<aeval z (mass f i) := by
  have hh := mass_lower f i hz
  linarith

theorem ordinary_masses_positive (f : Family) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) :
    0<aeval z (RH f) ∧ 0<aeval z (RG f) ∧ 0<aeval z (RB f) ∧
    0<aeval z (RD f) ∧ 0<aeval z (RHminus f) ∧
    0<aeval z (RGminus f) ∧ 0<aeval z (RBminus f) := by
  exact ⟨by simpa [mass] using mass_positive f 0 hz,
    by simpa [mass] using mass_positive f 1 hz,
    by simpa [mass] using mass_positive f 2 hz,
    by simpa [mass] using mass_positive f 3 hz,
    by simpa [mass] using mass_positive f 4 hz,
    by simpa [mass] using mass_positive f 5 hz,
    by simpa [mass] using mass_positive f 6 hz⟩

theorem equal_GA_masses_positive (f : Family) {z : ℝ}
    (hz : z∈Set.Icc (left f:ℝ) (right f:ℝ)) (i : Fin 4) :
    0<aeval z (equalGAR f i) := by
  fin_cases i
  · simpa [mass,equalGAR] using mass_positive f 7 hz
  · simpa [mass] using mass_positive f 8 hz
  · simpa [mass,equalGAR] using mass_positive f 9 hz
  · simpa [mass,equalGAR] using mass_positive f 10 hz

theorem equal_AB_masses_positive {z : ℝ}
    (hz : z∈Set.Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) :
    0<aeval z (equalABR i) := by
  have hz' : z∈Set.Icc (left .high:ℝ) (right .high:ℝ) := by
    norm_num [left,right,split,h]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  fin_cases i
  · simpa [mass,equalABR] using mass_positive .high 7 hz'
  · simpa [mass,equalABR] using mass_positive .high 11 hz'
  · simpa [mass,equalABR] using mass_positive .high 12 hz'
  · simpa [mass,equalABR] using mass_positive .high 10 hz'

def cutMidpoint (e : Cut) : ℚ := (cutAngle e+h)/2
def cutRadius (e : Cut) : ℚ := (h-cutAngle e)/2
def cutMassCentered (e : Cut) (i : Fin 4) : ℚ[X] :=
  DirectedPowerBounds.shift (cutMidpoint e) (cutR e i)

private def r42cutR : Cut→Fin 4→Scaled
  | .gaH => ![r42cR0u .gaH,r42cR1g .gaH,r42cR2g .gaH,r42cR3 .gaH]
  | .gaB => ![r42cR0 .gaB,r42cR1g .gaB,r42cR2u .gaB,r42cR3 .gaB]
  | .abG => ![r42cR0 .abG,r42cR1u .abG,r42cR2a .abG,r42cR3 .abG]
  | .abH => ![r42cR0u .abH,r42cR1a .abH,r42cR2a .abH,r42cR3 .abH]
private theorem r42cutR_rep (e : Cut) (i : Fin 4) : (r42cutR e i).Rep (cutR e i) := by
  cases e <;> fin_cases i
  exacts [r42cR0u_rep .gaH,r42cR1g_rep .gaH,r42cR2g_rep .gaH,r42cR3_rep .gaH,
    r42cR0_rep .gaB,r42cR1g_rep .gaB,r42cR2u_rep .gaB,r42cR3_rep .gaB,
    r42cR0_rep .abG,r42cR1u_rep .abG,r42cR2a_rep .abG,r42cR3_rep .abG,
    r42cR0u_rep .abH,r42cR1a_rep .abH,r42cR2a_rep .abH,r42cR3_rep .abH]

private def r42cmc (e : Cut) (i : Fin 4) : Scaled :=
  if cutAtG e then (r42cutR e i).center 1 40 19 40 else (r42cutR e i).center 1 50 27 50
private theorem r42cmc_rep (e : Cut) (i : Fin 4) : (r42cmc e i).Rep (cutMassCentered e i) := by
  rcases hb : cutAtG e with _|_ <;> simp only [r42cmc,hb,Bool.false_eq_true,↓reduceIte]
  · exact r42_shift_rep (r42cutR_rep e i) 1 50 27 50 (by norm_num)
      (by norm_num [cutMidpoint,cutAngle,hb,h]) (by norm_num)
  · exact r42_shift_rep (r42cutR_rep e i) 1 40 19 40 (by norm_num)
      (by norm_num [cutMidpoint,cutAngle,hb,h]) (by norm_num)

theorem cut_mass_identity (e : Cut) (i : Fin 4) :
    cutMassCentered e i=C ((cutMassCentered e i).coeff 0)+
      tail (cutMassCentered e i) 1 8 := by
  cases e <;> fin_cases i <;>
    exact r42_tail_identity (((r42cmc_rep _ _).natDegree_le (by decide +kernel)).trans
      (by decide +kernel))

theorem cut_mass_reserve (e : Cut) (i : Fin 4) :
    (93/100:ℚ)<(cutMassCentered e i).coeff 0-
      PowerTailBounds.norm (cutMassCentered e i) 1 8 (cutRadius e) := by
  cases e <;> fin_cases i <;>
    exact r42_reserve_of_rep (r42cmc_rep _ _) (by decide +kernel) _ _ _ (by decide +kernel)

theorem cut_mass_lower (e : Cut) (i : Fin 4) {z : ℝ}
    (hz : z∈Set.Icc (cutAngle e:ℝ) (h:ℝ)) :
    (93/100:ℝ)<aeval z (cutR e i) := by
  have hh : ((h:ℚ):ℝ)=7/10 := by norm_num [h]
  rw [hh] at hz
  have hx : |z-(cutMidpoint e:ℝ)|≤(cutRadius e:ℝ) := by
    apply abs_le.mpr
    simp only [cutMidpoint,cutRadius]
    push_cast
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := DirectedPowerBounds.constant_lower (cut_mass_identity e i) hx
  have hr := (Rat.cast_lt (K:=ℝ)).mpr (cut_mass_reserve e i)
  push_cast at hr
  have he : aeval (z-(cutMidpoint e:ℝ)) (cutMassCentered e i)=aeval z (cutR e i) := by
    simp [cutMassCentered]
  rw [he] at hb
  linarith

theorem cut_masses_positive (e : Cut) {z : ℝ}
    (hz : z∈Set.Icc (cutAngle e:ℝ) (h:ℝ)) (i : Fin 4) :
    0<aeval z (cutR e i) := by
  have hh := cut_mass_lower e i hz
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
end
end
end

section
/-!
## Positive actual H/G/B and equal-angle negative-A endpoints

Every numerator and positive tangent
denominator has already been proved from its explicit polynomial.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity Explicit
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 Rbar cbar sigmabar etaQ h)

private lemma r42_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc (left .low:ℝ) (right .low:ℝ) := by
  norm_num [left,right,split]
  exact ⟨hz.1,by linarith [hz.2]⟩

private lemma r42_high_dom {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    z∈Icc (left .high:ℝ) (right .high:ℝ) := by
  norm_num [left,right,split,PositiveTD.Certificate.h]
  exact ⟨by linarith [hz.1],by linarith [hz.2]⟩

private lemma r42_low_dom' {z : ℝ} (hz : z∈Icc (left .low:ℝ) (right .low:ℝ)) :
    z∈Icc 0 (1/5:ℝ) := by
  norm_num [left,right,split] at hz
  exact ⟨hz.1,by linarith [hz.2]⟩

private lemma r42_high_dom' {z : ℝ} (hz : z∈Icc (left .high:ℝ) (right .high:ℝ)) :
    z∈Icc (1/5:ℝ) (7/10:ℝ) := by
  norm_num [left,right,split,PositiveTD.Certificate.h] at hz
  exact ⟨by linarith [hz.1],by linarith [hz.2]⟩

theorem zero_reduced_identity (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) :
    reducedBaseline f true 0 z=nonradical f z-R*normSum f
      ![pairNorm (Explicit.k f z) 1 0,pairNorm (Explicit.k f z) (Explicit.l f z) 0,
        pairNorm (Explicit.l f z) (Explicit.m f z) 0,pairNorm (Explicit.c f z) 1 0] := by
  have hh := reduced_identity f true hz (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  simpa [secant,norms,lambdaG,lambdaB,Explicit.m] using hh

theorem reduced_zero_le (f : Family) {z : ℝ} :
    reducedBaseline f true 0 z≤PositiveTD.baseline (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z := by
  simpa only [baseline_zero] using reduced_le_baseline f true 0 z

theorem low_H_endpoint {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z+
      V R (Explicit.k .low z) 1 z := by
  have hzf := r42_low_dom hz
  have hn := ordinary_norm_bounds .low hzf
  obtain ⟨_,hrG,hrB,_,hrH,_,_⟩ := ordinary_masses_positive .low hzf
  have ht := PositiveTD.Certificate.taylor_bounds (family_frame_domain .low hzf)
  have hA : aeval z (elementary .low+C10-1)≤nonradical .low z+Real.cos z-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [elementary_lower .low hzf,ht.2.2.2.2.1]
  have hN : 0<aeval z (PositiveTD.Certificate.num3 (elementary .low+C10-1)
      (PG .low) (PB .low) (PHminus .low) (RG .low) (RB .low) (RHminus .low)) := by
    simpa [NH] using (low_numerators_positive hz).1
  have hp := PositiveTD.Certificate.num3_transfer hrG hrB hrH
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    hn.2.1 hn.2.2.1 hn.2.2.2.2.1 hA hN
  have he := zero_reduced_identity .low hzf
  have hl := reduced_zero_le (f:=Family.low) (z:=z)
  dsimp [normSum] at he
  dsimp [V]
  linarith only [hp,he,hl]

theorem high_H_endpoint {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (Explicit.k .high z) 1 z := by
  have hzf := r42_high_dom hz
  have hn := ordinary_norm_bounds .high hzf
  obtain ⟨_,hrG,hrB,hrD,hrH,_,_⟩ := ordinary_masses_positive .high hzf
  have ht := PositiveTD.Certificate.taylor_bounds (family_frame_domain .high hzf)
  have hA : aeval z (elementary .high+C10-1)≤nonradical .high z+Real.cos z-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [elementary_lower .high hzf,ht.2.2.2.2.1]
  have hN : 0<aeval z (PositiveTD.Certificate.num4 (elementary .high+C10-1)
      (PG .high) (PB .high) (PHminus .high) (PD .high)
      (RG .high) (RB .high) (RHminus .high) (RD .high)) := by
    simpa [NH] using (high_numerators_positive hz).1
  have hp := PositiveTD.Certificate.num4_transfer hrG hrB hrH hrD
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    hn.2.1 hn.2.2.1 hn.2.2.2.2.1 hn.2.2.2.1 hA hN
  have he := zero_reduced_identity .high hzf
  have hl := reduced_zero_le (f:=Family.high) (z:=z)
  dsimp [normSum] at he
  dsimp [V]
  linarith only [hp,he,hl]

theorem high_G_endpoint {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (Explicit.k .high z) (Explicit.l .high z) z := by
  have hzf := r42_high_dom hz
  have hn := ordinary_norm_bounds .high hzf
  obtain ⟨hrH,_,hrB,hrD,_,hrG,_⟩ := ordinary_masses_positive .high hzf
  have ht := PositiveTD.Certificate.taylor_bounds (family_frame_domain .high hzf)
  have hcos := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (family_positive .high hzf).2.1.le
  have hA : aeval z (elementary .high+l .high*(C10-1))≤
      nonradical .high z+Explicit.l .high z*(Real.cos z-1) := by
    simp only [map_add,map_mul,map_sub,map_one,l_eval]
    linarith [elementary_lower .high hzf]
  have hp := PositiveTD.Certificate.num4_transfer hrH hrB hrG hrD
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    hn.1 hn.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.1 hA
    (show 0<aeval z (PositiveTD.Certificate.num4 _ _ _ _ _ _ _ _ _) from
      (high_numerators_positive hz).2.1)
  have he := zero_reduced_identity .high hzf
  have hl := reduced_zero_le (f:=Family.high) (z:=z)
  dsimp [normSum] at he
  dsimp [V]
  linarith only [hp,he,hl]

theorem high_B_endpoint {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (min (Explicit.l .high z) (Explicit.m .high z))
        (max (Explicit.l .high z) (Explicit.m .high z)) z := by
  have hzf := r42_high_dom hz
  have hn := ordinary_norm_bounds .high hzf
  obtain ⟨hrH,hrG,_,hrD,_,_,hrB⟩ := ordinary_masses_positive .high hzf
  have ht := PositiveTD.Certificate.taylor_bounds (family_frame_domain .high hzf)
  have hq : max (Explicit.l .high z) (Explicit.m .high z)≤aeval z (qStar .high) := by
    simpa [qStar,PositiveTD.Certificate.h,frameCap] using high_tilted_envelope hz
  have hq0 : 0≤aeval z (qStar .high) :=
    ((family_positive .high hzf).2.1.le.trans (le_max_left _ _)).trans hq
  have hcos₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hq0
  have hcos₂ := mul_le_mul_of_nonpos_right hq (sub_nonpos.mpr (Real.cos_le_one z))
  have hA : aeval z (elementary .high+qStar .high*(C10-1))≤
      nonradical .high z+max (Explicit.l .high z) (Explicit.m .high z)*(Real.cos z-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [elementary_lower .high hzf]
  have hp := PositiveTD.Certificate.num4_transfer hrH hrG hrB hrD
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.2.2.2.2 hn.2.2.2.1 hA
    (show 0<aeval z (PositiveTD.Certificate.num4 _ _ _ _ _ _ _ _ _) from
      (high_numerators_positive hz).2.2.1)
  have he := zero_reduced_identity .high hzf
  have hl := reduced_zero_le (f:=Family.high) (z:=z)
  dsimp [normSum] at he
  have hsort : ∀ t, pairNorm (min (Explicit.l .high z) (Explicit.m .high z))
      (max (Explicit.l .high z) (Explicit.m .high z)) t=
      pairNorm (Explicit.l .high z) (Explicit.m .high z) t := by
    intro t
    rcases le_total (Explicit.l .high z) (Explicit.m .high z) with hlm|hlm
    · rw [min_eq_left hlm,max_eq_right hlm]
    · rw [min_eq_right hlm,max_eq_left hlm,pairNorm_symm]
  simp only [V,hsort]
  linarith only [hp,he,hl]

theorem equal_GA_endpoint (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) :
    0<baseline true (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z := by
  have hz' := family_frame_domain f hz
  have hc : 0<Real.cos z := by linarith [(transport_trig hz').1]
  have hn := equal_GA_norm_bounds f hz
  have hr := equal_GA_masses_positive f hz
  have hnonneg := scaled_norms_nonnegative f true (z:=z) hz'
  have hA := equal_elementary_lower f hz
  have he := scaled_identity f true hz hz'
  have hp : 0<Real.cos z*reducedBaseline f true z z := by
    cases f
    · have hN : 0<aeval z (PositiveTD.Certificate.num3 (AZ .low)
          (equalGAP .low 0) (equalGAP .low 1) (equalGAP .low 2)
          (equalGAR .low 0) (equalGAR .low 1) (equalGAR .low 2)) := by
        simpa [NZ] using (low_numerators_positive (r42_low_dom' hz)).2.1
      have hh := PositiveTD.Certificate.num3_transfer (hr 0) (hr 1) (hr 2)
        (hnonneg 0) (hnonneg 1) (hnonneg 2) (hn 0) (hn 1) (hn 2) hA hN
      simpa only [he,normSum,↓reduceIte,reduceCtorEq] using hh
    · have hN : 0<aeval z (PositiveTD.Certificate.num4 (AZ .high)
          (equalGAP .high 0) (equalGAP .high 1) (equalGAP .high 2) (equalGAP .high 3)
          (equalGAR .high 0) (equalGAR .high 1) (equalGAR .high 2) (equalGAR .high 3)) := by
        simpa [NZ] using (high_numerators_positive (r42_high_dom' hz)).2.2.2.1
      have hh := PositiveTD.Certificate.num4_transfer (hr 0) (hr 1) (hr 2) (hr 3)
        (hnonneg 0) (hnonneg 1) (hnonneg 2) (hnonneg 3)
        (hn 0) (hn 1) (hn 2) (hn 3) hA hN
      simpa only [he,normSum,↓reduceIte,reduceCtorEq] using hh
  have hb := (mul_pos_iff_of_pos_left hc).mp hp
  exact hb.trans_le (reduced_le_baseline f true z z)

theorem equal_AB_endpoint {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z z := by
  have hzf := r42_high_dom hz
  have hz' := family_frame_domain .high hzf
  have hc : 0<Real.cos z := by linarith [(transport_trig hz').1]
  have hn := equal_AB_norm_bounds hz
  have hr := equal_AB_masses_positive hz
  have hnonneg := scaled_norms_nonnegative .high false (z:=z) hz'
  have hp := PositiveTD.Certificate.num4_transfer (hr 0) (hr 1) (hr 2) (hr 3)
    (hnonneg 0) (hnonneg 1) (hnonneg 2) (hnonneg 3)
    (hn 0) (hn 1) (hn 2) (hn 3) (equal_elementary_lower .high hzf)
    (show 0<aeval z (PositiveTD.Certificate.num4 _ _ _ _ _ _ _ _ _) from
      (high_numerators_positive hz).2.2.2.2)
  have he := scaled_identity .high false hzf hz'
  have hprod : 0<Real.cos z*reducedBaseline .high false z z := by
    simpa only [he,normSum,↓reduceIte,reduceCtorEq] using hp
  exact ((mul_pos_iff_of_pos_left hc).mp hprod).trans_le
    (reduced_le_baseline .high false z z)

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
end
end
end

section
/-!
## The low mixed and separated negative-A / TD2 endpoints

The separated estimates keep the larger coefficient `m + .4 z`, which controls the secant weight
of the cycle (`low_SH_endpoint`, `low_SG_endpoint`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity Explicit
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 Rbar cbar sigmabar etaQ h ch Ch sh
  ch_cast Ch_cast sh_cast)

private theorem r41_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc ((left .low:ℚ):ℝ) ((right .low:ℚ):ℝ) := by
  norm_num [left,right,split]
  exact hz

theorem cap_norm_bounds {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    (pairNorm (Explicit.k .low z) 1 (-frameCap))^2≤aeval z PHcap ∧
    (pairNorm (Explicit.k .low z) (Explicit.l .low z) (-frameCap))^2≤aeval z PGcap := by
  have hzf := r41_low_dom hz
  obtain ⟨hk,hl,_,_⟩ := family_positive .low hzf
  have hcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hs := (PositiveTD.Certificate.taylor_bounds hcap).2.1
  have hH := PositiveTD.Certificate.negative_norm_sq_le (q:=1) hk (by norm_num) hcap hs
  have hG := PositiveTD.Certificate.negative_norm_sq_le hk hl hcap hs
  constructor
  · norm_num only [PHcap,PH,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,
      k_eval,eq_ratCast,Rat.cast_mul,sh_cast]
    linarith only [hH]
  · norm_num only [PGcap,PG,map_add,map_sub,map_mul,map_pow,aeval_C,
      k_eval,l_eval,eq_ratCast,Rat.cast_mul,sh_cast]
    linarith only [hG]

theorem phi_lower {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z phiLo≤PositiveAngularEnvelope.phi (frameCap-z) := by
  have ht := PositiveTD.Certificate.taylor_bounds hz
  have hcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have htcap := PositiveTD.Certificate.taylor_bounds hcap
  have hs : 0≤Real.sin z := (transport_trig hz).2.2.1
  have hsum : (ch:ℝ)+(sh:ℝ)≤Real.cos frameCap+Real.sin frameCap := by
    rw [ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.1]
  have hsum0 : 0≤Real.cos frameCap+Real.sin frameCap := by
    linarith [(transport_trig hcap).1,(transport_trig hcap).2.2.1]
  have hp := mul_le_mul hsum ht.2.2.2.2.1
    (show 0≤aeval z C10 by linarith [ht.2.2.2.1]) hsum0
  have hdiff : Real.cos frameCap-Real.sin frameCap≤(Ch:ℝ)-(sh:ℝ) := by
    rw [Ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.2]
  have hdiff0 : 0≤(Ch:ℝ)-(sh:ℝ) := by
    linarith [(transport_trig hcap).2.2.2.2]
  have hp' := mul_le_mul hdiff ht.2.2.1 hs hdiff0
  have he : PositiveAngularEnvelope.phi (frameCap-z)=
      (Real.cos frameCap+Real.sin frameCap)*Real.cos z-
        (Real.cos frameCap-Real.sin frameCap)*Real.sin z := by
    simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
    ring
  simp only [phiLo,map_sub,map_mul,aeval_C,eq_ratCast,Rat.cast_add]
  rw [he]
  linarith only [hp,hp']

theorem low_M_elementary {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    aeval z (elementary .low+k .low*(phiLo-1)+l .low*C (ch-1))≤
      nonradical .low z+Explicit.k .low z*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
        Explicit.l .low z*(Real.cos frameCap-1) := by
  have hzf := r41_low_dom hz
  obtain ⟨hk,hl,_,_⟩ := family_positive .low hzf
  have hphi := mul_le_mul_of_nonneg_left
    (sub_le_sub_right (phi_lower (family_frame_domain .low hzf)) 1) hk.le
  have hcap := PositiveTD.Certificate.taylor_bounds
    (show frameCap∈Icc 0 frameCap by exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hcos : (ch:ℝ)-1≤Real.cos frameCap-1 := by
    rw [ch_cast]
    linarith [hcap.2.2.2.2.1]
  have hp := mul_le_mul_of_nonneg_left hcos hl.le
  simp only [map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,eq_ratCast]
  linarith [elementary_lower .low hzf]

theorem low_M_endpoint {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z+
      mixedG (Explicit.k .low z) (Explicit.l .low z) z := by
  have hzf := r41_low_dom hz
  have hn := ordinary_norm_bounds .low hzf
  obtain ⟨hrH,_,hrB,_,_,hrG,_⟩ := ordinary_masses_positive .low hzf
  have hp := PositiveTD.Certificate.num3_transfer hrH hrB hrG
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    hn.1 hn.2.2.1 hn.2.2.2.2.2.1 (low_M_elementary hz)
    (show 0<aeval z (PositiveTD.Certificate.num3 _ _ _ _ _ _ _) from
      (low_numerators_positive hz).2.2.1)
  have he := zero_reduced_identity .low hzf
  have hl := reduced_zero_le (f:=Family.low) (z:=z)
  simp only [normSum,↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] at he
  unfold mixedG
  linarith only [hp,he,hl]

theorem low_separated_elementary {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    aeval z lowStar≤nonradical .low z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z) := by
  have hzf := r41_low_dom hz
  have hm := (tilted_bounds .low hzf).2.2
  have hgap : 0≤frameCap-z := by dsimp [frameCap]; linarith [hz.2]
  have hp : (Explicit.m .low z+(2/5)*z)*(frameCap-z)≤
      (aeval z (mHi .low)+(2/5)*z)*(frameCap-z) :=
    mul_le_mul_of_nonneg_right (by linarith) hgap
  simp only [lowStar,map_sub,map_mul,map_add,aeval_C,aeval_X,eq_ratCast]
  norm_num only [PositiveTD.Certificate.h]
  dsimp [frameCap] at hp ⊢
  linarith [elementary_lower .low hzf]

theorem low_SH_endpoint {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+
        V R (Explicit.k .low z) 1 frameCap := by
  have hzf := r41_low_dom hz
  have hn := ordinary_norm_bounds .low hzf
  have hncap := cap_norm_bounds hz
  obtain ⟨_,hrG,hrB,_,_,_,_⟩ := ordinary_masses_positive .low hzf
  have hcap := PositiveTD.Certificate.taylor_bounds
    (show frameCap∈Icc 0 frameCap by exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hA : aeval z (lowStar+C (ch-1))≤nonradical .low z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+Real.cos frameCap-1 := by
    simp only [map_add,aeval_C,eq_ratCast,Rat.cast_sub,Rat.cast_one,ch_cast]
    linarith [low_separated_elementary hz,hcap.2.2.2.2.1]
  have hp := PositiveTD.Certificate.num3_transfer hrG hrB
    (show 0<aeval z (C (77/100):ℚ[X]) by simp only [aeval_C,eq_ratCast]; norm_num)
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    hn.2.1 hn.2.2.1 hncap.1 hA
    (show 0<aeval z (PositiveTD.Certificate.num3 _ _ _ _ _ _ _) from
      (low_numerators_positive hz).2.2.2.1)
  have he := zero_reduced_identity .low hzf
  have hl := reduced_zero_le (f:=Family.low) (z:=z)
  simp only [normSum,↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] at he
  unfold V
  linarith only [hp,he,hl]

theorem low_SG_endpoint {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+
        V R (Explicit.k .low z) (Explicit.l .low z) frameCap := by
  have hzf := r41_low_dom hz
  have hn := ordinary_norm_bounds .low hzf
  have hncap := cap_norm_bounds hz
  obtain ⟨hrH,_,hrB,_,_,_,_⟩ := ordinary_masses_positive .low hzf
  have hlpos := (family_positive .low hzf).2.1
  have hcap := PositiveTD.Certificate.taylor_bounds
    (show frameCap∈Icc 0 frameCap by exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hcos : (ch:ℝ)-1≤Real.cos frameCap-1 := by
    rw [ch_cast]
    linarith [hcap.2.2.2.2.1]
  have hprod := mul_le_mul_of_nonneg_left hcos hlpos.le
  have hA : aeval z (lowStar+l .low*C (ch-1))≤nonradical .low z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+
        Explicit.l .low z*(Real.cos frameCap-1) := by
    simp only [map_add,map_mul,aeval_C,l_eval,eq_ratCast,Rat.cast_sub,Rat.cast_one]
    linarith [low_separated_elementary hz]
  have hrG : 0<aeval z (C (77/100)*l .low) := by
    simp only [map_mul,aeval_C,l_eval,eq_ratCast]
    have := hlpos
    positivity
  have hp := PositiveTD.Certificate.num3_transfer hrH hrB hrG
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _) (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    (PositiveTD.Certificate.pairNorm_nonneg _ _ _)
    hn.1 hn.2.2.1 hncap.2 hA
    (show 0<aeval z (PositiveTD.Certificate.num3 _ _ _ _ _ _ _) from
      (low_numerators_positive hz).2.2.2.2)
  have he := zero_reduced_identity .low hzf
  have hl := reduced_zero_le (f:=Family.low) (z:=z)
  simp only [normSum,↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] at he
  unfold V
  linarith only [hp,he,hl]

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
end
end
end

section
/-!
## All fourteen negative-flat-A / nonnegative-TD2 scalar endpoints

Every endpoint below uses the explicit prescribed
weights and the actual trigonometric norms. No scalar positivity remains
as a premise of these statements.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity Explicit
open PositiveTD.Certificate (h)

theorem cut_endpoint (e : Cut) {z : ℝ}
    (hz : z∈Icc (cutAngle e:ℝ) (h:ℝ)) :
    0<baseline (cutAtG e) (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z)
      (cutAngle e:ℝ) z+cutV e z := by
  have hn := cut_norm_bounds e hz
  have hr := cut_masses_positive e hz
  have hnonneg := cut_norms_nonnegative e hz
  have hp := PositiveTD.Certificate.num4_transfer (hr 0) (hr 1) (hr 2) (hr 3)
    (hnonneg 0) (hnonneg 1) (hnonneg 2) (hnonneg 3)
    (hn 0) (hn 1) (hn 2) (hn 3) (cut_elementary_lower e hz)
    (show 0<aeval z (PositiveTD.Certificate.num4 _ _ _ _ _ _ _ _ _) from
      cut_numerator_positive e hz)
  have he := cut_scaled_identity e hz
  have hprod : 0<Real.cos (cutAngle e:ℝ)*
      (reducedBaseline .high (cutAtG e) (cutAngle e:ℝ) z+cutV e z) := by
    simpa only [he,normSum,reduceCtorEq,↓reduceIte] using hp
  have hc : 0<Real.cos (cutAngle e:ℝ) := by
    linarith [(transport_trig (cut_domain e)).1]
  have hh := (mul_pos_iff_of_pos_left hc).mp hprod
  have hl := reduced_le_baseline .high (cutAtG e) (cutAngle e:ℝ) z
  linarith

theorem low_endpoints {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z+
      V R (Explicit.k .low z) 1 z ∧
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z+
      mixedG (Explicit.k .low z) (Explicit.l .low z) z ∧
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+V R (Explicit.k .low z) 1 frameCap ∧
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z-
      (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)+
        V R (Explicit.k .low z) (Explicit.l .low z) frameCap ∧
    0<baseline true (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z z := by
  exact ⟨low_H_endpoint hz,low_M_endpoint hz,low_SH_endpoint hz,low_SG_endpoint hz,
    equal_GA_endpoint .low (by norm_num [left,right,split]; exact hz)⟩

theorem high_endpoints {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (Explicit.k .high z) 1 z ∧
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (Explicit.k .high z) (Explicit.l .high z) z ∧
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (min (Explicit.l .high z) (Explicit.m .high z))
        (max (Explicit.l .high z) (Explicit.m .high z)) z ∧
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z z ∧
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z z := by
  exact ⟨high_H_endpoint hz,high_G_endpoint hz,high_B_endpoint hz,
    equal_GA_endpoint .high (by norm_num [left,right,split,PositiveTD.Certificate.h]; exact hz),
    equal_AB_endpoint hz⟩

theorem GA_cut_endpoints {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) (1/4) z+
      V R (Explicit.k .high z) 1 (z-1/4) ∧
    0<baseline true (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) (1/4) z+
      V R (Explicit.m .high z) (Explicit.l .high z) (z-1/4) := by
  have hzc (e : Cut) (he : cutAtG e=true) : z∈Icc ((cutAngle e:ℚ):ℝ) ((h:ℚ):ℝ) := by
    simp only [cutAngle,he,↓reduceIte]
    norm_num [PositiveTD.Certificate.h]
    exact hz
  have hH := cut_endpoint .gaH (hzc .gaH rfl)
  have hB := cut_endpoint .gaB (hzc .gaB rfl)
  constructor
  · simpa [cutAtG,cutAngle,cutV,cutCostCoefficient,cutRole,cutPCoefficient,cutQCoefficient,V] using hH
  · simpa [cutAtG,cutAngle,cutV,cutCostCoefficient,cutRole,cutPCoefficient,cutQCoefficient,V,
      pairNorm_symm (Explicit.m .high z) (Explicit.l .high z)] using hB

theorem AB_cut_endpoints {z : ℝ} (hz : z∈Icc (19/50:ℝ) (7/10:ℝ)) :
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) (19/50) z+
      V R (Explicit.k .high z) (Explicit.l .high z) (z-19/50) ∧
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) (19/50) z+
      V R (Explicit.k .high z) 1 (z-19/50) := by
  have hzc (e : Cut) (he : cutAtG e=false) : z∈Icc ((cutAngle e:ℚ):ℝ) ((h:ℚ):ℝ) := by
    simp only [cutAngle,he,Bool.false_eq_true,↓reduceIte]
    norm_num [PositiveTD.Certificate.h]
    exact hz
  have hG := cut_endpoint .abG (hzc .abG rfl)
  have hH := cut_endpoint .abH (hzc .abH rfl)
  constructor
  · simpa [cutAtG,cutAngle,cutV,cutCostCoefficient,cutRole,cutPCoefficient,cutQCoefficient,V] using hG
  · simpa [cutAtG,cutAngle,cutV,cutCostCoefficient,cutRole,cutPCoefficient,cutQCoefficient,V] using hH

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
end
end
end

section
/-!
## The low equal-angle comparison

Increasing the fixed coefficient
decreases the increment of the original zero-angle norm. The GA
equal-angle endpoint therefore also pays for the low AB endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowEqual
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open SecantCoordinate SecantBaseline

theorem norm_increment {k m l p : ℝ} (hk : 0<k) (hkm : k≤ m)
    (hl : 0<l) (hlp : l≤p) :
    pairNorm m p 0-pairNorm m l 0≤pairNorm k p 0-pairNorm k l 0 := by
  have hm : 0< m := hk.trans_le hkm
  have hksq : 0<k^2 := sq_pos_of_pos hk
  have hmsq : 0< m^2 := sq_pos_of_pos hm
  have hd (x : ℝ) : HasDerivAt
      (fun x => radical (k^2) x-radical (m^2) x)
      (x/radical (k^2) x-x/radical (m^2) x) x :=
    (radical_hasDerivAt hksq).sub (radical_hasDerivAt hmsq)
  have hmono : MonotoneOn (fun x => radical (k^2) x-radical (m^2) x) (Icc l p) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    intro x hx
    have hx0 : 0≤x := (hl.trans hx.1).le
    have hroot : radical (k^2) x≤radical (m^2) x := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg (sub_nonneg.mpr hkm) (by linarith : 0≤ m+k)]
    have hquot := div_le_div_of_nonneg_left hx0 (radical_positive hksq) hroot
    linarith
  have hh := hmono ⟨le_rfl,hlp⟩ ⟨hlp,le_rfl⟩ hlp
  dsimp [radical] at hh
  simp only [pairNorm_zero]
  linarith

theorem charge_comparison {k m l s : ℝ} (hk : 0<k) (hkm : k≤ m)
    (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    FlatTStress.secantCharge R l k s≤FlatTStress.secantCharge R l m s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hp : l≤l/Real.cos s := by
    apply (le_div_iff₀ hc).2
    nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one s) hl.le]
  have hh := norm_increment hk hkm hl hp
  have hm := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg qCap)
  dsimp [FlatTStress.secantCharge]
  linarith

theorem baseline_comparison {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 frameCap) :
    baseline true (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z≤
      baseline false (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z := by
  have hz' : z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
    norm_num [Certificate.left,Certificate.right,Certificate.split]
    exact hz
  have hp := Explicit.family_positive .low hz'
  have hk := (Explicit.family_basic_domain .low hz').2.2.2.1
  have hm := (Explicit.low_tilted hz).1
  have hh := charge_comparison (m:=Explicit.m .low z) hp.1 (by linarith) hp.2.1 hs
  rw [baseline_eq_extension true _ _ _ _ hs,baseline_eq_extension false _ _ _ _ hs]
  simp only [angularBaseline,affected,↓reduceIte,Bool.false_eq_true,baseline_zero]
  dsimp only [Explicit.m] at hh
  linarith

theorem original (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z z := by
  have hGA := (Certificate.low_endpoints hz).2.2.2.2
  cases atG
  · exact hGA.trans_le (baseline_comparison hz
      ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩)
  · exact hGA

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowEqual
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedNegativeCurves
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SecantCoordinate

def cosine (z x : ℝ) : ℝ := (Real.cos z+x*Real.sin z)/radical 1 x
def upper (r z x : ℝ) : ℝ :=
  Real.cos z+(13/12+Real.sin z)*x-R*AffectedNorm.norm r z x
def lower (r z x : ℝ) : ℝ :=
  radical 1 x+(13/12)*x+r*(cosine z x-1)-R*AffectedNorm.norm r z x
def upperFirst (r z x : ℝ) : ℝ := 13/12+Real.sin z-R*AffectedNorm.first r z x
def lowerFirst (r z x : ℝ) : ℝ :=
  x/radical 1 x+13/12+r*(Real.sin z-x*Real.cos z)/(radical 1 x)^3-R*AffectedNorm.first r z x
def lowerSecond (r z x : ℝ) : ℝ :=
  1/(radical 1 x)^3+r*(-Real.cos z*(1-2*x^2)-3*x*Real.sin z)/(radical 1 x)^5-
    R*AffectedNorm.second r z x

theorem cosine_arctan (z x : ℝ) : cosine z x=Real.cos (z-Real.arctan x) := by
  rw [Real.cos_sub,Real.cos_arctan,Real.sin_arctan]
  dsimp [cosine,radical]
  ring

theorem cosine_le_one (z x : ℝ) : cosine z x≤1 := by
  rw [cosine_arctan]
  exact Real.cos_le_one _

theorem cosine_hasDerivAt (z x : ℝ) :
    HasDerivAt (cosine z) ((Real.sin z-x*Real.cos z)/(radical 1 x)^3) x := by
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hd := (((hasDerivAt_id' x).mul_const (Real.sin z)).const_add (Real.cos z)).div
    (radical_hasDerivAt (A:=1) (by norm_num)) hW.ne'
  convert hd using 1
  · rfl
  · field_simp [hW.ne']
    nlinarith [congrArg (fun a : ℝ => a*Real.sin z) hW2]

theorem cosineFirst_hasDerivAt (z x : ℝ) :
    HasDerivAt (fun x => (Real.sin z-x*Real.cos z)/(radical 1 x)^3)
      ((-Real.cos z*(1-2*x^2)-3*x*Real.sin z)/(radical 1 x)^5) x := by
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hd := (((hasDerivAt_id' x).mul_const (Real.cos z)).const_sub (Real.sin z)).fun_div
    ((radical_hasDerivAt (A:=1) (by norm_num)).fun_pow 3) (pow_ne_zero 3 hW.ne')
  convert hd using 1
  simp only [Nat.cast_ofNat,show (3:ℕ)-1=2 from rfl]
  field_simp [hW.ne']
  nlinarith [congrArg (fun a : ℝ => a*Real.cos z) hW2]

theorem upper_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (upper r z) (upperFirst r z x) x := by
  convert (((hasDerivAt_id x).const_mul (13/12+Real.sin z)).const_add
    (Real.cos z)).sub ((AffectedNorm.norm_hasDerivAt hv).const_mul R) using 1
  · rfl
  · dsimp [upperFirst]
    ring

theorem upperFirst_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (upperFirst r z) (-R*AffectedNorm.second r z x) x := by
  convert ((AffectedNorm.first_hasDerivAt hv).const_mul R).const_sub
    (13/12+Real.sin z) using 1
  · rfl
  · ring

theorem lower_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (lower r z) (lowerFirst r z x) x := by
  have hd := (((radical_hasDerivAt (A:=1) (x:=x) (by norm_num)).add
    ((hasDerivAt_id x).const_mul (13/12:ℝ))).add
      (((cosine_hasDerivAt z x).sub_const 1).const_mul r)).sub
        ((AffectedNorm.norm_hasDerivAt hv).const_mul R)
  convert hd using 1
  · rfl
  · dsimp [lowerFirst]
    ring

theorem lowerFirst_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (lowerFirst r z) (lowerSecond r z x) x := by
  have hd := (((radicalFirst_hasDerivAt (A:=1) (x:=x) (by norm_num)).add_const
    (13/12:ℝ)).add ((cosineFirst_hasDerivAt z x).const_mul r)).sub
      ((AffectedNorm.first_hasDerivAt hv).const_mul R)
  convert hd using 1
  · funext y
    simp only [lowerFirst,Pi.add_apply,Pi.sub_apply]
    ring
  · dsimp [lowerSecond]
    ring

theorem upper_concave {r z a b : ℝ} (hv : 0<1-r*Real.sin z) :
    ConcaveOn ℝ (Icc a b) (upper r z) := by
  apply concave_of_deriv2 (fun x _ => upper_hasDerivAt hv)
    (fun x _ => upperFirst_hasDerivAt hv)
  intro x hx
  have hn : 0≤AffectedNorm.second r z x := by
    exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) 3)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg qCap)) hn

theorem branch_difference (r z x : ℝ) :
    upper r z x-lower r z x=(radical 1 x-r)*(cosine z x-1) := by
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  dsimp [upper,lower,cosine]
  field_simp [hW.ne']
  ring

theorem downward_derivative {r z x : ℝ} (hx : 0≤x) (he : radical 1 x=r) :
    upperFirst r z x≤lowerFirst r z x := by
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hid : upperFirst r z x-lowerFirst r z x=
      (x/radical 1 x)*(cosine z x-1) := by
    rw [←he]
    dsimp [upperFirst,lowerFirst,cosine]
    field_simp [hW.ne']
    nlinarith [congrArg (fun a : ℝ => a*Real.sin z) hW2]
  have hp := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hx hW.le)
    (sub_nonpos.mpr (cosine_le_one z x))
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedNegativeCurves
end
end
end
