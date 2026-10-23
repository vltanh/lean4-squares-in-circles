module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SecantBaseline
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2InversePower
public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeSlope

/-!
# The secant coordinate used by the negative-A angle companion

Uncompiled transcription of (10)--(11).  The coordinate is exactly
`x = tan s`; its inverse is retained in every negative-angle charge.
The two displayed derivatives are proved before any numerical bound
or endpoint reduction is applied.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.SecantCoordinate
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
  convert (hasDerivAt_id x).div (radical_hasDerivAt hA) hp.ne' using 1
  · rfl
  · field_simp [hp.ne']
    nlinarith

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
  have hroot : HasDerivAt (fun r => radical (1+r^2) x)
      (r/radical (1+r^2) x) r := by
    convert ((((hasDerivAt_id r).pow 2).const_add 1).add_const (x^2)).sqrt
      (by nlinarith [sq_nonneg r,sq_nonneg x] : 1+r^2+x^2≠0) using 1
    · rfl
    · dsimp [radical]
      ring
  have hd := (((((hasDerivAt_id r).pow 2).const_add 1).const_mul R).div
    (hroot.pow 3) (pow_ne_zero 3 hN.ne')).const_sub (1/(radical 1 x)^3)
  convert hd using 1
  · rfl
  · dsimp [ratioDerivative]
    field_simp [hN.ne']
    nlinarith [congrArg (fun u : ℝ => R*r*u) hN2]

/-- Enlarging the basic ratio in precisely the range used in (11). -/
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
    hcos,hnorm,Real.tan_arctan,base,radical,zero_pow,add_zero,
    Real.sqrt_one,mul_zero]
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
  · simpa only [Real.arctan_zero] using Real.arctan_le_arctan hx.1
  · simpa only [arctan_tan ha] using Real.arctan_le_arctan hx.2

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
  have hv := (V_hasDerivAt hp hq hθ).comp x ((Real.hasDerivAt_arctan x).const_sub z)
  have hb := (((base_hasDerivAt r x).sub_const (base r 0)).const_mul l).const_add B
  convert hb.add hv using 1
  · rfl
  · dsimp [pureFirst]
    ring

theorem pureFirst_hasDerivAt {l r p q z x : ℝ}
    (hp : 0<p) (hq : 0<q) (hθ : z-Real.arctan x∈Icc 0 frameCap) :
    HasDerivAt (pureFirst l r p q z) (pureSecond l r p q z x) x := by
  have hv := (Vd_hasDerivAt hp hq hθ).comp x ((Real.hasDerivAt_arctan x).const_sub z)
  have hden : 1+x^2≠0 := by positivity
  have hd := ((baseFirst_hasDerivAt r x).const_mul l).sub
    (hv.div (((hasDerivAt_id x).pow 2).const_add 1) hden)
  convert hd using 1
  · rfl
  · dsimp [pureSecond,negativeSecond]
    field_simp [hden]
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.SecantCoordinate
