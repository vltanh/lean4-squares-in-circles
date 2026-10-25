module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CurvatureConstants
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2NegativeSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.PowerTailBounds

/-!
# Eight squares: the original correlated late-range comparison for negative DE

The two
coefficient lines have their original slopes .3 and .305 and the common
right endpoint .863. The tangent and radical enclosures are proved by
alternating Taylor bounds and positive squaring at the stated endpoints.
-/

section
/-!
## The literal high-DE third-derivative polynomial certificates

The early degree-nine polynomial keeps its centered quadratic. The late logarithmic-derivative
numerator, a quartic, is a positive combination of squares and products of the distances to the
ends of `[0.613, 0.843]` (`late_fraction_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape.Certificate
open Polynomial

def early : ℚ[X] := C (6/25)+C 3*X*(1-X^2)^2*
  (-C (3577/10000)+C ((5/2)*(6423/10000)*(1319/2500))*X^2+
    C ((35/8)*(6423/10000)*(1319/2500)^2)*X^4)
def earlyCenter : ℚ[X] := CenteredMonomialBounds.translated (3/10) early
def earlyQuadratic : ℚ := earlyCenter.coeff 2-PowerTailBounds.norm earlyCenter 3 7 (3/10)

/-- The centered early polynomial, coefficient by coefficient. -/
private theorem r73_earlyCenter_eq : earlyCenter=
      C (3495832380142334529/100000000000000000000:ℚ)+
      C (287168023740894387/10000000000000000000:ℚ)*X+
      C (774769922213526279/250000000000000000:ℚ)*X^2+
      C (19820351254900317/25000000000000000:ℚ)*X^3+
      C (-35146473393297933/5000000000000000:ℚ)*X^4+
      C (-2740677778025511/500000000000000:ℚ)*X^5+
      C (20090207378871/25000000000000:ℚ)*X^6+
      C (13628542421853/2500000000000:ℚ)*X^7+
      C (6335932940001/1000000000000:ℚ)*X^8+
      C (234664182963/100000000000:ℚ)*X^9 := by
  apply Polynomial.funext
  intro x
  simp only [earlyCenter,CenteredMonomialBounds.translated,early,eval_comp,eval_add,eval_mul,
    eval_sub,eval_neg,eval_pow,eval_C,eval_X,eval_one]
  ring

theorem early_identity : earlyCenter=C (earlyCenter.coeff 0)+C (earlyCenter.coeff 1)*X+
    C (earlyCenter.coeff 2)*X^2+PowerTailBounds.tail earlyCenter 3 7 := by
  rw [r73_earlyCenter_eq]
  simp only [PowerTailBounds.tail,Fin.sum_univ_seven,Fin.val_zero,Fin.val_one,Fin.val_two,
    coeff_add,coeff_C_mul,coeff_X_pow,coeff_C,coeff_X]
  norm_num
  ring_nf

theorem early_reserve : (20557/10000:ℚ)<earlyQuadratic ∧
    (87/2500:ℚ)<earlyCenter.coeff 0-(earlyCenter.coeff 1)^2/(4*earlyQuadratic) := by
  simp only [earlyQuadratic,PowerTailBounds.norm,Fin.sum_univ_seven,r73_earlyCenter_eq,
    coeff_add,coeff_C_mul,coeff_X_pow,coeff_C,coeff_X]
  norm_num

theorem early_lower {y : ℝ} (hy : y∈Icc (0:ℝ) (3/5)) :
    (87/2500:ℝ)<aeval y early := by
  have hu : |y-3/10|≤(3/10:ℝ) := abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hq : (0:ℝ)<(earlyQuadratic:ℝ) := by
    have hh := Rat.cast_lt (K:=ℝ).mpr early_reserve.1
    push_cast at hh
    linarith
  have htail := PowerTailBounds.quadratic_lower early_identity (by norm_num : (0:ℚ)≤3/10)
    (by rw [show ((3/10:ℚ):ℝ)=3/10 by norm_num]; exact hu)
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(earlyCenter.coeff 0:ℝ)) (b:=(earlyCenter.coeff 1:ℝ)) (x:=y-3/10) hq
  have hr : (87/2500:ℝ)<(earlyCenter.coeff 0:ℝ)-
      (earlyCenter.coeff 1:ℝ)^2/(4*(earlyQuadratic:ℝ)) := by
    have hh := Rat.cast_lt (K:=ℝ).mpr early_reserve.2
    push_cast at hh
    exact hh
  have he : aeval (y-3/10) earlyCenter=aeval y early := by
    simp only [earlyCenter,CenteredMonomialBounds.translated,aeval_comp,map_add,aeval_C,aeval_X]
    congr 1
    simp only [eq_ratCast]
    push_cast
    ring_nf
  rw [he] at htail
  have hqq : (earlyQuadratic:ℝ)=(earlyCenter.coeff 2:ℝ)-
      (PowerTailBounds.norm earlyCenter 3 7 (3/10):ℝ) := by
    simp only [earlyQuadratic]
    push_cast
    ring
  rw [← hqq] at htail
  linarith

theorem late_fraction_lower {x : ℝ} (hx : x∈Icc (613/1000:ℝ) (843/1000)) :
    (637/5000:ℝ)<(27/20)*(1+x^2)*(1+x^2+827/1000)-
      x*(1+x^2+6*(827/1000)) := by
  have h1 : 0≤x-613/1000 := sub_nonneg.2 hx.1
  have h2 : 0≤843/1000-x := sub_nonneg.2 hx.2
  have hs := sq_nonneg (x-18/25)
  linarith [mul_nonneg hs h1,mul_nonneg (mul_nonneg hs h1) h2,
    mul_nonneg (sq_nonneg (x-3/4)) (pow_nonneg h2 2)]

end SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape.Certificate
end
end
end

section
/-!
## The binomial lower bound for the actual high-DE secant third derivative

The displayed degree-nine polynomial is used on its entire
native interval. The substitution is y=x/sqrt(1+x^2); the two square
roots are related by their exact positive squares before any rational
coefficient bound is applied.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape
open Candidate Secondary PositiveAngularEnvelope
open NegativeAPositiveTD.SecantCoordinate

namespace BinomialFive

def root (u : ℝ) : ℝ := Real.sqrt (1-u)
def value (u : ℝ) : ℝ := 1/(root u)^5
def first (u : ℝ) : ℝ := (5/2)/(root u)^7
def second (u : ℝ) : ℝ := (35/4)/(root u)^9

theorem root_pos {u : ℝ} (hu : u<1) : 0<root u :=
  Real.sqrt_pos.mpr (by linarith)
theorem root_sq {u : ℝ} (hu : u≤1) : (root u)^2=1-u :=
  Real.sq_sqrt (by linarith)
theorem root_derivative {u : ℝ} (hu : u<1) :
    HasDerivAt root (-1/(2*root u)) u := by
  convert ((hasDerivAt_id u).const_sub 1).sqrt (by linarith : 1-u≠0) using 1
  · rfl
  · dsimp [root]

theorem value_derivative {u : ℝ} (hu : u<1) : HasDerivAt value (first u) u := by
  have hp := root_pos hu
  have hd := (hasDerivAt_const u (1:ℝ)).div ((root_derivative hu).pow 5)
    (pow_ne_zero 5 hp.ne')
  convert hd using 1
  · rfl
  · dsimp [first]
    field_simp [hp.ne']
    ring

theorem first_derivative {u : ℝ} (hu : u<1) : HasDerivAt first (second u) u := by
  have hp := root_pos hu
  have hd := (hasDerivAt_const u (5/2:ℝ)).div ((root_derivative hu).pow 7)
    (pow_ne_zero 7 hp.ne')
  convert hd using 1
  · rfl
  · dsimp [second]
    field_simp [hp.ne']
    ring

theorem second_lower {u : ℝ} (hu : u∈Ico 0 1) : (35/4:ℝ)≤ second u := by
  have hp := root_pos hu.2
  have hsq := root_sq hu.2.le
  have hr : root u≤1 := by
    calc root u=Real.sqrt (1-u) := rfl
      _≤Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith [hu.1])
      _=1 := Real.sqrt_one
  have hpow : (root u)^9≤1 := by simpa using pow_le_pow_left₀ hp.le hr 9
  unfold second
  apply (le_div_iff₀ (pow_pos hp 9)).2
  nlinarith

/-- The first three positive binomial coefficients of (1-u)^(-5/2). -/
theorem lower {u : ℝ} (hu : u∈Ico 0 1) :
    1+(5/2)*u+(35/8)*u^2≤value u := by
  have hfirst : ∀v∈Icc 0 u,0≤first v-5/2-(35/4)*v := by
    have hm : MonotoneOn (fun v => first v-5/2-(35/4)*v) (Icc 0 u) := by
      apply monoOn_of_hasDeriv_nonneg
      · intro v hv
        exact (((first_derivative (hv.2.trans_lt hu.2)).sub_const (5/2)).sub
          ((hasDerivAt_id v).const_mul (35/4))).continuousAt.continuousWithinAt
      · intro v hv
        exact ((first_derivative (hv.2.trans hu.2)).sub_const (5/2)).sub
          ((hasDerivAt_id v).const_mul (35/4))
      · intro v hv
        linarith [second_lower ⟨hv.1.le,hv.2.trans hu.2⟩]
    intro v hv
    have hh := hm ⟨le_rfl,hu.1⟩ hv hv.1
    have h0 : first 0=5/2 := by simp [first,root]
    simp only [h0] at hh
    linarith
  have hm : MonotoneOn (fun v => value v-1-(5/2)*v-(35/8)*v^2) (Icc 0 u) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro v hv
      exact ((((value_derivative (hv.2.trans_lt hu.2)).sub_const 1).sub
        ((hasDerivAt_id v).const_mul (5/2))).sub
        (((hasDerivAt_id v).pow 2).const_mul (35/8))).continuousAt.continuousWithinAt
    · intro v hv
      exact (((value_derivative (hv.2.trans hu.2)).sub_const 1).sub
        ((hasDerivAt_id v).const_mul (5/2))).sub
        (((hasDerivAt_id v).pow 2).const_mul (35/8))
    · intro v hv
      have hh := hfirst v (Ioo_subset_Icc_self hv)
      simp only [id,Nat.cast_ofNat,mul_one]
      linarith
  have hh := hm ⟨le_rfl,hu.1⟩ ⟨hu.1,le_rfl⟩ hu.1
  have h0 : value 0=1 := by simp [value,root]
  simp only [h0] at hh
  linarith

end BinomialFive

def parameterThird (c x : ℝ) : ℝ :=
  3*R*x*c*(2*x^2-3*(1+c^2))/(radical (1+c^2) x)^7

theorem baseThird_parameter_derivative (c x : ℝ) :
    HasDerivAt (fun c => baseThird c x) (parameterThird c x) c := by
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  have hn2 := radical_square (A:=1+c^2) (x:=x) (by positivity)
  have hroot : HasDerivAt (fun c => radical (1+c^2) x)
      (c/radical (1+c^2) x) c := by
    convert ((((hasDerivAt_id c).pow 2).const_add 1).add_const (x^2)).sqrt
      (by positivity : 1+c^2+x^2≠0) using 1
    · rfl
    · dsimp [radical]
      ring
  have hd := ((((((hasDerivAt_id c).pow 2).const_add 1).const_mul R).div
    (hroot.pow 5) (pow_ne_zero 5 hn.ne')).sub_const
      (1/(radical 1 x)^5)).const_mul (3*x)
  convert hd using 1
  · rfl
  · dsimp [parameterThird]
    field_simp [hn.ne']
    linear_combination (-2*x*c)*hn2

theorem baseThird_antitone_parameter {c C x : ℝ}
    (hc : 0≤c) (hC : c≤C) (hx : 0≤x) (hx2 : 2*x^2≤3) :
    baseThird C x≤baseThird c x := by
  have hm : AntitoneOn (fun c => baseThird c x) (Icc c C) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun v _ => (baseThird_parameter_derivative v x).continuousAt.continuousWithinAt)
      (fun v _ => baseThird_parameter_derivative v x)
    intro v hv
    have hv0 : 0≤v := hc.trans hv.1.le
    have hnum : 3*R*x*v*(2*x^2-3*(1+v^2))≤0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg qCap)) hx) hv0)
        (by nlinarith [sq_nonneg v])
    exact div_nonpos_of_nonpos_of_nonneg hnum
      (pow_pos (radical_positive (by positivity : (0:ℝ)<1+v^2)) 7).le
  exact hm ⟨le_rfl,hC⟩ ⟨hC,le_rfl⟩ hC

namespace Early

abbrev C : ℝ := 1057/1000
abbrev coefficient : ℝ := 6423/10000
abbrev ratioLower : ℝ := 1319/2500

theorem coefficient_bounds :
    coefficient<R/(Real.sqrt (1+C^2))^3 ∧ ratioLower≤C^2/(1+C^2) := by
  have ha : 0<Real.sqrt (1+C^2) := Real.sqrt_pos.mpr (by positivity)
  have ha2 := Real.sq_sqrt (show 0≤1+C^2 by positivity)
  have hpow : ((Real.sqrt (1+C^2))^3)^2=(1+C^2)^3 := by
    rw [←pow_mul,show (3:ℕ)*2=2*3 by norm_num,pow_mul,ha2]
  have hs : (coefficient*(Real.sqrt (1+C^2))^3)^2<R^2 := by
    rw [mul_pow,hpow,radius_sq]
    norm_num [coefficient,C,qCap]
  constructor
  · apply (lt_div_iff₀ (pow_pos ha 3)).2
    nlinarith [Real.sqrt_nonneg qCap]
  · norm_num [ratioLower,C]

/-- Exact square-root normalization of the secant-coordinate derivative. -/
theorem normalized_identity {x : ℝ} (hx : 0≤x) :
    let w := radical 1 x
    let y := x/w
    let u := C^2/(1+C^2)*y^2
    baseThird C x=3*y*(1-y^2)^2*
      (R/(Real.sqrt (1+C^2))^3*BinomialFive.value u-1) := by
  dsimp only
  let w := radical 1 x
  let y := x/w
  let u := C^2/(1+C^2)*y^2
  let a := Real.sqrt (1+C^2)
  let b := BinomialFive.root u
  let n := radical (1+C^2) x
  have hw : 0<w := radical_positive (by norm_num : (0:ℝ)<1)
  have hw2 : w^2=1+x^2 := radical_square (by norm_num : (0:ℝ)<1)
  have ha : 0<a := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a^2=1+C^2 := Real.sq_sqrt (by positivity)
  have hy : 0≤y := div_nonneg hx hw.le
  have hyid : (1-y^2)*w^2=1 := by
    dsimp [y]
    field_simp [hw.ne']
    nlinarith only [hw2]
  have hy2 : y^2<1 := by
    have hw2pos := sq_pos_of_pos hw
    nlinarith
  have hr : C^2/(1+C^2)∈Ico (0:ℝ) 1 := by norm_num [C]
  have hu : u∈Ico (0:ℝ) 1 := by
    dsimp [u]
    exact ⟨mul_nonneg hr.1 (sq_nonneg y),by nlinarith [mul_le_mul_of_nonneg_right hr.2.le (sq_nonneg y)]⟩
  have hb : 0<b := BinomialFive.root_pos hu.2
  have hb2 : b^2=1-u := BinomialFive.root_sq hu.2.le
  have hn : 0<n := radical_positive (by positivity : 0<1+C^2)
  have hn2 : n^2=1+C^2+x^2 := radical_square (by positivity : 0<1+C^2)
  have hprod2 : (a*b*w)^2=n^2 := by
    rw [mul_pow,mul_pow,ha2,hb2,hn2]
    dsimp [u,y]
    field_simp [hw.ne']
    nlinarith only [hw2]
  have hprod : n=a*b*w := by nlinarith [mul_pos (mul_pos ha hb) hw]
  have hone : 1-y^2=1/w^2 := (eq_div_iff (pow_ne_zero 2 hw.ne')).2 hyid
  have hfactor : 3*x/w^5=3*y*(1-y^2)^2 := by
    rw [hone]
    dsimp [y]
    field_simp [hw.ne']
  have ha5 : a^5=(1+C^2)*a^3 := by
    calc a^5=a^2*a^3 := by ring
         _=(1+C^2)*a^3 := by rw [ha2]
  have hid : baseThird C x=(3*x/w^5)*(R/a^3*(1/b^5)-1) := by
    change 3*x*(R*(1+C^2)/n^5-1/w^5)=_
    rw [hprod,mul_pow,mul_pow,ha5]
    field_simp [ha.ne',hb.ne',hw.ne',show 1+C^2≠0 by positivity]
  rw [hid,hfactor]
  rfl

theorem parameter_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (3/4)) :
    -(6/25:ℝ)<baseThird C x := by
  have he := normalized_identity hx.1
  dsimp only at he
  obtain ⟨w,hw_def⟩ : ∃ w,w=radical 1 x := ⟨_,rfl⟩
  obtain ⟨y,hy_def⟩ : ∃ y,y=x/w := ⟨_,rfl⟩
  obtain ⟨u,hu_def⟩ : ∃ u,u=C^2/(1+C^2)*y^2 := ⟨_,rfl⟩
  rw [← hw_def,← hy_def,← hu_def] at he
  have hw : 0<w := hw_def ▸ radical_positive (by norm_num : (0:ℝ)<1)
  have hw2 : w^2=1+x^2 := hw_def ▸ radical_square (by norm_num : (0:ℝ)<1)
  have hy0 : 0≤y := hy_def ▸ div_nonneg hx.1 hw.le
  have hymax : y≤3/5 := by
    have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
    have hcross : x≤(3/5)*w := by nlinarith
    rw [hy_def]
    exact (div_le_iff₀ hw).2 hcross
  have hy : y∈Icc (0:ℝ) (3/5) := ⟨hy0,hymax⟩
  have hratio : C^2/(1+C^2)∈Ico (0:ℝ) 1 := by norm_num [C]
  have huy : (1319/2500)*y^2≤u := by
    rw [hu_def]
    exact mul_le_mul_of_nonneg_right coefficient_bounds.2 (sq_nonneg y)
  have hu : u∈Ico (0:ℝ) 1 := by
    have hy2 : y^2≤9/25 := by nlinarith
    rw [hu_def]
    refine ⟨mul_nonneg hratio.1 (sq_nonneg y),?_⟩
    have hh := mul_le_mul_of_nonneg_right hratio.2.le (sq_nonneg y)
    linarith
  have hbin := BinomialFive.lower hu
  have hsq := pow_le_pow_left₀ (by positivity : 0≤(1319/2500)*y^2) huy 2
  have hpoly : 1+(5/2)*(1319/2500)*y^2+(35/8)*(1319/2500)^2*y^4≤BinomialFive.value u := by
    nlinarith only [hbin,huy,hsq]
  have hp0 : 0≤1+(5/2)*(1319/2500)*y^2+(35/8)*(1319/2500)^2*y^4 := by positivity
  have hc0 : 0≤R/(Real.sqrt (1+C^2))^3 := by
    have := Real.sqrt_nonneg qCap
    unfold R
    positivity
  have hproduct := mul_le_mul coefficient_bounds.1.le hpoly hp0 hc0
  have hy1 : y^2≤1 := by nlinarith
  have hfactor : 0≤3*y*(1-y^2)^2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left (sub_le_sub_right hproduct 1) hfactor
  have hcertificate := Certificate.early_lower hy
  simp only [Certificate.early,map_add,map_sub,map_mul,map_pow,map_neg,map_one,
    Polynomial.aeval_C,Polynomial.aeval_X,eq_ratCast] at hcertificate
  push_cast at hcertificate
  rw [he]
  simp only [coefficient] at hscaled
  linarith only [hscaled,hcertificate]

/-- The complete early-range bound, before selecting a particular family. -/
theorem lower {c x : ℝ} (hc : c∈Icc (0:ℝ) C)
    (hx : x∈Icc (0:ℝ) (3/4)) : -(6/25:ℝ)<baseThird c x := by
  have hmono := baseThird_antitone_parameter hc.1 hc.2 hx.1
    (by nlinarith [pow_le_pow_left₀ hx.1 hx.2 2] : 2*x^2≤3)
  exact (parameter_lower hx).trans_le hmono

end Early
end SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape
end
end
end

section
/-!
## The ordinary part of the negative-DE third derivative

The full signed curvature tangent gives the stronger negative derivative
bounds. The early and late polynomial comparisons keep each actual
ordinary pair and its original larger coefficient.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope PairNormCalculus OrdinaryCurvatureBounds
open NegativeAPositiveTD.Curvature NegativeAPositiveTD.SecantCoordinate

def Vdd (p q t : ℝ) : ℝ := curvature R p q (-t)-q*Real.cos t
def Vddd (p q t : ℝ) : ℝ := -curvatureD R p q (-t)+q*Real.sin t
def numerator (p q d x : ℝ) : ℝ :=
  -Vddd p q d-6*x*Vdd p q d+2*(1-3*x^2)*Vd R p q d
def pureThird (l c p q θ x : ℝ) : ℝ :=
  l*baseThird c x+numerator p q (θ-Real.arctan x) x/(1+x^2)^3

theorem Vdd_hasDerivAt {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) : HasDerivAt (Vdd p q) (Vddd p q t) t := by
  have hc := (curvature_hasDerivAt (R:=R) hp hq
    (by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)).comp t (hasDerivAt_neg t)
  have hd := hc.sub ((Real.hasDerivAt_cos t).const_mul q)
  have hf : Vdd p q=fun s => (curvature R p q ∘ Neg.neg) s-q*Real.cos s := by
    funext s
    rfl
  rw [hf]
  exact hd.congr_deriv (by simp only [Vddd]; ring)

theorem pureSecond_hasDerivAt {l c p q θ x : ℝ} (hp : 0<p) (hq : 0<q)
    (hd : θ-Real.arctan x∈Icc 0 frameCap) :
    HasDerivAt (pureSecond l c p q θ) (pureThird l c p q θ x) x := by
  have harg := (Real.hasDerivAt_arctan x).const_sub θ
  have hV := (Vd_hasDerivAt (R:=R) hp hq hd).comp x harg
  have hVV := (Vdd_hasDerivAt hp hq hd).comp x harg
  have hden : 1+x^2≠0 := by positivity
  have h2 : HasDerivAt (fun y : ℝ => 1+y^2) (2*x) x :=
    ((hasDerivAt_pow 2 x).const_add 1).congr_deriv (by norm_num)
  have hsq : HasDerivAt (fun y : ℝ => (1+y^2)^2) (2*(1+x^2)*(2*x)) x :=
    (h2.pow 2).congr_deriv (by norm_num)
  have htwo : HasDerivAt (fun y : ℝ => 2*y) 2 x :=
    ((hasDerivAt_id' x).const_mul (2:ℝ)).congr_deriv (by norm_num)
  have hn := hVV.fun_add (htwo.fun_mul hV)
  have hratio := hn.fun_div hsq (pow_ne_zero 2 hden)
  have hd2 := ((baseSecond_hasDerivAt c x).const_mul l).fun_add hratio
  have hf : pureSecond l c p q θ=fun y => l*baseSecond c y+
      ((Vdd p q ∘ fun y => θ-Real.arctan y) y+2*y*(Vd R p q ∘ fun y => θ-Real.arctan y) y)/
        (1+y^2)^2 := by
    funext y
    simp only [pureSecond,negativeSecond,Vdd,Function.comp_apply]
  rw [hf]
  refine hd2.congr_deriv ?_
  simp only [pureThird,numerator,Vdd,Function.comp_apply]
  field_simp
  ring

/-- The complete quadratic negative-curvature tangent, before any
short-angle weakening. -/
theorem second_model {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) :
    Vdd p q d<q*(-3/10-d/3+d^2/2) := by
  have hq := hp.trans_le hpq
  have hconstants := universal_constants hp hpq hqp
  have ht := curvature_signed_tangent hp hpq hqp
    (t:=-d) (by rw [abs_neg,abs_of_nonneg hd.1]; exact hd.2)
  have hm := mul_le_mul_of_nonneg_right hconstants.2.1.le hd.1
  have hcos := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x:=d)) hq.le
  dsimp [Vdd]
  nlinarith

theorem third_model {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) :
    q*(1/3-d)< -Vddd p q d := by
  have hq := hp.trans_le hpq
  have hconst := (universal_constants hp hpq hqp).2.1
  have hcurv := curvatureD_antitone_signed hp hpq hqp
    (show -d∈Icc (-frameCap) frameCap by constructor <;> linarith [hd.1,hd.2])
    (show (0:ℝ)∈Icc (-frameCap) frameCap by norm_num [frameCap]) (by linarith [hd.1])
  rw [curvatureD_zero] at hcurv
  have hs := mul_le_mul_of_nonneg_left (Real.sin_le hd.1) hq.le
  dsimp [Vddd]
  linarith

theorem second_whole {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) :
    Vdd p q d< -(36/125)*q := by
  have hm := second_model hp hpq hqp hd
  have hq := hp.trans_le hpq
  have hpoly : -3/10-d/3+d^2/2≤-(36/125:ℝ) := by
    have h := mul_nonneg hd.1 (sub_nonneg.mpr hd.2)
    dsimp [frameCap] at *
    nlinarith
  exact hm.trans_le (by nlinarith [mul_le_mul_of_nonneg_left hpoly hq.le])

theorem second_short {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 (177/1000:ℝ)) :
    Vdd p q d< -(3/10)*q := by
  have hm := second_model hp hpq hqp
    ⟨hd.1,by norm_num [frameCap]; linarith [hd.2]⟩
  have hprod := mul_nonneg hd.1 (show 0≤2/3-d by linarith [hd.2])
  have hq := hp.trans_le hpq
  nlinarith [mul_nonneg hq.le hprod]

theorem third_whole {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) : Vddd p q d<(39/125)*q := by
  have hq := hp.trans_le hpq
  have hconst := (universal_constants hp hpq hqp).2.1
  have hcurv := curvatureD_antitone_signed hp hpq hqp
    (show -d∈Icc (-frameCap) frameCap by constructor <;> linarith [hd.1,hd.2])
    (show (0:ℝ)∈Icc (-frameCap) frameCap by norm_num [frameCap]) (by linarith [hd.1])
  rw [curvatureD_zero] at hcurv
  have hs := mul_lt_mul_of_pos_left (transport_trig hd).2.2.2.1 hq
  dsimp [Vddd]
  nlinarith

theorem first_upper {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) : Vd R p q d<(7/5)*q := by
  have hh := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hp hpq hqp
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hd hd.1
  have hzero : Vd R p q 0=slopeZero p q := by
    simp only [Vd,mixedNDerivative,normD1,slopeZero,sub_zero,mul_zero,
      Real.sin_zero,Real.cos_zero]
    ring_nf
  rw [hzero] at hh
  exact hh.trans_lt (universal_constants hp hpq hqp).2.2

theorem first_upper_late {p q d : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 (3/20:ℝ)) :
    Vd R p q d<q*(7/5-(3/10)*d) := by
  have hderiv (t : ℝ) (ht : t∈Icc 0 d) :=
    (Vd_hasDerivAt (R:=R) hp (hp.trans_le hpq)
      ⟨ht.1,by norm_num [frameCap]; linarith [ht.2,hd.2]⟩).neg
  have hh := derivative_reserve (f:=fun t => -Vd R p q t)
    (df:=fun t => -Vdd p q t) (k:=(3/10)*q)
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t (Ioo_subset_Icc_self ht))
    (fun t ht => by
      have hb := second_short hp hpq hqp
        (show t∈Icc 0 (177/1000:ℝ) by exact ⟨ht.1.le,by linarith [ht.2,hd.2]⟩)
      linarith)
    (show (0:ℝ)∈Icc 0 d from ⟨le_rfl,hd.1⟩)
    (show d∈Icc 0 d from ⟨hd.1,le_rfl⟩) hd.1
  have hzero := first_upper hp hpq hqp (d:=0) (by norm_num [frameCap])
  nlinarith

theorem numerator_early_low {p q d x : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (hd : d∈Icc 0 frameCap)
    (hx : 0≤x) (hx3 : 3*x^2≤1) : (137/200)*q<numerator p q d x := by
  have hq := hp.trans_le hpq
  have hqp : q≤2*p := by linarith
  have h₂ := second_whole hp hpq hqp hd
  have h₃ := third_whole hp hpq hqp hd
  have h₁ := Vd_lower hp hpq hratio hd
  have hmul₂ := mul_le_mul_of_nonpos_left h₂.le (show -6*x≤0 by linarith)
  have hmul₁ := mul_le_mul_of_nonneg_left h₁.le (show 0≤2*(1-3*x^2) by linarith)
  have hxu : x≤577351/1000000 := by nlinarith
  have hpoly : (137/200:ℝ)<4/3-39/125+(216/125)*x-4*x^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hxu)
      (show 0≤4*(x+577351/1000000)-216/125 by linarith)
    nlinarith
  have hqpoly := mul_lt_mul_of_pos_left hpoly hq
  dsimp [numerator]
  nlinarith

theorem numerator_early_middle {p q d x : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 (177/1000:ℝ))
    (hx : x∈Icc 0 (307/500:ℝ)) (hx3 : 1≤3*x^2) :
    (447/500)*q<numerator p q d x := by
  have hq := hp.trans_le hpq
  have hd' : d∈Icc 0 frameCap := ⟨hd.1,by norm_num [frameCap]; linarith [hd.2]⟩
  have h₂ := second_short hp hpq hqp hd
  have h₃ := third_model hp hpq hqp hd'
  have h₁ := first_upper hp hpq hqp hd'
  have hmul₂ := mul_le_mul_of_nonpos_left h₂.le (show -6*x≤0 by linarith [hx.1])
  have hmul₁ := mul_le_mul_of_nonpos_left h₁.le (show 2*(1-3*x^2)≤0 by linarith)
  have hpoly : (447/500:ℝ)<1/3-177/1000+(9/5)*x+(14/5)*(1-3*x^2) := by
    have hh := mul_nonneg (sub_nonneg.mpr hx.2)
      (show 0≤(42/5)*(x+307/500)-9/5 by linarith [hx.1])
    nlinarith
  have hqpoly := mul_lt_mul_of_pos_left hpoly hq
  have hqd := mul_le_mul_of_nonneg_left hd.2 hq.le
  dsimp [numerator]
  nlinarith

def latePolynomial (x : ℝ) : ℝ := 47/15+(9/5)*x-(42/5)*x^2

theorem numerator_late {p q d x : ℝ} (hp : 0<p) (hpq : p≤q)
    (hqp : q≤2*p) (hd : d∈Icc 0 (3/20:ℝ))
    (hx : 613/1000≤x) : q*latePolynomial x≤numerator p q d x := by
  have hq := hp.trans_le hpq
  have hd' : d∈Icc 0 frameCap := ⟨hd.1,by norm_num [frameCap]; linarith [hd.2]⟩
  have h₂ := second_model hp hpq hqp hd'
  have h₃ := third_model hp hpq hqp hd'
  have h₁ := first_upper_late hp hpq hqp hd
  have hx0 : 0≤x := by linarith
  have hx3 : 1≤3*x^2 := by nlinarith [sq_nonneg (x-613/1000)]
  have hmul₂ := mul_le_mul_of_nonpos_left h₂.le (show -6*x≤0 by linarith)
  have hmul₁ := mul_le_mul_of_nonpos_left h₁.le (show 2*(1-3*x^2)≤0 by linarith)
  have hdd : 3*x*d^2≤(9/20)*x*d := by
    have hh := mul_nonneg hd.1 (sub_nonneg.mpr hd.2)
    nlinarith [mul_nonneg hx0 hh]
  have hfactor : 0≤-(8/5)+(31/20)*x+(9/5)*x^2 := by
    nlinarith [sq_nonneg (x-613/1000)]
  have hrem := mul_nonneg hd.1 hfactor
  have hqrem := mul_nonneg hq.le
    (show 0≤d*(-8/5+2*x+(9/5)*x^2)-3*x*d^2 by nlinarith)
  dsimp [numerator,latePolynomial]
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape
open Candidate Secondary PositiveAngularEnvelope
open NegativeAPositiveTD.SecantCoordinate

namespace TrigonometricBounds
open NegativeAPositiveTD.NegativeSlope

theorem transition : (613/1000:ℝ)<Real.tan (11/20:ℝ) ∧
    Real.tan (11/20:ℝ)<307/500 := by
  have ht := rational_taylor (t:=11/20)
    (by norm_num [frameCap] : ((11/20:ℚ):ℝ)∈Icc 0 frameCap)
  rw [show ((11/20:ℚ):ℝ)=11/20 by norm_num] at ht
  have hc : 0<Real.cos (11/20:ℝ) := by
    linarith [(transport_trig (show (11/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).1]
  rw [Real.tan_eq_sin_div_cos]
  constructor
  · apply (lt_div_iff₀ hc).2
    norm_num [sinLo,cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,
      PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
      PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
    linarith [ht.1,ht.2.2.2]
  · apply (div_lt_iff₀ hc).2
    norm_num [sinHi,cosLo,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,
      PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
    linarith [ht.2.1,ht.2.2.1]

theorem middle_left : Real.tan (523/1000:ℝ)<577/1000 := by
  have ht := rational_taylor (t:=523/1000)
    (by norm_num [frameCap] : ((523/1000:ℚ):ℝ)∈Icc 0 frameCap)
  rw [show ((523/1000:ℚ):ℝ)=523/1000 by norm_num] at ht
  have hc : 0<Real.cos (523/1000:ℝ) := by
    linarith [(transport_trig (show (523/1000:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).1]
  rw [Real.tan_eq_sin_div_cos]
  apply (div_lt_iff₀ hc).2
  norm_num [sinHi,cosLo,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
  linarith [ht.2.1,ht.2.2.1]

theorem cap : (105286/125000:ℝ)<Real.tan frameCap ∧
    Real.tan frameCap<(842289/1000000:ℝ) ∧
    1/Real.cos frameCap<(65373/50000:ℝ) := by
  have ht := rational_taylor (t:=7/10)
    (by norm_num [frameCap] : ((7/10:ℚ):ℝ)∈Icc 0 frameCap)
  rw [show ((7/10:ℚ):ℝ)=7/10 by norm_num] at ht
  have hc : 0<Real.cos frameCap := by
    linarith [(transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1]
  norm_num [sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,
    PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
  refine ⟨?_,?_,?_⟩
  · rw [Real.tan_eq_sin_div_cos]
    apply (lt_div_iff₀ hc).2
    dsimp [frameCap] at *
    linarith [ht.1,ht.2.2.2]
  · rw [Real.tan_eq_sin_div_cos]
    apply (div_lt_iff₀ hc).2
    dsimp [frameCap] at *
    linarith [ht.2.1,ht.2.2.1]
  · apply (div_lt_iff₀ hc).2
    dsimp [frameCap] at *
    linarith [ht.2.2.1]

theorem radical_tan {s : ℝ} (hs : s∈Icc 0 frameCap) :
    radical 1 (Real.tan s)=1/Real.cos s := by
  have hh := Real.cos_arctan (Real.tan s)
  rw [arctan_tan hs] at hh
  rw [hh]
  simp [radical]

end TrigonometricBounds

namespace Late

def rate : Bool→ℝ | false=>3/10 | true=>61/200
def coefficient (bt3 : Bool) (x : ℝ) : ℝ :=
  863/1000+rate bt3*(frameCap-Real.arctan x)
def mass (c x : ℝ) : ℝ :=
  R*(1+c^2)*(1+x^2)^3/(radical (1+c^2) x)^5
def firstLog (c x : ℝ) : ℝ :=
  x*(1+x^2+6*c^2)/((1+x^2)*(1+x^2+c^2))
def bracket (c x : ℝ) : ℝ := 5/(1+x^2+c^2)-2/(1+c^2)
def secondLog (bt3 : Bool) (c x : ℝ) : ℝ := rate bt3*c/(1+x^2)*bracket c x
def total (bt3 : Bool) (x : ℝ) : ℝ := mass (coefficient bt3 x) x
def totalFirst (bt3 : Bool) (x : ℝ) : ℝ :=
  total bt3 x*(firstLog (coefficient bt3 x) x+secondLog bt3 (coefficient bt3 x) x)
def reserve (bt3 : Bool) (x : ℝ) : ℝ :=
  3*x*(total bt3 x-radical 1 x)+latePolynomial x

theorem rate_bounds (bt3 : Bool) : 0≤rate bt3 ∧ rate bt3≤61/200 := by
  cases bt3 <;> norm_num [rate]

theorem domain {x : ℝ} (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) :
    x∈Icc (613/1000:ℝ) (843/1000) ∧ Real.arctan x∈Icc (11/20:ℝ) frameCap := by
  have h0 : 0≤x := by linarith [hx.1,TrigonometricBounds.transition.1]
  have ha := arctan_interval (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ⟨h0,hx.2⟩
  have hlo := Real.arctan_strictMono.monotone hx.1
  rw [arctan_tan (show (11/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap])] at hlo
  exact ⟨⟨by linarith [hx.1,TrigonometricBounds.transition.1],
    by linarith [hx.2,TrigonometricBounds.cap.2.1]⟩,⟨hlo,ha.2⟩⟩

theorem coefficient_bounds (bt3 : Bool) {x : ℝ}
    (hx : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap)) :
    coefficient bt3 x∈Icc (863/1000:ℝ) (909/1000) := by
  have ha := (domain hx).2
  cases bt3 <;> dsimp [coefficient,rate,frameCap] at * <;>
    exact ⟨by linarith [ha.2],by linarith [ha.1]⟩

theorem coefficient_hasDerivAt (bt3 : Bool) (x : ℝ) :
    HasDerivAt (coefficient bt3) (-rate bt3/(1+x^2)) x := by
  have h := (((Real.hasDerivAt_arctan x).const_sub frameCap).const_mul (rate bt3)).const_add
    (863/1000:ℝ)
  unfold coefficient
  exact h.congr_deriv (by ring)

theorem coefficient_cap (bt3 : Bool) : coefficient bt3 (Real.tan frameCap)=863/1000 := by
  simp [coefficient,arctan_tan (show frameCap∈Icc 0 frameCap by norm_num [frameCap])]

theorem mass_pos (c x : ℝ) : 0< mass c x := by
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  dsimp [mass]
  positivity

theorem mass_upper_of_square {c x b : ℝ} (hb : 0<b)
    (h : qCap*(1+c^2)^2*(1+x^2)^6<b^2*(1+c^2+x^2)^5) : mass c x<b := by
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  have hn2 := radical_square (A:=1+c^2) (x:=x) (by positivity)
  have hp : ((radical (1+c^2) x)^5)^2=(1+c^2+x^2)^5 := by
    rw [←pow_mul,show (5:ℕ)*2=2*5 by norm_num,pow_mul,hn2]
  have hnum : (R*(1+c^2)*(1+x^2)^3)^2=qCap*(1+c^2)^2*(1+x^2)^6 := by
    rw [mul_pow,mul_pow,radius_sq]
    ring
  apply (div_lt_iff₀ (pow_pos hn 5)).2
  have hden : 0<b*(radical (1+c^2) x)^5 := mul_pos hb (pow_pos hn 5)
  nlinarith [mul_pow b ((radical (1+c^2) x)^5) 2]

theorem mass_lower_of_square {c x b : ℝ} (_hb : 0≤b)
    (h : b^2*(1+c^2+x^2)^5<qCap*(1+c^2)^2*(1+x^2)^6) : b< mass c x := by
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  have hn2 := radical_square (A:=1+c^2) (x:=x) (by positivity)
  have hp : ((radical (1+c^2) x)^5)^2=(1+c^2+x^2)^5 := by
    rw [←pow_mul,show (5:ℕ)*2=2*5 by norm_num,pow_mul,hn2]
  have hnum : (R*(1+c^2)*(1+x^2)^3)^2=qCap*(1+c^2)^2*(1+x^2)^6 := by
    rw [mul_pow,mul_pow,radius_sq]
    ring
  apply (lt_div_iff₀ (pow_pos hn 5)).2
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hright : 0<R*(1+c^2)*(1+x^2)^3 := by positivity
  nlinarith [mul_pow b ((radical (1+c^2) x)^5) 2]

theorem rational_mass_endpoints : mass (863/1000) (843/1000)<183/100 ∧
    (182777/100000:ℝ)< mass (863/1000) (105286/125000) := by
  constructor
  · apply mass_upper_of_square (by norm_num)
    norm_num [qCap]
  · apply mass_lower_of_square (by norm_num)
    norm_num [qCap]

/-- Multiplication by the actual positive denominator, not a changed coefficient. -/
theorem mass_identity (c x : ℝ) :
    (1+x^2)^3*baseThird c x=3*x*(mass c x-radical 1 x) := by
  have hw := radical_positive (A:=1) (x:=x) (by norm_num)
  have hn := radical_positive (A:=1+c^2) (x:=x) (by positivity)
  have hw2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hw6 : (1+x^2)^3=(radical 1 x)^6 := by
    rw [←hw2,←pow_mul]
  dsimp [baseThird,mass]
  rw [hw6]
  field_simp [hw.ne',hn.ne']

theorem mass_antitone_coefficient {c C x : ℝ}
    (hc : 0≤c) (hC : c≤C) (hx : 0<x) (hx2 : 2*x^2≤3) : mass C x≤ mass c x := by
  have hh := mul_le_mul_of_nonneg_left
    (baseThird_antitone_parameter hc hC hx.le hx2) (by positivity : 0≤(1+x^2)^3)
  rw [mass_identity,mass_identity] at hh
  nlinarith

end Late
end SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape
end
end
end
