module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEHighCertificates
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2InversePower

/-!
# The binomial lower bound for the actual high-DE secant third derivative

Uncompiled transcription of the early-range argument of the high-DE
companions. The displayed degree-nine polynomial is used on its entire
native interval. The substitution is y=x/sqrt(1+x^2); the two square
roots are related by their exact positive squares before any rational
coefficient bound is applied.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape
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
    ring

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

theorem second_lower {u : ℝ} (hu : u∈Ico 0 1) : (35/4:ℝ)≤second u := by
  have hp := root_pos hu.2
  have hsq := root_sq hu.2.le
  have hr : root u≤1 := by nlinarith
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
    norm_num [first,root] at hh
    exact hh
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
      norm_num only [pow_one]
      linarith
  have hh := hm ⟨le_rfl,hu.1⟩ ⟨hu.1,le_rfl⟩ hu.1
  norm_num [value,root] at hh
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
    nlinarith [congrArg (fun v : ℝ => 3*R*x*c*v) hn2]

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
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith [sq_nonneg v])
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
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
    ring
  have ha5 : a^5=(1+C^2)*a^3 := by
    calc a^5=a^2*a^3 := by ring
         _=(1+C^2)*a^3 := by rw [ha2]
  have hid : baseThird C x=(3*x/w^5)*(R/a^3*(1/b^5)-1) := by
    change 3*x*(R*(1+C^2)/n^5-1/w^5)=_
    rw [hprod,mul_pow,mul_pow,ha5]
    field_simp [ha.ne',hb.ne',hw.ne',show 1+C^2≠0 by positivity]
    ring
  rw [hid,hfactor]
  rfl

theorem parameter_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (3/4)) :
    -(6/25:ℝ)<baseThird C x := by
  let w := radical 1 x
  let y := x/w
  let u := C^2/(1+C^2)*y^2
  have hw : 0<w := radical_positive (by norm_num : (0:ℝ)<1)
  have hw2 : w^2=1+x^2 := radical_square (by norm_num : (0:ℝ)<1)
  have hy0 : 0≤y := div_nonneg hx.1 hw.le
  have hyid : y*w=x := by dsimp [y]; exact div_mul_cancel₀ x hw.ne'
  have hy2 : y^2*w^2=x^2 := by nlinarith only [congrArg (fun t : ℝ => t^2) hyid]
  have hymax : y≤3/5 := by
    have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
    have hcross : x≤(3/5)*w := by nlinarith
    exact (div_le_iff₀ hw).2 hcross
  have hy : y∈Icc (0:ℝ) (3/5) := ⟨hy0,hymax⟩
  have hratio : C^2/(1+C^2)∈Ico (0:ℝ) 1 := by norm_num [C]
  have huy : ratioLower*y^2≤u := mul_le_mul_of_nonneg_right coefficient_bounds.2 (sq_nonneg y)
  have hu : u∈Ico (0:ℝ) 1 := by
    dsimp [u]
    refine ⟨mul_nonneg hratio.1 (sq_nonneg y),?_⟩
    have hh := mul_le_mul_of_nonneg_right hratio.2.le (sq_nonneg y)
    nlinarith [pow_le_pow_left₀ hy0 hymax 2]
  have hbin := BinomialFive.lower hu
  have hsq := pow_le_pow_left₀ (show 0≤ratioLower*y^2 by norm_num [ratioLower]; positivity) huy 2
  have hpoly : 1+(5/2)*ratioLower*y^2+(35/8)*ratioLower^2*y^4≤BinomialFive.value u := by
    nlinarith only [hbin,huy,hsq]
  have hp0 : 0≤1+(5/2)*ratioLower*y^2+(35/8)*ratioLower^2*y^4 := by
    norm_num [ratioLower]
    positivity
  have hc0 : 0≤R/(Real.sqrt (1+C^2))^3 := by positivity
  have hproduct := mul_le_mul coefficient_bounds.1.le hpoly hp0 hc0
  have hfactor : 0≤3*y*(1-y^2)^2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left (sub_le_sub_right hproduct 1) hfactor
  have hcertificate := Certificate.early_lower hy
  norm_num only [Certificate.early,map_add,map_sub,map_mul,map_pow,map_one,
    Polynomial.aeval_C,Polynomial.aeval_X] at hcertificate
  have he := normalized_identity hx.1
  change baseThird C x=3*y*(1-y^2)^2*(R/(Real.sqrt (1+C^2))^3*BinomialFive.value u-1) at he
  rw [he]
  dsimp [coefficient,ratioLower] at hscaled
  nlinarith only [hscaled,hcertificate]

/-- The complete early-range bound, before selecting a particular family. -/
theorem lower {c x : ℝ} (hc : c∈Icc (0:ℝ) C)
    (hx : x∈Icc (0:ℝ) (3/4)) : -(6/25:ℝ)<baseThird c x := by
  have hmono := baseThird_antitone_parameter hc.1 hc.2 hx.1
    (by nlinarith [pow_le_pow_left₀ hx.1 hx.2 2] : 2*x^2≤3)
  exact (parameter_lower hx).trans_le hmono

end Early
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEHighShape
