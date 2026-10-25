module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.CorrelatedSameBlock
public import SquaresInCircles.Eight.Owners.Endpoint.RotationPenalty

/-!
# Eight squares: whole-interval angle reserves for crossed outer contacts

One degree-six Taylor polynomial controls the
complete enlarged comparison interval [0,.9].  On [.04,.7] its difference
from the left endpoint factors into a strictly positive polynomial.
These are continuous interval arguments; no angular partition is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedAngleReserve
open EndpointRotationPenalty

def curve (A k h : ℝ) : ℝ := charge*h-k*Real.sin h-A*(1-Real.cos h)

def polynomial (h : ℝ) : ℝ :=
  charge*h-(183/200)*(h-h^3/6+h^5/120)-
    (1/2)*(h^2/2-h^4/24+h^6/720)

def polynomialD (h : ℝ) : ℝ :=
  charge-(183/200)*(1-h^2/2+h^4/24)-
    (1/2)*(h-h^3/6+h^5/120)

theorem curve_hasDerivAt (A k h : ℝ) :
    HasDerivAt (curve A k)
      (charge-k*Real.cos h-A*Real.sin h) h := by
  have h1 : HasDerivAt (fun x : ℝ => charge*x) charge h :=
    ((hasDerivAt_id h).const_mul charge).congr_deriv (by simp)
  have h2 : HasDerivAt (fun x => k*Real.sin x) (k*Real.cos h) h :=
    (Real.hasDerivAt_sin h).const_mul k
  have h3 : HasDerivAt (fun x => A*(1-Real.cos x)) (A*Real.sin h) h :=
    (((Real.hasDerivAt_cos h).const_sub 1).const_mul A).congr_deriv (by ring)
  exact (h1.sub h2).sub h3

theorem polynomial_hasDerivAt (h : ℝ) :
    HasDerivAt polynomial (polynomialD h) h := by
  have hs : HasDerivAt (fun x : ℝ => x-x^3/6+x^5/120) (1-h^2/2+h^4/24) h :=
    (((hasDerivAt_id h).sub ((hasDerivAt_pow 3 h).div_const 6)).add
      ((hasDerivAt_pow 5 h).div_const 120)).congr_deriv (by simp; ring)
  have hc : HasDerivAt (fun x : ℝ => x^2/2-x^4/24+x^6/720) (h-h^3/6+h^5/120) h :=
    ((((hasDerivAt_pow 2 h).div_const 2).sub ((hasDerivAt_pow 4 h).div_const 24)).add
      ((hasDerivAt_pow 6 h).div_const 720)).congr_deriv (by simp; ring)
  have h1 : HasDerivAt (fun x : ℝ => charge*x) charge h :=
    ((hasDerivAt_id h).const_mul charge).congr_deriv (by simp)
  exact ((h1.sub (hs.const_mul (183/200))).sub (hc.const_mul (1/2)))

theorem polynomial_lower {h : ℝ} (hh : 0≤h) :
    polynomial h≤curve (1/2) (183/200) h := by
  have hs := sin_upper_five hh
  have hc := cos_lower_six hh
  dsimp [polynomial,curve]
  linarith

theorem polynomial_positive {h : ℝ} (hh : h∈Ioc 0 (9/10 : ℝ)) :
    0<polynomial h := by
  let x := 7/10-h
  have hx : x∈Icc (-(1/5) : ℝ) (7/10) := by
    dsimp [x]
    constructor <;> linarith [hh.1,hh.2]
  have hax : |x|≤7/10 := abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
  have hx2 : x^2≤49/100 := by
    have ht := pow_le_pow_left₀ (abs_nonneg x) hax 2
    rw [sq_abs] at ht
    norm_num at ht
    exact ht
  have hx3 : -(343/1000 : ℝ)≤x^3 := by
    have ht := pow_le_pow_left₀ (abs_nonneg x) hax 3
    rw [←abs_pow] at ht
    exact (abs_le.mp (by norm_num at ht ⊢; exact ht)).1
  have hx5 : -(16807/100000 : ℝ)≤x^5 := by
    have ht := pow_le_pow_left₀ (abs_nonneg x) hax 5
    rw [←abs_pow] at ht
    exact (abs_le.mp (by norm_num at ht ⊢; exact ht)).1
  have hx4 : x^4≤(49/100)*x^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)]
  have hp : 0<22780999/2205000000+(1236253/72000000)*x+
      (308611/1800000)*x^2+(1411/360000)*x^3-
      (181/18000)*x^4+x^5/1440 := by
    nlinarith [sq_nonneg x,hx.1]
  have hid : polynomial h=h*(22780999/2205000000+
      (1236253/72000000)*x+(308611/1800000)*x^2+
      (1411/360000)*x^3-(181/18000)*x^4+x^5/1440) := by
    dsimp [polynomial,charge,x]
    ring
  rw [hid]
  exact mul_pos hh.1 hp

theorem nonnegative {A k h : ℝ}
    (hA : A≤1/2) (hk : k≤183/200) (hh : h∈Icc 0 (9/10 : ℝ)) :
    0≤curve A k h := by
  have hs : 0≤Real.sin h := Real.sin_nonneg_of_nonneg_of_le_pi hh.1
    (by linarith [Real.pi_gt_three,hh.2])
  have hc : 0≤1-Real.cos h := sub_nonneg.mpr (Real.cos_le_one h)
  have hbase : 0≤curve (1/2) (183/200) h := by
    by_cases hz : h=0
    · simp [hz,curve]
    · exact (polynomial_positive ⟨lt_of_le_of_ne hh.1 (Ne.symm hz),hh.2⟩).le.trans
        (polynomial_lower hh.1)
  have hdiff : 0≤curve A k h-curve (1/2) (183/200) h := by
    have hp := mul_nonneg (sub_nonneg.mpr hk) hs
    have hq := mul_nonneg (sub_nonneg.mpr hA) hc
    dsimp [curve]
    nlinarith
  linarith

theorem polynomial_minimum {h : ℝ} (hh : h∈Icc (1/25 : ℝ) (7/10)) :
    polynomial (1/25)≤polynomial h := by
  let x := 7/10-h
  have hx : x∈Icc (0:ℝ) (33/50) := by
    dsimp [x]
    constructor <;> linarith [hh.1,hh.2]
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hx4 : x^4≤(1089/2500)*x^2 := by
    have ht := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
    nlinarith
  have hp : 0≤2370600577/459375000000+(10375907/1000000000)*x+
      (15439243/90000000)*x^2+(1291/300000)*x^3-
      (121/12000)*x^4+x^5/1440 := by
    nlinarith [pow_nonneg hx.1 3,pow_nonneg hx.1 5,sq_nonneg x,hx.1]
  have hid : polynomial h-polynomial (1/25)=(h-1/25)*
      (2370600577/459375000000+(10375907/1000000000)*x+
        (15439243/90000000)*x^2+(1291/300000)*x^3-
        (121/12000)*x^4+x^5/1440) := by
    dsimp [polynomial,charge,x]
    ring
  have hm := mul_nonneg (sub_nonneg.mpr hh.1) hp
  linarith

theorem remainder_monotone :
    MonotoneOn (fun h => curve (1/2) (183/200) h-polynomial h)
      (Icc 0 frameCap) := by
  have hderiv : ∀ x, HasDerivAt (fun h => curve (1/2) (183/200) h-polynomial h)
      ((charge-(183/200)*Real.cos x-(1/2)*Real.sin x)-polynomialD x) x :=
    fun x => (curve_hasDerivAt (1/2) (183/200) x).sub (polynomial_hasDerivAt x)
  apply monoOn_of_hasDeriv_nonneg (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
    (fun x _ => hderiv x)
  intro h hh
  have hc := cos_upper_four hh.1.le
  have hs := sin_upper_five hh.1.le
  dsimp only [polynomialD]
  linarith

/-- Every coefficient pair admitted by an actual crossed HG0 contact
has its complete [.04,.7] minimum at the left endpoint. -/
theorem minimum {A k h : ℝ} (hA : A≤1/2) (hk : k≤183/200)
    (hh : h∈Icc (1/25 : ℝ) frameCap) :
    curve A k (1/25)≤curve A k h := by
  have hsmall : (1/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hlarge : h∈Icc 0 frameCap := ⟨by linarith [hh.1],hh.2⟩
  have hrem := remainder_monotone hsmall hlarge hh.1
  have hpoly := polynomial_minimum (show h∈Icc (1/25 : ℝ) (7/10) from hh)
  have hs := CorrelatedSameBlock.sin_mono hsmall hlarge hh.1
  have hc := CorrelatedSameBlock.cos_anti hsmall hlarge hh.1
  have hp := mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hs)
  have hq := mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hc)
  dsimp [curve] at *
  nlinarith

end SquaresInCircles.Eight.CrossedAngleReserve
