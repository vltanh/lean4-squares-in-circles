module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic
public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein
public import SquaresInCircles.Eight.Owners.Endpoint.BudgetScalars
public import SquaresInCircles.Eight.Owners.Endpoint.RotationPenalty

/-!
# Eight squares: the unchanged source budget at an active common-frame cap boundary

The hypotheses (`BoundaryData`) are weak necessary bounds for the HG0 and BT2 contacts at the
same q. The endpoint budget uses the original H and T tangents. A two-radius square identity
forces the active A transverse corner above `48/49` (`BoundaryData.Y_gt`). On the lower half,
the same budget captures the opposite error below `.06` (`BoundaryData.angle_small`).
-/

section
/-!
## Whole-interval angle reserves for crossed outer contacts

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
end
end
end

section
/-!
## Shared exact rates for the crossed common-frame clamp

The transverse-corner parameters are Y for A
and B for the opposite middle point.  Every radical uses the actual q.
The scalar angle parameters are tangents of the two physical errors;
this separates rational rate algebra from the contact-angle bounds.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.CrossedClampRates

def radius (q Y : ℝ) : ℝ := Real.sqrt (q-Y^2)
def transverse (q Y : ℝ) : ℝ := radius q Y-1
def adjacent (q Y : ℝ) : ℝ := Real.sqrt (q-(transverse q Y)^2)

def inverseRate (q Y t : ℝ) : ℝ :=
  (radius q Y/Y)*(adjacent q Y-1+
    t*(adjacent q Y-transverse q Y)/(adjacent q Y-transverse q Y*t))

def hardRate (q B τ : ℝ) : ℝ :=
  radius q B*(B+(radius q B-1)*τ)/(B+radius q B*τ)

def angularInverseRate (q Y r : ℝ) : ℝ := inverseRate q Y (Real.tan r)
def angularHardRate (q B u : ℝ) : ℝ := hardRate q B (Real.tan u)

end SquaresInCircles.Eight.CrossedClampRates
end
end
end

section
/-!
## A uniform positive zero-tangent charge beyond the original frame span

Crossed algebraic comparisons can evaluate a
zero-tangent endpoint out to 1.1 even though the original real frames
have spread at most .7.  One Taylor polynomial, expanded at .7, has a
positive quadratic reserve over the complete interval [.195,1.1].
These are scalar comparisons, not assertions of a new wider source.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedZeroReserve
open EndpointRotationPenalty

theorem fixed_coefficient_strict {h : ℝ} (hh : h∈Icc (39/200 : ℝ) (11/10)) :
    7/1000<charge*h-(183/200)*Real.sin h-(1-Real.cos h)/2 := by
  let x := h-7/10
  let K := 493657/4800000+(121469/720000)*x-(263/24000)*x^2-
    (253/24000)*x^3-x^4/1440
  have hx : x∈Icc (-(101/200 : ℝ)) (2/5) := by
    dsimp [x]
    constructor <;> linarith [hh.1,hh.2]
  have habs : |x|≤101/200 := abs_le.mpr ⟨hx.1,by linarith [hx.2]⟩
  have hp (n : ℕ) : |x^n|≤(101/200 : ℝ)^n := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) habs n
  have h2 := (abs_le.mp (hp 2)).2
  have h3 := (abs_le.mp (hp 3)).2
  have h4 := (abs_le.mp (hp 4)).2
  have hK : 1/100≤K := by dsimp [K]; nlinarith [hx.1]
  have hquad := mul_le_mul_of_nonneg_right hK (sq_nonneg x)
  have hlinear : -(1/500)*|x|≤ -(3969253/2352000000)*x := by
    have hxabs := le_abs_self x
    have ha := abs_nonneg x
    nlinarith
  have hid : charge*h-(183/200)*(h-h^3/6+h^5/120)-
      (h^2/2-h^4/24+h^6/720)/2-7/1000=
      730999/3150000000-(3969253/2352000000)*x+K*x^2 := by
    dsimp [charge,x,K]
    ring
  have habssq : |x|^2=x^2 := sq_abs x
  have hpoly : 0<charge*h-(183/200)*(h-h^3/6+h^5/120)-
      (h^2/2-h^4/24+h^6/720)/2-7/1000 := by
    rw [hid]
    nlinarith [sq_nonneg (|x|-1/10)]
  have hh0 : 0≤h := by linarith [hh.1]
  have hs := sin_upper_five hh0
  have hc := cos_lower_six hh0
  linarith

theorem sin_nonneg {h : ℝ} (hh : h∈Icc (0:ℝ) (11/10)) : 0≤Real.sin h := by
  exact Real.sin_nonneg_of_nonneg_of_le_pi hh.1 (by linarith [hh.2,Real.pi_gt_three])

theorem strict {k h : ℝ} (hk : k≤183/200)
    (hh : h∈Icc (39/200 : ℝ) (11/10)) :
    7/1000<charge*h-k*Real.sin h-(1-Real.cos h)/2 := by
  have hs := sin_nonneg (show h∈Icc (0:ℝ) (11/10) from ⟨by linarith [hh.1],hh.2⟩)
  have hm := mul_le_mul_of_nonneg_right hk hs
  linarith [fixed_coefficient_strict hh]

theorem nonneg {k h : ℝ} (hk : k≤183/200)
    (hh : h∈Icc (0:ℝ) (11/10)) :
    0≤charge*h-k*Real.sin h-(1-Real.cos h)/2 := by
  by_cases hsmall : h≤39/200
  · have hs := Real.sin_le hh.1
    have hc := Real.one_sub_sq_div_two_le_cos (x := h)
    have hsq := mul_le_mul_of_nonneg_right hsmall hh.1
    have hmul := mul_le_mul_of_nonneg_right hk (sin_nonneg hh)
    dsimp [charge]
    linarith [sin_nonneg hh]
  · exact (show (0:ℝ)≤7/1000 by norm_num).trans
      (strict hk ⟨(lt_of_not_ge hsmall).le,hh.2⟩).le

end SquaresInCircles.Eight.CrossedZeroReserve
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedClampBudget
open CrossedClampRates EndpointRotationPenalty

structure BoundaryData (q Y r u bH bT : ℝ) : Prop where
  floor : qLow≤q
  ceiling : q≤qCap
  Y_mem : Y∈Icc (23/25 : ℝ) (Real.sqrt (q-9/4))
  r_mem : r∈Icc (0 : ℝ) (1/25)
  u_mem : u∈Icc 0 frameCap
  T_nonneg : 0≤bT
  HG : 1/2+(1-transverse q Y)*Real.cos r-
    (adjacent q Y-1)*Real.sin r≤bH
  BT : bT+1/2≤(CrossedClampRates.radius q (2-Y)-1)*Real.cos u-(2-Y)*Real.sin u
  budget : bH-bT+charge*(r-u)<1-EndpointBudgetScalars.S0

def U (q B u : ℝ) : ℝ := (CrossedClampRates.radius q B-1)*Real.sin u+B*Real.cos u
def V (q B u : ℝ) : ℝ := (CrossedClampRates.radius q B-1)*Real.cos u-B*Real.sin u
def g (q B u : ℝ) : ℝ :=
  (CrossedClampRates.radius q B-1)*(Real.cos u-1)-B*Real.sin u+charge*u
def F (q Y u : ℝ) : ℝ :=
  3-CrossedClampRates.radius q Y-(CrossedClampRates.radius q (2-Y)-1)*Real.cos u+(2-Y)*Real.sin u-charge*u

theorem cap_radicals {q Y : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (23/25 : ℝ) (Real.sqrt (q-9/4))) :
    Y<1291/1000 ∧ (2-Y)∈Ioc (709/1000 : ℝ) (27/25) ∧
      0<q-Y^2 ∧ CrossedClampRates.radius q Y∈Ico (3/2 : ℝ) (219/125) ∧
      transverse q Y∈Ico (1/2 : ℝ) (94/125) ∧
      0<q-(transverse q Y)^2 ∧ adjacent q Y∈Ioo (183/100 : ℝ) (383/200) ∧
      0<q-(2-Y)^2 ∧ CrossedClampRates.radius q (2-Y)∈Ioo (33/20 : ℝ) (37/20) ∧
      (CrossedClampRates.radius q Y)^2+Y^2=q ∧
      (adjacent q Y)^2+(transverse q Y)^2=q ∧
      (CrossedClampRates.radius q (2-Y))^2+(2-Y)^2=q := by
  have hqL' : (19577/5000:ℝ)≤q := hqL
  have hq' : q≤9789/2500 := hq
  have hY0 : 0≤Y := by linarith [hY.1]
  have htop : 0≤q-9/4 := by linarith
  have htop2 := Real.sq_sqrt htop
  have hY2 : Y^2≤q-9/4 := by
    have h := pow_le_pow_left₀ hY0 hY.2 2
    rwa [htop2] at h
  have hYlow2 : (23/25:ℝ)^2≤Y^2 := pow_le_pow_left₀ (by norm_num) hY.1 2
  have hYmax : Y<1291/1000 := by
    have h : Real.sqrt (q-9/4)<1291/1000 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num; linarith)
    linarith [hY.2]
  have hB : (2-Y)∈Ioc (709/1000 : ℝ) (27/25) := ⟨by linarith,by linarith [hY.1]⟩
  have hr : 0<q-Y^2 := by linarith
  have hR2 : (CrossedClampRates.radius q Y)^2=q-Y^2 := Real.sq_sqrt hr.le
  have hR : CrossedClampRates.radius q Y∈Ico (3/2 : ℝ) (219/125) :=
    ⟨(Real.le_sqrt (by norm_num) hr.le).2 (by norm_num; linarith),
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num; linarith)⟩
  have hD : transverse q Y∈Ico (1/2 : ℝ) (94/125) := by
    dsimp [transverse]
    constructor <;> linarith [hR.1,hR.2]
  have hD0 : 0≤transverse q Y := by linarith [hD.1]
  have hD2 : (transverse q Y)^2≤(94/125)^2 := pow_le_pow_left₀ hD0 hD.2.le 2
  have hD2' : (1/2:ℝ)^2≤(transverse q Y)^2 := pow_le_pow_left₀ (by norm_num) hD.1 2
  have hx : 0<q-(transverse q Y)^2 := by norm_num at hD2; linarith
  have hX2 : (adjacent q Y)^2=q-(transverse q Y)^2 := Real.sq_sqrt hx.le
  have hX : adjacent q Y∈Ioo (183/100 : ℝ) (383/200) :=
    ⟨Real.lt_sqrt_of_sq_lt (by norm_num at hD2 ⊢; linarith),
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num at hD2' ⊢; linarith)⟩
  have hB0 : 0≤2-Y := by linarith [hB.1]
  have hB2 : (2-Y)^2≤(27/25)^2 := pow_le_pow_left₀ hB0 hB.2 2
  have hB2' : (709/1000:ℝ)^2≤(2-Y)^2 := pow_le_pow_left₀ (by norm_num) hB.1.le 2
  have hb : 0<q-(2-Y)^2 := by norm_num at hB2; linarith
  have hZ2 : (CrossedClampRates.radius q (2-Y))^2=q-(2-Y)^2 := Real.sq_sqrt hb.le
  have hZ : CrossedClampRates.radius q (2-Y)∈Ioo (33/20 : ℝ) (37/20) :=
    ⟨Real.lt_sqrt_of_sq_lt (by norm_num at hB2 ⊢; linarith),
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num at hB2' ⊢; linarith)⟩
  exact ⟨hYmax,hB,hr,hR,hD,hx,hX,hb,hZ,by linarith,by linarith,by linarith⟩

theorem radius_pair_upper {q Y : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (23/25 : ℝ) (Real.sqrt (q-9/4))) :
    CrossedClampRates.radius q Y+CrossedClampRates.radius q (2-Y)≤2*Real.sqrt (qCap-1) := by
  obtain ⟨_,_,_,hR,_,_,_,_,hZ,hR2,_,hZ2⟩ := cap_radicals hqL hq hY
  have hroot0 := Real.sqrt_nonneg (qCap-1)
  have hroot2 := Real.sq_sqrt (by norm_num [qCap] : 0≤qCap-1)
  have hsq : (CrossedClampRates.radius q Y+CrossedClampRates.radius q (2-Y))^2≤(2*Real.sqrt (qCap-1))^2 := by
    rw [mul_pow,hroot2]
    nlinarith only [hR2,hZ2,hq,sq_nonneg (Y-1),sq_nonneg (CrossedClampRates.radius q Y-CrossedClampRates.radius q (2-Y))]
  exact le_of_pow_le_pow_left₀ (by norm_num) (by linarith only [hroot0]) hsq

theorem BoundaryData.F_lt {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) : F q Y u<1-EndpointBudgetScalars.S0 := by
  obtain ⟨_,_,_,_,hD,_,hX,_,_,_,_,_⟩ := cap_radicals C.floor C.ceiling C.Y_mem
  have hreserve := CrossedAngleReserve.nonnegative
    (show 1-transverse q Y≤1/2 by linarith [hD.1])
    (show adjacent q Y-1≤183/200 by linarith [hX.2])
    (show r∈Icc (0:ℝ) (9/10) from ⟨C.r_mem.1,by linarith [C.r_mem.2]⟩)
  have hleft : 5/2-CrossedClampRates.radius q Y≤bH+charge*r := by
    have hh := C.HG
    dsimp [CrossedAngleReserve.curve,transverse] at hreserve hh
    nlinarith
  have hright := C.BT
  have hbudget := C.budget
  dsimp [F]
  nlinarith

theorem BoundaryData.g_pos {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) : 0<g q (2-Y) u := by
  have hf := C.F_lt
  have hj := radius_pair_upper C.floor C.ceiling C.Y_mem
  have hid : F q Y u+g q (2-Y) u=4-CrossedClampRates.radius q Y-CrossedClampRates.radius q (2-Y) := by
    dsimp [F,g]
    ring
  dsimp [EndpointBudgetScalars.S0] at hf
  linarith

theorem U_hasDerivAt (q B u : ℝ) : HasDerivAt (U q B) (V q B u) u := by
  have h1 : HasDerivAt (fun x => (CrossedClampRates.radius q B-1)*Real.sin x+B*Real.cos x)
      ((CrossedClampRates.radius q B-1)*Real.cos u+B*(-Real.sin u)) u :=
    ((Real.hasDerivAt_sin u).const_mul (CrossedClampRates.radius q B-1)).fun_add
      ((Real.hasDerivAt_cos u).const_mul B)
  have e : V q B u=(CrossedClampRates.radius q B-1)*Real.cos u+B*(-Real.sin u) := by simp only [V]; ring
  rw [e]
  exact h1

theorem g_hasDerivAt (q B u : ℝ) :
    HasDerivAt (g q B) (charge-U q B u) u := by
  have h1 : HasDerivAt (fun x => (CrossedClampRates.radius q B-1)*(Real.cos x-1)-B*Real.sin x+charge*x)
      ((CrossedClampRates.radius q B-1)*(-Real.sin u)-B*Real.cos u+charge*1) u :=
    ((((Real.hasDerivAt_cos u).sub_const 1).const_mul (CrossedClampRates.radius q B-1)).fun_sub
      ((Real.hasDerivAt_sin u).const_mul B)).fun_add ((hasDerivAt_id' u).const_mul charge)
  have e : charge-U q B u=(CrossedClampRates.radius q B-1)*(-Real.sin u)-B*Real.cos u+charge*1 := by
    simp only [U]; ring
  rw [e]
  exact h1

theorem V_left {q B u v : ℝ} (hP : 0≤CrossedClampRates.radius q B-1) (hB : 0≤B)
    (hu : u∈Icc 0 frameCap) (hv : v∈Icc 0 u) : V q B u≤V q B v := by
  have hv' : v∈Icc 0 frameCap := ⟨hv.1,hv.2.trans hu.2⟩
  have hc := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.cos_anti hv' hu hv.2) hP
  have hs := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.sin_mono hv' hu hv.2) hB
  dsimp [V]
  linarith

theorem U_lower_of_contact {q B u v : ℝ} (hP : 0≤CrossedClampRates.radius q B-1) (hB : 0≤B)
    (hu : u∈Icc 0 frameCap) (hV : 1/2≤V q B u) (hv : v∈Icc 0 u) :
    B+v/2≤U q B v := by
  have hc : ContinuousOn (U q B) (Icc 0 u) := by unfold U; fun_prop
  have hh := derivative_reserve hc
    (fun z hz => U_hasDerivAt q B z)
    (fun z hz => hV.trans (V_left hP hB hu (Ioo_subset_Icc_self hz)))
    (show (0:ℝ)∈Icc 0 u from ⟨le_rfl,hu.1⟩) hv hv.1
  simp only [U,Real.sin_zero,Real.cos_zero,mul_zero,mul_one,zero_add,sub_zero] at hh ⊢
  linarith

theorem BoundaryData.Y_gt {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) : 48/49<Y := by
  obtain ⟨_,hB,_,_,_,_,_,_,hZ,_,_,_⟩ := cap_radicals C.floor C.ceiling C.Y_mem
  have hB0 : 0≤2-Y := by linarith [hB.1]
  have hP : 0≤CrossedClampRates.radius q (2-Y)-1 := by linarith [hZ.1]
  have hV : 1/2≤V q (2-Y) u := by dsimp [V]; linarith [C.BT,C.T_nonneg]
  by_contra hY
  have hBcharge : charge≤2-Y := by dsimp [charge]; linarith
  have hm : AntitoneOn (g q (2-Y)) (Icc 0 u) := by
    apply antiOn_of_hasDeriv_nonpos
    · unfold g; fun_prop
    · intro v hv
      exact g_hasDerivAt q (2-Y) v
    · intro v hv
      have hh := U_lower_of_contact hP hB0 C.u_mem hV (Ioo_subset_Icc_self hv)
      linarith [hv.1]
  have hh := hm (show (0:ℝ)∈Icc 0 u from ⟨le_rfl,C.u_mem.1⟩)
    (show u∈Icc 0 u from ⟨C.u_mem.1,le_rfl⟩) C.u_mem.1
  have hp := C.g_pos
  have h0 : g q (2-Y) 0=0 := by simp [g]
  linarith

theorem g_le_at_one {q B u : ℝ} (hqL : qLow≤q) (_hq : q≤qCap)
    (hB : B∈Icc (1:ℝ) (27/25)) (hu : u∈Icc 0 frameCap) :
    g q B u≤g q 1 u := by
  have hqL' := hqL
  dsimp [qLow] at hqL'
  have hB2 := pow_le_pow_left₀ (show 0≤B by linarith [hB.1]) hB.2 2
  have hrad : 0≤q-B^2 := by nlinarith
  have hZ2 : (CrossedClampRates.radius q B)^2=q-B^2 := Real.sq_sqrt hrad
  have hZ0 : 0≤CrossedClampRates.radius q B := Real.sqrt_nonneg _
  have hZ : 1≤CrossedClampRates.radius q B := by nlinarith
  have hR2 : (CrossedClampRates.radius q 1)^2=q-1 := by
    dsimp [CrossedClampRates.radius]
    rw [one_pow,Real.sq_sqrt (by linarith : 0≤q-1)]
  have hR0 : 0≤CrossedClampRates.radius q 1 := Real.sqrt_nonneg _
  have hR1 : (27/25:ℝ)≤CrossedClampRates.radius q 1 := by nlinarith
  have hsum : B+1≤CrossedClampRates.radius q 1+CrossedClampRates.radius q B := by linarith [hB.2]
  have hdiff : CrossedClampRates.radius q 1-CrossedClampRates.radius q B≤B-1 := by
    refine le_of_not_gt fun hcon => ?_
    have h1 := mul_lt_mul_of_pos_right hcon (show 0<CrossedClampRates.radius q 1+CrossedClampRates.radius q B by linarith)
    have h2 := mul_le_mul_of_nonneg_left hsum (show 0≤B-1 by linarith [hB.1])
    nlinarith
  have ht := transport_trig hu
  have hcs : 1-Real.cos u≤Real.sin u := by
    nlinarith [Real.sin_sq_add_cos_sq u,
      mul_nonneg (show 0≤Real.cos u by linarith [ht.1]) ht.2.2.1]
  have hm1 := mul_le_mul_of_nonneg_right hdiff (sub_nonneg.mpr ht.2.1)
  have hm2 := mul_le_mul_of_nonneg_left hcs (show 0≤B-1 by linarith [hB.1])
  dsimp [g]
  linarith

theorem g_one_small_negative {q : ℝ} (hqL : qLow≤q) :
    g q 1 (3/50)<0 := by
  have hqL' := hqL
  dsimp [qLow] at hqL'
  have hR0 : 0≤CrossedClampRates.radius q 1 := Real.sqrt_nonneg _
  have hR2 : (CrossedClampRates.radius q 1)^2=q-1 := by
    dsimp [CrossedClampRates.radius]
    rw [one_pow,Real.sq_sqrt (by linarith : 0≤q-1)]
  have hR : 8537/5000<CrossedClampRates.radius q 1 := by nlinarith
  have hc := cos_upper_four (show (0:ℝ)≤3/50 by norm_num)
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤3/50 by norm_num)
  have hc0 : Real.cos (3/50)-1<0 := by norm_num at hc ⊢; linarith
  have hm := mul_lt_mul_of_neg_right
    (show 8537/5000-1<CrossedClampRates.radius q 1-1 by linarith) hc0
  have hm' := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤8537/5000-1)
  dsimp [g,charge]
  nlinarith

theorem BoundaryData.angle_small {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) (hY : Y≤1) : u<3/50 := by
  obtain ⟨_,hB,_,_,_,_,_,_,hZ,_,_,_⟩ := cap_radicals C.floor C.ceiling C.Y_mem
  have hB1 : 1≤2-Y := by linarith
  have hP : 0≤CrossedClampRates.radius q (2-Y)-1 := by linarith [hZ.1]
  have hV : 1/2≤V q (2-Y) u := by dsimp [V]; linarith [C.BT,C.T_nonneg]
  by_contra hu
  have hlu : 3/50≤u := le_of_not_gt hu
  have hm : AntitoneOn (g q (2-Y)) (Icc (3/50) u) := by
    apply antiOn_of_hasDeriv_nonpos
    · unfold g; fun_prop
    · intro v hv
      exact g_hasDerivAt q (2-Y) v
    · intro v hv
      have hvi : v∈Icc 0 u := ⟨by linarith [hv.1],hv.2.le⟩
      have hh := U_lower_of_contact hP (by linarith : 0≤2-Y) C.u_mem hV hvi
      dsimp [charge]
      linarith [hv.1]
  have hh := hm (show (3/50:ℝ)∈Icc (3/50) u from ⟨le_rfl,hlu⟩)
    (show u∈Icc (3/50:ℝ) u from ⟨hlu,le_rfl⟩) hlu
  have hcompare := g_le_at_one C.floor C.ceiling ⟨hB1,hB.2⟩
    (show (3/50:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hn := g_one_small_negative C.floor
  have hp := C.g_pos
  linarith

end SquaresInCircles.Eight.CrossedClampBudget
end
end
end
