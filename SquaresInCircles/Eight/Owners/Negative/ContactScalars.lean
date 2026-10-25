module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import SquaresInCircles.Eight.Owners.AffineCircleEntry

/-!
# Eight squares: the two signed contact arcs for a negative first-primary error

The first endpoint scalar need only be between zero
and the actual outer-axis coordinate. This includes the reflected TD-negative
case, where the first scalar is a transverse coordinate rather than a primary.
No original sign of the moving intermediate is imposed.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace NegativeContact

/-- The negative-tangent branch uses a varying circle ordinate. -/
def S (P x : ℝ) : ℝ := Real.cos x-P
def U (q P x : ℝ) : ℝ := Real.sqrt (q-S P x^2)
def Xminus (q P x : ℝ) : ℝ := U q P x*Real.cos x+S P x*Real.sin x
def Zminus (q P x : ℝ) : ℝ := -U q P x*Real.sin x+S P x*Real.cos x

def minusPoint (q P x : ℝ) : SignedPoint :=
  ⟨Xminus q P x-1/2,1/2-Zminus q P x⟩

/-- The positive-tangent branch has a constant rotated circle ordinate. -/
def V (q P : ℝ) : ℝ := Real.sqrt (q-P^2)
def Xplus (q P x : ℝ) : ℝ := V q P*Real.cos x-P*Real.sin x
def Zplus (q P x : ℝ) : ℝ := V q P*Real.sin x+P*Real.cos x

def plusPoint (q P x : ℝ) : SignedPoint :=
  ⟨Xplus q P x-1/2,Zplus q P x-1/2⟩

def minusDemand (q P t x : ℝ) : ℝ :=
  1/2+Real.sin (t-x)-U q P x*Real.sin t+S P x*Real.cos t

def plusDemand (q P t x : ℝ) : ℝ :=
  1/2+Real.cos (t-x)+Real.sin (t-x)-V q P*Real.sin t-P*Real.cos t

def minusDemandDeriv (q P t x : ℝ) : ℝ :=
  -Real.cos (t-x)-S P x*Real.sin x/U q P x*Real.sin t-
    Real.sin x*Real.cos t

def plusDemandDeriv (t x : ℝ) : ℝ := Real.sin (t-x)-Real.cos (t-x)

/-- Sign of a derivative gives an actual one-sided strict improvement. -/
theorem eventually_right_lt {f : ℝ → ℝ} {x d : ℝ}
    (hd : HasDerivAt f d x) (hneg : d<0) :
    ∀ᶠ y in 𝓝[>] x, f y<f x := by
  have hs := hd.hasDerivWithinAt.limsup_slope_le'
    (s := Ioi x) (by simp) hneg
  filter_upwards [hs,self_mem_nhdsWithin] with y hy hxy
  have hden : 0<y-x := sub_pos.mpr hxy
  change (y-x)⁻¹*(f y-f x)<0 at hy
  have hdiff : f y-f x<0 := neg_of_mul_neg_right hy (inv_pos.mpr hden).le
  linarith

theorem eventually_right_gt {f : ℝ → ℝ} {x d : ℝ}
    (hd : HasDerivAt f d x) (hpos : 0<d) :
    ∀ᶠ y in 𝓝[>] x, f x<f y := by
  have h := eventually_right_lt hd.neg (by linarith : -d<0)
  filter_upwards [h] with y hy
  change -f y < -f x at hy
  linarith

/-- Weak inequalities at an active geometric boundary become strict in the
rightward direction when their actual derivative is positive. -/
theorem eventually_right_positive {f : ℝ → ℝ} {x d : ℝ}
    (hd : HasDerivAt f d x) (hvalue : 0≤f x) (hpos : 0<d) :
    ∀ᶠ y in 𝓝[>] x, 0<f y := by
  filter_upwards [eventually_right_gt hd hpos] with y hy
  exact hvalue.trans_lt hy

theorem scalar_bounds {q P x : ℝ} (hqL : qLow≤q) (_hqU : q≤qCap)
    (hP : P∈Icc (-1/2 : ℝ) (183/200)) (hx : x∈Icc (-7/10 : ℝ) 0) :
    -1<S P x ∧ S P x≤3/2 ∧ 129/100<U q P x ∧
      0<q-S P x^2 ∧ 0<q-P^2 := by
  have hxabs : |x|≤frameCap := by
    rw [abs_of_nonpos hx.2]
    show -x≤7/10
    linarith [hx.1]
  obtain ⟨hc,hsc,htan⟩ := AffineCircleEntry.signed_trig hxabs
  have hcle := Real.cos_le_one x
  have hSlo : -1<S P x := by dsimp [S]; linarith [hP.2]
  have hShi : S P x≤3/2 := by dsimp [S]; linarith [hP.1]
  have hSq : S P x^2≤9/4 := by nlinarith [sq_nonneg (S P x+1)]
  have hPq : P^2≤1 := by nlinarith [hP.1,hP.2]
  have hrad : 0<q-S P x^2 := by dsimp [qLow] at hqL; linarith
  have hr := Real.sq_sqrt hrad.le
  have hn := Real.sqrt_nonneg (q-S P x^2)
  refine ⟨hSlo,hShi,?_,hrad,?_⟩
  · dsimp [U]
    dsimp [qLow] at hqL
    nlinarith
  · dsimp [qLow] at hqL
    linarith

theorem minus_root_deriv {q P x : ℝ} (hrad : 0<q-S P x^2) :
    HasDerivAt (U q P) (S P x*Real.sin x/U q P x) x := by
  have hS : HasDerivAt (S P) (-Real.sin x) x := (Real.hasDerivAt_cos x).sub_const P
  have hd := ((hS.pow 2).const_sub q).sqrt (ne_of_gt hrad)
  have hU0 : Real.sqrt (q-S P x^2)≠0 := ne_of_gt (Real.sqrt_pos.mpr hrad)
  convert hd using 1
  · rfl
  · dsimp [U]
    field_simp

theorem minus_coordinate_derivatives {q P x : ℝ}
    (hrad : 0<q-S P x^2) :
    HasDerivAt (Xminus q P)
        (Zminus q P x*(1+Real.sin x/U q P x)) x ∧
      HasDerivAt (Zminus q P)
        (-Xminus q P x*(1+Real.sin x/U q P x)) x := by
  have hdU := minus_root_deriv hrad
  have hS : HasDerivAt (S P) (-Real.sin x) x := (Real.hasDerivAt_cos x).sub_const P
  have hU0 : U q P x≠0 := ne_of_gt (Real.sqrt_pos.mpr hrad)
  have hU2 : U q P x^2=q-S P x^2 := Real.sq_sqrt hrad.le
  constructor
  · convert (hdU.mul (Real.hasDerivAt_cos x)).add (hS.mul (Real.hasDerivAt_sin x)) using 1
    · rfl
    · dsimp [Xminus,Zminus]
      field_simp [hU0]
      nlinarith [hU2]
  · convert ((hdU.neg).mul (Real.hasDerivAt_sin x)).add
      (hS.mul (Real.hasDerivAt_cos x)) using 1
    · rfl
    · dsimp [Xminus,Zminus]
      field_simp [hU0]
      nlinarith [hU2]

theorem plus_coordinate_derivatives (q P x : ℝ) :
    HasDerivAt (Xplus q P) (-Zplus q P x) x ∧
      HasDerivAt (Zplus q P) (Xplus q P x) x := by
  constructor
  · convert ((Real.hasDerivAt_cos x).const_mul (V q P)).sub
      ((Real.hasDerivAt_sin x).const_mul P) using 1
    · rfl
    · dsimp [Zplus]
      ring
  · convert ((Real.hasDerivAt_sin x).const_mul (V q P)).add
      ((Real.hasDerivAt_cos x).const_mul P) using 1
    · rfl
    · dsimp [Xplus]
      ring

theorem demand_derivatives {q P t x : ℝ} (hrad : 0<q-S P x^2) :
    HasDerivAt (minusDemand q P t) (minusDemandDeriv q P t x) x ∧
      HasDerivAt (plusDemand q P t) (plusDemandDeriv t x) x := by
  have hsub : HasDerivAt (fun z : ℝ => t-z) (-1) x :=
    (hasDerivAt_id' x).const_sub t
  have hS : HasDerivAt (S P) (-Real.sin x) x := (Real.hasDerivAt_cos x).sub_const P
  constructor
  · convert (((hsub.sin).const_add (1/2)).sub
      ((minus_root_deriv hrad).mul_const (Real.sin t))).add
      (hS.mul_const (Real.cos t)) using 1
    · rfl
    · dsimp [minusDemandDeriv]
      ring
  · convert ((((hsub.cos).const_add (1/2)).add hsub.sin).sub_const
      (V q P*Real.sin t)).sub_const (P*Real.cos t) using 1
    · rfl
    · dsimp [plusDemandDeriv]
      ring

theorem minus_rotation (q P x : ℝ) :
    Xminus q P x*Real.sin x+Zminus q P x*Real.cos x=S P x ∧
      Xminus q P x*Real.cos x-Zminus q P x*Real.sin x=U q P x := by
  constructor
  · dsimp [Xminus,Zminus]
    linear_combination (S P x)*Real.sin_sq_add_cos_sq x
  · dsimp [Xminus,Zminus]
    linear_combination (U q P x)*Real.sin_sq_add_cos_sq x

/-- The derivative is negative at every actual negative-error contact. -/
theorem minus_demand_negative {q P t x : ℝ}
    (hx : x∈Ico (-7/10 : ℝ) 0) (ht : t∈Ioc 0 (7/10 : ℝ))
    (hv : t-x≤7/10) (hU : 0<U q P x)
    (hX : 0<Xminus q P x) (hZ : 1/2≤Zminus q P x)
    (hsort : Zminus q P x≤Xminus q P x) :
    minusDemandDeriv q P t x< -1/10 := by
  have hs : -x∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  obtain ⟨hcs,hcs1,hss0,hss,hscs⟩ := transport_trig hs
  obtain ⟨hcv,hcv1,hsv0,hsv,hscv⟩ := transport_trig
    (show t-x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith [ht.1,hx.2])
  have hrat : S P x/U q P x<1 := by
    apply (div_lt_one hU).mpr
    obtain ⟨hc,hsc,htan⟩ := AffineCircleEntry.signed_trig
      (show |x|≤frameCap by rw [abs_of_neg hx.2]; show -x≤7/10; linarith [hx.1])
    obtain ⟨hrot₁,hrot₂⟩ := minus_rotation q P x
    have hspos := Real.sin_pos_of_pos_of_lt_pi (show 0< -x by linarith [hx.2])
      (by linarith [hx.1,Real.pi_gt_three])
    rw [Real.sin_neg] at hspos
    have h₁ := mul_nonneg (sub_nonneg.mpr hsort) hc.le
    have h₂ := mul_pos hspos (show 0<Xminus q P x+Zminus q P x by linarith)
    nlinarith
  have hbracket : 0<Real.cos (-x)-(S P x/U q P x)*Real.sin (-x) := by
    have hh := mul_lt_mul_of_pos_right hrat
      (Real.sin_pos_of_pos_of_lt_pi (show 0< -x by linarith [hx.2])
        (by linarith [hx.1,Real.pi_gt_three]))
    linarith
  have htpos := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,Real.pi_gt_three])
  have hid : minusDemandDeriv q P t x=
      -(Real.cos (t-x)-Real.sin (t-x))-
        Real.sin t*(Real.cos (-x)-(S P x/U q P x)*Real.sin (-x)) := by
    dsimp [minusDemandDeriv]
    simp only [Real.sin_neg,Real.cos_neg,Real.cos_sub,Real.sin_sub]
    ring
  rw [hid]
  have hp := mul_pos htpos hbracket
  linarith

theorem plus_demand_negative {t x : ℝ} (hv : t-x∈Icc 0 (7/10 : ℝ)) :
    plusDemandDeriv t x< -1/10 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hv
  dsimp [plusDemandDeriv]
  linarith

/-- Exact demands; the signs here are actual state signs, not sign guesses. -/
theorem minus_contact_and_demand {q P t x : ℝ}
    (hx : x∈Icc (-7/10 : ℝ) 0) (hv : t-x∈Icc 0 (7/10 : ℝ)) :
    P+1/2+(minusPoint q P x).a*Real.sin x-
      (minusPoint q P x).y*Real.cos x=edgeWidth x ∧
    edgeWidth (t-x)-(minusPoint q P x).a*Real.sin (t-x)-
      (minusPoint q P x).y*Real.cos (t-x)=minusDemand q P t x := by
  have hw : edgeWidth x=(1+Real.cos x-Real.sin x)/2 := by
    have h := edgeWidth_positive_formula
      (show -x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith [hx.1,hx.2])
    simpa only [edgeWidth_neg,Real.cos_neg,Real.sin_neg,← sub_eq_add_neg] using h
  rw [hw,edgeWidth_positive_formula hv]
  constructor
  · dsimp [minusPoint,Xminus,Zminus,S]
    linear_combination (Real.cos x-P)*Real.sin_sq_add_cos_sq x
  · dsimp [minusPoint,Xminus,Zminus,minusDemand,S]
    simp only [Real.sin_sub,Real.cos_sub]
    linear_combination (-(U q P x)*Real.sin t+(Real.cos x-P)*Real.cos t)*
      Real.sin_sq_add_cos_sq x

theorem plus_contact_and_demand {q P t x : ℝ}
    (hx : x∈Icc (-7/10 : ℝ) 0) (hv : t-x∈Icc 0 (7/10 : ℝ)) :
    P+1/2+(plusPoint q P x).a*Real.sin x-
      (plusPoint q P x).y*Real.cos x=edgeWidth x ∧
    edgeWidth (t-x)-(plusPoint q P x).a*Real.sin (t-x)-
      (plusPoint q P x).y*Real.cos (t-x)=plusDemand q P t x := by
  have hw : edgeWidth x=(1+Real.cos x-Real.sin x)/2 := by
    have h := edgeWidth_positive_formula
      (show -x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith [hx.1,hx.2])
    simpa only [edgeWidth_neg,Real.cos_neg,Real.sin_neg,← sub_eq_add_neg] using h
  rw [hw,edgeWidth_positive_formula hv]
  constructor
  · dsimp [plusPoint,Xplus,Zplus]
    linear_combination (-P)*Real.sin_sq_add_cos_sq x
  · dsimp [plusPoint,Xplus,Zplus,plusDemand]
    simp only [Real.sin_sub,Real.cos_sub]
    linear_combination (-(V q P)*Real.sin t-P*Real.cos t)*Real.sin_sq_add_cos_sq x

end NegativeContact
end SquaresInCircles.Eight