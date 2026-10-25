module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import SquaresInCircles.Eight.Owners.OccupiedSignedConcentration
public import SquaresInCircles.Eight.Owners.PairedPrimaryGeometry

/-!
# Eight squares: the endpoint on the circle for a primary pair of opposite signs

The opposite demand is minimized on one compact contact strip. At every minimum with negative
first error, a contact curve to the right strictly decreases the demand (`right_improvement`),
also at the lower diagonal and at the join at zero tangent. So the minimum is at the first
alignment, and the pair moves to a point on the circle of the same `q` with `B - y = 1`
(`first_negative_alignment`). Local reflection gives the second alignment
(`second_negative_alignment`).
-/

section
/-!
## The two signed contact arcs for a negative first-primary error

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
end
end
end

section
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace NegativeContact
open PairedPrimary

private theorem signedPoint_eq {p r : SignedPoint} (ha : p.a=r.a) (hy : p.y=r.y) : p=r := by
  cases p
  cases r
  simp only [SignedPoint.mk.injEq]
  exact ⟨ha,hy⟩

theorem upper_diagonal_impossible {q B x : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap) (hB : B≤axisCoordinate q)
    (hx : x∈Icc (-7/10 : ℝ) 0) : contact q B x (diagonalCoordinate q)<0 := by
  obtain ⟨hc0,hc1,hA0,hA1⟩ := uniform_circle_reserves hqL hqU
  have htrig := transport_trig
    (show -x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith [hx.1,hx.2])
  have hsum := one_le_abs_cos_add_abs_sin (-x)
  rw [abs_of_pos (by linarith [htrig.1] : 0<Real.cos (-x)),
    abs_of_nonneg htrig.2.2.1,Real.cos_neg,Real.sin_neg] at hsum
  have hm := mul_le_mul_of_nonneg_left hsum (by linarith : 0≤diagonalCoordinate q)
  rw [contact,(arc_diagonal hqL).1]
  have hw := edgeWidth_ge_one x
  dsimp [axisCoordinate] at hB
  nlinarith

theorem recover_minus {q B x : ℝ} {p : SignedPoint}
    (hp : p.Sorted) (ho : p.Outer q) (hy : p.y≤0)
    (hx : x∈Ico (-7/10 : ℝ) 0)
    (hcontact : B+p.a*Real.sin x-p.y*Real.cos x=edgeWidth x) :
    minusPoint q (B-1/2) x=p := by
  obtain ⟨hc,hsc,htan⟩ := AffineCircleEntry.signed_trig
    (show |x|≤frameCap by rw [abs_of_neg hx.2]; show -x≤7/10; linarith only [hx.1])
  have hsneg : Real.sin x<0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (show 0< -x by linarith only [hx.2])
      (by linarith only [hx.1,Real.pi_gt_three])
    simpa only [Real.sin_neg,neg_pos] using h
  let X := p.a+1/2
  let Z := 1/2-p.y
  have hX : 0<X := by dsimp [X]; linarith only [hp.1]
  have hZ : 0<Z := by dsimp [Z]; linarith only [hy]
  have hcircle : X^2+Z^2=q := by
    simpa [X,Z,SignedPoint.Outer,SignedPoint.circle,abs_of_nonpos hy,sub_eq_add_neg,
      add_comm] using ho
  have hw : edgeWidth x=(1+Real.cos x-Real.sin x)/2 := by
    have h := edgeWidth_positive_formula
      (show -x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith only [hx.1,hx.2])
    simpa only [edgeWidth_neg,Real.cos_neg,Real.sin_neg,← sub_eq_add_neg] using h
  have hfirst : X*Real.sin x+Z*Real.cos x=S (B-1/2) x := by
    dsimp [X,Z,S]
    rw [hw] at hcontact
    linarith only [hcontact]
  have hrot : 0<X*Real.cos x-Z*Real.sin x := by
    linarith only [mul_pos hX hc,mul_neg_of_pos_of_neg hZ hsneg]
  have hrot2 : (X*Real.cos x-Z*Real.sin x)^2=q-S (B-1/2) x^2 := by
    have hid := circle_rotation_identity X Z x
    rw [hfirst,hcircle] at hid
    linarith only [hid]
  have hU : U q (B-1/2) x=X*Real.cos x-Z*Real.sin x := by
    rw [U,← hrot2,Real.sqrt_sq_eq_abs,abs_of_pos hrot]
  apply signedPoint_eq
  · dsimp [minusPoint,Xminus]
    rw [hU,← hfirst]
    have hid : (X*Real.cos x-Z*Real.sin x)*Real.cos x+
        (X*Real.sin x+Z*Real.cos x)*Real.sin x=X := by
      linear_combination X*Real.sin_sq_add_cos_sq x
    rw [hid]
    dsimp [X]
    ring
  · dsimp [minusPoint,Zminus]
    rw [hU,← hfirst]
    have hid : -(X*Real.cos x-Z*Real.sin x)*Real.sin x+
        (X*Real.sin x+Z*Real.cos x)*Real.cos x=Z := by
      linear_combination Z*Real.sin_sq_add_cos_sq x
    rw [hid]
    dsimp [Z]
    ring

theorem recover_plus {q B x : ℝ} {p : SignedPoint}
    (hp : p.Sorted) (ho : p.Outer q) (hy : 0≤p.y)
    (hx : x∈Ico (-7/10 : ℝ) 0)
    (hcontact : B+p.a*Real.sin x-p.y*Real.cos x=edgeWidth x) :
    plusPoint q (B-1/2) x=p := by
  obtain ⟨hc,hsc,htan⟩ := AffineCircleEntry.signed_trig
    (show |x|≤frameCap by rw [abs_of_neg hx.2]; show -x≤7/10; linarith only [hx.1])
  have hsneg : Real.sin x<0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (show 0< -x by linarith only [hx.2])
      (by linarith only [hx.1,Real.pi_gt_three])
    simpa only [Real.sin_neg,neg_pos] using h
  let X := p.a+1/2
  let Z := p.y+1/2
  have hX : 0<X := by dsimp [X]; linarith only [hp.1]
  have hZ : 0<Z := by dsimp [Z]; linarith only [hy]
  have hZX : Z≤X := by dsimp [Z,X]; simpa [abs_of_nonneg hy] using hp.2
  have hcircle : X^2+Z^2=q := by
    simpa [X,Z,SignedPoint.Outer,SignedPoint.circle,abs_of_nonneg hy] using ho
  have hw : edgeWidth x=(1+Real.cos x-Real.sin x)/2 := by
    have h := edgeWidth_positive_formula
      (show -x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith only [hx.1,hx.2])
    simpa only [edgeWidth_neg,Real.cos_neg,Real.sin_neg,← sub_eq_add_neg] using h
  have hfirst : Z*Real.cos x-X*Real.sin x=B-1/2 := by
    dsimp [X,Z]
    rw [hw] at hcontact
    linarith only [hcontact]
  have hrot : 0<X*Real.cos x+Z*Real.sin x := by
    rw [abs_of_neg hsneg] at hsc
    have hmul := mul_le_mul_of_nonpos_right hZX hsneg.le
    have hpos := mul_pos hX (by linarith only [hsc] : 0<Real.cos x+Real.sin x)
    linarith only [hmul,hpos]
  have hrot2 : (X*Real.cos x+Z*Real.sin x)^2=q-(B-1/2)^2 := by
    have hid := circle_rotation_identity X (-Z) x
    have hf : X*Real.sin x-Z*Real.cos x= -(B-1/2) := by linarith only [hfirst]
    linear_combination hid+hcircle-(X*Real.sin x-Z*Real.cos x-(B-1/2))*hf
  have hV : V q (B-1/2)=X*Real.cos x+Z*Real.sin x := by
    rw [V,← hrot2,Real.sqrt_sq_eq_abs,abs_of_pos hrot]
  apply signedPoint_eq
  · dsimp [plusPoint,Xplus]
    rw [hV,← hfirst]
    have hid : (X*Real.cos x+Z*Real.sin x)*Real.cos x-
        (Z*Real.cos x-X*Real.sin x)*Real.sin x=X := by
      linear_combination X*Real.sin_sq_add_cos_sq x
    rw [hid]
    dsimp [X]
    ring
  · dsimp [plusPoint,Zplus]
    rw [hV,← hfirst]
    have hid : (X*Real.cos x+Z*Real.sin x)*Real.sin x+
        (Z*Real.cos x-X*Real.sin x)*Real.cos x=Z := by
      linear_combination Z*Real.sin_sq_add_cos_sq x
    rw [hid]
    dsimp [Z]
    ring

theorem minus_point_circle {q P x : ℝ} (hrad : 0≤q-S P x^2)
    (hZ : 1/2≤Zminus q P x) : (minusPoint q P x).Outer q := by
  have hr := Real.sq_sqrt hrad
  have hid := circle_rotation_identity (U q P x) (-S P x) x
  dsimp [SignedPoint.Outer,SignedPoint.circle,minusPoint]
  rw [abs_of_nonpos (by linarith : 1/2-Zminus q P x≤0)]
  dsimp [Xminus,Zminus,U] at hid ⊢
  nlinarith

theorem plus_point_circle {q P x : ℝ} (hrad : 0≤q-P^2)
    (hZ : 1/2≤Zplus q P x) : (plusPoint q P x).Outer q := by
  have hr := Real.sq_sqrt hrad
  have hid := circle_rotation_identity (V q P) P x
  dsimp [SignedPoint.Outer,SignedPoint.circle,plusPoint]
  rw [abs_of_nonneg (by linarith : 0≤Zplus q P x-1/2)]
  dsimp [Xplus,Zplus,V] at hid ⊢
  nlinarith

/-- A local contact curve to the right is feasible and strictly decreases the demand. At the
active lower diagonal the derivative of `X - Z` is positive; at zero tangent the positive branch
has a positive height derivative. -/
theorem right_improvement {q B t x y : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : 0≤B ∧ B≤axisCoordinate q)
    (hx : x∈Ico (-7/10 : ℝ) 0) (ht : t∈Ioc 0 (7/10 : ℝ))
    (hv : t-x≤7/10) (hy : |y|≤diagonalCoordinate q)
    (hcontact : contact q B x y=0) :
    ∃ z y' : ℝ, x<z ∧ z<0 ∧ |y'|≤diagonalCoordinate q ∧
      contact q B z y'=0 ∧ required q t z y'<required q t x y := by
  let P := B-1/2
  let p := arc q y
  obtain ⟨hp,ho,hcore⟩ := SignedPoint.outerAt_spec hqL hy
  have hP : P∈Icc (-1/2 : ℝ) (183/200) := by
    obtain ⟨hc0,hc1,hA0,hA1⟩ := uniform_circle_reserves hqL hqU
    have hB2 : B≤Real.sqrt (q-1/4)-1/2 := hB.2
    constructor <;> dsimp only [P] <;> linarith only [hB.1,hB2,hA1]
  have hroots := scalar_bounds hqL hqU hP ⟨hx.1,hx.2.le⟩
  have hbase : B+p.a*Real.sin x-p.y*Real.cos x=edgeWidth x := by
    have h : B+(arc q y).a*Real.sin x-y*Real.cos x-edgeWidth x=0 := hcontact
    show B+(arc q y).a*Real.sin x-y*Real.cos x=edgeWidth x
    linarith only [h]
  have hupper : y<diagonalCoordinate q := by
    have hle := (abs_le.mp hy).2
    apply lt_of_le_of_ne hle
    intro heq
    rw [heq] at hcontact
    linarith only [hcontact,upper_diagonal_impossible hqL hqU hB.2 ⟨hx.1,hx.2.le⟩]
  have hyarc : p.y=y := rfl
  have hxevent : ∀ᶠ z in 𝓝[>] x, z∈Ico (-7/10 : ℝ) 0 ∧
      t-z∈Icc 0 (7/10 : ℝ) := by
    have hzneg : ∀ᶠ z in 𝓝[>] x, z<0 :=
      (eventually_lt_nhds hx.2).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hzneg] with z hxz hz
    have hxz' : x<z := hxz
    refine ⟨⟨hx.1.trans hxz.le,hz⟩,⟨?_,?_⟩⟩ <;> linarith only [ht.1,hz,hxz',hv]
  by_cases hyneg : y<0
  · have hrec : minusPoint q P x=p := recover_minus hp ho
      (by simpa [hyarc] using hyneg.le) hx hbase
    have hX : 1/2<Xminus q P x := by
      have h := congrArg SignedPoint.a hrec
      dsimp [minusPoint] at h
      linarith only [h,hp.1]
    have hZ : 1/2<Zminus q P x := by
      have h := congrArg SignedPoint.y hrec
      dsimp [minusPoint] at h
      rw [hyarc] at h
      linarith only [h,hyneg]
    have hsort : Zminus q P x≤Xminus q P x := by
      have hs : |p.y|≤p.a := hp.2
      rw [← hrec] at hs
      dsimp [minusPoint] at hs
      rw [abs_of_neg (by linarith only [hZ] : 1/2-Zminus q P x<0)] at hs
      linarith only [hs]
    obtain ⟨hdX,hdZ⟩ := minus_coordinate_derivatives hroots.2.2.2.1
    have hfactor : 0<1+Real.sin x/U q P x := by
      have hU : 0<U q P x := by linarith only [hroots.2.2.1]
      have hs := Real.neg_one_le_sin x
      have hlt : -1<Real.sin x/U q P x := by
        rw [lt_div_iff₀ hU]
        linarith only [hroots.2.2.1,hs]
      linarith only [hlt]
    have hdsort : HasDerivAt (fun z => Xminus q P z-Zminus q P z)
        ((Xminus q P x+Zminus q P x)*(1+Real.sin x/U q P x)) x := by
      convert hdX.sub hdZ using 1
      ring
    have hsortevent := eventually_right_positive hdsort (sub_nonneg.mpr hsort)
      (mul_pos (by linarith only [hX,hZ]) hfactor)
    have hZevent : ∀ᶠ z in 𝓝[>] x, 1/2<Zminus q P z :=
      (hdZ.continuousAt.eventually (lt_mem_nhds hZ)).filter_mono nhdsWithin_le_nhds
    have hdemand := (demand_derivatives (t := t) hroots.2.2.2.1).1
    have hnegative := minus_demand_negative hx ht hv
      (by linarith only [hroots.2.2.1]) (by linarith only [hX]) hZ.le hsort
    have hcostevent := eventually_right_lt hdemand (hnegative.trans (by norm_num))
    obtain ⟨z,hxz,hxzdom,hzcost,hzsort,hzZ⟩ :=
      (eventually_mem_nhdsWithin.and (hxevent.and (hcostevent.and (hsortevent.and hZevent)))).exists
    let p' := minusPoint q P z
    have hzroots := scalar_bounds hqL hqU hP ⟨hxzdom.1.1,hxzdom.1.2.le⟩
    have hps : p'.Sorted := by
      dsimp [p',minusPoint,SignedPoint.Sorted]
      rw [abs_of_neg (by linarith only [hzZ] : 1/2-Zminus q P z<0)]
      constructor <;> linarith only [hzsort,hzZ]
    have hpo : p'.Outer q := minus_point_circle hzroots.2.2.2.1.le hzZ.le
    have hpa : p'=arc q p'.y := eq_outerAt_of_outer hps hpo
    have hproj := minus_contact_and_demand (q := q) (P := P) ⟨hxzdom.1.1,hxzdom.1.2.le⟩ hxzdom.2
    have hproj0 := minus_contact_and_demand (q := q) (P := P) ⟨hx.1,hx.2.le⟩
      (show t-x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith only [ht.1,hx.2,hv])
    refine ⟨z,p'.y,hxz,hxzdom.1.2,(SignedPoint.outer_bounds hps hpo).2.1,?_,?_⟩
    · dsimp [contact]
      rw [← hpa]
      dsimp [p',P] at hproj
      linarith only [hproj.1]
    · dsimp [required]
      rw [← hpa]
      have ha : (minusPoint q P x).a=(arc q y).a := congrArg SignedPoint.a hrec
      have hy' : (minusPoint q P x).y=y := congrArg SignedPoint.y hrec
      have h0 := hproj0.2
      rw [ha,hy'] at h0
      have h1 : edgeWidth (t-z)-p'.a*Real.sin (t-z)-p'.y*Real.cos (t-z)=minusDemand q P t z :=
        hproj.2
      linarith only [h0,h1,hzcost]
  · have hypos : 0≤y := le_of_not_gt hyneg
    have hrec : plusPoint q P x=p := recover_plus hp ho
      (by simpa [hyarc] using hypos) hx hbase
    have hX : 1/2<Xplus q P x := by
      have h := congrArg SignedPoint.a hrec
      dsimp [plusPoint] at h
      linarith only [h,hp.1]
    have hZ : 1/2≤Zplus q P x := by
      have h := congrArg SignedPoint.y hrec
      dsimp [plusPoint] at h
      rw [hyarc] at h
      linarith only [h,hypos]
    have hsort : Zplus q P x<Xplus q P x := by
      have hs : |p.y|<p.a := strict_sorting_of_inner_tangent hqL
        (show |y|<diagonalCoordinate q by simpa [abs_of_nonneg hypos] using hupper)
      rw [← hrec] at hs
      dsimp [plusPoint] at hs
      rw [abs_of_nonneg (by linarith only [hZ] : 0≤Zplus q P x-1/2)] at hs
      linarith only [hs]
    obtain ⟨hdX,hdZ⟩ := plus_coordinate_derivatives q P x
    have hZevent := eventually_right_positive (hdZ.sub_const (1/2))
      (sub_nonneg.mpr hZ) (by linarith only [hX] : 0<Xplus q P x)
    have hsortevent : ∀ᶠ z in 𝓝[>] x, Zplus q P z<Xplus q P z := by
      have h : ∀ᶠ z in 𝓝[>] x, 0<(Xplus q P-Zplus q P) z :=
        ((hdX.sub hdZ).continuousAt.eventually
          (lt_mem_nhds (sub_pos.mpr hsort))).filter_mono nhdsWithin_le_nhds
      filter_upwards [h] with z hz
      have hz' : 0<Xplus q P z-Zplus q P z := hz
      linarith only [hz']
    have hdemand := (demand_derivatives (t := t) hroots.2.2.2.1).2
    have hnegative := plus_demand_negative
      (show t-x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith only [ht.1,hx.2,hv])
    have hcostevent := eventually_right_lt hdemand (hnegative.trans (by norm_num))
    obtain ⟨z,hxz,hxzdom,hzcost,hzsort,hzZ⟩ :=
      (eventually_mem_nhdsWithin.and (hxevent.and (hcostevent.and (hsortevent.and hZevent)))).exists
    let p' := plusPoint q P z
    have hps : p'.Sorted := by
      dsimp [p',plusPoint,SignedPoint.Sorted]
      rw [abs_of_pos hzZ]
      constructor <;> linarith only [hzsort,hzZ]
    have hpo : p'.Outer q := plus_point_circle hroots.2.2.2.2.le (by linarith only [hzZ])
    have hpa : p'=arc q p'.y := eq_outerAt_of_outer hps hpo
    have hproj := plus_contact_and_demand (q := q) (P := P) ⟨hxzdom.1.1,hxzdom.1.2.le⟩ hxzdom.2
    have hproj0 := plus_contact_and_demand (q := q) (P := P) ⟨hx.1,hx.2.le⟩
      (show t-x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith only [ht.1,hx.2,hv])
    refine ⟨z,p'.y,hxz,hxzdom.1.2,(SignedPoint.outer_bounds hps hpo).2.1,?_,?_⟩
    · dsimp [contact]
      rw [← hpa]
      dsimp [p',P] at hproj
      linarith only [hproj.1]
    · dsimp [required]
      rw [← hpa]
      have ha : (plusPoint q P x).a=(arc q y).a := congrArg SignedPoint.a hrec
      have hy' : (plusPoint q P x).y=y := congrArg SignedPoint.y hrec
      have h0 := hproj0.2
      rw [ha,hy'] at h0
      have h1 : edgeWidth (t-z)-p'.a*Real.sin (t-z)-p'.y*Real.cos (t-z)=plusDemand q P t z :=
        hproj.2
      linarith only [h0,h1,hzcost]

/-- A primary pair of opposite signs has an aligned endpoint on the circle of the same `q`. -/
theorem first_negative_alignment {q B D u v : ℝ} {p : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : 0≤B ∧ B≤axisCoordinate q)
    (hu : u∈Ico (-7/10 : ℝ) 0) (hv : v∈Ioc 0 (7/10 : ℝ))
    (ht : 0<u+v)
    (hp : p.Sorted) (hcore : p.AvoidsCore) (hc : p.Contained q)
    (hfirst : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (hsecond : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    ∃ p' : SignedPoint, p'.Sorted ∧ p'.Outer q ∧ p'.AvoidsCore ∧
      B-p'.y=1 ∧ edgeWidth (u+v)≤p'.a*Real.sin (u+v)+p'.y*Real.cos (u+v)+D := by
  let t := u+v
  have htmem : t∈Ioc 0 (7/10 : ℝ) := ⟨ht,by dsimp [t]; linarith [hu.2,hv.2]⟩
  obtain ⟨p₀,hp₀,ho₀,hcore₀,hfirst₀,hsecond₀⟩ :=
    AffineCircleEntry.primary_outer_entry hp hcore hc
      (show |u|≤frameCap by rw [abs_of_neg hu.2]; show -u≤7/10; linarith [hu.1])
      htmem hfirst hsecond
  have harc₀ := eq_outerAt_of_outer hp₀ ho₀
  have hy₀ := (SignedPoint.outer_bounds hp₀ ho₀).2.1
  have hcontact₀ : 0≤contact q B u p₀.y := by
    rw [harc₀] at hfirst₀
    exact sub_nonneg.mpr hfirst₀
  have hcost₀ : required q t u p₀.y≤D := by
    dsimp [required,t]
    rw [show u+v-u=v by ring,← harc₀]
    linarith
  obtain ⟨m,hm,hcost,hmin⟩ := contact_region_minimum
    (l := u) (u := 0) (a := -diagonalCoordinate q) (b := diagonalCoordinate q)
    (contact := fun z : ℝ×ℝ => contact q B z.1 z.2)
    (cost := fun z : ℝ×ℝ => required q t z.1 z.2)
    (by dsimp [contact,arc,SignedPoint.outerAt,edgeWidth,pairWidth]; fun_prop)
    (by dsimp [required,arc,SignedPoint.outerAt,edgeWidth,pairWidth]; fun_prop)
    (p₀ := (u,p₀.y)) ⟨⟨le_rfl,hu.2.le⟩,abs_le.mp hy₀,hcontact₀⟩
  have hmv : t-m.1∈Icc 0 (7/10 : ℝ) := by
    constructor <;> dsimp [t] <;> linarith [hm.1.1,hm.1.2,hv.2,ht]
  have hmx : m.1∈Icc (-7/10 : ℝ) 0 := ⟨hu.1.trans hm.1.1,hm.1.2⟩
  have hact := upper_or_contact_at_minimum (x := m.1) (y := m.2)
    (contact := fun z : ℝ×ℝ => contact q B z.1 z.2)
    (cost := fun z : ℝ×ℝ => required q t z.1 z.2) hm hmin
    (by dsimp [contact,arc,SignedPoint.outerAt,edgeWidth,pairWidth]; fun_prop)
    (required_strictAnti hqL hmv)
  have hzero : contact q B m.1 m.2=0 := by
    rcases hact with hdiag | hzero
    · rw [hdiag] at hm
      exact False.elim (not_lt_of_ge hm.2.2
        (upper_diagonal_impossible hqL hqU hB.2 hmx))
    · exact hzero
  have hxzero : m.1=0 := by
    by_contra hn
    have hxneg : m.1<0 := lt_of_le_of_ne hm.1.2 hn
    obtain ⟨x,y,hxm,hx0,hy,hcontact,hbetter⟩ := right_improvement hqL hqU hB
      ⟨hmx.1,hxneg⟩ htmem hmv.2 (abs_le.mpr hm.2.1) hzero
    have hxmin : x∈Icc u 0 := ⟨hm.1.1.trans hxm.le,hx0.le⟩
    have hbad := hmin (x,y) hxmin (abs_le.mp hy) hcontact.ge
    exact not_lt_of_ge hbad hbetter
  let p' := arc q m.2
  obtain ⟨hps,hpo,hpc⟩ := SignedPoint.outerAt_spec hqL (abs_le.mpr hm.2.1)
  refine ⟨p',hps,hpo,hpc,?_,?_⟩
  · rw [hxzero] at hzero
    have h : B+(arc q m.2).a*Real.sin 0-m.2*Real.cos 0-edgeWidth 0=0 := hzero
    simp only [Real.sin_zero,Real.cos_zero,edgeWidth_zero] at h
    show B-m.2=1
    linarith
  · have hb := hcost.trans hcost₀
    rw [hxzero] at hb
    have hb' : edgeWidth (u+v-0)-(arc q m.2).a*Real.sin (u+v-0)-
        m.2*Real.cos (u+v-0)≤D := hb
    simp only [sub_zero] at hb'
    show edgeWidth (u+v)≤(arc q m.2).a*Real.sin (u+v)+m.2*Real.cos (u+v)+D
    linarith

/-- The mirror statement, by local reflection, which exchanges the primary inequalities and
negates only the signed tangent of the point; E and the other states are untouched. -/
theorem second_negative_alignment {q B D u v : ℝ} {p : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hD : 0≤D ∧ D≤axisCoordinate q)
    (hu : u∈Ioc 0 (7/10 : ℝ)) (hv : v∈Ico (-7/10 : ℝ) 0)
    (ht : 0<u+v)
    (hp : p.Sorted) (hcore : p.AvoidsCore) (hc : p.Contained q)
    (hfirst : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (hsecond : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    ∃ p' : SignedPoint, p'.Sorted ∧ p'.Outer q ∧ p'.AvoidsCore ∧
      p'.y+D=1 ∧ edgeWidth (u+v)≤B+p'.a*Real.sin (u+v)-p'.y*Real.cos (u+v) := by
  obtain ⟨p',hps,hpo,hpc,hfirst',hsecond'⟩ := first_negative_alignment (D := B) hqL hqU hD
    hv hu (by linarith)
    ((SignedPoint.reflect_sorted p).mpr hp)
    ((SignedPoint.reflect_avoidsCore p).mpr hcore)
    ((SignedPoint.reflect_contained p q).mpr hc)
    (by dsimp [SignedPoint.reflect]; linarith [hsecond])
    (by dsimp [SignedPoint.reflect]; linarith [hfirst])
  refine ⟨p'.reflect,(SignedPoint.reflect_sorted p').mpr hps,
    (SignedPoint.reflect_outer p' q).mpr hpo,(SignedPoint.reflect_avoidsCore p').mpr hpc,?_,?_⟩
  · dsimp [SignedPoint.reflect]
    linarith
  · rw [add_comm v u] at hsecond'
    dsimp [SignedPoint.reflect]
    linarith

end NegativeContact
end SquaresInCircles.Eight
end
end
end
