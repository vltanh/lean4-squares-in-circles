import SquaresInCircles.Common.Analysis
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv

/-!
# One-variable tools

The estimates of the six-square proof come down to functions of one angle at a
time. A function with a nonpositive second derivative on an interval is concave
there, and a concave function exceeds inside the interval every bound that it
exceeds at both ends; concavity survives an affine change of the argument, and a
function on a rectangle that is concave in each variable is positive once it is
positive at the four corners. A quartic positive at both ends of an interval is
positive where a quadratic `Q` is nonpositive, since it exceeds its chord by
`-(x - l)(u - x) Q x`.

The first harmonic `A cos x + B sin x` is minus its own second derivative, so it
is concave where it is nonnegative, in particular on `[0, π/2]` when
`A, B ≥ 0`. Subtracting `R √(p + q sin x)` keeps it concave where `q² ≤ p²` and
the radical is at most four times the harmonic, since the radical has the second
derivative `-r/4 + (p² - q²)/(4r³)`. The length `L` of a constant vector of
length `a` plus a turning vector of length `b` has `L² = P + Q cos x + T sin x`
with `P = a² + b²` and `Q² + T² = 4a²b²`; the second derivative of `-R L` is
`R (L⁴ - (a² - b²)²)/(4L³)`, at most `R ab/(a + b)`, because
`4abL³ - (a + b)(L⁴ - (a² - b²)²)` is `a + b - L` times a polynomial with
nonnegative terms, and nonpositive when `a ≤ b` and `L² ≤ b² - a²`.

For `|t| ≤ r` an angle has `cos t ≥ 1 - r²/2` and `|sin t| ≤ r`; the Taylor
polynomials of degrees four to seven bracket `cos` on the whole line and `sin`
for `x ≥ 0`, and on the whole line once chosen by the sign of `x`, which gives
rational brackets at the points where the estimates are evaluated;
a square root lies below its tangents; and the half-angle ratio
`sin t/(1 + cos t) = tan (t/2)` lies between `t/2` and `11t/20` on `[0, 4/5]`.
-/

noncomputable section
open Set

namespace SquaresInCircles.Six

/-! ### Concavity -/

/-- A function whose second derivative is nonpositive on `[l, u]` is concave
there. -/
lemma concave_of_deriv2 {f f' f'' : ℝ → ℝ} {l u : ℝ}
    (hf : ∀ x ∈ Icc l u, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc l u, HasDerivAt f' (f'' x) x)
    (h : ∀ x ∈ Icc l u, f'' x ≤ 0) : ConcaveOn ℝ (Icc l u) f :=
  concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l u)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => (hf' x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => h x (interior_subset hx))

/-- A concave function exceeds inside `[l, u]` every bound that it exceeds at
both ends. -/
lemma concave_gt_of_endpoints {f : ℝ → ℝ} {l u x c : ℝ}
    (hf : ConcaveOn ℝ (Icc l u) f) (hx : l ≤ x ∧ x ≤ u) (hl : c < f l) (hu : c < f u) :
    c < f x :=
  (lt_min hl hu).trans_le
    (hf.min_le_of_mem_Icc ⟨le_rfl,hx.1.trans hx.2⟩ ⟨hx.1.trans hx.2,le_rfl⟩ hx)

/-- A function concave on `[L, U]`, composed with an affine map from `[l, u]`
into `[L, U]`, is concave on `[l, u]`. -/
lemma concave_affine_argument {f : ℝ → ℝ} {L U l u a b : ℝ}
    (hf : ConcaveOn ℝ (Icc L U) f) (hmap : ∀ x ∈ Icc l u, a*x+b ∈ Icc L U) :
    ConcaveOn ℝ (Icc l u) (fun x => f (a*x+b)) := by
  refine ⟨convex_Icc l u,?_⟩
  intro x hx y hy r s hr hs hrs
  have h := hf.2 (hmap x hx) (hmap y hy) hr hs hrs
  have hid : a*(r*x+s*y)+b=r*(a*x+b)+s*(a*y+b) := by
    linear_combination -b*hrs
  simpa only [smul_eq_mul,hid] using h

/-- An affine function is concave. -/
lemma affine_concave (a b l u : ℝ) : ConcaveOn ℝ (Icc l u) (fun x : ℝ => a*x+b) := by
  refine ⟨convex_Icc l u,fun x _ y _ p q _ _ hpq => ?_⟩
  simp only [smul_eq_mul]
  have he : p*(a*x+b)+q*(a*y+b)=a*(p*x+q*y)+b*(p+q) := by ring
  rw [he,hpq,mul_one]

/-- A function on `[l, u] × [L, U]`, concave in the first variable and concave
in the second on the edges `x = l` and `x = u`, is positive if it is positive
at the four corners. -/
lemma positive_on_separately_concave_rectangle {f : ℝ → ℝ → ℝ} {l u L U x y : ℝ}
    (hx : l ≤ x ∧ x ≤ u) (hy : L ≤ y ∧ y ≤ U)
    (hfirst : ∀ t ∈ Icc L U, ConcaveOn ℝ (Icc l u) (fun z => f z t))
    (hleft : ConcaveOn ℝ (Icc L U) (f l))
    (hright : ConcaveOn ℝ (Icc L U) (f u))
    (hll : 0 < f l L) (hlu : 0 < f l U) (hul : 0 < f u L) (huu : 0 < f u U) : 0 < f x y :=
  concave_gt_of_endpoints (f := fun z => f z y) (hfirst y hy) hx
    (concave_gt_of_endpoints (f := f l) hleft hy hll hlu)
    (concave_gt_of_endpoints (f := f u) hright hy hul huu)

/-- The quartic with the coefficients `a0, …, a4`. -/
def quartic (a0 a1 a2 a3 a4 x : ℝ) : ℝ :=
  a0+a1*x+a2*x^2+a3*x^3+a4*x^4

/-- If the quadratic `Q x` of `hcurv` is nonpositive, a quartic positive at `l`
and `u` is positive at `x ∈ [l, u]`, since it exceeds its chord by
`-(x - l)(u - x) Q x`. -/
theorem quartic_positive_of_chord {a0 a1 a2 a3 a4 l u x : ℝ}
    (hlu : l < u) (hx : l ≤ x ∧ x ≤ u)
    (hl : 0 < quartic a0 a1 a2 a3 a4 l)
    (hu : 0 < quartic a0 a1 a2 a3 a4 u)
    (hcurv : a2+a3*(x+l+u)+a4*(x^2+(l+u)*x+l^2+l*u+u^2) ≤ 0) :
    0 < quartic a0 a1 a2 a3 a4 x := by
  have hleft : 0 ≤ u-x := sub_nonneg.mpr hx.2
  have hright : 0 ≤ x-l := sub_nonneg.mpr hx.1
  have hcorr := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hlu.le) hright) hleft) hcurv
  have hid : (u-l)*quartic a0 a1 a2 a3 a4 x =
      (u-x)*quartic a0 a1 a2 a3 a4 l+(x-l)*quartic a0 a1 a2 a3 a4 u-
      (u-l)*(x-l)*(u-x)*(a2+a3*(x+l+u)+a4*(x^2+(l+u)*x+l^2+l*u+u^2)) := by
    dsimp [quartic]
    ring
  have hchord : 0 < (u-x)*quartic a0 a1 a2 a3 a4 l+(x-l)*quartic a0 a1 a2 a3 a4 u := by
    rcases lt_or_eq_of_le hx.2 with hxu | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hxu) hl)
        (mul_nonneg hright hu.le)
    · simpa using mul_pos (sub_pos.mpr hlu) hu
  by_contra! hbad
  have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlu.le) hbad
  nlinarith only [hid,hcorr,hchord,hmul]

/-! ### First harmonics -/

/-- The first harmonic `A cos x + B sin x`. -/
def harmonic (A B x : ℝ) : ℝ := A*Real.cos x+B*Real.sin x

/-- The derivative of `harmonic A B` is `harmonic B (-A)`. -/
lemma harmonic_hasDerivAt (A B x : ℝ) :
    HasDerivAt (harmonic A B) (harmonic B (-A) x) x :=
  (((Real.hasDerivAt_cos x).const_mul A).add ((Real.hasDerivAt_sin x).const_mul B)).congr_deriv
    (by simp only [harmonic]; ring)

/-- `cos` and `sin` are nonnegative on `[0, π/2]`. -/
lemma cos_sin_nonneg {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
    0 ≤ Real.cos x ∧ 0 ≤ Real.sin x :=
  ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hx.2⟩,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_pos])⟩

/-- A first harmonic with nonnegative coefficients is nonnegative on
`[0, π/2]`. -/
lemma harmonic_nonneg {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
    0 ≤ A*Real.cos x+B*Real.sin x :=
  add_nonneg (mul_nonneg hA (cos_sin_nonneg hx).1) (mul_nonneg hB (cos_sin_nonneg hx).2)

/-- A first harmonic is concave where it is nonnegative: its second derivative
is its negative. -/
lemma harmonic_concave {A B l u : ℝ} (h : ∀ x ∈ Icc l u, 0 ≤ A*Real.cos x+B*Real.sin x) :
    ConcaveOn ℝ (Icc l u) (harmonic A B) :=
  concave_of_deriv2 (fun x _ => harmonic_hasDerivAt A B x)
    (fun x _ => harmonic_hasDerivAt B (-A) x)
    (fun x hx => by have := h x hx; simp only [harmonic]; linarith)

/-- `K + A cos x + B sin x`, with `A, B ≥ 0`, is positive on `[l, u] ⊆ [0, π/2]`
as soon as it is positive at both ends. -/
lemma harmonic_pos_of_endpoints {K A B l u x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hl : 0 ≤ l) (hu : u ≤ Real.pi/2) (hx : l ≤ x ∧ x ≤ u)
    (hleft : 0 < K+A*Real.cos l+B*Real.sin l) (hright : 0 < K+A*Real.cos u+B*Real.sin u) :
    0 < K+A*Real.cos x+B*Real.sin x := by
  have hc := harmonic_concave (A := A) (B := B) (l := l) (u := u)
    fun y hy => harmonic_nonneg hA hB ⟨hl.trans hy.1,hy.2.trans hu⟩
  have h := concave_gt_of_endpoints hc hx (c := -K)
    (by simp only [harmonic]; linarith) (by simp only [harmonic]; linarith)
  simp only [harmonic] at h
  linarith

/-! ### Radicals and rotating lengths -/

/-- `A cos x + B sin x - R √(p + q sin x)`. -/
def radicalTrig (A B p q R x : ℝ) : ℝ :=
  A*Real.cos x+B*Real.sin x-R*Real.sqrt (p+q*Real.sin x)

lemma radical_second_identity {p q s c r : ℝ} (hr : r ≠ 0)
    (hsq : r^2=p+q*s) (hu : c^2+s^2=1) :
    -q*s/(2*r)-q^2*c^2/(4*r^3) = -r/4+(p^2-q^2)/(4*r^3) := by
  calc
    _ = (-2*q*s*r^2-q^2*c^2)/(4*r^3) := by field_simp [hr]; ring
    _ = (-r^4+p^2-q^2)/(4*r^3) := by
      congr 1
      linear_combination (r^2+p-q*s)*hsq-q^2*hu
    _ = _ := by field_simp [hr]; ring

lemma radical_first_derivative {p q x : ℝ} (hx : 0 < p+q*Real.sin x) :
    HasDerivAt (fun y => Real.sqrt (p+q*Real.sin y))
      (q*Real.cos x/(2*Real.sqrt (p+q*Real.sin x))) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul q).const_add p).sqrt (ne_of_gt hx)
  simpa only [mul_comm] using h

lemma radical_second_derivative {p q x : ℝ} (hx : 0 < p+q*Real.sin x) :
    HasDerivAt (fun y => q*Real.cos y/(2*Real.sqrt (p+q*Real.sin y)))
      (-Real.sqrt (p+q*Real.sin x)/4+
        (p^2-q^2)/(4*(Real.sqrt (p+q*Real.sin x))^3)) x := by
  let r := Real.sqrt (p+q*Real.sin x)
  have hr : 0 < r := Real.sqrt_pos.mpr hx
  have hroot := radical_first_derivative hx
  have hd := ((Real.hasDerivAt_cos x).const_mul q).div (hroot.const_mul 2)
    (mul_ne_zero (by norm_num) (ne_of_gt hr))
  have hformula : HasDerivAt (fun y => q*Real.cos y/(2*Real.sqrt (p+q*Real.sin y)))
      (-q*Real.sin x/(2*r)-q^2*(Real.cos x)^2/(4*r^3)) x := by
    convert hd using 1
    field_simp [ne_of_gt hr]
    ring
  have hsq : r^2=p+q*Real.sin x := Real.sq_sqrt hx.le
  rw [radical_second_identity (ne_of_gt hr) hsq
    (by nlinarith [Real.sin_sq_add_cos_sq x])] at hformula
  exact hformula

/-- `A cos x + B sin x - R √(p + q sin x)` is concave on `[l, u]` if `R ≥ 0`,
`q² ≤ p²`, and on `[l, u]` the radicand is positive and
`R √(p + q sin x) ≤ 4 (A cos x + B sin x)`. -/
theorem radicalTrig_concave {A B p q R l u : ℝ}
    (hR : 0 ≤ R) (hpq : q^2 ≤ p^2)
    (hroot : ∀ x ∈ Icc l u, 0 < p+q*Real.sin x)
    (hbound : ∀ x ∈ Icc l u,
      R*Real.sqrt (p+q*Real.sin x) ≤ 4*(A*Real.cos x+B*Real.sin x)) :
    ConcaveOn ℝ (Icc l u) (radicalTrig A B p q R) := by
  let d : ℝ → ℝ := fun x => -A*Real.sin x+B*Real.cos x-
    R*(q*Real.cos x/(2*Real.sqrt (p+q*Real.sin x)))
  let dd : ℝ → ℝ := fun x => -A*Real.cos x-B*Real.sin x-
    R*(-Real.sqrt (p+q*Real.sin x)/4+(p^2-q^2)/(4*(Real.sqrt (p+q*Real.sin x))^3))
  have hd (x : ℝ) (hx : x ∈ Icc l u) : HasDerivAt (radicalTrig A B p q R) (d x) x := by
    convert (((Real.hasDerivAt_cos x).const_mul A).add
      ((Real.hasDerivAt_sin x).const_mul B)).sub
      ((radical_first_derivative (hroot x hx)).const_mul R) using 1
    · funext y
      simp only [radicalTrig,Pi.add_apply,Pi.sub_apply]
    · simp only [d]
      ring
  have hdd (x : ℝ) (hx : x ∈ Icc l u) : HasDerivAt d (dd x) x := by
    convert (((Real.hasDerivAt_sin x).const_mul (-A)).add
      ((Real.hasDerivAt_cos x).const_mul B)).sub
      ((radical_second_derivative (hroot x hx)).const_mul R) using 1
    simp only [dd]
    ring
  refine concave_of_deriv2 hd hdd fun x hx => ?_
  have hr : 0 < Real.sqrt (p+q*Real.sin x) := Real.sqrt_pos.mpr (hroot x hx)
  have hquot : 0 ≤ R*((p^2-q^2)/(4*(Real.sqrt (p+q*Real.sin x))^3)) :=
    mul_nonneg hR (div_nonneg (sub_nonneg.mpr hpq) (by positivity))
  have hb := hbound x hx
  dsimp [dd]
  nlinarith

private lemma negative_sqrt_quotient_identity {z L d dd r : ℝ}
    (hL : 0 < L) (hs : L^2=z) :
    r*(d^2-2*z*dd)/(4*z*L) = ((-r*dd)*(2*L)-(-r*d)*(2*(d/(2*L))))/(2*L)^2 := by
  subst z
  field_simp [ne_of_gt hL]
  ring

/-- The derivative of `-r f'/(2√f)`, the derivative of `-r√f`, is
`r (f'² - 2f f'')/(4f√f)` where `f > 0`. -/
lemma hasDerivAt_negative_sqrt {f d : ℝ → ℝ} {r x dd : ℝ}
    (hf : HasDerivAt f (d x) x) (hd : HasDerivAt d dd x) (hx : 0 < f x) :
    HasDerivAt (fun y => -r*d y/(2*Real.sqrt (f y)))
      (r*((d x)^2-2*f x*dd)/(4*f x*Real.sqrt (f x))) x := by
  have hroot := hf.sqrt (ne_of_gt hx)
  have hpos : 0 < Real.sqrt (f x) := Real.sqrt_pos.mpr hx
  have hden : 2*Real.sqrt (f x) ≠ 0 := ne_of_gt (by positivity)
  have hquot := HasDerivAt.div (hd.const_mul (-r)) (hroot.const_mul 2) hden
  convert hquot using 1
  all_goals first
    | rfl
    | exact negative_sqrt_quotient_identity hpos (Real.sq_sqrt hx.le)

/-- The squared length `P + Q cos x + T sin x` of a constant vector plus a
turning one. -/
def harmonicArg (P Q T x : ℝ) : ℝ := P+Q*Real.cos x+T*Real.sin x

/-- Minus `R` times the length. -/
def harmonicRoot (R P Q T x : ℝ) : ℝ := -R*Real.sqrt (harmonicArg P Q T x)

/-- The derivative of `harmonicRoot`. -/
def harmonicRootD (R P Q T x : ℝ) : ℝ :=
  -R*(-Q*Real.sin x+T*Real.cos x)/(2*Real.sqrt (harmonicArg P Q T x))

/-- The second derivative of `harmonicRoot`. -/
def harmonicCurvature (R P Q T x : ℝ) : ℝ :=
  let z := Q*Real.cos x+T*Real.sin x
  R*(z^2+2*P*z+Q^2+T^2)/(4*(P+z)*Real.sqrt (P+z))

lemma harmonicRoot_deriv {R P Q T x : ℝ} (hx : 0 < harmonicArg P Q T x) :
    HasDerivAt (harmonicRoot R P Q T) (harmonicRootD R P Q T x) x := by
  have hd : HasDerivAt (harmonicArg P Q T) (-Q*Real.sin x+T*Real.cos x) x := by
    convert ((((Real.hasDerivAt_cos x).const_mul Q).add
      ((Real.hasDerivAt_sin x).const_mul T)).const_add P) using 1
    · funext y
      simp only [harmonicArg,Pi.add_apply,add_assoc]
    · ring
  have hroot := hd.sqrt (ne_of_gt hx)
  convert hroot.const_mul (-R) using 1
  · rfl
  · simp only [harmonicRootD]
    ring

lemma harmonicRoot_second {R P Q T x : ℝ} (hx : 0 < harmonicArg P Q T x) :
    HasDerivAt (harmonicRootD R P Q T) (harmonicCurvature R P Q T x) x := by
  have hf : HasDerivAt (harmonicArg P Q T) (-Q*Real.sin x+T*Real.cos x) x := by
    convert ((((Real.hasDerivAt_cos x).const_mul Q).add
      ((Real.hasDerivAt_sin x).const_mul T)).const_add P) using 1
    · funext y
      simp only [harmonicArg,Pi.add_apply,add_assoc]
    · ring
  have hd : HasDerivAt (fun y => -Q*Real.sin y+T*Real.cos y)
      (-Q*Real.cos x-T*Real.sin x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul (-Q)).add
      ((Real.hasDerivAt_cos x).const_mul T) using 1
    ring
  have hh := hasDerivAt_negative_sqrt (r := R) hf hd hx
  have hid : (-Q*Real.sin x+T*Real.cos x)^2-
      2*harmonicArg P Q T x*(-Q*Real.cos x-T*Real.sin x) =
      (Q*Real.cos x+T*Real.sin x)^2+2*P*(Q*Real.cos x+T*Real.sin x)+Q^2+T^2 := by
    dsimp [harmonicArg]
    linear_combination (Q^2+T^2)*(Real.sin_sq_add_cos_sq x)
  have hA : harmonicArg P Q T x=P+(Q*Real.cos x+T*Real.sin x) := by
    dsimp only [harmonicArg]
    ring
  convert hh using 1
  · rfl
  · rw [hid,hA]
    rfl

lemma harmonic_amplitude_bound {a b Q T x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hQT : Q^2+T^2=4*a^2*b^2) :
    |Q*Real.cos x+T*Real.sin x| ≤ 2*a*b := by
  have hid : (Q*Real.cos x+T*Real.sin x)^2+(-Q*Real.sin x+T*Real.cos x)^2=Q^2+T^2 := by
    linear_combination (Q^2+T^2)*(Real.sin_sq_add_cos_sq x)
  have hnonneg : 0 ≤ 2*a*b := by positivity
  have hs : (Q*Real.cos x+T*Real.sin x)^2 ≤ (2*a*b)^2 := by
    nlinarith [sq_nonneg (-Q*Real.sin x+T*Real.cos x)]
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

lemma harmonic_arg_positive {a b P Q T x : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : a ≠ b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2) : 0 < harmonicArg P Q T x := by
  have hl := (abs_le.mp (harmonic_amplitude_bound (x := x) ha hb hQT)).1
  have hd : 0 < (a-b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  dsimp [harmonicArg]
  nlinarith

lemma harmonic_length_bound {a b P Q T x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2) :
    Real.sqrt (harmonicArg P Q T x) ≤ a+b := by
  have hl := (abs_le.mp (harmonic_amplitude_bound (x := x) ha hb hQT)).1
  have hu := (abs_le.mp (harmonic_amplitude_bound (x := x) ha hb hQT)).2
  have harg : 0 ≤ harmonicArg P Q T x := by
    dsimp [harmonicArg]
    nlinarith [sq_nonneg (a-b)]
  have hr := Real.sq_sqrt harg
  have hn := Real.sqrt_nonneg (harmonicArg P Q T x)
  dsimp [harmonicArg] at *
  nlinarith

lemma rotating_length_factor (a b L : ℝ) :
    4*a*b*L^3-(a+b)*(L^4-(a^2-b^2)^2) =
      (a+b-L)*((a+b)*L^3+(a-b)^2*L^2+(a+b)*(a-b)^2*L+(a+b)^2*(a-b)^2) := by ring

/-- Where the squared length is positive, the second derivative of `-R` times
the length is at most `R ab/(a + b)`. -/
theorem harmonicCurvature_le_harmonic_mean {R a b P Q T x : ℝ}
    (hR : 0 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2)
    (hx : 0 < harmonicArg P Q T x) :
    harmonicCurvature R P Q T x ≤ R*a*b/(a+b) := by
  let L := Real.sqrt (harmonicArg P Q T x)
  have hL : 0 < L := Real.sqrt_pos.mpr hx
  have hLup : L ≤ a+b := harmonic_length_bound ha hb hP hQT
  have hLsq : L^2=harmonicArg P Q T x := Real.sq_sqrt hx.le
  have he : harmonicCurvature R P Q T x = R*(L^4-(a^2-b^2)^2)/(4*L^3) := by
    have hs : L^2=P+(Q*Real.cos x+T*Real.sin x) := by
      rw [hLsq]
      dsimp only [harmonicArg]
      ring
    have hid : (Q*Real.cos x+T*Real.sin x)^2+2*P*(Q*Real.cos x+T*Real.sin x)+Q^2+T^2 =
        L^4-(a^2-b^2)^2 := by
      linear_combination hQT-(P+a^2+b^2)*hP-(L^2+P+(Q*Real.cos x+T*Real.sin x))*hs
    have hroot : Real.sqrt (P+(Q*Real.cos x+T*Real.sin x))=L := by
      rw [← hs]
      exact Real.sqrt_sq hL.le
    dsimp only [harmonicCurvature]
    rw [hid,hroot,← hs]
    ring
  rw [he]
  have hpositive : 0 ≤ (a+b)*L^3+(a-b)^2*L^2+(a+b)*(a-b)^2*L+(a+b)^2*(a-b)^2 := by
    positivity
  have hprod := mul_nonneg (sub_nonneg.mpr hLup) hpositive
  rw [← rotating_length_factor] at hprod
  have hprodR := mul_nonneg hR hprod
  apply (div_le_div_iff₀ (show 0 < 4*L^3 by positivity) hab).mpr
  nlinarith only [hprodR]

lemma harmonic_mean_mono {a b A B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b)
    (hA : a ≤ A) (hB : b ≤ B) : a*b/(a+b) ≤ A*B/(A+B) := by
  have hAB : 0 < A+B := by linarith
  have hp := mul_nonneg (mul_nonneg ha (ha.trans hA)) (sub_nonneg.mpr hB)
  have hq := mul_nonneg (mul_nonneg hb (hb.trans hB)) (sub_nonneg.mpr hA)
  apply (div_le_div_iff₀ hab hAB).mpr
  nlinarith only [hp,hq]

/-- If `a ≤ b` and `Q cos x + T sin x ≤ -2a²`, so that the squared length is at
most `b² - a²`, the second derivative is nonpositive. -/
theorem harmonicCurvature_nonpos_of_opposition {R a b P Q T x : ℝ}
    (hR : 0 ≤ R) (ha : 0 ≤ a) (hb : a ≤ b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2)
    (hx : 0 < harmonicArg P Q T x)
    (hop : Q*Real.cos x+T*Real.sin x ≤ -2*a^2) :
    harmonicCurvature R P Q T x ≤ 0 := by
  have hsq := mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ a+b by linarith)
  have hsecond : 0 ≤ Q*Real.cos x+T*Real.sin x+2*b^2 := by
    dsimp [harmonicArg] at hx
    nlinarith
  have hproduct := mul_nonpos_of_nonpos_of_nonneg
    (show Q*Real.cos x+T*Real.sin x+2*a^2 ≤ 0 by linarith) hsecond
  have hid : (Q*Real.cos x+T*Real.sin x)^2+2*P*(Q*Real.cos x+T*Real.sin x)+Q^2+T^2 =
      (Q*Real.cos x+T*Real.sin x+2*a^2)*(Q*Real.cos x+T*Real.sin x+2*b^2) := by
    linear_combination 2*(Q*Real.cos x+T*Real.sin x)*hP+hQT
  have hA : 0 < P+(Q*Real.cos x+T*Real.sin x) := by
    have h := hx
    dsimp only [harmonicArg] at h
    linarith
  dsimp only [harmonicCurvature]
  rw [hid]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hR hproduct)
    (mul_nonneg (by linarith) (Real.sqrt_nonneg _))

/-! ### Small angles and quadrants -/

/-- A small angle: for `|t| ≤ r`, `1 - r²/2 ≤ cos t` and `|sin t| ≤ r`. -/
lemma small_angle {t r : ℝ} (ht : |t| ≤ r) :
    1-r^2/2 ≤ Real.cos t ∧ |Real.sin t| ≤ r := by
  have ht2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at ht2
  exact ⟨by nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)],
    Real.abs_sin_le_abs.trans ht⟩

/-- A small nonnegative angle: for `0 ≤ x ≤ r ≤ 3`, `1 - r²/2 ≤ cos x` and
`0 ≤ sin x ≤ r`. -/
lemma small_angle_nonneg {x r : ℝ} (hx : 0 ≤ x ∧ x ≤ r) (hr : r ≤ 3) :
    1-r^2/2 ≤ Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x ≤ r := by
  have h := small_angle (show |x| ≤ r by rw [abs_of_nonneg hx.1]; exact hx.2)
  exact ⟨h.1,Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_gt_three]),
    (le_abs_self _).trans h.2⟩

lemma cos_pi_add (x : ℝ) : Real.cos (Real.pi+x) = -Real.cos x := by
  rw [add_comm,Real.cos_add_pi]

lemma sin_pi_add (x : ℝ) : Real.sin (Real.pi+x) = -Real.sin x := by
  rw [add_comm,Real.sin_add_pi]

lemma one_le_abs_cos_add_abs_sin (t : ℝ) : 1 ≤ |Real.cos t|+|Real.sin t| := by
  have hc := abs_nonneg (Real.cos t)
  have hs := abs_nonneg (Real.sin t)
  have hu := Real.sin_sq_add_cos_sq t
  have hp := mul_nonneg hc hs
  by_contra! h
  have hprod := mul_pos (sub_pos.mpr h)
    (show 0 < 1+(|Real.cos t|+|Real.sin t|) by linarith)
  nlinarith [sq_abs (Real.cos t),sq_abs (Real.sin t)]

/-- Rational bounds on `cos t` and `sin t` for `0 ≤ t ≤ π/4`. -/
lemma east_quadrant_trig {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.pi/4) :
    7/10 ≤ Real.cos t ∧ 0 ≤ Real.sin t ∧ Real.sin t ≤ Real.cos t := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ht0
    (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos]) ht
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ t by linarith [Real.pi_pos])
    (show Real.pi/4 ≤ Real.pi/2 by linarith [Real.pi_pos]) ht
  rw [Real.cos_pi_div_four] at hc
  rw [Real.sin_pi_div_four] at hs
  have hsqrt : (7:ℝ)/10 ≤ Real.sqrt 2/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  exact ⟨hsqrt.trans hc,
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos]),hs.trans hc⟩

/-- `cos x + sin x` increases on `[0, π/4]`. -/
lemma cos_add_sin_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Real.pi/4) :
    Real.cos x+Real.sin x ≤ Real.cos y+Real.sin y := by
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ x+Real.pi/4 by linarith [Real.pi_pos])
    (show y+Real.pi/4 ≤ Real.pi/2 by linarith)
    (show x+Real.pi/4 ≤ y+Real.pi/4 by linarith)
  simp only [Real.sin_add,Real.sin_pi_div_four,Real.cos_pi_div_four] at h
  apply (mul_le_mul_iff_right₀ (show 0 < Real.sqrt 2/2 by positivity)).mp
  nlinarith only [h]

/-- A quadratic upper bound for `cos` on `[-π, π]`. -/
lemma cos_le_one_sub_fifth_sq {t : ℝ} (ht : |t| ≤ Real.pi) :
    Real.cos t ≤ 1-t^2/5 := by
  have hpi : Real.pi < (22:ℝ)/7 := by linarith [Real.pi_lt_d4]
  have hp := mul_pos (sub_pos.mpr hpi)
    (show 0 < (22:ℝ)/7+Real.pi by linarith [Real.pi_pos])
  have hpi2 : Real.pi^2 < 10 := by nlinarith
  have hcoeff : (1:ℝ)/5 ≤ 2/Real.pi^2 := by
    apply (le_div_iff₀ (pow_pos Real.pi_pos 2)).mpr
    linarith
  have hm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg t)
  have hc := Real.cos_le_one_sub_mul_cos_sq ht
  nlinarith

/-! ### Taylor brackets and tangents -/

/-- The Taylor polynomial of degree 6 of `cos`, below it on the whole line. -/
def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720

/-- The Taylor polynomial of degree 4 of `cos`, above it on the whole line. -/
def cosUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/24

/-- The Taylor polynomial of degree 7 of `sin`, below it for `x ≥ 0`. -/
def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040

/-- The Taylor polynomial of degree 5 of `sin`, above it for `x ≥ 0`. -/
def sinUpper (x : ℝ) : ℝ := x-x^3/6+x^5/120

/-- A Taylor polynomial below `sin` on the whole line: `sinLower` for `x ≥ 0`,
`sinUpper` for `x < 0`. -/
def sinBelow (x : ℝ) : ℝ := if 0 ≤ x then sinLower x else sinUpper x

/-- A Taylor polynomial above `sin` on the whole line. -/
def sinAbove (x : ℝ) : ℝ := if 0 ≤ x then sinUpper x else sinLower x

lemma cosLower_le (x : ℝ) : cosLower x ≤ Real.cos x := by
  rcases le_total 0 x with hx | hx
  · exact cos_lower_six hx
  · have h := cos_lower_six (x := -x) (by linarith)
    rw [Real.cos_neg] at h
    dsimp [cosLower]
    nlinarith only [h]

lemma le_cosUpper (x : ℝ) : Real.cos x ≤ cosUpper x := by
  rcases le_total 0 x with hx | hx
  · exact cos_upper_four hx
  · have h := cos_upper_four (x := -x) (by linarith)
    rw [Real.cos_neg] at h
    dsimp [cosUpper]
    nlinarith only [h]

lemma sinLower_le {x : ℝ} (hx : 0 ≤ x) : sinLower x ≤ Real.sin x := sin_lower_seven hx

lemma le_sinUpper {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ sinUpper x := sin_upper_five hx

lemma sinBelow_le (x : ℝ) : sinBelow x ≤ Real.sin x := by
  by_cases hx : 0 ≤ x
  · simpa only [sinBelow,ite_eq_left hx] using sinLower_le hx
  · have h := le_sinUpper (x := -x) (by linarith)
    rw [Real.sin_neg] at h
    simp only [sinBelow,ite_eq_right hx,sinUpper] at h ⊢
    nlinarith only [h]

lemma le_sinAbove (x : ℝ) : Real.sin x ≤ sinAbove x := by
  by_cases hx : 0 ≤ x
  · simpa only [sinAbove,ite_eq_left hx] using le_sinUpper hx
  · have h := sinLower_le (x := -x) (by linarith)
    rw [Real.sin_neg] at h
    simp only [sinAbove,ite_eq_right hx,sinLower] at h ⊢
    nlinarith only [h]

lemma trig_bracket_half :
    (8775:ℝ)/10000 ≤ Real.cos (1/2) ∧ Real.cos (1/2) ≤ 878/1000 ∧
    (4794:ℝ)/10000 ≤ Real.sin (1/2) ∧ Real.sin (1/2) ≤ 4795/10000 := by
  have h := trig_bracket (l := 1/2) (u := 1/2) (x := 1/2) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  norm_num at h
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma trig_bracket_two_thirds :
    (157:ℝ)/200 ≤ Real.cos (2/3) ∧ Real.cos (2/3) ≤ 787/1000 ∧
    (309:ℝ)/500 ≤ Real.sin (2/3) ∧ Real.sin (2/3) ≤ 619/1000 := by
  have h := trig_bracket (l := 2/3) (u := 2/3) (x := 2/3) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  norm_num at h
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma trig_bracket_seven_sixths :
    (3931:ℝ)/10000 ≤ Real.cos (7/6) ∧ Real.cos (7/6) ≤ 2/5 ∧
    (9194:ℝ)/10000 ≤ Real.sin (7/6) ∧ Real.sin (7/6) ≤ 9201/10000 := by
  have h := trig_bracket (l := 7/6) (u := 7/6) (x := 7/6) (by norm_num)
    (by linarith [Real.pi_gt_d2]) ⟨le_rfl,le_rfl⟩
  norm_num at h
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- The tangent majorant of the square root: `√y ≤ (y + c²)/(2c)` for `c > 0`. -/
lemma sqrt_le_tangent {y c : ℝ} (hc : 0 < c) (hy : 0 ≤ y) : Real.sqrt y ≤ (y+c^2)/(2*c) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg (Real.sqrt y-c),Real.sq_sqrt hy]

/-- The tangent majorant squared dominates: `y ≤ ((y + c²)/(2c))²` for `c > 0`. -/
lemma sq_le_tangent_sq {y c : ℝ} (hc : 0 < c) : y ≤ ((y+c^2)/(2*c))^2 := by
  rw [div_pow,le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (y-c^2)]

/-! ### The half-angle ratio -/

/-- `sin t/(1 + cos t)`, which is `tan (t/2)`. -/
def halfRatio (t : ℝ) : ℝ := Real.sin t/(1+Real.cos t)

lemma small_polynomial_trig {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) :
    17/25 ≤ Real.cos t ∧ (89/100)*t ≤ Real.sin t ∧
      Real.sin t ≤ t ∧ 1+(12/25)*t ≤ Real.cos t+Real.sin t := by
  have hsq := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ 4/5+t by linarith [ht.1])
  have ht2 : t^2 ≤ 16/25 := by nlinarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hs := Real.sin_ge_sub_cube ht.1
  have hsinprod := mul_nonneg ht.1 (show 0 ≤ 1-89/100-t^2/6 by linarith)
  have hsumprod := mul_nonneg ht.1 (show 0 ≤ 1-12/25-t/2-t^2/6 by linarith [ht.2])
  exact ⟨by linarith,by nlinarith only [hs,hsinprod],Real.sin_le ht.1,
    by nlinarith only [hs,hc,hsumprod]⟩

lemma halfRatio_den_pos {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) : 0 < 1+Real.cos t := by
  linarith [(small_polynomial_trig ht).1]

lemma halfRatio_nonnegative {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) : 0 ≤ halfRatio t := by
  apply div_nonneg _ (halfRatio_den_pos ht).le
  nlinarith [(small_polynomial_trig ht).2.1,ht.1]

lemma halfRatio_identities {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) :
    halfRatio t*(1+Real.cos t)=Real.sin t ∧ halfRatio t*Real.sin t=1-Real.cos t := by
  have hden := ne_of_gt (halfRatio_den_pos ht)
  constructor
  · exact div_mul_cancel₀ _ hden
  · unfold halfRatio
    field_simp [hden]
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- `tan (t/2) ≥ t/2`, as `2 sin t - t (1 + cos t)` increases from `0`. -/
lemma halfRatio_lower {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) : t/2 ≤ halfRatio t := by
  let H : ℝ → ℝ := fun x => Real.cos x-1+x*Real.sin x
  have hHd (x : ℝ) : HasDerivAt H (x*Real.cos x) x := by
    convert ((Real.hasDerivAt_cos x).sub_const 1).fun_add
      ((hasDerivAt_id x).fun_mul (Real.hasDerivAt_sin x)) using 1 <;> dsimp [H]
    ring
  have hHm : MonotoneOn H (Icc 0 (4/5)) := by
    apply monoOn_of_hasDeriv_nonneg (by dsimp [H]; fun_prop)
      (fun x _ => hHd x)
    intro x hx
    exact mul_nonneg hx.1.le (by linarith [(small_polynomial_trig ⟨hx.1.le,hx.2.le⟩).1])
  let F : ℝ → ℝ := fun x => 2*Real.sin x-x*(1+Real.cos x)
  have hFd (x : ℝ) : HasDerivAt F (H x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul 2).fun_sub
      ((hasDerivAt_id x).fun_mul ((Real.hasDerivAt_cos x).const_add 1)) using 1 <;>
      dsimp [F,H]
    ring
  have hFm : MonotoneOn F (Icc 0 (4/5)) :=
    monoOn_of_hasDeriv_nonneg (by dsimp [F]; fun_prop)
      (fun x _ => hFd x) (fun x hx => by
        simpa [H] using hHm (show (0:ℝ) ∈ Icc 0 (4/5) by constructor <;> norm_num)
          ⟨hx.1.le,hx.2.le⟩ hx.1.le)
  have hF := hFm (show (0:ℝ) ∈ Icc 0 (4/5) by constructor <;> norm_num) ht ht.1
  have hF' : 0 ≤ 2*Real.sin t-t*(1+Real.cos t) := by simpa [F] using hF
  unfold halfRatio
  apply (le_div_iff₀ (halfRatio_den_pos ht)).mpr
  nlinarith only [hF']

/-- `tan (t/2) ≤ 11t/20` on `[0, 4/5]`, by the Taylor bound of `sin` of degree
five. -/
lemma halfRatio_upper {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) : halfRatio t ≤ (11/20)*t := by
  have hsq := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ 4/5+t by linarith [ht.1])
  have ht2 : t^2 ≤ 16/25 := by nlinarith
  have hfour := mul_nonneg (sub_nonneg.mpr ht2) (show 0 ≤ 16/25+t^2 by positivity)
  have hp := mul_nonneg ht.1 (show 0 ≤ 1/10-(13/120)*t^2-t^4/120 by nlinarith)
  have hs := sin_upper_five ht.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hcm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (11/20)*t by linarith [ht.1])
  unfold halfRatio
  apply (div_le_iff₀ (halfRatio_den_pos ht)).mpr
  nlinarith only [hp,hs,hcm]

/-- `cos q - cos d ≥ 89 (d² - q²)/200` for `0 ≤ q ≤ d ≤ 4/5`, since
`cos x + 89x²/200` decreases there. -/
lemma cosine_difference_lower {q d : ℝ} (hq : 0 ≤ q) (hqd : q ≤ d) (hd : d ≤ 4/5) :
    (89/200)*(d^2-q^2) ≤ Real.cos q-Real.cos d := by
  let f : ℝ → ℝ := fun x => Real.cos x+(89/200)*x^2
  have hfd (x : ℝ) : HasDerivAt f (-Real.sin x+(89/100)*x) x := by
    convert (Real.hasDerivAt_cos x).fun_add (((hasDerivAt_id x).fun_pow 2).const_mul (89/200))
      using 1 <;> dsimp [f]
    ring
  have hanti : AntitoneOn f (Icc 0 (4/5)) := by
    apply antiOn_of_hasDeriv_nonpos (by dsimp [f]; fun_prop) (fun x _ => hfd x)
    intro x hx
    linarith [(small_polynomial_trig ⟨hx.1.le,hx.2.le⟩).2.1]
  have h := hanti ⟨hq,hqd.trans hd⟩ ⟨hq.trans hqd,hd⟩ hqd
  dsimp [f] at h
  linarith

lemma halfRatio_shift {w d : ℝ} (hw : 0 ≤ w ∧ w ≤ 4/5) :
    Real.sin (d-w)+halfRatio w*Real.cos (d-w)=Real.sin d-halfRatio w*Real.cos d := by
  have h := halfRatio_identities hw
  rw [Real.sin_sub,Real.cos_sub]
  linear_combination Real.sin d*h.2+Real.cos d*h.1

end SquaresInCircles.Six
