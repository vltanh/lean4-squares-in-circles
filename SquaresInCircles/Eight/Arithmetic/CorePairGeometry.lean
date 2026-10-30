module

public import SquaresInCircles.Eight.Arithmetic.Arctangent
public import SquaresInCircles.Eight.BoundaryGeometry

/-!
# Eight squares: pairs of two core squares

A square of a boundary cycle whose state lies on the core side or the core corner (`CoreState`)
has its centre within `4/5` of the origin (`core_radius_sq`). Two consecutive squares of the
cycle have centres at least `1` apart, by their separating axis, so the angle between the
directions of two consecutive core centres exceeds `4/3` (`core_gap`), whichever axis separates
them.

The core labels `k (7/12 - a) + l b` of the four-type pair bounds and of the common quarter-word
increments (`CoreLabel`) have markers `arctan (b / a) - k (7/12 - a) - l b` in
`(-177/1000, 177/1000)` on the closed core side and the closed core corner (`marker_mem`): on the
side by `x - x³/3 ≤ arctan x` and the tangent of `arctan` at `3/4`, on the corner by
`arctan (6/7) > 2/3`, the tangent at `6/7` and the circle equation (`corner_geometry`); the values
of `arctan` at `3/4` and `6/7` are bounded in `Arctangent.lean`. So the cost of an edge between
two core squares, with the signed markers of its ends, exceeds `4/3 - 354/1000 > 979/1000`
(`core_cost`), for all signs and separating axes at once. With the bound `21/100` of the frame
charge (`charge_upper`) this gives the pairs of two core charts in `FourTypePairs.lean` and in
`WordGeometry.lean`; `Candidate/GeometricCoreMarker.lean` uses `core_gap` and `charge_upper`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CorePairGeometry

/-- The coefficient `k` of the core label of the four-type pair bounds. -/
def K : ℝ := 7506931/1000000
/-- The coefficient `l` of the core label of the four-type pair bounds. -/
def g : ℝ := 269343/250000

/-- The core label `k (7/12 - a) + l b`. -/
def label (k l a b : ℝ) : ℝ := k*(7/12-a)+l*b

/-- The coefficients of the two core labels: of the four-type pairs, and of the common
quarter-word increments. -/
def CoreLabel (k l : ℝ) : Prop := (k=K ∧ l=g) ∨ (k=73/10 ∧ l=291/250)

/-- The closed core side and the closed core corner, with `b ≤ a`. -/
def CoreState (a b : ℝ) : Prop :=
  (a=7/12 ∧ 0 ≤ b ∧ b ≤ 1/2) ∨
  (1/2 ≤ b ∧ b ≤ a ∧ (a-1/2)^2+(b-1/2)^2=(1/12:ℝ)^2)

/-- `arctan` lies below its tangents on `[0, ∞)`, where it is concave. -/
theorem arctan_tangent {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    Real.arctan x ≤ Real.arctan t+(x-t)/(1+t^2) := by
  let f : ℝ → ℝ := fun y => Real.arctan y-(1/(1+t^2))*y
  let d : ℝ → ℝ := fun y => 1/(1+y^2)-1/(1+t^2)
  have hd (y : ℝ) : HasDerivAt f (d y) y := by
    have h := (Real.hasDerivAt_arctan y).sub ((hasDerivAt_id y).const_mul (1/(1+t^2)))
    simp only [id, mul_one] at h
    exact h
  have hleft (y : ℝ) (hy : y ∈ Icc 0 t) : 0 ≤ d y := by
    have : 1/(1+t^2) ≤ 1/(1+y^2) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [hy.1, hy.2])
    simp only [d]
    linarith
  have hright (y : ℝ) (hy : y ∈ Icc t (max x t)) : d y ≤ 0 := by
    have : 1/(1+y^2) ≤ 1/(1+t^2) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [hy.1, hy.2])
    simp only [d]
    linarith
  have hh := le_at_peak (l := 0) (c := t) (u := max x t) (x := x)
    ⟨ht, le_max_right x t⟩ ⟨hx, le_max_left x t⟩ (by fun_prop) hd hleft hright
  simp only [f] at hh
  have he : (x-t)/(1+t^2)=(1/(1+t^2))*x-(1/(1+t^2))*t := by ring
  linarith

theorem arctan_lower_three {x : ℝ} (hx : 0 ≤ x) : x-x^3/3 ≤ Real.arctan x := by
  have hh := nonneg_of_deriv_nonneg (fun z : ℝ => Real.arctan z-(z-z^3/3))
    (Real.differentiable_arctan.sub (by fun_prop)) (by norm_num) (fun y _ => by
      have hy : (0:ℝ) < 1+y^2 := by positivity
      have hd : deriv (fun z : ℝ => Real.arctan z-(z-z^3/3)) y = y^4/(1+y^2) := by
        rw [deriv_fun_sub (Real.differentiableAt_arctan y) (by fun_prop), Real.deriv_arctan]
        simp (disch := fun_prop)
        field_simp
        ring
      rw [hd]
      positivity) hx
  linarith

theorem arctan_six_sevenths : (2/3:ℝ) < Real.arctan (6/7:ℝ) := by
  have h := Arithmetic.atanLower_le (x := (6/7:ℝ)) (by norm_num)
  norm_num [Arithmetic.atanLower] at h
  linarith

/-- On `[0, ∞)`, `x - x³/3 ≤ arctan x < 161/250 + (16/25)(x - 3/4)`: the tangent at `3/4`, with
`arctan (3/4) < 161/250`. -/
theorem side_angle {x : ℝ} (hx : 0 ≤ x) :
    x-x^3/3 ≤ Real.arctan x ∧ Real.arctan x < 161/250+(16/25)*(x-3/4) := by
  have hu := arctan_tangent hx (show (0:ℝ) ≤ 3/4 by norm_num)
  have h := Arithmetic.arctan_le_atanUpper (x := (3/4:ℝ)) (by norm_num)
  norm_num [Arithmetic.atanUpper] at h hu
  exact ⟨arctan_lower_three hx, by linarith⟩

/-- The circle equation of the core corner bounds its primary coordinate and gives a quadratic
and a linear bound of the radial loss `7/12 - a` in `b - 1/2`. -/
theorem corner_geometry {a b : ℝ} (hb : 1/2 ≤ b) (hab : b ≤ a)
    (hc : (a-1/2)^2+(b-1/2)^2=(1/12:ℝ)^2) :
    67/120 < a ∧ a ≤ 7/12 ∧ 7/12-a ≤ (b-1/2)/2 ∧ 6*(b-1/2)^2 ≤ 7/12-a := by
  have hd : 0 ≤ b-1/2 := by linarith
  have hsq := pow_le_pow_left₀ hd (by linarith : b-1/2 ≤ a-1/2) 2
  have hal : 67/120 < a := by nlinarith
  have hau : a ≤ 7/12 := by nlinarith [sq_nonneg (b-1/2)]
  refine ⟨hal, hau, ?_, by nlinarith [sq_nonneg (a-7/12)]⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) hd, sq_nonneg (b-1/2)]

/-- On the core corner `2/3 < arctan (b / a) < 1247/1750 + (9/5)(b - 1/2)`, by the tangent of
`arctan` at `6/7`. -/
theorem corner_angle {a b : ℝ} (hb : 1/2 ≤ b) (hab : b ≤ a)
    (hc : (a-1/2)^2+(b-1/2)^2=(1/12:ℝ)^2) :
    2/3 < Real.arctan (b/a) ∧ Real.arctan (b/a) < 1247/1750+(9/5)*(b-1/2) := by
  obtain ⟨hal, hau, -, -⟩ := corner_geometry hb hab hc
  have ha : 0 < a := by linarith
  have hx : 0 ≤ b/a := div_nonneg (by linarith) ha.le
  have hxL : (6/7:ℝ) ≤ b/a := (le_div_iff₀ ha).mpr (by linarith)
  have ht := arctan_tangent hx (show (0:ℝ) ≤ 6/7 by norm_num)
  have hratio : (49/85:ℝ)*(b/a-6/7) ≤ (9/5)*(b-1/2) := by
    have hdiv : (b/a)*a=b := div_mul_cancel₀ b (ne_of_gt ha)
    apply (mul_le_mul_iff_of_pos_right ha).mp
    nlinarith [mul_nonneg (by linarith : 0 ≤ a-5/9) (by linarith : 0 ≤ b-1/2)]
  have h67 := (side_angle (x := 6/7) (by norm_num)).2
  norm_num at ht h67
  exact ⟨lt_of_lt_of_le arctan_six_sevenths (Real.arctan_mono hxL), by linarith⟩

/-- On the core, the markers of both core labels lie in `(-177/1000, 177/1000)`. -/
theorem marker_mem {k l a b : ℝ} (hkl : CoreLabel k l) (h : CoreState a b) :
    -(177/1000:ℝ) < Real.arctan (b/a)-label k l a b ∧
      Real.arctan (b/a)-label k l a b < 177/1000 := by
  simp only [label]
  rcases h with ⟨rfl, hb, hbu⟩ | ⟨hb, hab, hc⟩
  · obtain ⟨hl, hu⟩ := side_angle (x := b/(7/12)) (by positivity)
    have hx : b/(7/12)=(12/7)*b := by ring
    rw [hx] at hl hu ⊢
    have hcube : ((12/7)*b)^3 ≤ (36/49)*((12/7)*b) := by
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ (12/7)*b)
        (by linarith : (12/7)*b ≤ 6/7) 2) (by positivity : 0 ≤ (12/7)*b)
      nlinarith
    rcases hkl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num [K, g] at hu ⊢ <;>
      constructor <;> nlinarith
  · obtain ⟨hal, -, -, hloss⟩ := corner_geometry hb hab hc
    obtain ⟨hl, hu⟩ := corner_angle hb hab hc
    rcases hkl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num [K, g] <;> constructor
    · nlinarith
    · nlinarith [sq_nonneg (12*(7506931/1000000)*(b-1/2)-(9/5-269343/250000))]
    · nlinarith
    · nlinarith [sq_nonneg (12*(73/10)*(b-1/2)-(9/5-291/250))]

/-- A core centre lies within `4/5` of the origin. -/
theorem core_radius_sq {a b : ℝ} (h : CoreState a b) : a^2+b^2 < 16/25 := by
  rcases h with ⟨rfl, hb, hbu⟩ | ⟨hb, hab, hc⟩
  · nlinarith
  · nlinarith [sq_nonneg (a-b), sq_nonneg (a+b-1-3/25)]

/-- A vertex of a boundary cycle that is not on the outer circle is in a core state. -/
theorem boundary_core_state {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hk : C.kind i ≠ .outer) : CoreState (C.a i) (C.b i) := by
  have hb := C.boundary i
  cases he : C.kind i with
  | outer => exact absurd he hk
  | coreSide =>
      simp only [he, BoundaryState] at hb
      exact Or.inl ⟨hb.1, C.b_nonneg i, hb.2⟩
  | coreCorner =>
      simp only [he, BoundaryState] at hb
      exact Or.inr ⟨hb.1, C.b_le_a i, hb.2⟩

/-- `r² + s² - (7/16) r s ≤ 1` on `[0, 4/5]²`. -/
theorem chord_upper {r s : ℝ} (hr : 0 ≤ r ∧ r ≤ 4/5) (hs : 0 ≤ s ∧ s ≤ 4/5) :
    r^2+s^2-(7/16)*r*s ≤ 1 := by
  nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hr.2), mul_nonneg hs.1 (sub_nonneg.mpr hs.2),
    mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hs.2)]

/-- Two consecutive centres in core states are more than `4/3` apart in direction. -/
theorem core_gap {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hi : CoreState (C.a i) (C.b i)) (hj : CoreState (C.a (next i)) (C.b (next i))) :
    (4/3:ℝ) < angleGap C.beta i := by
  have hr0 := C.radius_pos i
  have hs0 := C.radius_pos (next i)
  have hr : C.radius i < 4/5 := by nlinarith [C.radius_sq i, core_radius_sq hi]
  have hs : C.radius (next i) < 4/5 := by nlinarith [C.radius_sq (next i), core_radius_sq hj]
  have hd := signed_axis_center_distance (C.feasible i)
  rw [polar_pair_distance (C.center_cos i) (C.center_sin i)
    (C.center_cos (next i)) (C.center_sin (next i))] at hd
  have hcos : Real.cos (C.beta (next i)-C.beta i)=Real.cos (angleGap C.beta i) := by
    by_cases hlast : i=6 <;> simp [angleGap, hlast, Real.cos_add_two_pi]
  rw [hcos] at hd
  change 1 ≤ C.radius i^2+C.radius (next i)^2-
    2*C.radius i*C.radius (next i)*Real.cos (angleGap C.beta i) at hd
  have hmax := chord_upper ⟨hr0.le, hr.le⟩ ⟨hs0.le, hs.le⟩
  have hfour : (7/32:ℝ) < Real.cos (4/3) := by
    have hh := cos_lower_six (x := (4/3:ℝ)) (by norm_num)
    norm_num at hh
    linarith
  by_contra! hbad
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi (C.gap_pos i).le
    (by linarith [Real.pi_gt_three] : (4/3:ℝ) ≤ Real.pi) hbad
  nlinarith [mul_pos (mul_pos hr0 hs0) (sub_pos.mpr (lt_of_lt_of_le hfour hm))]

/-- The signed marker `α - σ L(a, b)` of a core vertex lies in `(-177/1000, 177/1000)`. -/
theorem boundary_marker_mem {k l q : ℝ} (hkl : CoreLabel k l) (C : BoundaryCycle q) (i : Vertex)
    (hk : C.kind i ≠ .outer) :
    -(177/1000:ℝ) < C.alpha i-C.sigma i*label k l (C.a i) (C.b i) ∧
      C.alpha i-C.sigma i*label k l (C.a i) (C.b i) < 177/1000 := by
  have h := marker_mem hkl (boundary_core_state C i hk)
  rcases C.sigma_sign i with hσ | hσ <;>
    simp only [BoundaryCycle.alpha, BoundaryCycle.tangent, hσ, neg_one_mul, one_mul, neg_div,
      Real.arctan_neg] <;>
    constructor <;> linarith [h.1, h.2]

/-- The cost of a core/core edge with the signed markers of a core label exceeds `979/1000`. -/
theorem core_cost {k l q : ℝ} (hkl : CoreLabel k l) (C : BoundaryCycle q) (i : Vertex)
    (hi : C.kind i ≠ .outer) (hj : C.kind (next i) ≠ .outer) :
    (979/1000:ℝ) < angleGap C.beta i+
      (C.alpha (next i)-C.sigma (next i)*label k l (C.a (next i)) (C.b (next i)))-
      (C.alpha i-C.sigma i*label k l (C.a i) (C.b i)) := by
  have hg := core_gap C i (boundary_core_state C i hi) (boundary_core_state C (next i) hj)
  have hmi := boundary_marker_mem hkl C i hi
  have hmj := boundary_marker_mem hkl C (next i) hj
  linarith [hmi.2, hmj.1]

/-- The frame charge `(|cos φ| + |sin φ| - 1)/2` is below `21/100`. -/
theorem charge_upper (φ : ℝ) : periodicFrameCost φ < 21/100 := by
  have hu := Real.sin_sq_add_cos_sq φ
  simp only [periodicFrameCost]
  nlinarith [sq_abs (Real.cos φ), sq_abs (Real.sin φ),
    sq_nonneg (|Real.cos φ|-|Real.sin φ|), abs_nonneg (Real.cos φ), abs_nonneg (Real.sin φ)]

end SquaresInCircles.Eight.CorePairGeometry
