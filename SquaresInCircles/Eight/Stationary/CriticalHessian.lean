module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.Order.Compact
public import SquaresInCircles.Eight.Stationary.FixedEval

/-!
# Eight squares: the Hessian at a critical point

On the strip `(79/40)² ≤ q ≤ 9789/2500`, `87/100 ≤ u ≤ 1` (`CriticalStrip`) the circle
equations bound the radicals of `Convexity.lean` (`CriticalStrip.bounds`). Rational support lines
of the circles give `p > 3/2 - u` for the slope `p = -v'` (`slope_affine_lower`) and
`w - 1 - 6u/7 > 3/70` (`left_support_lower`), and the bounds give `Z > (13/10)(1 + p)` for the
curvature ratio `Z = q/((2-u)U²) + p q/(Y V²)` (`curvatureRatio_lower`) and `q/r³ < 4/5`
(`right_curvature_upper`).

`StripCritical` is a point of the strip with `0 ≤ s/c ≤ 1/5` where both partial derivatives of
the defect vanish; the defect may have either sign. There the tilt and position derivatives of
`(k₁, k₂)` are proportional, `k_t = κ k_u` (`StripCritical.derivative_proportionality`), and the
determinant of the Hessian is `4 k₁² (A (σ κ² - 2 τ κ + ν) + σ ν - τ²)`
(`StripCritical.normalized_hessian_identity`), where `A = |k_u|²/k₁` and `σ`, `τ`, `ν` are the
position, mixed and tilt normal terms divided by `k₁`. The circle bounds give `A > 17/50`,
`κ > 7/5`, `0 < τ < 7/8`, `ν > 9/100`, `κ σ > 3`, `σ > 27/16`, hence
`det > (237/5000) k₁² > 0` (`StripCritical.hessian_reserve`).

On `SmoothDomain` (the radical domain with `q < 4` and the four radicals positive) the nested
radicals are differentiable, `p' = -p Z` (`slopeRatio_deriv`), and the position derivative
`2 positionHalf` has position derivative `positionSecond` (`position_second_deriv`) and tilt
derivative `mixedSecond` (`mixed_angle_deriv`). The position entry is positive, since `k₁` and
`k₂` are positive and have the positive second position derivatives `rightSecond` and
`leftSecond`, which come from the curvature of the circles (`SmoothDomain.positionSecond_pos`). A
stationary chain is a critical point of the strip (`stationary_isStripCritical`). `Envelope.lean`
uses the Hessian bound for the second derivative of the envelope in the tilt.
-/

section
/-!
## Convexity of the chain in the position

The chain of `Coordinates.lean` is written with the downward position `u = -y` and the four
successive square roots `r, U, Y, w` (`lowerRight`, `topRight`, `topHeight`, `lowerLeft`), with
`V = 3 - U` (`topLeft`) and `v = 2 - Y` (`lowerHeight`); the radical domain `Domain q u` is
`u ≥ 0` with the four radicands nonnegative. For `q < 4` a chord of a disk lies in the disk, so
applying it successively along the chain shows that the domain is convex and that the two
components `k₁, k₂` of the fifth corner are convex in `u`, the first strictly. Both are positive
for `0 < c ≤ 1`, `0 ≤ s ≤ 1`, so the defect `k₁² + k₂² - q` is strictly convex on the whole
domain, endpoints included (`strictConvexOn_defect`), and has at most one minimum
(`minimizer_unique`). The chart gives the coordinates of a chain (`coordinate_values`,
`coordinate_defect`). For `q₀ < q₁ < 4` the radicals `r` and `w` grow and `v` shrinks with the
radius (`domain_radius_inclusion`), so at every position of the domain and every such tilt the
defect at `q₁` is less than the defect at `q₀` minus `q₁ - q₀` (`defect_radius_decrease`).

Where the four radicals are positive the defect is differentiable in the position, with
derivative `2 positionHalf` (`position_deriv`); in the tilt `t`, with `c = cos t`, `s = sin t`,
it has the first and second derivatives `tiltFirst` and `tiltSecond` (`defect_angle_deriv`,
`defect_angle_second_deriv`). Throughout the strip `(79/40)² ≤ q ≤ 9789/2500`, `0 ≤ s/c ≤ 1/5`,
the circle equations bound the radicals at `u = 87/100` by successive square comparisons, and
five coefficient bounds then give `positionHalf < 0` there (`comparison_position_negative`). By
strict convexity every critical position lies to the right (`stationary_position_lower`) and is
the global minimum on the radical domain (`stationary_global_minimum`); a stationary chain has
`87/100 < -y` (`stationary_coordinate_lower`). At the trial position `u = 15/16` the squared norm
`k₁² + k₂²` is at most a cubic in `s/c` that lies below its chord, with both ends below `4`, so
`k₁² + k₂² < 4` at every position minimum, whatever the sign of the defect
(`position_minimum_norm_lt_four`). `CriticalHessian.lean` and `Envelope.lean` build on these
results.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Stationary.FiveCornerGeometry

/-! ### The chain and its convexity in the position -/

/-- The upper half of the circle of squared radius `q`, `√(q - x²)`. -/
def upper (q x : ℝ) : ℝ := Real.sqrt (q-x^2)
/-- `r = √(q - u²)`, the abscissa of the lower right corner of `A`. -/
def lowerRight (q u : ℝ) : ℝ := upper q u
/-- `U = √(q - (2 - u)²)`, the abscissa of the upper right corner of `B`, at height `2 - u`. -/
def topRight (q u : ℝ) : ℝ := upper q (2-u)
/-- `V = 3 - U`, minus the abscissa of the upper left corner of `D`. -/
def topLeft (q u : ℝ) : ℝ := 3-topRight q u
/-- `Y = √(q - V²)`, the height of the upper left corner of `D`. -/
def topHeight (q u : ℝ) : ℝ := upper q (topLeft q u)
/-- `v = 2 - Y`, minus the height of the lower left corner of `E`. -/
def lowerHeight (q u : ℝ) : ℝ := 2-topHeight q u
/-- `w = √(q - v²)`, minus the abscissa of the lower left corner of `E`. -/
def lowerLeft (q u : ℝ) : ℝ := upper q (lowerHeight q u)

/-- `k₁ = 2 - c (r - 1) + s u`, minus the first coordinate `h₁` of the fifth corner in the
frame `(c, s)` of `H`. -/
def firstComponent (q c s u : ℝ) : ℝ :=
  2-c*(lowerRight q u-1)+s*u
/-- `k₂ = 1 + c v - s (w - 1)`, minus the second coordinate `h₂` of the fifth corner. -/
def secondComponent (q c s u : ℝ) : ℝ :=
  1+c*lowerHeight q u-s*(lowerLeft q u-1)
/-- The defect `k₁² + k₂² - q`, by which the squared norm of the fifth corner exceeds `q`. -/
def defect (q c s u : ℝ) : ℝ :=
  firstComponent q c s u^2+secondComponent q c s u^2-q

/-- The radical domain of the chain: `u ≥ 0` and the four radicands are nonnegative. -/
structure Domain (q u : ℝ) : Prop where
  height_nonneg : 0 ≤ u
  first_radicand : u^2 ≤ q
  second_radicand : (2-u)^2 ≤ q
  third_radicand : topLeft q u^2 ≤ q
  fourth_radicand : lowerHeight q u^2 ≤ q

theorem upper_nonneg (q x : ℝ) : 0 ≤ upper q x := Real.sqrt_nonneg _

theorem upper_circle {q x : ℝ} (hx : x^2 ≤ q) :
    upper q x^2+x^2=q := by
  dsimp [upper]
  rw [Real.sq_sqrt (sub_nonneg.mpr hx)]
  ring

theorem upper_lt_two {q x : ℝ} (hq : q<4) (hx : x^2 ≤ q) :
    upper q x<2 := by
  nlinarith [upper_circle hx,upper_nonneg q x,sq_nonneg x,sq_nonneg (upper q x-2)]

theorem upper_antitone {q x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    upper q y ≤ upper q x := by
  apply Real.sqrt_le_sqrt
  nlinarith

theorem weighted_square_gap (x y a b : ℝ) (hab : a+b=1) :
    a*x^2+b*y^2-(a*x+b*y)^2=a*b*(x-y)^2 := by
  have hb : b=1-a := by linarith
  rw [hb]
  ring

theorem weighted_square_le (x y : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (a*x+b*y)^2 ≤ a*x^2+b*y^2 := by
  have hn := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y))
  linarith [weighted_square_gap x y a b hab]

theorem square_mono_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x^2 ≤ y^2 := by
  have hp := mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg (le_trans hx hxy) hx)
  nlinarith

theorem square_strict_mono_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x<y) :
    x^2<y^2 := by
  have hp := mul_pos (sub_pos.mpr hxy) (by linarith : 0<y+x)
  nlinarith

theorem disk_chord {q x₀ x₁ y₀ y₁ a b : ℝ}
    (h₀ : x₀^2+y₀^2 ≤ q) (h₁ : x₁^2+y₁^2 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (a*x₀+b*x₁)^2+(a*y₀+b*y₁)^2 ≤ q := by
  calc
    _ ≤ a*(x₀^2+y₀^2)+b*(x₁^2+y₁^2) := by
      nlinarith [weighted_square_le x₀ x₁ ha hb hab,
        weighted_square_le y₀ y₁ ha hb hab]
    _ ≤ a*q+b*q := add_le_add
      (mul_le_mul_of_nonneg_left h₀ ha) (mul_le_mul_of_nonneg_left h₁ hb)
    _ = q := by rw [← add_mul,hab,one_mul]

theorem disk_chord_strict {q x₀ x₁ y₀ y₁ a b : ℝ}
    (h₀ : x₀^2+y₀^2 ≤ q) (h₁ : x₁^2+y₁^2 ≤ q) (hxy : x₀≠x₁)
    (ha : 0<a) (hb : 0<b) (hab : a+b=1) :
    (a*x₀+b*x₁)^2+(a*y₀+b*y₁)^2 < q := by
  have hp : 0<a*b*(x₀-x₁)^2 :=
    mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))
  have hn := mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (y₀-y₁))
  have hx := weighted_square_gap x₀ x₁ a b hab
  have hy := weighted_square_gap y₀ y₁ a b hab
  have hq : a*q+b*q=q := by rw [← add_mul,hab,one_mul]
  have h₀' := mul_le_mul_of_nonneg_left h₀ ha.le
  have h₁' := mul_le_mul_of_nonneg_left h₁ hb.le
  nlinarith

/-- A chord of the circle lies below the positive square-root branch. -/
theorem upper_mix {q x y a b : ℝ} (hx : x^2 ≤ q) (hy : y^2 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (a*x+b*y)^2 ≤ q ∧
      a*upper q x+b*upper q y ≤ upper q (a*x+b*y) := by
  have hd := disk_chord
    (by nlinarith [upper_circle hx] : x^2+upper q x^2 ≤ q)
    (by nlinarith [upper_circle hy] : y^2+upper q y^2 ≤ q) ha hb hab
  have hr : (a*x+b*y)^2 ≤ q := by
    nlinarith [sq_nonneg (a*upper q x+b*upper q y)]
  have hn : 0 ≤ a*upper q x+b*upper q y :=
    add_nonneg (mul_nonneg ha (upper_nonneg q x))
      (mul_nonneg hb (upper_nonneg q y))
  refine ⟨hr,?_⟩
  by_contra! hh
  have hs := square_strict_mono_nonneg (upper_nonneg q (a*x+b*y)) hh
  nlinarith [upper_circle hr]

theorem upper_mix_strict {q x y a b : ℝ} (hx : x^2 ≤ q) (hy : y^2 ≤ q)
    (hxy : x≠y) (ha : 0<a) (hb : 0<b) (hab : a+b=1) :
    a*upper q x+b*upper q y < upper q (a*x+b*y) := by
  have hd := disk_chord_strict
    (by nlinarith [upper_circle hx] : x^2+upper q x^2 ≤ q)
    (by nlinarith [upper_circle hy] : y^2+upper q y^2 ≤ q) hxy ha hb hab
  have hr := (upper_mix hx hy ha.le hb.le hab).1
  have hn : 0 ≤ a*upper q x+b*upper q y :=
    add_nonneg (mul_nonneg ha.le (upper_nonneg q x))
      (mul_nonneg hb.le (upper_nonneg q y))
  by_contra! hh
  have hs := square_mono_nonneg (upper_nonneg q (a*x+b*y)) hh
  nlinarith [upper_circle hr]

theorem Domain.height_lt_two {q u : ℝ} (hu : Domain q u) (hq : q<4) : u<2 := by
  nlinarith [hu.first_radicand,hu.height_nonneg,sq_nonneg (u-2)]

theorem Domain.lowerHeight_pos {q u : ℝ} (hu : Domain q u) (hq : q<4) :
    0<lowerHeight q u := by
  have hh := upper_lt_two hq hu.third_radicand
  dsimp [lowerHeight,topHeight]
  linarith

theorem Domain.topLeft_pos {q u : ℝ} (hu : Domain q u) (hq : q<4) :
    0<topLeft q u := by
  have hh := upper_lt_two hq hu.second_radicand
  dsimp [topLeft,topRight]
  linarith

/-- Positive radicals lie in the radical domain. -/
theorem domain_of_pos {q u : ℝ} (hu : 0 ≤ u) (hr : 0<lowerRight q u) (hU : 0<topRight q u)
    (hY : 0<topHeight q u) (hw : 0<lowerLeft q u) : Domain q u :=
  ⟨hu,sub_nonneg.mp (Real.sqrt_pos.mp hr).le,sub_nonneg.mp (Real.sqrt_pos.mp hU).le,
    sub_nonneg.mp (Real.sqrt_pos.mp hY).le,sub_nonneg.mp (Real.sqrt_pos.mp hw).le⟩

/-- Successive disk chords: the domain is convex, and the outer horizontal coordinates `r`, `w`
are concave and the lower height `v` convex in the position. -/
theorem mix_domain_and_bounds {q u₀ u₁ a b : ℝ} (hq : q<4)
    (h₀ : Domain q u₀) (h₁ : Domain q u₁)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    Domain q (a*u₀+b*u₁) ∧
    a*lowerRight q u₀+b*lowerRight q u₁ ≤ lowerRight q (a*u₀+b*u₁) ∧
    lowerHeight q (a*u₀+b*u₁) ≤ a*lowerHeight q u₀+b*lowerHeight q u₁ ∧
    a*lowerLeft q u₀+b*lowerLeft q u₁ ≤ lowerLeft q (a*u₀+b*u₁) := by
  have hr := upper_mix h₀.first_radicand h₁.first_radicand ha hb hab
  have hU := upper_mix h₀.second_radicand h₁.second_radicand ha hb hab
  have hlinear : a*(2-u₀)+b*(2-u₁)=2-(a*u₀+b*u₁) := by nlinarith [hab]
  rw [hlinear] at hU
  have hV : topLeft q (a*u₀+b*u₁) ≤ a*topLeft q u₀+b*topLeft q u₁ := by
    dsimp [topLeft,topRight]
    nlinarith [hU.2,hab]
  have hVm : 0 ≤ topLeft q (a*u₀+b*u₁) := by
    have hh := upper_lt_two hq hU.1
    dsimp [topLeft,topRight]
    linarith
  have hY := upper_mix h₀.third_radicand h₁.third_radicand ha hb hab
  have hVrad : topLeft q (a*u₀+b*u₁)^2 ≤ q := by
    exact le_trans (square_mono_nonneg hVm hV) hY.1
  have hYm : a*topHeight q u₀+b*topHeight q u₁ ≤ topHeight q (a*u₀+b*u₁) :=
    le_trans hY.2 (upper_antitone hVm hV)
  have hv : lowerHeight q (a*u₀+b*u₁) ≤
      a*lowerHeight q u₀+b*lowerHeight q u₁ := by
    dsimp [lowerHeight]
    nlinarith [hYm,hab]
  have hvm : 0 ≤ lowerHeight q (a*u₀+b*u₁) := by
    have hh := upper_lt_two hq hVrad
    dsimp [lowerHeight,topHeight]
    linarith
  have hw := upper_mix h₀.fourth_radicand h₁.fourth_radicand ha hb hab
  have hvrad : lowerHeight q (a*u₀+b*u₁)^2 ≤ q := by
    exact le_trans (square_mono_nonneg hvm hv) hw.1
  refine ⟨⟨add_nonneg (mul_nonneg ha h₀.height_nonneg)
    (mul_nonneg hb h₁.height_nonneg),hr.1,hU.1,hVrad,hvrad⟩,hr.2,hv,?_⟩
  exact le_trans hw.2 (upper_antitone hvm hv)

theorem domain_convex {q : ℝ} (hq : q<4) :
    Convex ℝ {u : ℝ | Domain q u} := by
  intro u₀ h₀ u₁ h₁ a b ha hb hab
  simpa only [smul_eq_mul,Set.mem_ofPred_eq] using (mix_domain_and_bounds hq h₀ h₁ ha hb hab).1

theorem unit_le_one {c s : ℝ} (hunit : c^2+s^2=1) : c ≤ 1 ∧ s ≤ 1 :=
  ⟨by nlinarith [sq_nonneg s,sq_nonneg (c-1)],by nlinarith [sq_nonneg c,sq_nonneg (s-1)]⟩

theorem components_pos {q c s u : ℝ} (hq : q<4) (hu : Domain q u)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1) :
    0<firstComponent q c s u ∧ 0<secondComponent q c s u := by
  have hr := upper_lt_two hq hu.first_radicand
  have hw := upper_lt_two hq hu.fourth_radicand
  have hv := hu.lowerHeight_pos hq
  have hcr := mul_pos hc (sub_pos.mpr hr)
  have hsw := mul_nonneg hs (sub_nonneg.mpr hw.le)
  have hcv := mul_pos hc hv
  have hsu' := mul_nonneg hs hu.height_nonneg
  constructor
  · dsimp [firstComponent,lowerRight]
    nlinarith
  · dsimp [secondComponent,lowerLeft]
    nlinarith

theorem firstComponent_mix_strict {q c s u₀ u₁ a b : ℝ}
    (h₀ : Domain q u₀) (h₁ : Domain q u₁) (hu : u₀≠u₁)
    (hc : 0<c) (ha : 0<a) (hb : 0<b) (hab : a+b=1) :
    firstComponent q c s (a*u₀+b*u₁) <
      a*firstComponent q c s u₀+b*firstComponent q c s u₁ := by
  have hr := upper_mix_strict h₀.first_radicand h₁.first_radicand hu ha hb hab
  have hcr := mul_lt_mul_of_pos_left hr hc
  have hbase : a*(2+c)+b*(2+c)=2+c := by rw [← add_mul,hab,one_mul]
  dsimp [firstComponent,lowerRight]
  nlinarith

theorem secondComponent_mix {q c s u₀ u₁ a b : ℝ} (hq : q<4)
    (h₀ : Domain q u₀) (h₁ : Domain q u₁)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    secondComponent q c s (a*u₀+b*u₁) ≤
      a*secondComponent q c s u₀+b*secondComponent q c s u₁ := by
  obtain ⟨_,_,hv,hw⟩ := mix_domain_and_bounds hq h₀ h₁ ha hb hab
  have hcv := mul_le_mul_of_nonneg_left hv hc
  have hsw := mul_le_mul_of_nonneg_left hw hs
  have hbase : a*(1+s)+b*(1+s)=1+s := by rw [← add_mul,hab,one_mul]
  dsimp [secondComponent]
  nlinarith

/-- The strict Jensen inequality for the defect on the whole radical domain. -/
theorem defect_mix_strict {q c s u₀ u₁ a b : ℝ} (hq : q<4)
    (h₀ : Domain q u₀) (h₁ : Domain q u₁) (hu : u₀≠u₁)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1)
    (ha : 0<a) (hb : 0<b) (hab : a+b=1) :
    defect q c s (a*u₀+b*u₁) < a*defect q c s u₀+b*defect q c s u₁ := by
  have hm := (mix_domain_and_bounds hq h₀ h₁ ha.le hb.le hab).1
  have hp := components_pos hq hm hc hcu hs hsu
  have h₁m := firstComponent_mix_strict (s:=s) h₀ h₁ hu hc ha hb hab
  have h₂m := secondComponent_mix hq h₀ h₁ hc.le hs ha.le hb.le hab
  have h₁sq : firstComponent q c s (a*u₀+b*u₁)^2 <
      (a*firstComponent q c s u₀+b*firstComponent q c s u₁)^2 := by
    exact square_strict_mono_nonneg hp.1.le h₁m
  have h₂sq : secondComponent q c s (a*u₀+b*u₁)^2 ≤
      (a*secondComponent q c s u₀+b*secondComponent q c s u₁)^2 := by
    exact square_mono_nonneg hp.2.le h₂m
  have hJ₁ := weighted_square_le
    (firstComponent q c s u₀) (firstComponent q c s u₁) ha.le hb.le hab
  have hJ₂ := weighted_square_le
    (secondComponent q c s u₀) (secondComponent q c s u₁) ha.le hb.le hab
  have hqsum : a*q+b*q=q := by rw [← add_mul,hab,one_mul]
  dsimp [defect]
  nlinarith

/-- For `q < 4`, `0 < c ≤ 1` and `0 ≤ s ≤ 1` the defect is strictly convex in the position on
the radical domain. -/
theorem strictConvexOn_defect {q c s : ℝ} (hq : q<4)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1) :
    StrictConvexOn ℝ {u : ℝ | Domain q u} (defect q c s) := by
  refine ⟨domain_convex hq,?_⟩
  intro u₀ h₀ u₁ h₁ hu a b ha hb hab
  simpa only [smul_eq_mul] using defect_mix_strict hq h₀ h₁ hu
    hc hcu hs hsu ha hb hab

/-- At a fixed tilt the defect has at most one minimum on the radical domain. -/
theorem minimizer_unique {q c s u₀ u₁ : ℝ} (hq : q<4)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1)
    (h₀ : Domain q u₀) (h₁ : Domain q u₁)
    (hm₀ : ∀ u, Domain q u → defect q c s u₀ ≤ defect q c s u)
    (hm₁ : ∀ u, Domain q u → defect q c s u₁ ≤ defect q c s u) : u₀=u₁ := by
  by_contra hu
  have hm := (mix_domain_and_bounds hq h₀ h₁
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).1
  have hj := defect_mix_strict hq h₀ h₁ hu hc hcu hs hsu
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2) (by norm_num)
  have hL := hm₀ _ hm
  have hR := hm₁ _ hm
  linarith

theorem defect_continuous (q c s : ℝ) : Continuous (defect q c s) := by
  unfold defect firstComponent secondComponent lowerRight lowerLeft lowerHeight topHeight
    topLeft topRight upper
  fun_prop

/-- The chart at `u = -y` gives the coordinates of a chain. -/
theorem coordinate_values {d : Coordinates} (hd : d.IsChain) :
    lowerRight d.q (-d.y)=d.x₁ ∧ topRight d.q (-d.y)=d.x₂ ∧
    topLeft d.q (-d.y)= -d.x₃ ∧ topHeight d.q (-d.y)=d.y₃ ∧
    lowerHeight d.q (-d.y)= -d.y₄ ∧ lowerLeft d.q (-d.y)= -d.x₄ := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hd.radicals
  have hr : lowerRight d.q (-d.y)=d.x₁ := by
    simpa [lowerRight,upper,neg_sq] using h₁.symm
  have hU : topRight d.q (-d.y)=d.x₂ := by
    rw [h₂,topRight,upper,show (2:ℝ)- -d.y=d.y+2 by ring]
  have hV : topLeft d.q (-d.y)= -d.x₃ := by
    rw [topLeft,hU]
    dsimp [Coordinates.x₃]
    ring
  have hY : topHeight d.q (-d.y)=d.y₃ := by
    rw [topHeight,hV]
    simpa [upper,neg_sq] using h₃.symm
  have hv : lowerHeight d.q (-d.y)= -d.y₄ := by
    rw [lowerHeight,hY]
    dsimp [Coordinates.y₄]
    ring
  have hw : lowerLeft d.q (-d.y)= -d.x₄ := by
    rw [lowerLeft,hv]
    dsimp [upper]
    rw [neg_sq,h₄]
    ring
  exact ⟨hr,hU,hV,hY,hv,hw⟩

theorem coordinate_domain {d : Coordinates} (hd : d.IsChain) (hy : d.y ≤ 0) :
    Domain d.q (-d.y) := by
  obtain ⟨_,_,hV,_,hv,_⟩ := coordinate_values hd
  refine ⟨by linarith,?_,?_,?_,?_⟩
  · nlinarith [hd.first_circle,sq_nonneg d.x₁]
  · nlinarith [hd.second_circle,sq_nonneg d.x₂]
  · rw [hV,neg_sq]
    nlinarith [hd.third_circle,sq_nonneg d.y₃]
  · rw [hv,neg_sq]
    nlinarith [hd.fourth_circle,sq_nonneg d.x₄]

theorem coordinate_defect {d : Coordinates} (hd : d.IsChain) :
    defect d.q d.c d.s (-d.y)=d.defect := by
  obtain ⟨hr,_,_,_,hv,hw⟩ := coordinate_values hd
  have h₁ : firstComponent d.q d.c d.s (-d.y)= -d.h₁ := by
    rw [firstComponent,hr]
    dsimp [Coordinates.h₁]
    ring
  have h₂ : secondComponent d.q d.c d.s (-d.y)= -d.h₂ := by
    rw [secondComponent,hv,hw]
    dsimp [Coordinates.h₂]
    ring
  rw [defect,h₁,h₂,Coordinates.defect]
  ring

/-! ### The defect decreases with the radius -/

theorem upper_radicand_strict {q₀ q₁ x₀ x₁ : ℝ}
    (h₀ : x₀^2 ≤ q₀) (h₁ : x₁^2 ≤ q₁)
    (hgap : q₀-x₀^2<q₁-x₁^2) : upper q₀ x₀<upper q₁ x₁ := by
  have hc₀ := upper_circle h₀
  have hc₁ := upper_circle h₁
  by_contra! hh
  have hs := square_mono_nonneg (upper_nonneg q₁ x₁) hh
  nlinarith

theorem upper_radius_strict {q₀ q₁ x : ℝ} (h : x^2 ≤ q₀) (hq : q₀<q₁) :
    upper q₀ x<upper q₁ x :=
  upper_radicand_strict h (h.trans hq.le) (by linarith)

/-- The radical domain grows with the radius, `r` and `w` increase and `v` decreases. -/
theorem domain_radius_inclusion {q₀ q₁ u : ℝ} (hq : q₀<q₁) (hqu : q₁<4)
    (h : Domain q₀ u) :
    Domain q₁ u ∧ lowerRight q₀ u<lowerRight q₁ u ∧
      lowerHeight q₁ u<lowerHeight q₀ u ∧ lowerLeft q₀ u<lowerLeft q₁ u := by
  have hfirst : u^2 ≤ q₁ := h.first_radicand.trans hq.le
  have hsecond : (2-u)^2 ≤ q₁ := h.second_radicand.trans hq.le
  have hr : lowerRight q₀ u<lowerRight q₁ u := upper_radius_strict h.first_radicand hq
  have hU : topRight q₀ u<topRight q₁ u := upper_radius_strict h.second_radicand hq
  have hV : topLeft q₁ u<topLeft q₀ u := by dsimp [topLeft]; linarith
  have hV₁ : 0 ≤ topLeft q₁ u := by
    have hh := upper_lt_two hqu hsecond
    dsimp [topLeft,topRight]
    linarith
  have hVs := square_mono_nonneg hV₁ hV.le
  have hthird : topLeft q₁ u^2 ≤ q₁ := hVs.trans (h.third_radicand.trans hq.le)
  have hY : topHeight q₀ u<topHeight q₁ u :=
    upper_radicand_strict h.third_radicand hthird (by linarith)
  have hv : lowerHeight q₁ u<lowerHeight q₀ u := by dsimp [lowerHeight]; linarith
  have hv₁ : 0 ≤ lowerHeight q₁ u := by
    have hh := upper_lt_two hqu hthird
    dsimp [lowerHeight,topHeight]
    linarith
  have hvs := square_mono_nonneg hv₁ hv.le
  have hfourth : lowerHeight q₁ u^2 ≤ q₁ := hvs.trans (h.fourth_radicand.trans hq.le)
  have hw : lowerLeft q₀ u<lowerLeft q₁ u :=
    upper_radicand_strict h.fourth_radicand hfourth (by linarith)
  exact ⟨⟨h.height_nonneg,hfirst,hsecond,hthird,hfourth⟩,hr,hv,hw⟩

theorem components_radius_strict {q₀ q₁ c s u : ℝ}
    (hq : q₀<q₁) (hqu : q₁<4) (h : Domain q₀ u) (hc : 0<c) (hs : 0 ≤ s) :
    firstComponent q₁ c s u<firstComponent q₀ c s u ∧
      secondComponent q₁ c s u<secondComponent q₀ c s u := by
  obtain ⟨_,hr,hv,hw⟩ := domain_radius_inclusion hq hqu h
  have hcr := mul_lt_mul_of_pos_left hr hc
  have hcv := mul_lt_mul_of_pos_left hv hc
  have hsw := mul_le_mul_of_nonneg_left hw.le hs
  constructor
  · dsimp [firstComponent]
    linarith
  · dsimp [secondComponent]
    linarith

/-- The squared norm `k₁² + k₂²` decreases strictly with the radius. -/
theorem defect_radius_strict {q₀ q₁ c s u : ℝ}
    (hq : q₀<q₁) (hqu : q₁<4) (h : Domain q₀ u)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1) :
    defect q₁ c s u+q₁<defect q₀ c s u+q₀ := by
  have hdom := (domain_radius_inclusion hq hqu h).1
  obtain ⟨hk₁,hk₂⟩ := components_pos hqu hdom hc hcu hs hsu
  obtain ⟨h₁,h₂⟩ := components_radius_strict hq hqu h hc hs
  have hs₁ := square_strict_mono_nonneg hk₁.le h₁
  have hs₂ := square_strict_mono_nonneg hk₂.le h₂
  dsimp [defect]
  linarith

/-- The defect decreases faster than the squared radius grows. -/
theorem defect_radius_decrease {q₀ q₁ c s u : ℝ}
    (hq : q₀<q₁) (hqu : q₁<4) (h : Domain q₀ u)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1) :
    defect q₁ c s u<defect q₀ c s u-(q₁-q₀) := by
  linarith [defect_radius_strict hq hqu h hc hcu hs hsu]

/-! ### The position derivative and the comparison at `87/100` -/

/-- The slope `p = -v'` of the lower height. -/
def slopeRatio (q u : ℝ) : ℝ :=
  (2-u)*topLeft q u/(topRight q u*topHeight q u)
/-- Half the position derivative of the defect. -/
def positionHalf (q c s u : ℝ) : ℝ :=
  firstComponent q c s u*(s+c*u/lowerRight q u)-
    secondComponent q c s u*slopeRatio q u*(c+s*lowerHeight q u/lowerLeft q u)

theorem upper_curve_deriv {q u : ℝ} {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' u) (hr : 0<upper q (f u)) :
    HasDerivAt (fun x => upper q (f x)) (-f u*f'/upper q (f u)) u := by
  have hrad : q-f u^2≠0 := ne_of_gt (Real.sqrt_pos.mp hr)
  refine (((hasDerivAt_const u q).fun_sub (hf.fun_pow 2)).sqrt hrad).congr_deriv ?_
  have hr' : Real.sqrt (q-f u^2)≠0 := ne_of_gt hr
  rw [show upper q (f u)=Real.sqrt (q-f u^2) from rfl]
  field_simp
  norm_num
  ring

theorem radical_derivatives {q u : ℝ} (hr : 0<lowerRight q u) (hU : 0<topRight q u)
    (hY : 0<topHeight q u) (hw : 0<lowerLeft q u) :
    HasDerivAt (lowerRight q) (-u/lowerRight q u) u ∧
    HasDerivAt (topRight q) ((2-u)/topRight q u) u ∧
    HasDerivAt (topLeft q) (-((2-u)/topRight q u)) u ∧
    HasDerivAt (topHeight q) (slopeRatio q u) u ∧
    HasDerivAt (lowerHeight q) (-slopeRatio q u) u ∧
    HasDerivAt (lowerLeft q) (lowerHeight q u*slopeRatio q u/lowerLeft q u) u := by
  have dr : HasDerivAt (lowerRight q) (-u/lowerRight q u) u :=
    (upper_curve_deriv (hasDerivAt_id' u) hr).congr_deriv (by rw [mul_one]; rfl)
  have dU : HasDerivAt (topRight q) ((2-u)/topRight q u) u :=
    (upper_curve_deriv ((hasDerivAt_id' u).const_sub 2) hU).congr_deriv (by
      rw [show upper q (2-u)=topRight q u from rfl]; ring)
  have dV : HasDerivAt (topLeft q) (-((2-u)/topRight q u)) u := dU.const_sub 3
  have dY : HasDerivAt (topHeight q) (slopeRatio q u) u :=
    (upper_curve_deriv dV hY).congr_deriv (by
      rw [show upper q (topLeft q u)=topHeight q u from rfl,slopeRatio]
      field_simp)
  have dv : HasDerivAt (lowerHeight q) (-slopeRatio q u) u := dY.const_sub 2
  have dw : HasDerivAt (lowerLeft q) (lowerHeight q u*slopeRatio q u/lowerLeft q u) u :=
    (upper_curve_deriv dv hw).congr_deriv (by
      rw [show upper q (lowerHeight q u)=lowerLeft q u from rfl]; ring)
  exact ⟨dr,dU,dV,dY,dv,dw⟩

theorem components_position_deriv {q c s u : ℝ} (hr : 0<lowerRight q u)
    (hU : 0<topRight q u) (hY : 0<topHeight q u) (hw : 0<lowerLeft q u) :
    HasDerivAt (firstComponent q c s) (s+c*u/lowerRight q u) u ∧
    HasDerivAt (secondComponent q c s)
      (-slopeRatio q u*(c+s*lowerHeight q u/lowerLeft q u)) u := by
  obtain ⟨dr,-,-,-,dv,dw⟩ := radical_derivatives hr hU hY hw
  exact ⟨(((dr.sub_const 1).const_mul c).const_sub 2).fun_add
      ((hasDerivAt_id' u).const_mul s) |>.congr_deriv (by ring),
    ((dv.const_mul c).const_add 1).fun_sub ((dw.sub_const 1).const_mul s)
      |>.congr_deriv (by ring)⟩

theorem position_deriv {q c s u : ℝ}
    (hr : 0<lowerRight q u) (hU : 0<topRight q u)
    (hY : 0<topHeight q u) (hw : 0<lowerLeft q u) :
    HasDerivAt (defect q c s) (2*positionHalf q c s u) u := by
  obtain ⟨dk₁,dk₂⟩ := components_position_deriv (c:=c) (s:=s) hr hU hY hw
  exact (((dk₁.fun_pow 2).fun_add (dk₂.fun_pow 2)).sub_const q).congr_deriv (by
    rw [positionHalf]; push_cast; ring)

/-- `u/r` at `u = 87/100`. -/
def comparisonX (q : ℝ) : ℝ := 87/100/lowerRight q (87/100)
/-- `v/w` at `u = 87/100`. -/
def comparisonY (q : ℝ) : ℝ := lowerHeight q (87/100)/lowerLeft q (87/100)

/-- Rational bounds on the radicals, on `p` and on the two ratios at `u = 87/100`. -/
structure ComparisonBounds (q : ℝ) : Prop where
  r_lower : 1773/1000<lowerRight q (87/100)
  U_lower : 1619/1000<topRight q (87/100)
  Y_lower : 1411/1000<topHeight q (87/100)
  v_lower : 576/1000<lowerHeight q (87/100)
  w_lower : 1885/1000<lowerLeft q (87/100)
  w_upper : lowerLeft q (87/100)<1894/1000
  p_lower : 671/1000<slopeRatio q (87/100)
  p_upper : slopeRatio q (87/100)<684/1000
  x_lower : 489/1000<comparisonX q
  x_upper : comparisonX q<491/1000
  y_lower : 3/10<comparisonY q
  y_upper : comparisonY q<5/16

theorem sqrt_between {x a b : ℝ} (hb : 0 ≤ b)
    (hl : a^2<x) (hu : x<b^2) : a<Real.sqrt x ∧ Real.sqrt x<b := by
  have hx : 0 ≤ x := by nlinarith [sq_nonneg a]
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  constructor
  · by_contra! hh
    have hsq := square_mono_nonneg hn hh
    nlinarith
  · by_contra! hh
    have hsq := square_mono_nonneg hb hh
    nlinarith

/-- Successive square comparisons at the position `87/100`, uniform in the radius. -/
theorem comparison_bounds {q : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500) : ComparisonBounds q := by
  have hr : 1773/1000<lowerRight q (87/100) ∧ lowerRight q (87/100)<1778/1000 := by
    apply sqrt_between (by norm_num) <;> nlinarith
  have hU : 1619/1000<topRight q (87/100) ∧ topRight q (87/100)<1625/1000 := by
    apply sqrt_between (by norm_num) <;> nlinarith
  have hV : 1375/1000<topLeft q (87/100) ∧ topLeft q (87/100)<1381/1000 := by
    dsimp [topLeft]
    constructor <;> linarith [hU.1,hU.2]
  have hY : 1411/1000<topHeight q (87/100) ∧ topHeight q (87/100)<1424/1000 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ topLeft q (87/100)) hV.2.le
      nlinarith
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1375/1000) hV.1.le
      nlinarith
  have hv : 576/1000<lowerHeight q (87/100) ∧ lowerHeight q (87/100)<589/1000 := by
    dsimp [lowerHeight]
    constructor <;> linarith [hY.1,hY.2]
  have hw : 1885/1000<lowerLeft q (87/100) ∧ lowerLeft q (87/100)<1894/1000 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ lowerHeight q (87/100)) hv.2.le
      nlinarith
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 576/1000) hv.1.le
      nlinarith
  have hUp : 0<topRight q (87/100) := by linarith [hU.1]
  have hYp : 0<topHeight q (87/100) := by linarith [hY.1]
  have hprodL : (1619/1000:ℝ)*(1411/1000) ≤ topRight q (87/100)*topHeight q (87/100) :=
    mul_le_mul hU.1.le hY.1.le (by norm_num) hUp.le
  have hprodU : topRight q (87/100)*topHeight q (87/100) ≤ (1625/1000:ℝ)*(1424/1000) :=
    mul_le_mul hU.2.le hY.2.le hYp.le (by norm_num)
  have hp : 671/1000<slopeRatio q (87/100) ∧ slopeRatio q (87/100)<684/1000 := by
    dsimp only [slopeRatio]
    constructor
    · rw [lt_div_iff₀ (mul_pos hUp hYp)]
      have hs := mul_le_mul_of_nonneg_left hprodU (by norm_num : (0:ℝ) ≤ 671/1000)
      nlinarith [hV.1]
    · rw [div_lt_iff₀ (mul_pos hUp hYp)]
      have hs := mul_le_mul_of_nonneg_left hprodL (by norm_num : (0:ℝ) ≤ 684/1000)
      nlinarith [hV.2]
  have hx : 489/1000<comparisonX q ∧ comparisonX q<491/1000 := by
    dsimp only [comparisonX]
    constructor
    · rw [lt_div_iff₀ (by linarith : 0<lowerRight q (87/100))]
      nlinarith [hr.2]
    · rw [div_lt_iff₀ (by linarith : 0<lowerRight q (87/100))]
      nlinarith [hr.1]
  have hy : 3/10<comparisonY q ∧ comparisonY q<5/16 := by
    dsimp only [comparisonY]
    constructor
    · rw [lt_div_iff₀ (by linarith : 0<lowerLeft q (87/100))]
      nlinarith [hw.2,hv.1]
    · rw [div_lt_iff₀ (by linarith : 0<lowerLeft q (87/100))]
      nlinarith [hw.1,hv.2]
  exact ⟨hr.1,hU.1,hY.1,hv.1,hw.1,hw.2,hp.1,hp.2,hx.1,hx.2,hy.1,hy.2⟩

/-- The coefficient of `L` in `comparisonPolynomial`. -/
def coefficientLc (q : ℝ) : ℝ := 2*comparisonX q-slopeRatio q (87/100)
/-- The coefficient of `h L` in `comparisonPolynomial`. -/
def coefficientLs (q : ℝ) : ℝ := 2-slopeRatio q (87/100)*comparisonY q
/-- Minus the constant term of `comparisonPolynomial`. -/
def coefficientQc (q : ℝ) : ℝ :=
  (lowerRight q (87/100)-1)*comparisonX q+
    slopeRatio q (87/100)*lowerHeight q (87/100)
/-- The coefficient of `h` in `comparisonPolynomial`. -/
def coefficientJ (q : ℝ) : ℝ :=
  87/100*comparisonX q-(lowerRight q (87/100)-1)-
    slopeRatio q (87/100)*lowerHeight q (87/100)*comparisonY q+
      slopeRatio q (87/100)*(lowerLeft q (87/100)-1)
/-- The coefficient of `h²` in `comparisonPolynomial`. -/
def coefficientQs (q : ℝ) : ℝ :=
  87/100+slopeRatio q (87/100)*(lowerLeft q (87/100)-1)*comparisonY q

/-- The five coefficients of `positionHalf (87/100)` as a quadratic in `s/c`. -/
theorem comparison_coefficients {q : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500) :
    coefficientLc q ≤ 5/16 ∧ coefficientLs q ≤ 9/5 ∧ 61/80 ≤ coefficientQc q ∧
      coefficientJ q ≤ 3/20 ∧ coefficientQs q ≤ 17/16 := by
  have h := comparison_bounds hql hqu
  have hp : 0 ≤ slopeRatio q (87/100) := by linarith [h.p_lower]
  have hv : 0 ≤ lowerHeight q (87/100) := by linarith [h.v_lower]
  have hy : 0 ≤ comparisonY q := by linarith [h.y_lower]
  have hpy : (671/1000:ℝ)*(3/10) ≤ slopeRatio q (87/100)*comparisonY q :=
    mul_le_mul h.p_lower.le h.y_lower.le (by norm_num) hp
  have hrx : (773/1000:ℝ)*(489/1000) ≤ (lowerRight q (87/100)-1)*comparisonX q :=
    mul_le_mul (by linarith [h.r_lower]) h.x_lower.le (by norm_num)
      (by linarith [h.r_lower])
  have hpv : (671/1000:ℝ)*(576/1000) ≤ slopeRatio q (87/100)*lowerHeight q (87/100) :=
    mul_le_mul h.p_lower.le h.v_lower.le (by norm_num) hp
  have hpvy : (671/1000:ℝ)*(576/1000)*(3/10) ≤
      slopeRatio q (87/100)*lowerHeight q (87/100)*comparisonY q :=
    mul_le_mul hpv h.y_lower.le (by norm_num) (mul_nonneg hp hv)
  have hpw : slopeRatio q (87/100)*(lowerLeft q (87/100)-1) ≤ (684/1000:ℝ)*(894/1000) :=
    mul_le_mul h.p_upper.le (by linarith [h.w_upper])
      (by linarith [h.w_lower]) (by norm_num)
  have hpwy : slopeRatio q (87/100)*(lowerLeft q (87/100)-1)*comparisonY q ≤
      (684/1000:ℝ)*(894/1000)*(5/16) :=
    mul_le_mul hpw h.y_upper.le hy (by norm_num)
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp only [coefficientLc]
    linarith [h.x_upper,h.p_lower]
  · dsimp only [coefficientLs]
    linarith
  · dsimp only [coefficientQc]
    linarith
  · dsimp only [coefficientJ]
    nlinarith [h.x_upper,h.r_lower]
  · dsimp only [coefficientQs]
    linarith

/-- `positionHalf` at `u = 87/100` divided by `c²`, in `h = s/c` and `L = 1/c`
(`comparison_position_identity`). -/
def comparisonPolynomial (q h L : ℝ) : ℝ :=
  L*coefficientLc q-coefficientQc q+h*(L*coefficientLs q+coefficientJ q)+
    h^2*coefficientQs q

/-- `comparisonPolynomial ≤ -81/20000` for `0 ≤ h ≤ 1/5` and `0 ≤ L ≤ 51/50`. -/
theorem comparisonPolynomial_bound {q h L : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hh : 0 ≤ h) (hhu : h ≤ 1/5) (hL : 0 ≤ L) (hLu : L ≤ 51/50) :
    comparisonPolynomial q h L ≤ -(81/20000) := by
  obtain ⟨hLc,hLs,hQc,hJ,hQs⟩ := comparison_coefficients hql hqu
  have h₀ : L*coefficientLc q ≤ (51/50:ℝ)*(5/16) :=
    (mul_le_mul_of_nonneg_left hLc hL).trans
      (mul_le_mul_of_nonneg_right hLu (by norm_num))
  have h₁ : L*coefficientLs q+coefficientJ q ≤ (51/50:ℝ)*(9/5)+3/20 := by
    have h := (mul_le_mul_of_nonneg_left hLs hL).trans
      (mul_le_mul_of_nonneg_right hLu (by norm_num))
    linarith
  have h₂ : h*(L*coefficientLs q+coefficientJ q) ≤
      (1/5:ℝ)*((51/50)*(9/5)+3/20) :=
    (mul_le_mul_of_nonneg_left h₁ hh).trans
      (mul_le_mul_of_nonneg_right hhu (by norm_num))
  have h₃ : h^2*coefficientQs q ≤ (1/25:ℝ)*(17/16) := by
    have hs : h^2 ≤ (1/25:ℝ) := by nlinarith [square_mono_nonneg hh hhu]
    exact (mul_le_mul_of_nonneg_left hQs (sq_nonneg h)).trans
      (mul_le_mul_of_nonneg_right hs (by norm_num))
  dsimp only [comparisonPolynomial]
  linarith

theorem scaled_position_identity (r v w p x y u c s : ℝ) (hc : c≠0) :
    (2-c*(r-1)+s*u)*(s+c*x)-(1+c*v-s*(w-1))*p*(c+s*y) =
    c^2*((1/c)*(2*x-p)-((r-1)*x+p*v)+
      (s/c)*((1/c)*(2-p*y)+(u*x-(r-1)-p*v*y+p*(w-1)))+
        (s/c)^2*(u+p*(w-1)*y)) := by
  field_simp
  ring

theorem comparison_position_identity {q c s : ℝ} (hc : c≠0) :
    positionHalf q c s (87/100)=c^2*comparisonPolynomial q (s/c) (1/c) := by
  have h := scaled_position_identity
    (lowerRight q (87/100)) (lowerHeight q (87/100))
    (lowerLeft q (87/100)) (slopeRatio q (87/100))
    (comparisonX q) (comparisonY q) (87/100) c s hc
  simpa [positionHalf,comparisonPolynomial,coefficientLc,coefficientLs,coefficientQc,
    coefficientJ,coefficientQs,comparisonX,comparisonY,firstComponent,secondComponent,
    div_eq_mul_inv,mul_assoc] using h

/-- `positionHalf < 0` at `u = 87/100` throughout the strip. -/
theorem comparison_position_negative {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1) :
    positionHalf q c s (87/100)<0 := by
  have hh : 0 ≤ s/c := div_nonneg hs hc.le
  have hL : 0 ≤ (1:ℝ)/c := (div_pos (by norm_num) hc).le
  have hsq : ((1:ℝ)/c)^2=1+(s/c)^2 := by
    field_simp
    nlinarith
  have hh2 : (s/c)^2 ≤ (1/25:ℝ) := by
    nlinarith [square_mono_nonneg hh ht]
  have hLu : (1:ℝ)/c ≤ 51/50 := by
    by_contra! hbad
    have hbig := square_strict_mono_nonneg (by norm_num : (0:ℝ) ≤ 51/50) hbad
    nlinarith
  have hb := comparisonPolynomial_bound hql hqu hh ht hL hLu
  rw [comparison_position_identity (ne_of_gt hc)]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos hc) (by linarith)

/-- In the strip a critical position lies to the right of `87/100`. -/
theorem stationary_position_lower {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1)
    (hu : Domain q u) (hstat : HasDerivAt (defect q c s) 0 u) : 87/100<u := by
  have hq : q<4 := by linarith
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  have hconv := strictConvexOn_defect hq hc hcu hs hsu
  have hb := comparison_bounds hql hqu
  have hr : 0<lowerRight q (87/100) := lt_trans (by norm_num) hb.r_lower
  have hU : 0<topRight q (87/100) := lt_trans (by norm_num) hb.U_lower
  have hY : 0<topHeight q (87/100) := lt_trans (by norm_num) hb.Y_lower
  have hw : 0<lowerLeft q (87/100) := lt_trans (by norm_num) hb.w_lower
  have hcomp := domain_of_pos (by norm_num) hr hU hY hw
  have hd := position_deriv (c:=c) (s:=s) hr hU hY hw
  have hn := comparison_position_negative hql hqu hc hs ht hunit
  by_contra! hle
  rcases lt_or_eq_of_le hle with hlt | rfl
  · have h₁ := hconv.lt_slope_of_hasDerivAt hu hcomp hlt hstat
    have h₂ := hconv.slope_lt_of_hasDerivAt hu hcomp hlt hd
    linarith
  · have he := hstat.unique hd
    linarith

/-- A critical position is the global minimum at its tilt on the whole radical domain. -/
theorem stationary_global_minimum {q c s u : ℝ} (hq : q<4)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1)
    (hu : Domain q u) (hstat : HasDerivAt (defect q c s) 0 u) :
    ∀ v, Domain q v → defect q c s u ≤ defect q c s v := by
  have hconv := (strictConvexOn_defect hq hc hcu hs hsu).convexOn
  intro v hv
  rcases lt_trichotomy u v with hlt | rfl | hlt
  · have h := hconv.le_slope_of_hasDerivAt hu hv hlt hstat
    rw [slope_def_field,le_div_iff₀ (sub_pos.mpr hlt)] at h
    linarith
  · rfl
  · have h := hconv.slope_le_of_hasDerivAt hv hu hlt hstat
    rw [slope_def_field,div_le_iff₀ (sub_pos.mpr hlt)] at h
    linarith

/-- In the chart `2 positionHalf` is minus `positionDerivative`, since `u = -y`. -/
theorem coordinate_positionHalf {d : Coordinates} (hd : d.IsChain) :
    2*positionHalf d.q d.c d.s (-d.y)= -d.positionDerivative := by
  obtain ⟨hr,hU,hV,hY,hv,hw⟩ := coordinate_values hd
  have hp : slopeRatio d.q (-d.y)= -d.y₄deriv := by
    rw [slopeRatio,hV,hU,hY]
    dsimp [Coordinates.y₄deriv]
    field_simp [ne_of_gt hd.x₂_pos,ne_of_gt hd.y₃_pos]
    ring
  have hfirst : firstComponent d.q d.c d.s (-d.y)= -d.h₁ := by
    rw [firstComponent,hr]
    dsimp [Coordinates.h₁]
    ring
  have hsecond : secondComponent d.q d.c d.s (-d.y)= -d.h₂ := by
    rw [secondComponent,hv,hw]
    dsimp [Coordinates.h₂]
    ring
  rw [positionHalf,hfirst,hsecond,hr,hv,hw,hp]
  dsimp [Coordinates.positionDerivative,Coordinates.h₁deriv,Coordinates.h₂deriv]
  field_simp [ne_of_gt hd.x₁_pos,ne_of_lt hd.x₄_neg]
  ring

/-- The tilt of a stationary chain: `0 < c`, `0 ≤ s`, `s/c ≤ 1/5`. -/
theorem stationary_tilt {d : Coordinates} (hd : d.IsStationary) :
    0<d.c ∧ 0 ≤ d.s ∧ d.s/d.c ≤ 1/5 := by
  have hc : 0<d.c :=
    halfAngleCos_pos (by rw [abs_lt]; constructor <;> linarith [hd.z_pos,hd.z_lt_one])
  have hden : 0<1-d.z^2 := by nlinarith [hd.z_pos,hd.z_lt_one]
  have he : d.s/d.c=2*d.z/(1-d.z^2) := by
    dsimp [Coordinates.c,Coordinates.s,halfAngleCos,halfAngleSin]
    field_simp
  exact ⟨hc,(halfAngleSin_pos hd.z_pos).le,he ▸ hd.tilt_range.le⟩

/-- A stationary chain has `87/100 < -y`. -/
theorem stationary_coordinate_lower {d : Coordinates} (hd : d.IsStationary) :
    87/100< -d.y := by
  obtain ⟨hc,hs,ht⟩ := stationary_tilt hd
  have hdom := coordinate_domain hd.toIsChain (by linarith [hd.y_upper])
  obtain ⟨hr,hU,_,hY,_,hw⟩ := coordinate_values hd.toIsChain
  have hp := position_deriv (q:=d.q) (c:=d.c) (s:=d.s) (u:=-d.y)
    (by rw [hr]; exact hd.x₁_pos) (by rw [hU]; exact hd.x₂_pos)
    (by rw [hY]; exact hd.y₃_pos) (by rw [hw]; linarith [hd.x₄_neg])
  rw [coordinate_positionHalf hd.toIsChain,hd.position_stationary,neg_zero] at hp
  exact stationary_position_lower hd.q_lower hd.q_upper hc hs ht d.unit hdom hp

/-! ### The tilt derivatives -/

/-- The tilt derivative of `k₁` (`firstComponent_angle_deriv`). -/
def firstTilt (q c s u : ℝ) : ℝ := s*(lowerRight q u-1)+c*u
/-- The tilt derivative of `k₂` (`secondComponent_angle_deriv`). -/
def secondTilt (q c s u : ℝ) : ℝ := -s*lowerHeight q u-c*(lowerLeft q u-1)
/-- The tilt derivative of the defect (`defect_angle_deriv`). -/
def tiltFirst (q c s u : ℝ) : ℝ :=
  2*(firstComponent q c s u*firstTilt q c s u+
    secondComponent q c s u*secondTilt q c s u)
/-- The second tilt derivative of the defect (`defect_angle_second_deriv`). -/
def tiltSecond (q c s u : ℝ) : ℝ :=
  2*(firstTilt q c s u^2+secondTilt q c s u^2+
    firstComponent q c s u*(2-firstComponent q c s u)+
    secondComponent q c s u*(1-secondComponent q c s u))

theorem firstComponent_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => firstComponent q (Real.cos x) (Real.sin x) u)
      (firstTilt q (Real.cos t) (Real.sin t) u) t :=
  (((Real.hasDerivAt_cos t).mul_const (lowerRight q u-1)).const_sub 2).fun_add
    ((Real.hasDerivAt_sin t).mul_const u) |>.congr_deriv (by rw [firstTilt]; ring)

theorem secondComponent_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => secondComponent q (Real.cos x) (Real.sin x) u)
      (secondTilt q (Real.cos t) (Real.sin t) u) t :=
  (((Real.hasDerivAt_cos t).mul_const (lowerHeight q u)).const_add 1).fun_sub
    ((Real.hasDerivAt_sin t).mul_const (lowerLeft q u-1))

theorem firstTilt_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => firstTilt q (Real.cos x) (Real.sin x) u)
      (2-firstComponent q (Real.cos t) (Real.sin t) u) t :=
  ((Real.hasDerivAt_sin t).mul_const (lowerRight q u-1)).fun_add
    ((Real.hasDerivAt_cos t).mul_const u) |>.congr_deriv (by rw [firstComponent]; ring)

theorem secondTilt_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => secondTilt q (Real.cos x) (Real.sin x) u)
      (1-secondComponent q (Real.cos t) (Real.sin t) u) t :=
  ((Real.hasDerivAt_sin t).fun_neg.mul_const (lowerHeight q u)).fun_sub
    ((Real.hasDerivAt_cos t).mul_const (lowerLeft q u-1)) |>.congr_deriv
      (by rw [secondComponent]; ring)

theorem defect_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => defect q (Real.cos x) (Real.sin x) u)
      (tiltFirst q (Real.cos t) (Real.sin t) u) t :=
  (((firstComponent_angle_deriv q u t).fun_pow 2).fun_add
    ((secondComponent_angle_deriv q u t).fun_pow 2)).sub_const q |>.congr_deriv
      (by rw [tiltFirst]; push_cast; ring)

theorem defect_angle_second_deriv (q u t : ℝ) :
    HasDerivAt (fun x => tiltFirst q (Real.cos x) (Real.sin x) u)
      (tiltSecond q (Real.cos t) (Real.sin t) u) t :=
  (((firstComponent_angle_deriv q u t).fun_mul (firstTilt_angle_deriv q u t)).fun_add
    ((secondComponent_angle_deriv q u t).fun_mul (secondTilt_angle_deriv q u t))).const_mul 2
      |>.congr_deriv (by rw [tiltSecond]; ring)

/-- In the chart `tiltFirst` is `tiltDerivative`. -/
theorem coordinate_tiltFirst {d : Coordinates} (hd : d.IsChain) :
    tiltFirst d.q d.c d.s (-d.y)=d.tiltDerivative := by
  obtain ⟨hr,_,_,_,hv,hw⟩ := coordinate_values hd
  rw [tiltFirst,firstComponent,secondComponent,firstTilt,secondTilt,hr,hv,hw,
    Coordinates.tiltDerivative,Coordinates.h₁,Coordinates.h₂]
  ring

/-! ### The fifth corner at a position minimum -/

/-- The trial position `u = 15/16` lies in the radical domain, with bounds on `r`, `v` and `w`. -/
theorem normTrial_bounds {q : ℝ} (hql : (79/40:ℝ)^2 ≤ q) (hqu : q<4) :
    Domain q (15/16) ∧ 1738/1000<lowerRight q (15/16) ∧
      lowerHeight q (15/16)<546/1000 ∧ 1898/1000<lowerLeft q (15/16) := by
  have hr : 1738/1000<lowerRight q (15/16) ∧ lowerRight q (15/16)<2 := by
    apply sqrt_between (by norm_num) <;> nlinarith
  have hU : 1664/1000<topRight q (15/16) ∧ topRight q (15/16)<2 := by
    apply sqrt_between (by norm_num) <;> nlinarith
  have hV : 0<topLeft q (15/16) ∧ topLeft q (15/16)<1336/1000 := by
    dsimp [topLeft]
    constructor <;> linarith [hU.1,hU.2]
  have hY : 1454/1000<topHeight q (15/16) ∧ topHeight q (15/16)<2 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg hV.1.le hV.2.le
      nlinarith
    · nlinarith [sq_nonneg (topLeft q (15/16))]
  have hv : 0<lowerHeight q (15/16) ∧ lowerHeight q (15/16)<546/1000 := by
    dsimp [lowerHeight]
    constructor <;> linarith [hY.1,hY.2]
  have hw : 1898/1000<lowerLeft q (15/16) ∧ lowerLeft q (15/16)<2 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg hv.1.le hv.2.le
      nlinarith
    · nlinarith [sq_nonneg (lowerHeight q (15/16))]
  exact ⟨domain_of_pos (by norm_num) (by linarith [hr.1]) (by linarith [hU.1])
    (by linarith [hY.1]) (by linarith [hw.1]),hr.1,hv.2,hw.1⟩

/-- `c ≥ 1 - h²/2` when `c > 0` and `c² (1 + h²) = 1`. -/
theorem cosine_from_tangent_lower {c h : ℝ} (hc : 0<c)
    (hunit : c^2*(1+h^2)=1) : 1-h^2/2 ≤ c := by
  have hc2 : c^2 ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg h)]
  have hcu : c ≤ 1 := by nlinarith [sq_nonneg (c-1)]
  have hfactor : 0 ≤ 1+c-2*c^2 := by
    have hh := mul_nonneg (by linarith : 0 ≤ 1-c) (by linarith : 0 ≤ 2*c+1)
    nlinarith
  have hprod := mul_nonneg (sq_nonneg h) hfactor
  have he : (1+c)*(h^2-2+2*c)=h^2*(1+c-2*c^2)+2*(c^2*(1+h^2)-1) := by ring
  have hnon : 0 ≤ (1+c)*(h^2-2+2*c) := by rw [he,hunit]; nlinarith
  have hd : 0 ≤ h^2-2+2*c := by
    by_contra! hh
    exact (not_lt_of_ge hnon) (mul_neg_of_pos_of_neg (by linarith) hh)
  linarith

/-- A cubic in `h = s/c`: for `0 ≤ h ≤ 1/5` it bounds `k₁² + k₂²` at `u = 15/16` from above and
is less than `4` (`trial_upper_norm`, `trialPolynomial_lt_four`). -/
def trialPolynomial (h : ℝ) : ℝ :=
  5+2*(1-h^2/2)*(-(93/100)+h*(977/1000))+
    (369/500-h*(15/16))^2+(273/500-h*(449/500))^2

/-- The cubic lies below its chord on `[0, 1/5]`. -/
theorem trialPolynomial_chord {h : ℝ} (hh : 0 ≤ h) (hhu : h ≤ 1/5) :
    trialPolynomial h ≤ (1-5*h)*trialPolynomial 0+5*h*trialPolynomial (1/5) := by
  let C : ℝ := 93/100+(15/16)^2+(449/500)^2
  have he : (1-5*h)*trialPolynomial 0+5*h*trialPolynomial (1/5)-trialPolynomial h =
      h*(1/5-h)*(C-(977/1000)*(h+1/5)) := by
    dsimp [trialPolynomial,C]
    ring
  have hC : 0 ≤ C-(977/1000)*(h+1/5) := by
    dsimp [C]
    nlinarith
  have hn := mul_nonneg (mul_nonneg hh (by linarith : 0 ≤ 1/5-h)) hC
  linarith

theorem trialPolynomial_lt_four {h : ℝ} (hh : 0 ≤ h) (hhu : h ≤ 1/5) :
    trialPolynomial h<4 := by
  have hc := trialPolynomial_chord hh hhu
  have he : trialPolynomial 0 ≤ trialPolynomial (1/5) := by norm_num [trialPolynomial]
  have hlast : trialPolynomial (1/5)<4 := by norm_num [trialPolynomial]
  have hp := mul_nonneg (by linarith : 0 ≤ 1-5*h) (sub_nonneg.mpr he)
  nlinarith

theorem trial_upper_norm {c h : ℝ} (hc : 0<c) (hh : 0 ≤ h) (hhu : h ≤ 1/5)
    (hunit : c^2*(1+h^2)=1) :
    (2+c*(-(369/500)+h*(15/16)))^2+
      (1+c*(273/500-h*(449/500)))^2<4 := by
  let L : ℝ := -(93/100)+h*(977/1000)
  let Q : ℝ := (369/500-h*(15/16))^2+(273/500-h*(449/500))^2
  have hL : L<0 := by dsimp [L]; linarith
  have hQ : 0 ≤ Q := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hc2 : c^2 ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg h)]
  have hcl := cosine_from_tangent_lower hc hunit
  have hLc : c*L ≤ (1-h^2/2)*L := mul_le_mul_of_nonpos_right hcl hL.le
  have hQc := mul_le_mul_of_nonneg_right hc2 hQ
  have hnorm : (2+c*(-(369/500)+h*(15/16)))^2+
      (1+c*(273/500-h*(449/500)))^2=5+2*c*L+c^2*Q := by
    dsimp [L,Q]
    ring
  have hbound : 5+2*c*L+c^2*Q ≤ trialPolynomial h := by
    have e : trialPolynomial h=5+2*(1-h^2/2)*L+Q := by
      dsimp only [trialPolynomial,L,Q]
      ring
    rw [e]
    linarith
  rw [hnorm]
  exact hbound.trans_lt (trialPolynomial_lt_four hh hhu)

theorem normTrial_norm_lt_four {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q<4)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1) :
    firstComponent q c s (15/16)^2+secondComponent q c s (15/16)^2<4 := by
  obtain ⟨hdom,hr,hv,hw⟩ := normTrial_bounds hql hqu
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  obtain ⟨hk₁,hk₂⟩ := components_pos hqu hdom hc hcu hs hsu
  have hcs : c*(s/c)=s := by field_simp [ne_of_gt hc]
  have hh : 0 ≤ s/c := div_nonneg hs hc.le
  have hquarter : c^2*(1+(s/c)^2)=1 := by
    field_simp [ne_of_gt hc]
    nlinarith
  have h₁ : firstComponent q c s (15/16) ≤ 2+c*(-(369/500)+(s/c)*(15/16)) := by
    have hm := mul_le_mul_of_nonneg_left hr.le hc.le
    dsimp [firstComponent]
    nlinarith
  have h₂ : secondComponent q c s (15/16) ≤ 1+c*(273/500-(s/c)*(449/500)) := by
    have hm₁ := mul_le_mul_of_nonneg_left hv.le hc.le
    have hm₂ := mul_le_mul_of_nonneg_left hw.le hs
    dsimp [secondComponent]
    nlinarith
  have hs₁ := square_mono_nonneg hk₁.le h₁
  have hs₂ := square_mono_nonneg hk₂.le h₂
  have htrial := trial_upper_norm hc hh ht hquarter
  linarith

/-- `k₁² + k₂² < 4` at every position minimum. -/
theorem position_minimum_norm_lt_four {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q<4)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1)
    (hmin : ∀ v, Domain q v → defect q c s u ≤ defect q c s v) :
    firstComponent q c s u^2+secondComponent q c s u^2<4 := by
  have hb := normTrial_norm_lt_four hql hqu hc hs ht hunit
  have hm := hmin (15/16) (normTrial_bounds hql hqu).1
  dsimp [defect] at hm
  linarith

/-- `k₁² + k₂² < 4` at every critical position. -/
theorem position_stationary_norm_lt_four {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q<4)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1)
    (hu : Domain q u) (hstat : HasDerivAt (defect q c s) 0 u) :
    firstComponent q c s u^2+secondComponent q c s u^2<4 := by
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  exact position_minimum_norm_lt_four hql hqu hc hs ht hunit
    (stationary_global_minimum hqu hc hcu hs hsu hu hstat)

end SquaresInCircles.Eight.Stationary.FiveCornerGeometry
end
end
end

section
@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Stationary.FiveCornerGeometry

/-! ### The strip `87/100 ≤ u ≤ 1` -/

/-- The strip `(79/40)² ≤ q ≤ 9789/2500`, `87/100 ≤ u ≤ 1`. -/
structure CriticalStrip (q u : ℝ) : Prop where
  q_lower : (79/40:ℝ)^2 ≤ q
  q_upper : q ≤ 9789/2500
  u_lower : 87/100 ≤ u
  u_upper : u ≤ 1

/-- Rational bounds on the radicals and on `p` throughout the strip. -/
structure StripBounds (q u : ℝ) : Prop where
  domain : Domain q u
  r_lower : 17/10<lowerRight q u
  r_upper : lowerRight q u<16/9
  U_lower : 1619/1000<topRight q u
  V_lower : 1292/1000<topLeft q u
  V_upper : topLeft q u<1381/1000
  Y_lower : 1411/1000<topHeight q u
  Y_upper : topHeight q u<3/2
  v_lower : 1/2<lowerHeight q u
  v_upper : lowerHeight q u<589/1000
  w_lower : 1885/1000<lowerLeft q u
  w_upper : lowerLeft q u<48/25
  p_lower : 1/2<slopeRatio q u

/-- The circle equations give the bounds of `StripBounds`. -/
theorem CriticalStrip.bounds {q u : ℝ} (h : CriticalStrip q u) : StripBounds q u := by
  have hu : 0 ≤ u := by linarith [h.u_lower]
  have hA : 1 ≤ 2-u ∧ 2-u ≤ 113/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hr : 17/10<lowerRight q u ∧ lowerRight q u<16/9 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg hu h.u_upper
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 87/100) h.u_lower
      nlinarith [h.q_upper]
  have hU : 1619/1000<topRight q u ∧ topRight q u<1708/1000 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ 2-u) hA.2
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1) hA.1
      nlinarith [h.q_upper]
  have hV : 1292/1000<topLeft q u ∧ topLeft q u<1381/1000 := by
    dsimp [topLeft]
    constructor <;> linarith [hU.1,hU.2]
  have hY : 1411/1000<topHeight q u ∧ topHeight q u<3/2 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ topLeft q u) hV.2.le
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1292/1000) hV.1.le
      nlinarith [h.q_upper]
  have hv : 1/2<lowerHeight q u ∧ lowerHeight q u<589/1000 := by
    dsimp [lowerHeight]
    constructor <;> linarith [hY.1,hY.2]
  have hw : 1885/1000<lowerLeft q u ∧ lowerLeft q u<48/25 := by
    apply sqrt_between (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ lowerHeight q u) hv.2.le
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hv.1.le
      nlinarith [h.q_upper]
  have hUp : 0<topRight q u := by linarith [hU.1]
  have hYp : 0<topHeight q u := by linarith [hY.1]
  have hprodU : topRight q u*topHeight q u ≤ (1708/1000:ℝ)*(3/2) :=
    mul_le_mul hU.2.le hY.2.le hYp.le (by norm_num)
  have hnumL : (1292/1000:ℝ) ≤ (2-u)*topLeft q u := by
    have hh := mul_le_mul hA.1 hV.1.le (by norm_num : (0:ℝ) ≤ 1292/1000)
      (by linarith : 0 ≤ 2-u)
    nlinarith
  have hp : 1/2<slopeRatio q u := by
    dsimp [slopeRatio]
    rw [lt_div_iff₀ (mul_pos hUp hYp)]
    nlinarith
  exact ⟨domain_of_pos hu (by linarith [hr.1]) hUp hYp (by linarith [hw.1]),hr.1,hr.2,hU.1,
    hV.1,hV.2,hY.1,hY.2,hv.1,hv.2,hw.1,hw.2,hp⟩

/-- Two rational upper support lines of the top circles. -/
theorem top_support_upper {q u : ℝ} (h : CriticalStrip q u) :
    topRight q u<141/125+(29/50)*u ∧ topHeight q u<1+u/2 := by
  have hb := h.bounds
  have hUcircle : topRight q u^2+(2-u)^2=q := upper_circle hb.domain.second_radicand
  have hYcircle : topHeight q u^2+topLeft q u^2=q := upper_circle hb.domain.third_radicand
  let L : ℝ := 141/125+(29/50)*u
  let V : ℝ := 3-L
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hL : 0<L := by dsimp [L]; linarith [h.u_lower]
  have hgap : q<L^2+(2-u)^2 := by
    have he : L^2+(2-u)^2-9789/2500 =
        26/15625+(117/6250)*(1-u)+(3341/2500)*(1-u)^2 := by dsimp [L]; ring
    nlinarith [h.q_upper,sq_nonneg (1-u)]
  have hUl : topRight q u<L := by
    by_contra! hh
    have hs := square_mono_nonneg hL.le hh
    nlinarith
  have hV : 0<V := by dsimp [V,L]; linarith [h.u_upper]
  have hVl : V<topLeft q u := by dsimp [V,topLeft]; linarith
  have hV2 := square_strict_mono_nonneg hV.le hVl
  have hYgap : q<(1+u/2)^2+V^2 := by
    have he : (1+u/2)^2+V^2-9789/2500 =
        229/62500-(4/3125)*(1-u)+(733/1250)*(1-u)^2 := by dsimp [V,L]; ring
    nlinarith [h.q_upper,sq_nonneg (1-u)]
  have hYl : topHeight q u<1+u/2 := by
    by_contra! hh
    have hs := square_mono_nonneg (by linarith [h.u_lower] : 0 ≤ 1+u/2) hh
    nlinarith
  exact ⟨hUl,hYl⟩

/-- `p > 3/2 - u`: after the support lines of `top_support_upper`, the difference is a cubic in
`1 - u` with positive terms. -/
theorem slope_affine_lower {q u : ℝ} (h : CriticalStrip q u) :
    3/2-u<slopeRatio q u := by
  have hb := h.bounds
  obtain ⟨hU,hY⟩ := top_support_upper h
  let L : ℝ := 141/125+(29/50)*u
  let V : ℝ := 3-L
  let Y : ℝ := 1+u/2
  have hUp : 0<topRight q u := by linarith [hb.U_lower]
  have hYp : 0<topHeight q u := by linarith [hb.Y_lower]
  have hLp : 0<L := by dsimp [L]; linarith [h.u_lower]
  have hYp' : 0<Y := by dsimp [Y]; linarith [h.u_lower]
  have hprod : topRight q u*topHeight q u ≤ L*Y :=
    mul_le_mul hU.le hY.le hYp.le hLp.le
  have hV : V<topLeft q u := by dsimp [V,L,topLeft]; linarith
  have hn := mul_le_mul_of_nonneg_left hV.le (by linarith [h.u_upper] : 0 ≤ 2-u)
  have hd := mul_le_mul_of_nonneg_left hprod (by linarith [h.u_upper] : 0 ≤ 3/2-u)
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hrem : 0 ≤ (1-u)^2*(2159/1000-(29/100)*(1-u)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hpoly : (3/2-u)*L*Y<(2-u)*V := by
    have he : (2-u)*V-(3/2-u)*L*Y =
        11/1000+(43/250)*(1-u)+(1-u)^2*(2159/1000-(29/100)*(1-u)) := by
      dsimp [V,L,Y]
      ring
    nlinarith
  dsimp [slopeRatio]
  rw [lt_div_iff₀ (mul_pos hUp hYp)]
  nlinarith

/-- `u (1 + p) > 141/100` on the strip. -/
theorem position_slope_product_lower {q u : ℝ} (h : CriticalStrip q u) :
    141/100<u*(1+slopeRatio q u) := by
  have hp := slope_affine_lower h
  have hu : 0<u := by linarith [h.u_lower]
  have hh := mul_pos hu (sub_pos.mpr hp)
  have hc := mul_nonneg (sub_nonneg.mpr h.u_lower)
    (by linarith [h.u_upper] : 0 ≤ 163/100-u)
  nlinarith

/-- Two rational lower support lines: `U > 9/10 + 4u/5` and `v < 38/25 - u`. -/
theorem top_support_lower {q u : ℝ} (h : CriticalStrip q u) :
    9/10+(4/5)*u<topRight q u ∧ lowerHeight q u<38/25-u := by
  have hb := h.bounds
  have hUcircle : topRight q u^2+(2-u)^2=q := upper_circle hb.domain.second_radicand
  have hYcircle : topHeight q u^2+topLeft q u^2=q := upper_circle hb.domain.third_radicand
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hpos : 0 ≤ (1-u)*(18/25-(41/25)*(1-u)) := mul_nonneg ht.1 (by linarith)
  have hUl : 9/10+(4/5)*u<topRight q u := by
    have hg : (9/10+(4/5)*u)^2<topRight q u^2 := by
      nlinarith [h.q_lower]
    by_contra! hh
    have hs := square_mono_nonneg (x:=topRight q u) (upper_nonneg _ _) hh
    nlinarith
  have hYsq : (u+12/25)^2<topHeight q u^2 := by
    dsimp [topLeft] at hYcircle
    nlinarith [h.u_upper]
  have hY : u+12/25<topHeight q u := by
    by_contra! hh
    have hs := square_mono_nonneg (x:=topHeight q u) (upper_nonneg _ _) hh
    nlinarith
  refine ⟨hUl,?_⟩
  dsimp [lowerHeight]
  linarith

/-- A lower support line of the left circle: `w > 73/70 + 6u/7`. -/
theorem left_support_lower {q u : ℝ} (h : CriticalStrip q u) :
    3/70<lowerLeft q u-1-(6/7)*u := by
  have hb := h.bounds
  have hv := (top_support_lower h).2
  have hvp : 0 ≤ lowerHeight q u := by linarith [hb.v_lower]
  have hv2 := square_mono_nonneg hvp hv.le
  have hwcircle : lowerLeft q u^2+lowerHeight q u^2=q :=
    upper_circle hb.domain.fourth_radicand
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hn := mul_nonneg ht.1 (by linarith : 0 ≤ 388/175-(85/49)*(1-u))
  have hw2 : (73/70+(6/7)*u)^2<lowerLeft q u^2 := by
    nlinarith [h.q_lower]
  have hw : 73/70+(6/7)*u<lowerLeft q u := by
    by_contra! hh
    have hs := square_mono_nonneg (x:=lowerLeft q u) (upper_nonneg _ _) hh
    nlinarith
  linarith

/-- The curvature ratio `Z = q/((2-u)U²) + p q/(Y V²)`, with `p' = -p Z` (`slopeRatio_deriv`). -/
def curvatureRatio (q u : ℝ) : ℝ :=
  q/((2-u)*topRight q u^2)+slopeRatio q u*q/(topHeight q u*topLeft q u^2)

/-- `Z > (13/10)(1 + p)`: `q/((2-u)U²)` and `q/(Y V²)` both exceed `13/10`. -/
theorem curvatureRatio_lower {q u : ℝ} (h : CriticalStrip q u) :
    (13/10)*(1+slopeRatio q u)<curvatureRatio q u := by
  have hb := h.bounds
  have hA : 1 ≤ 2-u ∧ 2-u ≤ 113/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hAs := square_mono_nonneg (by linarith : 0 ≤ 2-u) hA.2
  have hAc : 0 ≤ q-((2-u)^2+(113/100)*(2-u)+(113/100)^2) := by
    nlinarith [h.q_lower]
  have hprod := mul_nonneg (by linarith : 0 ≤ 113/100-(2-u)) hAc
  have hUcircle : topRight q u^2+(2-u)^2=q := upper_circle hb.domain.second_radicand
  have hfirstNum : (13/10)*((2-u)*topRight q u^2)<q := by
    have he := congrArg (fun x : ℝ => (2-u)*x) hUcircle
    nlinarith [h.q_upper]
  have hUp : 0<topRight q u := by linarith [hb.U_lower]
  have hYp : 0<topHeight q u := by linarith [hb.Y_lower]
  have hVp : 0<topLeft q u := by linarith [hb.V_lower]
  have hfirst : 13/10<q/((2-u)*topRight q u^2) := by
    rw [lt_div_iff₀ (mul_pos (by linarith) (sq_pos_of_pos hUp))]
    exact hfirstNum
  have hVs := square_mono_nonneg hVp.le hb.V_upper.le
  have hden := mul_le_mul hb.Y_upper.le hVs (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)
  have hsecond : 13/10<q/(topHeight q u*topLeft q u^2) := by
    rw [lt_div_iff₀ (mul_pos hYp (sq_pos_of_pos hVp))]
    nlinarith [h.q_lower]
  have hp : 0<slopeRatio q u := by linarith [hb.p_lower]
  have hh := mul_lt_mul_of_pos_left hsecond hp
  calc
    _ < q/((2-u)*topRight q u^2)+slopeRatio q u*(q/(topHeight q u*topLeft q u^2)) := by
      nlinarith
    _ = curvatureRatio q u := by dsimp [curvatureRatio]; ring

/-- `q/r³ < 4/5` on the strip. -/
theorem right_curvature_upper {q u : ℝ} (h : CriticalStrip q u) :
    q/lowerRight q u^3<4/5 := by
  have hb := h.bounds
  have hr : 0<lowerRight q u := by linarith [hb.r_lower]
  have hu : 0 ≤ u := by linarith [h.u_lower]
  have hus := square_mono_nonneg hu h.u_upper
  have hrs := square_strict_mono_nonneg (by norm_num : (0:ℝ) ≤ 17/10) hb.r_lower
  have hm := mul_nonneg (by linarith [hb.r_lower] : 0 ≤ (4/5)*lowerRight q u-34/25)
    (sq_nonneg (lowerRight q u))
  have hc : lowerRight q u^2+u^2=q := upper_circle hb.domain.first_radicand
  rw [div_lt_iff₀ (pow_pos hr 3)]
  nlinarith

/-! ### The Hessian at a critical point -/

/-- `s + c u/r`, the position derivative of `k₁`. -/
def positionA (q c s u : ℝ) : ℝ := s+c*u/lowerRight q u
/-- `c + s v/w`; the position derivative of `k₂` is `-p (c + s v/w)`. -/
def positionB (q c s u : ℝ) : ℝ := c+s*lowerHeight q u/lowerLeft q u
/-- Minus the position derivative of `k₂`. -/
def positionb (q c s u : ℝ) : ℝ := slopeRatio q u*positionB q c s u
/-- `c q/r³`, the second position derivative of `k₁`. -/
def rightSecond (q c u : ℝ) : ℝ := c*q/lowerRight q u^3
/-- The second position derivative of `k₂`. -/
def leftSecond (q c s u : ℝ) : ℝ :=
  slopeRatio q u*curvatureRatio q u*positionB q c s u+
    s*q*slopeRatio q u^2/lowerLeft q u^3
/-- `|k_u|²`, the squared norm of the position derivative of `(k₁, k₂)`. -/
def positionNorm (q c s u : ℝ) : ℝ := positionA q c s u^2+positionb q c s u^2
/-- The position normal term `k₁ k₁'' + k₂ k₂''`. -/
def positionNormal (q c s u : ℝ) : ℝ :=
  firstComponent q c s u*rightSecond q c u+secondComponent q c s u*leftSecond q c s u
/-- The mixed normal term: `(k₁, k₂)` against the tilt derivative of its position derivative. -/
def mixedNormal (q c s u : ℝ) : ℝ :=
  firstComponent q c s u*(c-s*u/lowerRight q u)+
    secondComponent q c s u*slopeRatio q u*(s-c*lowerHeight q u/lowerLeft q u)
/-- The tilt normal term `k₁ (2 - k₁) + k₂ (1 - k₂)`: `(k₁, k₂)` against its second tilt
derivative. -/
def tiltNormal (q c s u : ℝ) : ℝ :=
  2*firstComponent q c s u+secondComponent q c s u-
    (firstComponent q c s u^2+secondComponent q c s u^2)
/-- The second position derivative of the defect, `2 (|k_u|² + positionNormal)`. -/
def positionSecond (q c s u : ℝ) : ℝ :=
  2*(positionNorm q c s u+positionNormal q c s u)
/-- The mixed second derivative of the defect in the tilt and the position. -/
def mixedSecond (q c s u : ℝ) : ℝ :=
  2*(positionA q c s u*firstTilt q c s u-positionb q c s u*secondTilt q c s u+
    mixedNormal q c s u)
/-- `κ`, the tilt derivative of `k₁` divided by its position derivative. -/
def tangentRatio (q c s u : ℝ) : ℝ := firstTilt q c s u/positionA q c s u
/-- `σ`, the position normal term divided by `k₁`. -/
def normalizedPosition (q c s u : ℝ) : ℝ := positionNormal q c s u/firstComponent q c s u
/-- `τ`, the mixed normal term divided by `k₁`. -/
def normalizedMixed (q c s u : ℝ) : ℝ := mixedNormal q c s u/firstComponent q c s u
/-- `ν`, the tilt normal term divided by `k₁`. -/
def normalizedTilt (q c s u : ℝ) : ℝ := tiltNormal q c s u/firstComponent q c s u
/-- The determinant of the Hessian of the defect in the tilt and the position. -/
def hessianDeterminant (q c s u : ℝ) : ℝ :=
  positionSecond q c s u*tiltSecond q c s u-mixedSecond q c s u^2

/-- A critical point of the defect in the strip, at a tilt with `0 ≤ s/c ≤ 1/5`; the defect may
have either sign. -/
structure StripCritical (q c s u : ℝ) : Prop where
  strip : CriticalStrip q u
  cosine_pos : 0<c
  sine_nonneg : 0 ≤ s
  unit : c^2+s^2=1
  tilt_upper : s/c ≤ 1/5
  position_zero : positionHalf q c s u=0
  tilt_zero : tiltFirst q c s u=0

/-- A tilt with `0 ≤ s/c ≤ 1/5` has `c > 49/50` and `5 s ≤ c`. -/
theorem small_tilt_bounds {c s : ℝ} (hc : 0<c) (hs : 0 ≤ s)
    (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    49/50<c ∧ c ≤ 1 ∧ s ≤ 1 ∧ 5*s ≤ c := by
  have ht' : s ≤ (1/5)*c := (div_le_iff₀ hc).mp ht
  have hs2 := square_mono_nonneg hs ht'
  have hcL : 49/50<c := by
    by_contra! hh
    have hsq := square_mono_nonneg hc.le hh
    nlinarith
  obtain ⟨hcU,hsU⟩ := unit_le_one hunit
  exact ⟨hcL,hcU,hsU,by linarith⟩

theorem CriticalStrip.quotient_bounds {q u : ℝ} (h : CriticalStrip q u) :
    783/1600<u/lowerRight q u ∧ u/lowerRight q u<1 ∧
    25/96<lowerHeight q u/lowerLeft q u ∧ lowerHeight q u/lowerLeft q u<1 := by
  have hb := h.bounds
  have hr : 0<lowerRight q u := by linarith [hb.r_lower]
  have hw : 0<lowerLeft q u := by linarith [hb.w_lower]
  refine ⟨?_,?_,?_,?_⟩
  · rw [lt_div_iff₀ hr]
    nlinarith [hb.r_upper,h.u_lower]
  · rw [div_lt_iff₀ hr]
    linarith [hb.r_lower,h.u_upper]
  · rw [lt_div_iff₀ hw]
    nlinarith [hb.v_lower,hb.w_upper]
  · rw [div_lt_iff₀ hw]
    linarith [hb.v_upper,hb.w_lower]

theorem positionB_lower {q c s u : ℝ} (h : CriticalStrip q u)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    1 ≤ positionB q c s u := by
  obtain ⟨_,_,hy,_⟩ := h.quotient_bounds
  obtain ⟨_,_,_,hst⟩ := small_tilt_bounds hc hs hunit ht
  let y : ℝ := lowerHeight q u/lowerLeft q u
  have hyp : 0 ≤ y := by dsimp [y]; linarith
  have hcy := mul_le_mul_of_nonneg_left (show 1/4 ≤ y by dsimp [y]; linarith) hc.le
  have hprod := mul_nonneg hs (by nlinarith : 0 ≤ 2*c*y-s)
  have hnon : 0 ≤ c+s*y := add_nonneg hc.le (mul_nonneg hs hyp)
  have hsq : 1 ≤ (c+s*y)^2 := by nlinarith [sq_nonneg (s*y)]
  have hB : 1 ≤ c+s*y := by
    by_contra! hh
    have hbad := square_strict_mono_nonneg hnon hh
    nlinarith
  simpa [positionB,y,div_eq_mul_inv,mul_assoc] using hB

theorem StripCritical.components_pos {q c s u : ℝ} (h : StripCritical q c s u) :
    0<firstComponent q c s u ∧ 0<secondComponent q c s u := by
  obtain ⟨hc,hs⟩ := unit_le_one h.unit
  exact FiveCornerGeometry.components_pos (by linarith [h.strip.q_upper]) h.strip.bounds.domain
    h.cosine_pos hc h.sine_nonneg hs

theorem StripCritical.position_derivative_zero {q c s u : ℝ} (h : StripCritical q c s u) :
    HasDerivAt (defect q c s) 0 u := by
  have hb := h.strip.bounds
  have hd := position_deriv (q:=q) (c:=c) (s:=s) (u:=u)
    (by linarith [hb.r_lower]) (by linarith [hb.U_lower])
    (by linarith [hb.Y_lower]) (by linarith [hb.w_lower])
  simpa [h.position_zero] using hd

theorem StripCritical.norm_lt_four {q c s u : ℝ} (h : StripCritical q c s u) :
    firstComponent q c s u^2+secondComponent q c s u^2<4 :=
  position_stationary_norm_lt_four h.strip.q_lower (by linarith [h.strip.q_upper])
    h.cosine_pos h.sine_nonneg h.tilt_upper h.unit h.strip.bounds.domain h.position_derivative_zero

theorem StripCritical.position_equation {q c s u : ℝ} (h : StripCritical q c s u) :
    firstComponent q c s u*positionA q c s u=
      secondComponent q c s u*positionb q c s u := by
  have hp := h.position_zero
  dsimp [positionHalf,positionA,positionb,positionB] at *
  nlinarith

theorem StripCritical.tilt_equation {q c s u : ℝ} (h : StripCritical q c s u) :
    firstComponent q c s u*firstTilt q c s u=
      secondComponent q c s u*(-secondTilt q c s u) := by
  have hp := h.tilt_zero
  dsimp [tiltFirst] at hp
  nlinarith

theorem StripCritical.positionA_pos {q c s u : ℝ} (h : StripCritical q c s u) :
    0<positionA q c s u := by
  have hu : 0<u := by linarith [h.strip.u_lower]
  have hr : 0<lowerRight q u := by linarith [h.strip.bounds.r_lower]
  have hm := div_pos (mul_pos h.cosine_pos hu) hr
  dsimp [positionA]
  linarith [h.sine_nonneg]

theorem StripCritical.firstTilt_pos {q c s u : ℝ} (h : StripCritical q c s u) :
    0<firstTilt q c s u := by
  have hp := mul_pos h.cosine_pos (by linarith [h.strip.u_lower] : 0<u)
  have hn := mul_nonneg h.sine_nonneg (by linarith [h.strip.bounds.r_lower] : 0 ≤ lowerRight q u-1)
  dsimp [firstTilt]
  linarith

theorem secondComponent_gt_one {q c s u : ℝ} (h : CriticalStrip q u)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    1<secondComponent q c s u := by
  have hb := h.bounds
  obtain ⟨_,_,_,hst⟩ := small_tilt_bounds hc hs hunit ht
  have hv := mul_lt_mul_of_pos_left hb.v_lower hc
  have hw := mul_le_mul_of_nonneg_left (by linarith [hb.w_upper] : lowerLeft q u-1 ≤ 23/25) hs
  dsimp [secondComponent]
  nlinarith

theorem tilt_ratio_lower {q c s u : ℝ} (h : CriticalStrip q u)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    (6/7)*firstTilt q c s u< -secondTilt q c s u := by
  have hb := h.bounds
  obtain ⟨_,_,_,hst⟩ := small_tilt_bounds hc hs hunit ht
  have hw := mul_lt_mul_of_pos_left (left_support_lower h) hc
  have hv : -(1/6)<lowerHeight q u-(6/7)*(lowerRight q u-1) := by
    linarith [hb.v_lower,hb.r_upper]
  have hv' := mul_le_mul_of_nonneg_left hv.le hs
  dsimp [firstTilt,secondTilt]
  nlinarith

/-- At a critical point `k₁/2 < k₂ < 7 k₁/6`. -/
theorem StripCritical.component_ratio {q c s u : ℝ} (h : StripCritical q c s u) :
    (1/2)*firstComponent q c s u<secondComponent q c s u ∧
      secondComponent q c s u<(7/6)*firstComponent q c s u := by
  obtain ⟨hk₁,hk₂⟩ := h.components_pos
  have hnorm := h.norm_lt_four
  have hk₁u : firstComponent q c s u<2 := by nlinarith [sq_nonneg (secondComponent q c s u)]
  have hk₂l := secondComponent_gt_one h.strip h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have he := h.tilt_equation
  have hr := tilt_ratio_lower h.strip h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hprod := mul_pos hk₂ (sub_pos.mpr hr)
  have hd := h.firstTilt_pos
  refine ⟨by linarith,?_⟩
  by_contra! hh
  have hp := mul_nonneg (by linarith : 0 ≤ (6/7)*secondComponent q c s u-firstComponent q c s u) hd.le
  nlinarith

/-- In the cone `x/2 < y < 7x/6` inside the circle `x² + y² < 4`,
`2x + y - (x² + y²) > 9x/100`. -/
theorem normal_reserve {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hn : x^2+y^2<4) (hlo : x/2<y) (hhi : y<(7/6)*x) :
    (9/100)*x<2*x+y-(x^2+y^2) := by
  have hcone := mul_nonneg (by linarith : 0 ≤ y-x/2) (by linarith : 0 ≤ (7/6)*x-y)
  have hside := mul_nonneg hx.le (by linarith : 0 ≤ (7/6)*x-y)
  have hsqx := sq_pos_of_pos hx
  have hquad : 4*(x^2+y^2)<((191/100)*x+y)^2 := by nlinarith
  have hnorm : 0<x^2+y^2 := by nlinarith [sq_nonneg y]
  have hbound := mul_lt_mul_of_pos_right hn hnorm
  by_contra! hh
  have hL : 0 ≤ (191/100)*x+y := by positivity
  have hs := square_mono_nonneg hL (show (191/100)*x+y ≤ x^2+y^2 by linarith)
  nlinarith

/-- `ν > 9/100`. -/
theorem StripCritical.normalizedTilt_lower {q c s u : ℝ} (h : StripCritical q c s u) :
    9/100<normalizedTilt q c s u := by
  obtain ⟨hk₁,hk₂⟩ := h.components_pos
  obtain ⟨hl,hu⟩ := h.component_ratio
  have hn := normal_reserve hk₁ hk₂ h.norm_lt_four (by linarith) hu
  dsimp [normalizedTilt,tiltNormal]
  rw [lt_div_iff₀ hk₁]
  exact hn

theorem mixed_cancellation (k₁ k₂ p c s x y : ℝ) (hunit : c^2+s^2=1)
    (hpos : k₁*(s+c*x)=k₂*p*(c+s*y)) :
    (k₁*(c-s*x)+k₂*p*(s-c*y))*(c+s*y)=k₁*(1-x*y) := by
  linear_combination -(s-c*y)*hpos+k₁*(1-x*y)*hunit

theorem StripCritical.normalizedMixed_formula {q c s u : ℝ} (h : StripCritical q c s u) :
    normalizedMixed q c s u=
      (1-(u/lowerRight q u)*(lowerHeight q u/lowerLeft q u))/positionB q c s u := by
  have hk₁ := h.components_pos.1
  have hB := positionB_lower h.strip h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hp := h.position_equation
  have he := mixed_cancellation (firstComponent q c s u) (secondComponent q c s u)
    (slopeRatio q u) c s (u/lowerRight q u) (lowerHeight q u/lowerLeft q u) h.unit
    (by simpa [positionA,positionb,positionB,div_eq_mul_inv,mul_assoc] using hp)
  have he' : mixedNormal q c s u*positionB q c s u=
      firstComponent q c s u*(1-(u/lowerRight q u)*(lowerHeight q u/lowerLeft q u)) := by
    simpa [mixedNormal,positionB,div_eq_mul_inv,mul_assoc] using he
  dsimp only [normalizedMixed]
  apply (div_eq_div_iff (ne_of_gt hk₁) (ne_of_gt (show 0<positionB q c s u by linarith))).2
  nlinarith

/-- `0 < τ < 7/8`. -/
theorem StripCritical.normalizedMixed_bounds {q c s u : ℝ} (h : StripCritical q c s u) :
    0<normalizedMixed q c s u ∧ normalizedMixed q c s u<7/8 := by
  obtain ⟨hxl,hxu,hyl,hyu⟩ := h.strip.quotient_bounds
  let x : ℝ := u/lowerRight q u
  let y : ℝ := lowerHeight q u/lowerLeft q u
  have hx : 0<x := by dsimp [x]; linarith
  have hy : 0<y := by dsimp [y]; linarith
  have hxyL : (783/1600:ℝ)*(25/96) ≤ x*y :=
    mul_le_mul hxl.le hyl.le (by norm_num) hx.le
  have hxyU : x*y<1 := by
    have hm := mul_lt_mul_of_pos_right hxu hy
    dsimp [x,y] at *
    nlinarith
  have hB := positionB_lower h.strip h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hBp : 0<positionB q c s u := by linarith
  rw [h.normalizedMixed_formula]
  change 0<(1-x*y)/positionB q c s u ∧ (1-x*y)/positionB q c s u<7/8
  refine ⟨div_pos (by linarith) hBp,?_⟩
  rw [div_lt_iff₀ hBp]
  nlinarith

/-- `|k_u|²/k₁ > 17/50`. -/
theorem StripCritical.positionNorm_lower {q c s u : ℝ} (h : StripCritical q c s u) :
    17/50<positionNorm q c s u/firstComponent q c s u := by
  have hb := h.strip.bounds
  obtain ⟨hxl,_,_,_⟩ := h.strip.quotient_bounds
  obtain ⟨hcL,_,_,_⟩ := small_tilt_bounds h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hB := positionB_lower h.strip h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hk := h.components_pos.1
  have hcx := mul_lt_mul_of_pos_left hxl h.cosine_pos
  have ha : s+19/40<positionA q c s u := by
    dsimp [positionA]
    have he : c*(u/lowerRight q u)=c*u/lowerRight q u := by ring
    nlinarith
  have hp : 0<slopeRatio q u := by linarith [hb.p_lower]
  have hbmul := mul_le_mul_of_nonneg_left hB hp.le
  have hb' : 1/2<positionb q c s u := by dsimp [positionb]; nlinarith [hb.p_lower]
  have hcr := mul_lt_mul_of_pos_left (show 7/10<lowerRight q u-1 by linarith [hb.r_lower]) h.cosine_pos
  have hsu := mul_le_mul_of_nonneg_left h.strip.u_upper h.sine_nonneg
  have hkU : firstComponent q c s u<s+657/500 := by dsimp [firstComponent]; nlinarith
  have has := square_strict_mono_nonneg (by linarith [h.sine_nonneg] : 0 ≤ s+19/40) ha
  have hbs := square_strict_mono_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hb'
  dsimp [positionNorm]
  rw [lt_div_iff₀ hk]
  nlinarith [sq_nonneg s,h.sine_nonneg]

theorem StripCritical.tangentRatio_formula {q c s u : ℝ} (h : StripCritical q c s u) :
    tangentRatio q c s u=lowerRight q u-(s/c)/(s/c+u/lowerRight q u) := by
  have hr : 0<lowerRight q u := by linarith [h.strip.bounds.r_lower]
  have ha := h.positionA_pos
  have hc := h.cosine_pos
  have hh : 0 ≤ s/c := div_nonneg h.sine_nonneg hc.le
  have hx : 0<u/lowerRight q u := div_pos (by linarith [h.strip.u_lower]) hr
  have hden : 0<s/c+u/lowerRight q u := by linarith
  have hsum : 0<s*lowerRight q u+c*u := by
    nlinarith [mul_nonneg h.sine_nonneg hr.le,mul_pos hc (by linarith [h.strip.u_lower] : 0<u)]
  rw [tangentRatio,firstTilt,positionA]
  field_simp [ne_of_gt hsum]
  ring

/-- `7/5 < κ < 16/9`. -/
theorem StripCritical.tangentRatio_bounds {q c s u : ℝ} (h : StripCritical q c s u) :
    7/5<tangentRatio q c s u ∧ tangentRatio q c s u<16/9 := by
  have hb := h.strip.bounds
  obtain ⟨hxl,_,_,_⟩ := h.strip.quotient_bounds
  have hh : 0 ≤ s/c := div_nonneg h.sine_nonneg h.cosine_pos.le
  have hden : 0<s/c+u/lowerRight q u := by linarith
  have hφ : (s/c)/(s/c+u/lowerRight q u)<3/10 := by
    rw [div_lt_iff₀ hden]
    nlinarith [h.tilt_upper]
  have hφp : 0 ≤ (s/c)/(s/c+u/lowerRight q u) := div_nonneg hh hden.le
  rw [h.tangentRatio_formula]
  constructor <;> linarith [hb.r_lower,hb.r_upper]

theorem StripCritical.positionNormal_lower {q c s u : ℝ} (h : StripCritical q c s u) :
    rightSecond q c u+positionA q c s u*curvatureRatio q u ≤ normalizedPosition q c s u := by
  obtain ⟨hk₁,hk₂⟩ := h.components_pos
  have hp := h.position_equation
  dsimp [positionb] at hp
  have hq : 0 ≤ q := by linarith [h.strip.q_lower]
  have hw : 0<lowerLeft q u := by linarith [h.strip.bounds.w_lower]
  have hn : 0 ≤ s*q*slopeRatio q u^2/lowerLeft q u^3 :=
    div_nonneg (mul_nonneg (mul_nonneg h.sine_nonneg hq) (sq_nonneg _)) (pow_pos hw 3).le
  have hrem := mul_nonneg hk₂.le hn
  have he : positionNormal q c s u-firstComponent q c s u*
      (rightSecond q c u+positionA q c s u*curvatureRatio q u)=
      secondComponent q c s u*(s*q*slopeRatio q u^2/lowerLeft q u^3) := by
    dsimp [positionNormal,leftSecond]
    linear_combination -curvatureRatio q u*hp
  dsimp only [normalizedPosition]
  rw [le_div_iff₀ hk₁]
  nlinarith

/-- The bound behind `κ σ > 3`, for every tangent `h ≥ 0`. -/
theorem angular_curvature_reserve {h : ℝ} (hh : 0 ≤ h) :
    1531/500<1+(783/1600:ℝ)^2+1833/1000+273/200*h-4/5*(h/(h+783/1600)) := by
  have hd : 0<h+783/1600 := by linarith
  have key : 4/5*h<(1+(783/1600:ℝ)^2+1833/1000+273/200*h-1531/500)*(h+783/1600) := by
    nlinarith [sq_nonneg (h-9/200)]
  have hlt : 4/5*(h/(h+783/1600))<1+(783/1600:ℝ)^2+1833/1000+273/200*h-1531/500 := by
    rw [mul_div_assoc',div_lt_iff₀ hd]
    exact key
  linarith

/-- `κ σ > 3`. -/
theorem StripCritical.tangent_position_reserve {q c s u : ℝ} (h : StripCritical q c s u) :
    3<tangentRatio q c s u*normalizedPosition q c s u := by
  have hb := h.strip.bounds
  obtain ⟨hxl,_,_,_⟩ := h.strip.quotient_bounds
  obtain ⟨hcL,_,_,_⟩ := small_tilt_bounds h.cosine_pos h.sine_nonneg h.unit h.tilt_upper
  have hc := h.cosine_pos
  have hκp : 0<tangentRatio q c s u := by linarith [h.tangentRatio_bounds.1]
  have hd := h.firstTilt_pos
  have hr : 0<lowerRight q u := by linarith [hb.r_lower]
  have ht : 0 ≤ s/c := div_nonneg h.sine_nonneg hc.le
  have hden : 0<s/c+u/lowerRight q u := by linarith
  have hcs : c*(s/c)=s := mul_div_cancel₀ s (ne_of_gt hc)
  -- `κ σ ≥ c (κ Q) + d Z`, where `Q = q/r³` and `κ A = d`
  have hka : tangentRatio q c s u*positionA q c s u=firstTilt q c s u := by
    rw [tangentRatio]
    field_simp [ne_of_gt h.positionA_pos]
  have hσ : c*(tangentRatio q c s u*(q/lowerRight q u^3))+
      firstTilt q c s u*curvatureRatio q u ≤ tangentRatio q c s u*normalizedPosition q c s u := by
    have hm := mul_le_mul_of_nonneg_left h.positionNormal_lower hκp.le
    have e : tangentRatio q c s u*(rightSecond q c u+positionA q c s u*curvatureRatio q u)=
        c*(tangentRatio q c s u*(q/lowerRight q u^3))+firstTilt q c s u*curvatureRatio q u := by
      rw [← hka,rightSecond]
      ring
    linarith
  -- `κ Q = 1 + x² - φ Q`, with `x = u/r`, `φ = t/(t+x)`, `t = s/c`
  have hκQ : 1+(783/1600)^2-4/5*((s/c)/(s/c+783/1600)) <
      tangentRatio q c s u*(q/lowerRight q u^3) := by
    have he : lowerRight q u^2+u^2=q := upper_circle hb.domain.first_radicand
    have hrQ : lowerRight q u*(q/lowerRight q u^3)=1+(u/lowerRight q u)^2 := by
      have hr0 := ne_of_gt hr
      calc lowerRight q u*(q/lowerRight q u^3)=(lowerRight q u^2+u^2)/lowerRight q u^2 := by
            rw [he]
            field_simp
        _ = 1+(u/lowerRight q u)^2 := by
            field_simp
    have hφQ := mul_le_mul_of_nonneg_left (right_curvature_upper h.strip).le
      (div_nonneg ht hden.le)
    have hφ : (s/c)/(s/c+u/lowerRight q u) ≤ (s/c)/(s/c+783/1600) :=
      div_le_div_of_nonneg_left ht (by linarith) (by linarith)
    have hx := square_strict_mono_nonneg (by norm_num : (0:ℝ) ≤ 783/1600) hxl
    rw [h.tangentRatio_formula,sub_mul,hrQ]
    linarith
  -- `d Z > d (13/10) (1 + p) ≥ (1833/1000) c + (273/200) s`
  have hdZ : 1833/1000*c+273/200*s<firstTilt q c s u*curvatureRatio q u := by
    have hZ := mul_lt_mul_of_pos_left (curvatureRatio_lower h.strip) hd
    have hrp : 21/20 ≤ (lowerRight q u-1)*(1+slopeRatio q u) := by
      have hm := mul_le_mul (show 7/10 ≤ lowerRight q u-1 by linarith [hb.r_lower])
        (show 3/2 ≤ 1+slopeRatio q u by linarith [hb.p_lower]) (by norm_num)
        (by linarith [hb.r_lower])
      linarith
    have e : firstTilt q c s u*(13/10*(1+slopeRatio q u))=
        13/10*(c*(u*(1+slopeRatio q u)))+13/10*(s*((lowerRight q u-1)*(1+slopeRatio q u))) := by
      rw [firstTilt]
      ring
    have h₁ := mul_lt_mul_of_pos_left (position_slope_product_lower h.strip) hc
    have h₂ := mul_le_mul_of_nonneg_left hrp h.sine_nonneg
    linarith
  have hangle := mul_lt_mul_of_pos_left (angular_curvature_reserve ht) hc
  linarith [mul_lt_mul_of_pos_left hκQ hc]

/-- `σ > 27/16`. -/
theorem StripCritical.normalizedPosition_lower {q c s u : ℝ} (h : StripCritical q c s u) :
    27/16<normalizedPosition q c s u := by
  have hk := h.tangentRatio_bounds
  have hprod := h.tangent_position_reserve
  have hκp : 0<tangentRatio q c s u := by linarith
  have hσp : 0<normalizedPosition q c s u := by
    by_contra! hh
    have hm := mul_nonpos_of_nonneg_of_nonpos hκp.le hh
    linarith
  have hm := mul_lt_mul_of_pos_right hk.2 hσp
  nlinarith

/-- At a critical point the tilt derivative of `(k₁, k₂)` is `κ` times its position derivative. -/
theorem StripCritical.derivative_proportionality {q c s u : ℝ} (h : StripCritical q c s u) :
    firstTilt q c s u=tangentRatio q c s u*positionA q c s u ∧
      secondTilt q c s u= -tangentRatio q c s u*positionb q c s u := by
  have ha := h.positionA_pos
  have hk₂ := h.components_pos.2
  have hfirst : firstTilt q c s u=tangentRatio q c s u*positionA q c s u := by
    dsimp [tangentRatio]
    field_simp [ne_of_gt ha]
  have hp := h.position_equation
  have ht := h.tilt_equation
  have hp' := congrArg (fun x : ℝ => tangentRatio q c s u*x) hp
  have hf' := congrArg (fun x : ℝ => firstComponent q c s u*x) hfirst
  refine ⟨hfirst,?_⟩
  apply mul_left_cancel₀ (ne_of_gt hk₂)
  nlinarith

/-- The determinant of the Hessian in terms of `κ`, `|k_u|²` and the three normal terms. -/
theorem StripCritical.hessian_identity {q c s u : ℝ} (h : StripCritical q c s u) :
    hessianDeterminant q c s u=4*(
      positionNorm q c s u*(positionNormal q c s u*tangentRatio q c s u^2-
        2*mixedNormal q c s u*tangentRatio q c s u+tiltNormal q c s u)+
      positionNormal q c s u*tiltNormal q c s u-mixedNormal q c s u^2) := by
  obtain ⟨hd,he⟩ := h.derivative_proportionality
  have hmix : mixedSecond q c s u=
      2*(tangentRatio q c s u*positionNorm q c s u+mixedNormal q c s u) := by
    dsimp only [mixedSecond,positionNorm]
    rw [hd,he]
    ring
  have htt : tiltSecond q c s u=
      2*(tangentRatio q c s u^2*positionNorm q c s u+tiltNormal q c s u) := by
    dsimp only [tiltSecond,positionNorm,tiltNormal]
    rw [hd,he]
    ring
  rw [hessianDeterminant,hmix,htt,positionSecond]
  ring

theorem StripCritical.normalized_hessian_identity {q c s u : ℝ} (h : StripCritical q c s u) :
    hessianDeterminant q c s u/(4*firstComponent q c s u^2)=
      (positionNorm q c s u/firstComponent q c s u)*
        (normalizedPosition q c s u*tangentRatio q c s u^2-
          2*normalizedMixed q c s u*tangentRatio q c s u+normalizedTilt q c s u)+
      normalizedPosition q c s u*normalizedTilt q c s u-normalizedMixed q c s u^2 := by
  rw [h.hessian_identity]
  dsimp only [normalizedPosition,normalizedMixed,normalizedTilt]
  field_simp [ne_of_gt h.components_pos.1]

/-- The rational inequality behind `StripCritical.hessian_reserve`. -/
theorem normalized_determinant_reserve {A κ σ τ ν : ℝ}
    (hA : 17/50<A) (hκ : 7/5<κ) (hτl : 0<τ) (hτu : τ<7/8)
    (hν : 9/100<ν) (hκσ : 3<κ*σ) (hσ : 27/16<σ) :
    237/20000<A*(σ*κ^2-2*τ*κ+ν)+σ*ν-τ^2 := by
  have hκp : 0<κ := by linarith
  have hνp : 0<ν := by linarith
  have hterm : 5/4<κ*σ-2*τ := by linarith
  have hm := mul_lt_mul_of_pos_left hterm hκp
  have hbracket : 46/25<σ*κ^2-2*τ*κ+ν := by nlinarith
  have hbracketp : 0<σ*κ^2-2*τ*κ+ν := by linarith
  have hmA := mul_lt_mul_of_pos_right hA hbracketp
  have hmB := mul_lt_mul_of_pos_left hbracket (by norm_num : (0:ℝ)<17/50)
  have hmσ := mul_lt_mul_of_pos_right hσ hνp
  have hmν := mul_lt_mul_of_pos_left hν (by norm_num : (0:ℝ)<27/16)
  have hτsq := square_strict_mono_nonneg hτl.le hτu
  nlinarith

/-- `det Hess > (237/5000) k₁²` at every critical point of the strip. -/
theorem StripCritical.hessian_reserve {q c s u : ℝ} (h : StripCritical q c s u) :
    (237/5000)*firstComponent q c s u^2<hessianDeterminant q c s u := by
  obtain ⟨hτl,hτu⟩ := h.normalizedMixed_bounds
  have hbound := normalized_determinant_reserve h.positionNorm_lower h.tangentRatio_bounds.1
    hτl hτu h.normalizedTilt_lower h.tangent_position_reserve h.normalizedPosition_lower
  rw [← h.normalized_hessian_identity] at hbound
  have hk := h.components_pos.1
  rw [lt_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hk))] at hbound
  nlinarith

/-- The determinant of the Hessian is positive at every critical point of the strip. -/
theorem StripCritical.hessian_pos {q c s u : ℝ} (h : StripCritical q c s u) :
    0<hessianDeterminant q c s u := by
  have hp := mul_pos (by norm_num : (0:ℝ)<237/5000) (sq_pos_of_pos h.components_pos.1)
  linarith [h.hessian_reserve]

/-! ### The second derivatives -/

/-- The radical domain with `q < 4` and the four radicals positive. -/
structure SmoothDomain (q u : ℝ) : Prop extends Domain q u where
  radius_lt_four : q<4
  r_pos : 0<lowerRight q u
  U_pos : 0<topRight q u
  Y_pos : 0<topHeight q u
  w_pos : 0<lowerLeft q u

theorem circle_ratio_derivative (A U V Y q : ℝ)
    (hA : A≠0) (hU : U≠0) (hV : V≠0) (hY : Y≠0)
    (hcircle₁ : U^2+A^2=q) (hcircle₂ : Y^2+V^2=q) :
    ((-1*V+A*(-(A/U)))*(U*Y)-(A*V)*((A/U)*Y+U*(A*V/(U*Y))))/(U*Y)^2=
      -(A*V/(U*Y))*(q/(A*U^2)+(A*V/(U*Y))*q/(Y*V^2)) := by
  calc _ = -(U^2+A^2)*V/(Y*U^3)-(Y^2+V^2)*A^2/(U^2*Y^3) := by
        field_simp
        ring
    _ = -q*V/(Y*U^3)-q*A^2/(U^2*Y^3) := by rw [hcircle₁,hcircle₂]
    _ = _ := by
        field_simp
        ring

/-- `p' = -p Z`. -/
theorem slopeRatio_deriv {q u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (slopeRatio q) (-slopeRatio q u*curvatureRatio q u) u := by
  obtain ⟨_,dU,dV,dY,_,_⟩ := radical_derivatives h.r_pos h.U_pos h.Y_pos h.w_pos
  have hA : 0<2-u := by linarith [h.toDomain.height_lt_two h.radius_lt_four]
  have hV := h.toDomain.topLeft_pos h.radius_lt_four
  exact (((hasDerivAt_id' u).const_sub 2).fun_mul dV).fun_div (dU.fun_mul dY)
    (ne_of_gt (mul_pos h.U_pos h.Y_pos)) |>.congr_deriv
      (circle_ratio_derivative (2-u) (topRight q u) (topLeft q u) (topHeight q u) q
        (ne_of_gt hA) (ne_of_gt h.U_pos) (ne_of_gt hV) (ne_of_gt h.Y_pos)
        (upper_circle h.second_radicand) (upper_circle h.third_radicand))

theorem rightRatio_deriv {q u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (fun v => v/lowerRight q v) (q/lowerRight q u^3) u := by
  have hr := ne_of_gt h.r_pos
  have he : lowerRight q u^2+u^2=q := upper_circle h.first_radicand
  refine ((hasDerivAt_id' u).fun_div (radical_derivatives h.r_pos h.U_pos h.Y_pos h.w_pos).1
    hr).congr_deriv ?_
  calc _ = (lowerRight q u^2+u^2)/lowerRight q u^3 := by
        field_simp
        ring
    _ = _ := by rw [he]

theorem lowerRatio_deriv {q u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (fun v => lowerHeight q v/lowerLeft q v)
      (-slopeRatio q u*q/lowerLeft q u^3) u := by
  obtain ⟨_,_,_,_,dv,dw⟩ := radical_derivatives h.r_pos h.U_pos h.Y_pos h.w_pos
  have hw := ne_of_gt h.w_pos
  have he : lowerLeft q u^2+lowerHeight q u^2=q := upper_circle h.fourth_radicand
  refine (dv.fun_div dw hw).congr_deriv ?_
  calc _ = -slopeRatio q u*(lowerLeft q u^2+lowerHeight q u^2)/lowerLeft q u^3 := by
        field_simp
        ring
    _ = _ := by rw [he]

theorem positionA_deriv {q c s u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (positionA q c s) (rightSecond q c u) u := by
  convert ((rightRatio_deriv h).const_mul c).const_add s using 1
  · funext v
    rw [positionA]
    ring
  · rw [rightSecond]
    ring

theorem positionB_deriv {q c s u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (positionB q c s) (-s*slopeRatio q u*q/lowerLeft q u^3) u := by
  convert ((lowerRatio_deriv h).const_mul s).const_add c using 1
  · funext v
    rw [positionB]
    ring
  · ring

/-- The position derivative of `2 positionHalf` is `positionSecond`. -/
theorem position_second_deriv {q c s u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (fun v => 2*positionHalf q c s v) (positionSecond q c s u) u := by
  obtain ⟨dk₁,dk₂⟩ := components_position_deriv (c:=c) (s:=s) h.r_pos h.U_pos h.Y_pos h.w_pos
  exact ((dk₁.fun_mul (positionA_deriv h)).fun_sub
    ((dk₂.fun_mul (slopeRatio_deriv h)).fun_mul (positionB_deriv h))).const_mul 2
      |>.congr_deriv (by
        rw [positionSecond,positionNorm,positionNormal,positionb,leftSecond,positionA,
          positionB]
        ring)

/-- The position entry of the Hessian is positive wherever the four radicals are. -/
theorem SmoothDomain.positionSecond_pos {q c s u : ℝ} (h : SmoothDomain q u)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) :
    0<positionSecond q c s u := by
  have hq : 0<q := by
    have he : lowerRight q u^2+u^2=q := upper_circle h.first_radicand
    nlinarith [sq_pos_of_pos h.r_pos,sq_nonneg u]
  have hA : 0<2-u := by linarith [h.toDomain.height_lt_two h.radius_lt_four]
  have hV := h.toDomain.topLeft_pos h.radius_lt_four
  have hv := h.toDomain.lowerHeight_pos h.radius_lt_four
  have hp : 0<slopeRatio q u := div_pos (mul_pos hA hV) (mul_pos h.U_pos h.Y_pos)
  have hZ : 0<curvatureRatio q u :=
    add_pos (div_pos hq (mul_pos hA (pow_pos h.U_pos 2)))
      (div_pos (mul_pos hp hq) (mul_pos h.Y_pos (pow_pos hV 2)))
  have hB : 0<positionB q c s u := by
    have hh := div_nonneg (mul_nonneg hs hv.le) h.w_pos.le
    rw [positionB]
    linarith
  have hright : 0<rightSecond q c u := div_pos (mul_pos hc hq) (pow_pos h.r_pos 3)
  have hleft : 0<leftSecond q c s u := by
    have hh := div_nonneg (mul_nonneg (mul_nonneg hs hq.le) (sq_nonneg (slopeRatio q u)))
      (pow_nonneg h.w_pos.le 3)
    have hpZB := mul_pos (mul_pos hp hZ) hB
    rw [leftSecond]
    linarith
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  obtain ⟨hk₁,hk₂⟩ := components_pos h.radius_lt_four h.toDomain hc hcu hs hsu
  have hnormal : 0<positionNormal q c s u :=
    add_pos (mul_pos hk₁ hright) (mul_pos hk₂ hleft)
  rw [positionSecond,positionNorm]
  nlinarith [sq_nonneg (positionA q c s u),sq_nonneg (positionb q c s u)]

theorem positionA_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => positionA q (Real.cos x) (Real.sin x) u)
      (Real.cos t-Real.sin t*u/lowerRight q u) t :=
  (Real.hasDerivAt_sin t).fun_add (((Real.hasDerivAt_cos t).mul_const u).div_const
    (lowerRight q u)) |>.congr_deriv (by ring)

theorem positionB_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => positionB q (Real.cos x) (Real.sin x) u)
      (-Real.sin t+Real.cos t*lowerHeight q u/lowerLeft q u) t :=
  (Real.hasDerivAt_cos t).fun_add (((Real.hasDerivAt_sin t).mul_const (lowerHeight q u)).div_const
    (lowerLeft q u))

/-- The tilt derivative of `2 positionHalf` is `mixedSecond`. -/
theorem mixed_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun x => 2*positionHalf q (Real.cos x) (Real.sin x) u)
      (mixedSecond q (Real.cos t) (Real.sin t) u) t :=
  (((firstComponent_angle_deriv q u t).fun_mul (positionA_angle_deriv q u t)).fun_sub
    (((secondComponent_angle_deriv q u t).mul_const (slopeRatio q u)).fun_mul
      (positionB_angle_deriv q u t))).const_mul 2 |>.congr_deriv (by
        rw [mixedSecond,mixedNormal,positionb,positionA,positionB]
        ring)

/-- A stationary chain is a critical point of the strip. -/
theorem stationary_isStripCritical {d : Coordinates} (hd : d.IsStationary) :
    StripCritical d.q d.c d.s (-d.y) := by
  obtain ⟨hc,hs,ht⟩ := stationary_tilt hd
  refine ⟨⟨hd.q_lower,hd.q_upper,(stationary_coordinate_lower hd).le,
    by linarith [hd.y_lower]⟩,hc,hs,d.unit,ht,?_,?_⟩
  · have hp := coordinate_positionHalf hd.toIsChain
    rw [hd.position_stationary] at hp
    linarith
  · rw [coordinate_tiltFirst hd.toIsChain]
    exact hd.tilt_stationary

end SquaresInCircles.Eight.Stationary.FiveCornerGeometry
end
end
end
