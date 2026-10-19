module

public import SquaresInCircles.Eight.ExactFamily.Coordinates
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.Order.Compact

/-!
# Eight squares: convexity of the chain in the position

The chain of `Coordinates` is written with the downward position `u = -y` and the four successive
square roots `r, U, Y, w` (`lowerRight`, `topRight`, `topHeight`, `lowerLeft`); the radical domain
`Domain q u` is `u ≥ 0` with the four radicands nonnegative. For `q < 4` a chord of a disk lies in
the disk, so applying it successively along the chain shows that the domain is convex and that the
two components `k₁, k₂` of the fifth corner are convex in `u`, the first strictly. Both are
positive for `0 < c ≤ 1`, `0 ≤ s ≤ 1`, so the defect `k₁² + k₂² - q` is strictly convex on the
whole domain, endpoints included (`strictConvexOn_defect`), and has at most one minimum
(`minimizer_unique`). The chart agrees with `Coordinates` (`coordinate_values`,
`coordinate_defect`). For `q₀ < q₁ < 4` each circle contains the smaller one, so
`F(q₁) < F(q₀) - (q₁ - q₀)` at every position and every tilt with `c > 0`, `s ≥ 0`
(`defect_radius_decrease`).

Where the four radicals are positive the defect is differentiable in the position, with
derivative `2 positionHalf` (`position_deriv`), and in the tilt `t`, with `c = cos t`, `s = sin t`,
it has the derivatives `tiltFirst` and `tiltSecond`. Throughout the strip
`(79/40)² ≤ q ≤ 9789/2500`, `0 ≤ s/c ≤ 1/5`, the circle equations bound the radicals at
`u = 87/100` by successive square comparisons, and five coefficient bounds then give
`positionHalf < 0` there (`comparison_position_negative`). By strict convexity every critical
position lies to the right (`stationary_position_lower`) and is the global minimum on the radical
domain (`stationary_global_minimum`); a stationary chain has `87/100 < -y`
(`stationary_coordinate_lower`). At the trial position `u = 15/16` the squared norm `k₁² + k₂²`
is at most a cubic in `s/c` that lies below its chord, with both ends below `4`, so
`k₁² + k₂² < 4` at every position minimum, whatever the sign of the defect
(`position_minimum_norm_lt_four`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

/-! ### The chain and its convexity in the position -/

def upper (q x : ℝ) : ℝ := Real.sqrt (q-x^2)
def lowerRight (q u : ℝ) : ℝ := upper q u
def topRight (q u : ℝ) : ℝ := upper q (2-u)
def topLeft (q u : ℝ) : ℝ := 3-topRight q u
def topHeight (q u : ℝ) : ℝ := upper q (topLeft q u)
def lowerHeight (q u : ℝ) : ℝ := 2-topHeight q u
def lowerLeft (q u : ℝ) : ℝ := upper q (lowerHeight q u)

def firstComponent (q c s u : ℝ) : ℝ :=
  2-c*(lowerRight q u-1)+s*u
def secondComponent (q c s u : ℝ) : ℝ :=
  1+c*lowerHeight q u-s*(lowerLeft q u-1)
def defect (q c s u : ℝ) : ℝ :=
  firstComponent q c s u^2+secondComponent q c s u^2-q

/-- The real-radical domain of the chain in the downward position. -/
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

/-- The chart is the chain of `Coordinates` with `u = -y`. -/
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

def comparisonX (q : ℝ) : ℝ := 87/100/lowerRight q (87/100)
def comparisonY (q : ℝ) : ℝ := lowerHeight q (87/100)/lowerLeft q (87/100)

structure ComparisonBounds (q : ℝ) : Prop where
  r_lower : 1773/1000<lowerRight q (87/100)
  r_upper : lowerRight q (87/100)<1778/1000
  U_lower : 1619/1000<topRight q (87/100)
  V_lower : 1375/1000<topLeft q (87/100)
  V_upper : topLeft q (87/100)<1381/1000
  Y_lower : 1411/1000<topHeight q (87/100)
  Y_upper : topHeight q (87/100)<1424/1000
  v_lower : 576/1000<lowerHeight q (87/100)
  v_upper : lowerHeight q (87/100)<589/1000
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
  exact ⟨hr.1,hr.2,hU.1,hV.1,hV.2,hY.1,hY.2,hv.1,hv.2,
    hw.1,hw.2,hp.1,hp.2,hx.1,hx.2,hy.1,hy.2⟩

def coefficientLc (q : ℝ) : ℝ := 2*comparisonX q-slopeRatio q (87/100)
def coefficientLs (q : ℝ) : ℝ := 2-slopeRatio q (87/100)*comparisonY q
def coefficientQc (q : ℝ) : ℝ :=
  (lowerRight q (87/100)-1)*comparisonX q+
    slopeRatio q (87/100)*lowerHeight q (87/100)
def coefficientJ (q : ℝ) : ℝ :=
  87/100*comparisonX q-(lowerRight q (87/100)-1)-
    slopeRatio q (87/100)*lowerHeight q (87/100)*comparisonY q+
      slopeRatio q (87/100)*(lowerLeft q (87/100)-1)
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

def comparisonPolynomial (q h L : ℝ) : ℝ :=
  L*coefficientLc q-coefficientQc q+h*(L*coefficientLs q+coefficientJ q)+
    h^2*coefficientQs q

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

/-- A critical position lies right of `87/100`. -/
theorem stationary_position_lower {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1)
    (hu : Domain q u) (hstat : HasDerivAt (defect q c s) 0 u) : 87/100<u := by
  have hq : q<4 := by linarith
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  have hconv := strictConvexOn_defect hq hc hcu hs hsu
  have hb := comparison_bounds hql hqu
  have hcomp := domain_of_pos (u:=87/100) (by norm_num) (by linarith [hb.r_lower])
    (by linarith [hb.U_lower]) (by linarith [hb.Y_lower]) (by linarith [hb.w_lower])
  have hd := position_deriv (q:=q) (c:=c) (s:=s) (u:=87/100)
    (by linarith [hb.r_lower]) (by linarith [hb.U_lower])
    (by linarith [hb.Y_lower]) (by linarith [hb.w_lower])
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

def firstTilt (q c s u : ℝ) : ℝ := s*(lowerRight q u-1)+c*u
def secondTilt (q c s u : ℝ) : ℝ := -s*lowerHeight q u-c*(lowerLeft q u-1)
def tiltFirst (q c s u : ℝ) : ℝ :=
  2*(firstComponent q c s u*firstTilt q c s u+
    secondComponent q c s u*secondTilt q c s u)
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

theorem coordinate_tiltFirst {d : Coordinates} (hd : d.IsChain) :
    tiltFirst d.q d.c d.s (-d.y)=d.tiltDerivative := by
  obtain ⟨hr,_,_,_,hv,hw⟩ := coordinate_values hd
  rw [tiltFirst,firstComponent,secondComponent,firstTilt,secondTilt,hr,hv,hw,
    Coordinates.tiltDerivative,Coordinates.h₁,Coordinates.h₂]
  ring

/-! ### The fifth corner at a position minimum -/

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

theorem position_stationary_norm_lt_four {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q<4)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1)
    (hu : Domain q u) (hstat : HasDerivAt (defect q c s) 0 u) :
    firstComponent q c s u^2+secondComponent q c s u^2<4 := by
  obtain ⟨hcu,hsu⟩ := unit_le_one hunit
  exact position_minimum_norm_lt_four hql hqu hc hs ht hunit
    (stationary_global_minimum hqu hc hcu hs hsu hu hstat)

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry
