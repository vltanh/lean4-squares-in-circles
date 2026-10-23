module

public import SquaresInCircles.Eight.ExactFamily.CircleConvexity

/-!
# Strict radius decrease by nested circle inclusion

Uncompiled draft.  Increasing the squared radius enlarges the radical
position domain, increases both lower horizontal coordinates, and lowers
the final downward height.  Both positive corner components therefore
strictly decrease.  This finite comparison is stronger than the radius
derivative bound and does not require a differentiable minimizing envelope.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

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

/-- All intermediate signs and domain inclusions follow from the circle
equations.  No radius-dependent minimizer is chosen in this argument. -/
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

/-- The squared norm itself strictly decreases with radius, uniformly
over the full position domain and all admissible nonnegative tilts. -/
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

/-- The value of any minimum at the larger radius obeys the same strict
comparison.  Only its defining minimum property is needed. -/
theorem minimum_radius_strict {q₀ q₁ c s u₀ u₁ : ℝ}
    (hq : q₀<q₁) (hqu : q₁<4) (h₀ : Domain q₀ u₀)
    (hc : 0<c) (hcu : c ≤ 1) (hs : 0 ≤ s) (hsu : s ≤ 1)
    (hmin : ∀ u, Domain q₁ u → defect q₁ c s u₁ ≤ defect q₁ c s u) :
    defect q₁ c s u₁+q₁<defect q₀ c s u₀+q₀ := by
  have hm := hmin u₀ (domain_radius_inclusion hq hqu h₀).1
  linarith [defect_radius_strict hq hqu h₀ hc hcu hs hsu]

/-- Once the angular-envelope argument proves global minimality, this
finite comparison rules out two zero minima at distinct radii. -/
theorem radius_eq_of_zero_global_minima {q₀ q₁ c₀ s₀ c₁ s₁ u₀ u₁ : ℝ}
    (hq₀ : q₀<4) (hq₁ : q₁<4) (hu₀ : Domain q₀ u₀) (hu₁ : Domain q₁ u₁)
    (hc₀ : 0<c₀) (hcu₀ : c₀ ≤ 1) (hs₀ : 0 ≤ s₀) (hsu₀ : s₀ ≤ 1)
    (hc₁ : 0<c₁) (hcu₁ : c₁ ≤ 1) (hs₁ : 0 ≤ s₁) (hsu₁ : s₁ ≤ 1)
    (hz₀ : defect q₀ c₀ s₀ u₀=0) (hz₁ : defect q₁ c₁ s₁ u₁=0)
    (hm₀ : ∀ u, Domain q₀ u → defect q₀ c₀ s₀ u₀ ≤ defect q₀ c₁ s₁ u)
    (hm₁ : ∀ u, Domain q₁ u → defect q₁ c₁ s₁ u₁ ≤ defect q₁ c₀ s₀ u) :
    q₀=q₁ := by
  rcases lt_trichotomy q₀ q₁ with hlt | heq | hlt
  · have hd := defect_radius_decrease hlt hq₁ hu₀ hc₀ hcu₀ hs₀ hsu₀
    have hm := hm₁ u₀ (domain_radius_inclusion hlt hq₁ hu₀).1
    rw [hz₀] at hd
    rw [hz₁] at hm
    linarith
  · exact heq
  · have hd := defect_radius_decrease hlt hq₀ hu₁ hc₁ hcu₁ hs₁ hsu₁
    have hm := hm₀ u₁ (domain_radius_inclusion hlt hq₀ hu₁).1
    rw [hz₁] at hd
    rw [hz₀] at hm
    linarith

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry
