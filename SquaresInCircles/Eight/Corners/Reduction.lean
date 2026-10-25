module

public import SquaresInCircles.Common.Trigonometry
public import SquaresInCircles.Eight.Stationary.Convexity
public import SquaresInCircles.Eight.Equality.Basic

/-!
# Eight squares: the scalar reduction of five corners

Let `d` be five corners that span and lie in the disk of radius `R < 2`; nothing else is assumed
of them. Going round the chain from A to E, each corner is bounded by the point of the circle of
squared radius `R²` at the height or the abscissa that the spans give it, so the height
`u = -(d.point 0).2` of the first corner lies in the radical domain at `R²`
(`radial_domain_of_spans`), and the fifth corner has components at most `-k₁` and `-k₂` in the
frame of the turn (`support_caps_of_spans`). Hence the defect of the radical chain at
`(R², cos t, sin t, u)` is nonpositive (`scalar_reduction`), and even at most `|d.point 4|² - R²`
(`defect_le_last_corner`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.FiveCorner
open GeometricModel

open Set
open Stationary
namespace Scalar
abbrev upper := FiveCornerGeometry.upper
abbrev lowerRight := FiveCornerGeometry.lowerRight
abbrev topRight := FiveCornerGeometry.topRight
abbrev topLeft := FiveCornerGeometry.topLeft
abbrev topHeight := FiveCornerGeometry.topHeight
abbrev lowerHeight := FiveCornerGeometry.lowerHeight
abbrev lowerLeft := FiveCornerGeometry.lowerLeft
abbrev firstComponent := FiveCornerGeometry.firstComponent
abbrev secondComponent := FiveCornerGeometry.secondComponent
abbrev defect := FiveCornerGeometry.defect
abbrev Domain := FiveCornerGeometry.Domain
end Scalar

open Scalar

/-- The five spans, written with the dot product `dot`. -/
structure SpanBounds (d : FiveCorner) : Prop where
  angle_lower : 0 ≤ d.angle
  angle_upper : d.angle ≤ Real.pi / 4
  ab : 2 ≤ (d.point 1).2 - (d.point 0).2
  bd : 3 ≤ (d.point 1).1 - (d.point 2).1
  de : 2 ≤ (d.point 2).2 - (d.point 3).2
  eh : 1 + Real.sin d.angle ≤ dot (GeometricModel.f d.angle)
    (sub (d.point 3) (d.point 4))
  ah : 2 + Real.cos d.angle ≤ dot (GeometricModel.e d.angle)
    (sub (d.point 0) (d.point 4))

theorem spans_iff_spanBounds (d : FiveCorner) : d.spans ↔ SpanBounds d := by
  constructor
  · rintro ⟨ht₀, ht₁, hab, hbd, hde, heh, hah⟩
    exact ⟨ht₀, ht₁, hab, hbd, hde,
      by simpa [dot, sub, GeometricModel.f] using heh,
      by simpa [dot, sub, GeometricModel.e] using hah⟩
  · rintro ⟨ht₀, ht₁, hab, hbd, hde, heh, hah⟩
    exact ⟨ht₀, ht₁, hab, hbd, hde,
      by simpa [dot, sub, GeometricModel.f] using heh,
      by simpa [dot, sub, GeometricModel.e] using hah⟩

theorem angle_trig {t : ℝ} (ht : t ∈ Icc 0 (Real.pi / 4)) :
    0 < Real.cos t ∧ Real.cos t ≤ 1 ∧
    0 ≤ Real.sin t ∧ Real.sin t ≤ 1 := by
  obtain ⟨hc, hs, -⟩ := east_quadrant_trig ht.1 ht.2
  exact ⟨by linarith, Real.cos_le_one _, hs, Real.sin_le_one _⟩

def inFrame (t a b : ℝ) : Point :=
  (Real.cos t * a - Real.sin t * b, Real.sin t * a + Real.cos t * b)

theorem dot_e_inFrame (t a b : ℝ) :
    dot (GeometricModel.e t) (inFrame t a b) = a := by
  dsimp [dot, GeometricModel.e, inFrame]
  linear_combination a * (Real.sin_sq_add_cos_sq t)

theorem dot_f_inFrame (t a b : ℝ) :
    dot (GeometricModel.f t) (inFrame t a b) = b := by
  dsimp [dot, GeometricModel.f, inFrame]
  linear_combination b * (Real.sin_sq_add_cos_sq t)

theorem normSq_inFrame (t a b : ℝ) :
    normSq (inFrame t a b) = a ^ 2 + b ^ 2 := by
  dsimp [normSq, inFrame]
  linear_combination (a ^ 2 + b ^ 2) * (Real.sin_sq_add_cos_sq t)

theorem frame_energy (t : ℝ) (p : Point) :
    dot (GeometricModel.e t) p ^ 2 + dot (GeometricModel.f t) p ^ 2 =
      normSq p := by
  dsimp [normSq, dot, GeometricModel.e, GeometricModel.f]
  linear_combination (p.1 ^ 2 + p.2 ^ 2) * (Real.sin_sq_add_cos_sq t)

theorem coordinates_mem {p : Point} {R : ℝ} (hR : 0 ≤ R)
    (hp : normSq p ≤ R ^ 2) :
    p.1 ∈ Icc (-R) R ∧ p.2 ∈ Icc (-R) R := by
  dsimp [normSq] at hp
  have hx : p.1 ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg p.2]
  have hy : p.2 ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg p.1]
  exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

/-- Five corners that span and lie in the disk of radius `R < 2` give a position
`u = -(d.point 0).2` in the radical domain at `R²`. -/
theorem radial_domain_of_spans {d : FiveCorner} {R : ℝ}
    (hd : d.spans) (hfit : d.fits R) (hR : R < 2) :
    Domain (R ^ 2) (-(d.point 0).2) := by
  let u := -(d.point 0).2
  let q := R ^ 2
  have h := (spans_iff_spanBounds d).1 hd
  have h₀ := coordinates_mem hfit.1 (hfit.2 0)
  have h₁ := coordinates_mem hfit.1 (hfit.2 1)
  have hq : q < 4 := by dsimp [q]; nlinarith [hfit.1]
  have hu : 0 ≤ u := by dsimp [u]; linarith [h.ab, h₁.2.2]
  have huR : u ≤ R := by dsimp [u]; linarith [h₀.2.1]
  have hY₀ : 0 < 2-u := by linarith
  have hYB : 2-u ≤ (d.point 1).2 := by dsimp [u]; linarith [h.ab]
  have hr : u ^ 2 ≤ q := by
    have hp := hfit.2 0
    dsimp [u, q, normSq] at *
    nlinarith [sq_nonneg (d.point 0).1]
  have hUb := FiveCornerGeometry.square_mono_nonneg hY₀.le hYB
  have hUrad : (2-u) ^ 2 ≤ q := by
    have hp := hfit.2 1
    dsimp [q, normSq] at *
    nlinarith [sq_nonneg (d.point 1).1]
  have hBx : (d.point 1).1 ≤ topRight q u := by
    apply Real.le_sqrt_of_sq_le
    have hp := hfit.2 1
    dsimp [q, normSq] at *
    nlinarith
  have hU : topRight q u < 2 := FiveCornerGeometry.upper_lt_two hq hUrad
  have hV : 0 ≤ topLeft q u := by
    dsimp only [Scalar.topLeft, FiveCornerGeometry.topLeft]
    linarith
  have hDx : topLeft q u ≤ -(d.point 2).1 := by
    dsimp only [Scalar.topLeft, FiveCornerGeometry.topLeft]
    linarith [h.bd]
  have hVs := FiveCornerGeometry.square_mono_nonneg hV hDx
  have hVrad : topLeft q u ^ 2 ≤ q := by
    have hp := hfit.2 2
    dsimp [q, normSq] at *
    nlinarith [sq_nonneg (d.point 2).2]
  have hDy : (d.point 2).2 ≤ topHeight q u := by
    apply Real.le_sqrt_of_sq_le
    have hp := hfit.2 2
    dsimp [q, normSq] at *
    nlinarith
  have hY : topHeight q u < 2 := FiveCornerGeometry.upper_lt_two hq hVrad
  have hv : 0 ≤ lowerHeight q u := by
    dsimp only [Scalar.lowerHeight, FiveCornerGeometry.lowerHeight]
    linarith
  have hEy : lowerHeight q u ≤ -(d.point 3).2 := by
    dsimp only [Scalar.lowerHeight, FiveCornerGeometry.lowerHeight]
    linarith [h.de]
  have hvs := FiveCornerGeometry.square_mono_nonneg hv hEy
  have hvrad : lowerHeight q u ^ 2 ≤ q := by
    have hp := hfit.2 3
    dsimp [q, normSq] at *
    nlinarith [sq_nonneg (d.point 3).1]
  exact ⟨hu, hr, hUrad, hVrad, hvrad⟩

/-- The fifth corner has components at most `-k₁` and `-k₂` in the frame of the turn, each corner
before it being bounded by the circle. -/
theorem support_caps_of_spans {d : FiveCorner} {R : ℝ}
    (hd : d.spans) (hfit : d.fits R) (hR : R < 2) :
    dot (GeometricModel.e d.angle) (d.point 4) ≤
      -firstComponent (R ^ 2) (Real.cos d.angle) (Real.sin d.angle) (-(d.point 0).2) ∧
    dot (GeometricModel.f d.angle) (d.point 4) ≤
      -secondComponent (R ^ 2) (Real.cos d.angle) (Real.sin d.angle) (-(d.point 0).2) := by
  let u := -(d.point 0).2
  let q := R ^ 2
  have h := (spans_iff_spanBounds d).1 hd
  have hdom := radial_domain_of_spans hd hfit hR
  obtain ⟨hc, -, hs, -⟩ := angle_trig ⟨h.angle_lower, h.angle_upper⟩
  have hq : q < 4 := by dsimp [q]; nlinarith [hfit.1]
  have hAx : (d.point 0).1 ≤ lowerRight q u := by
    apply Real.le_sqrt_of_sq_le
    have hp := hfit.2 0
    dsimp [q, u, normSq] at *
    nlinarith
  have hYB : 2-u ≤ (d.point 1).2 := by dsimp [u]; linarith [h.ab]
  have huR : u ≤ R := by
    have hh := coordinates_mem hfit.1 (hfit.2 0)
    dsimp [u]
    linarith [hh.2.1]
  have hYBsq := FiveCornerGeometry.square_mono_nonneg (by linarith : 0 ≤ 2-u) hYB
  have hBx : (d.point 1).1 ≤ topRight q u := by
    apply Real.le_sqrt_of_sq_le
    have hp := hfit.2 1
    dsimp [q, normSq] at *
    nlinarith
  have hDx : topLeft q u ≤ -(d.point 2).1 := by
    dsimp only [Scalar.topLeft, FiveCornerGeometry.topLeft]
    linarith [h.bd]
  have hDxsq := FiveCornerGeometry.square_mono_nonneg
    (hdom.topLeft_pos hq).le hDx
  have hDy : (d.point 2).2 ≤ topHeight q u := by
    apply Real.le_sqrt_of_sq_le
    have hp := hfit.2 2
    dsimp [q, normSq] at *
    nlinarith
  have hEy : lowerHeight q u ≤ -(d.point 3).2 := by
    dsimp only [Scalar.lowerHeight, FiveCornerGeometry.lowerHeight]
    linarith [h.de]
  have hEysq := FiveCornerGeometry.square_mono_nonneg
    (hdom.lowerHeight_pos hq).le hEy
  have hEx : -(d.point 3).1 ≤ lowerLeft q u := by
    apply Real.le_sqrt_of_sq_le
    have hp := hfit.2 3
    dsimp [q, normSq] at *
    nlinarith
  have hAc := mul_le_mul_of_nonneg_left hAx hc.le
  have hEc := mul_le_mul_of_nonneg_left hEy hc.le
  have hEs := mul_le_mul_of_nonneg_left hEx hs
  have hah := h.ah
  have heh := h.eh
  rw [dot_sub_right] at hah heh
  constructor
  · dsimp only [Scalar.firstComponent, FiveCornerGeometry.firstComponent, dot,
      GeometricModel.e, u] at *
    linarith
  · dsimp only [Scalar.secondComponent, FiveCornerGeometry.secondComponent, dot,
      GeometricModel.f] at *
    linarith

/-- Five corners that span and lie in the disk of radius `R < 2` give a position in the radical
domain with a nonpositive defect. -/
theorem scalar_reduction {d : FiveCorner} {R : ℝ}
    (hd : d.spans) (hfit : d.fits R) (hR : R < 2) :
    Domain (R ^ 2) (-(d.point 0).2) ∧
    defect (R ^ 2) (Real.cos d.angle) (Real.sin d.angle) (-(d.point 0).2) ≤ 0 := by
  have h := (spans_iff_spanBounds d).1 hd
  have hdom := radial_domain_of_spans hd hfit hR
  obtain ⟨he, hf⟩ := support_caps_of_spans hd hfit hR
  obtain ⟨hc, hcu, hs, hsu⟩ := angle_trig ⟨h.angle_lower, h.angle_upper⟩
  have hq : R ^ 2 < 4 := by nlinarith [hfit.1]
  obtain ⟨hk₁, hk₂⟩ := FiveCornerGeometry.components_pos hq hdom hc hcu hs hsu
  have he' := FiveCornerGeometry.square_mono_nonneg hk₁.le
    (show firstComponent (R ^ 2) (Real.cos d.angle) (Real.sin d.angle)
      (-(d.point 0).2) ≤ -dot (GeometricModel.e d.angle) (d.point 4) by linarith)
  have hf' := FiveCornerGeometry.square_mono_nonneg hk₂.le
    (show secondComponent (R ^ 2) (Real.cos d.angle) (Real.sin d.angle)
      (-(d.point 0).2) ≤ -dot (GeometricModel.f d.angle) (d.point 4) by linarith)
  have henergy := frame_energy d.angle (d.point 4)
  have hlast := hfit.2 4
  refine ⟨hdom, ?_⟩
  dsimp only [Scalar.defect, FiveCornerGeometry.defect]
  nlinarith

/-- The defect is at most `|d.point 4|² - R²`, so a strict slack of the fifth corner gives a
negative defect. -/
theorem defect_le_last_corner {d : FiveCorner} {R : ℝ}
    (hd : d.spans) (hfit : d.fits R) (hR : R < 2) :
    defect (R ^ 2) (Real.cos d.angle) (Real.sin d.angle) (-(d.point 0).2) ≤
      normSq (d.point 4)-R ^ 2 := by
  have h := (spans_iff_spanBounds d).1 hd
  have hdom := radial_domain_of_spans hd hfit hR
  obtain ⟨he, hf⟩ := support_caps_of_spans hd hfit hR
  obtain ⟨hc, hcu, hs, hsu⟩ := angle_trig ⟨h.angle_lower, h.angle_upper⟩
  have hq : R ^ 2 < 4 := by nlinarith [hfit.1]
  obtain ⟨hk₁, hk₂⟩ := FiveCornerGeometry.components_pos hq hdom hc hcu hs hsu
  have he' := FiveCornerGeometry.square_mono_nonneg hk₁.le
    (show firstComponent (R ^ 2) (Real.cos d.angle) (Real.sin d.angle)
      (-(d.point 0).2) ≤ -dot (GeometricModel.e d.angle) (d.point 4) by linarith)
  have hf' := FiveCornerGeometry.square_mono_nonneg hk₂.le
    (show secondComponent (R ^ 2) (Real.cos d.angle) (Real.sin d.angle)
      (-(d.point 0).2) ≤ -dot (GeometricModel.f d.angle) (d.point 4) by linarith)
  have henergy := frame_energy d.angle (d.point 4)
  dsimp only [Scalar.defect, FiveCornerGeometry.defect]
  nlinarith

end SquaresInCircles.Eight.FiveCorner
