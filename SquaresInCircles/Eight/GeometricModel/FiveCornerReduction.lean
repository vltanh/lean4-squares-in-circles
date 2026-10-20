module

public import SquaresInCircles.Eight.GeometricModel.Basic
public import SquaresInCircles.Eight.ExactFamily.CircleConvexity
public import SquaresInCircles.Common.Trigonometry

/-!
# The arbitrary five-point chain and its exact scalar reduction

Uncompiled draft. The five points are arbitrary points in a disk.
There is no square-coordinate, owner, core, or contact-equality premise.
The monotone circle replacement supplies every radical-domain inequality.

Source: HAND_FIVE_CORNER_MODEL_SELECTION.md, Section 2.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GeometricModel.FiveCorner

open Set
open ExactFamily
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

/-- The five spans with the repository's Euclidean dot product. -/
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

/-- The circle replacement, with all five projected contacts exact. -/
def scalarChain (q u t : ℝ) : FiveCorner where
  angle := t
  point := ![(lowerRight q u, -u),
    (topRight q u, 2-u),
    (-topLeft q u, topHeight q u),
    (-lowerLeft q u, -lowerHeight q u),
    inFrame t (-firstComponent q (Real.cos t) (Real.sin t) u)
      (-secondComponent q (Real.cos t) (Real.sin t) u)]

theorem scalarChain_contacts (q u t : ℝ) :
    ((scalarChain q u t).point 1).2 -
        ((scalarChain q u t).point 0).2 = 2 ∧
    ((scalarChain q u t).point 1).1 -
        ((scalarChain q u t).point 2).1 = 3 ∧
    ((scalarChain q u t).point 2).2 -
        ((scalarChain q u t).point 3).2 = 2 ∧
    dot (GeometricModel.f t)
        (sub ((scalarChain q u t).point 3) ((scalarChain q u t).point 4)) =
      1 + Real.sin t ∧
    dot (GeometricModel.e t)
        (sub ((scalarChain q u t).point 0) ((scalarChain q u t).point 4)) =
      2 + Real.cos t := by
  constructor
  · simp [scalarChain]
  constructor
  · simp [scalarChain, FiveCornerGeometry.topLeft]
  constructor
  · simp [scalarChain, FiveCornerGeometry.lowerHeight]
  constructor
  · simp only [scalarChain, Matrix.cons_val_succ, Matrix.cons_val_zero,
      dot_sub_right, dot_f_inFrame]
    dsimp [dot, GeometricModel.f, FiveCornerGeometry.secondComponent]
    ring
  · simp only [scalarChain, Matrix.cons_val_succ, Matrix.cons_val_zero,
      dot_sub_right, dot_e_inFrame]
    dsimp [dot, GeometricModel.e, FiveCornerGeometry.firstComponent]
    ring

theorem scalarChain_spans {q u t : ℝ} (ht : t ∈ Icc 0 (Real.pi / 4)) :
    (scalarChain q u t).spans := by
  obtain ⟨hab, hbd, hde, heh, hah⟩ := scalarChain_contacts q u t
  apply (spans_iff_spanBounds _).2
  exact ⟨ht.1, ht.2, hab.ge, hbd.ge, hde.ge, heh.ge, hah.ge⟩

theorem scalarChain_fits {q u t : ℝ} (hdom : Domain q u)
    (hF : defect q (Real.cos t) (Real.sin t) u ≤ 0) :
    (scalarChain q u t).fits (Real.sqrt q) := by
  have hq : 0 ≤ q := (sq_nonneg u).trans hdom.first_radicand
  refine ⟨Real.sqrt_nonneg _, fun i => ?_⟩
  rw [Real.sq_sqrt hq]
  fin_cases i
  · simpa [scalarChain, normSq, FiveCornerGeometry.lowerRight] using
      (FiveCornerGeometry.upper_circle hdom.first_radicand).le
  · simpa [scalarChain, normSq, FiveCornerGeometry.topRight] using
      (FiveCornerGeometry.upper_circle hdom.second_radicand).le
  · have h := FiveCornerGeometry.upper_circle hdom.third_radicand
    simpa [scalarChain, normSq, FiveCornerGeometry.topHeight, add_comm] using h.le
  · simpa [scalarChain, normSq, FiveCornerGeometry.lowerLeft] using
      (FiveCornerGeometry.upper_circle hdom.fourth_radicand).le
  · have hlast : firstComponent q (Real.cos t) (Real.sin t) u ^ 2 +
        secondComponent q (Real.cos t) (Real.sin t) u ^ 2 ≤ q := by
      dsimp [FiveCornerGeometry.defect] at hF
      linarith
    simpa [scalarChain, normSq_inFrame] using hlast

/-- A feasible original chain supplies the entire radical domain. -/
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
    dsimp [FiveCornerGeometry.topLeft]
    linarith
  have hDx : topLeft q u ≤ -(d.point 2).1 := by
    dsimp [FiveCornerGeometry.topLeft]
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
    dsimp [FiveCornerGeometry.lowerHeight]
    linarith
  have hEy : lowerHeight q u ≤ -(d.point 3).2 := by
    dsimp [FiveCornerGeometry.lowerHeight]
    linarith [h.de]
  have hvs := FiveCornerGeometry.square_mono_nonneg hv hEy
  have hvrad : lowerHeight q u ^ 2 ≤ q := by
    have hp := hfit.2 3
    dsimp [q, normSq] at *
    nlinarith [sq_nonneg (d.point 3).1]
  exact ⟨hu, hr, hUrad, hVrad, hvrad⟩

/-- Capping improves the two remaining projected requirements. -/
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
    dsimp [FiveCornerGeometry.topLeft]
    linarith [h.bd]
  have hDxsq := FiveCornerGeometry.square_mono_nonneg
    (hdom.topLeft_pos hq).le hDx
  have hDy : (d.point 2).2 ≤ topHeight q u := by
    apply Real.le_sqrt_of_sq_le
    have hp := hfit.2 2
    dsimp [q, normSq] at *
    nlinarith
  have hEy : lowerHeight q u ≤ -(d.point 3).2 := by
    dsimp [FiveCornerGeometry.lowerHeight]
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
  · dsimp [FiveCornerGeometry.firstComponent, dot, GeometricModel.e, u] at *
    linarith
  · dsimp [FiveCornerGeometry.secondComponent, dot, GeometricModel.f] at *
    linarith

/-- Full-domain scalar necessity for the original points. -/
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
  dsimp [FiveCornerGeometry.defect]
  nlinarith

/-- The last original corner's strict slack survives the circle capping. -/
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
  dsimp [FiveCornerGeometry.defect]
  nlinarith

theorem feasible_iff_scalar {R : ℝ} (hR₀ : 0 ≤ R) (hR : R < 2) :
    (∃ d : FiveCorner, d.spans ∧ d.fits R) ↔
      ∃ t ∈ Icc 0 (Real.pi / 4), ∃ u, Domain (R ^ 2) u ∧
        defect (R ^ 2) (Real.cos t) (Real.sin t) u ≤ 0 := by
  constructor
  · rintro ⟨d, hd, hf⟩
    have hb := (spans_iff_spanBounds d).1 hd
    exact ⟨d.angle, ⟨hb.angle_lower, hb.angle_upper⟩,
      -(d.point 0).2, scalar_reduction hd hf hR⟩
  · rintro ⟨t, ht, u, hdom, hF⟩
    refine ⟨scalarChain (R ^ 2) u t, scalarChain_spans ht, ?_⟩
    simpa [Real.sqrt_sq hR₀] using scalarChain_fits hdom hF

theorem full_domain_strictConvex {q t : ℝ} (hq : q < 4)
    (ht : t ∈ Icc 0 (Real.pi / 4)) :
    StrictConvexOn ℝ {u : ℝ | Domain q u}
      (defect q (Real.cos t) (Real.sin t)) := by
  obtain ⟨hc, hcu, hs, hsu⟩ := angle_trig ht
  exact FiveCornerGeometry.strictConvexOn_defect hq hc hcu hs hsu

end SquaresInCircles.Eight.GeometricModel.FiveCorner
