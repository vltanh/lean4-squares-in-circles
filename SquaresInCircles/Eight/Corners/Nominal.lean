module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import SquaresInCircles.Common.Trigonometry
public import SquaresInCircles.Eight.Equality.Angles
public import SquaresInCircles.Eight.Stationary.CriticalHessian
public import SquaresInCircles.Eight.Stationary.System

/-!
# Eight squares: the single polynomial nominal support and global tilt localization

The completed-circle inequality is applied directly to
the five arbitrary points. Its masses and contact weights are one explicit
family on the full sine interval [0,3/10], including the zero E force at
sine zero. No core or sorted-coordinate hypothesis is present.

-/

section
/-!
## The scalar reduction of five corners

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
end
end
end

section
/-!
## One support on the complete high-tilt arc

One constant choice of five positive contact weights is used throughout.
The coefficient collection applies to arbitrary five points.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.FiveCorner
open GeometricModel

open Set

def spanForces (t a b d η : ℝ) : Fin 5 → Point :=
  ![(Real.cos t, Real.sin t-a), (b,a), (-b,d),
    (-η*Real.sin t, η*Real.cos t-d),
    (η*Real.sin t-Real.cos t, -η*Real.cos t-Real.sin t)]

def spanDemand (t a b d η : ℝ) : ℝ :=
  2*a+3*b+2*d+η+2+η*Real.sin t+Real.cos t

theorem weighted_spans {p : FiveCorner} (hp : p.spans)
    {a b d η : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hη : 0 ≤ η) :
    spanDemand p.angle a b d η ≤
      ∑ i : Fin 5, dot (spanForces p.angle a b d η i) (p.point i) := by
  have h := (spans_iff_spanBounds p).1 hp
  have h₁ := mul_le_mul_of_nonneg_left h.ab ha
  have h₂ := mul_le_mul_of_nonneg_left h.bd hb
  have h₃ := mul_le_mul_of_nonneg_left h.de hd
  have h₄ := mul_le_mul_of_nonneg_left h.eh hη
  have h₅ := h.ah
  simp only [Fin.sum_univ_five, spanForces, Matrix.cons_val, dot, sub,
    GeometricModel.e, GeometricModel.f, spanDemand] at *
  linarith

theorem dot_le_disk_support {v p : Point} {R : ℝ}
    (hR : 0 ≤ R) (hp : normSq p ≤ R ^ 2) :
    dot v p ≤ R * Real.sqrt (normSq v) := by
  have hc := cauchy_sq v p
  have hm := mul_le_mul_of_nonneg_left hp (normSq_nonneg v)
  have hs := Real.sq_sqrt (normSq_nonneg v)
  have hsq : (R*Real.sqrt (normSq v)) ^ 2 = R ^ 2*normSq v := by
    rw [mul_pow, hs]
  have hn : 0 ≤ R*Real.sqrt (normSq v) := mul_nonneg hR (Real.sqrt_nonneg _)
  nlinarith

theorem disk_stress {p : FiveCorner} {R a b d η : ℝ}
    (hp : p.spans) (hR : p.fits R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hη : 0 ≤ η) :
    spanDemand p.angle a b d η ≤
      R * ∑ i : Fin 5, Real.sqrt (normSq (spanForces p.angle a b d η i)) := by
  have h := weighted_spans hp ha hb hd hη
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
    dot_le_disk_support hR.1 (hR.2 i) (v := spanForces p.angle a b d η i))
  rw [← Finset.mul_sum] at hs
  exact h.trans hs

namespace HighTilt

def a : ℝ := 23/30
def b : ℝ := 31/32
def d : ℝ := 9/10
def η : ℝ := 6/7
def ceiling : ℝ := 9789/2500
def supportRadius : ℝ := 4947/2500
def lowerAngle : ℝ := Real.arcsin (3/10)
def P₁ : ℝ := 1+a^2
def P₄ : ℝ := d^2+η^2
def g₁ (t : ℝ) : ℝ := Real.sqrt (harmonicArg P₁ 0 (-2*a) t)
def g₄ (t : ℝ) : ℝ := Real.sqrt (harmonicArg P₄ (-2*d*η) 0 t)
def K : ℝ := Real.sqrt (a^2+b^2) + Real.sqrt (b^2+d^2) + Real.sqrt (1+η^2)
def totalNorm (t : ℝ) : ℝ := K+g₁ t+g₄ t
def baseDemand : ℝ := 2*a+3*b+2*d+η+2
def gap (t : ℝ) : ℝ :=
  baseDemand-supportRadius*K + harmonic 1 η t +
    harmonicRoot supportRadius P₁ 0 (-2*a) t +
    harmonicRoot supportRadius P₄ (-2*d*η) 0 t

theorem gap_eq (t : ℝ) :
    gap t = spanDemand t a b d η-supportRadius*totalNorm t := by
  dsimp [gap, spanDemand, totalNorm, baseDemand, harmonic, harmonicRoot, g₁, g₄]
  ring

theorem root₁_pos (t : ℝ) : 0 < harmonicArg P₁ 0 (-2*a) t := by
  exact harmonic_arg_positive (a := 1) (b := a)
    (by norm_num) (by norm_num [a]) (by norm_num [a])
    (by norm_num [P₁]) (by ring)

theorem root₄_pos (t : ℝ) : 0 < harmonicArg P₄ (-2*d*η) 0 t := by
  exact harmonic_arg_positive (a := d) (b := η)
    (by norm_num [d]) (by norm_num [η]) (by norm_num [d, η])
    (by rfl) (by ring)

theorem force_norms (t : ℝ) :
    (fun i : Fin 5 => Real.sqrt (normSq (spanForces t a b d η i))) =
      ![g₁ t, Real.sqrt (a^2+b^2), Real.sqrt (b^2+d^2),
        g₄ t, Real.sqrt (1+η^2)] := by
  funext i
  fin_cases i
  all_goals
    simp only [spanForces]
    congr 1
  · dsimp [normSq, g₁, harmonicArg, P₁]
    linear_combination Real.sin_sq_add_cos_sq t
  · dsimp [normSq]
    ring
  · dsimp [normSq]
    ring
  · dsimp [normSq, g₄, harmonicArg, P₄]
    linear_combination η^2 * Real.sin_sq_add_cos_sq t
  · dsimp [normSq]
    linear_combination (1+η^2) * Real.sin_sq_add_cos_sq t

theorem norm_sum (t : ℝ) :
    (∑ i : Fin 5, Real.sqrt (normSq (spanForces t a b d η i))) = totalNorm t := by
  rw [force_norms]
  simp [Fin.sum_univ_succ, totalNorm, K]
  ring

theorem norm_positive (t : ℝ) : 0 < totalNorm t := by
  have hg : 0 < g₁ t := Real.sqrt_pos.mpr (root₁_pos t)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have h₄ : 0 ≤ g₄ t := Real.sqrt_nonneg _
  dsimp [totalNorm]
  linarith

/-- The norm curvature identity, in the general first-harmonic form. -/
theorem harmonicCurvature_le_quarter {R P Q T x : ℝ}
    (hR : 0 ≤ R) (hpq : Q^2+T^2 ≤ P^2)
    (hx : 0 < harmonicArg P Q T x) :
    harmonicCurvature R P Q T x ≤ R*Real.sqrt (harmonicArg P Q T x)/4 := by
  let z := Q*Real.cos x+T*Real.sin x
  let L := Real.sqrt (P+z)
  have hA : harmonicArg P Q T x = P+z := by
    dsimp only [harmonicArg, z]
    ring
  have hz : 0 < P+z := hA ▸ hx
  have hL : 0 < L := Real.sqrt_pos.mpr hz
  have hLs : L^2=P+z := Real.sq_sqrt hz.le
  have hden : 0 < 4*(P+z)*L := by positivity
  have hp := mul_nonneg hR (sub_nonneg.mpr hpq)
  rw [hA]
  change R*(z^2+2*P*z+Q^2+T^2)/(4*(P+z)*L) ≤ R*L/4
  rw [div_le_iff₀ hden]
  nlinarith [congrArg (fun y : ℝ => R*(P+z)*y) hLs]

theorem root_bounds {t : ℝ} (ht : t ∈ Icc 0 (Real.pi/4)) :
    g₁ t < 13/10 ∧ g₄ t < 7/10 := by
  obtain ⟨hc, hs, -⟩ := east_quadrant_trig ht.1 ht.2
  have h₁ := Real.sq_sqrt (root₁_pos t).le
  have h₄ := Real.sq_sqrt (root₄_pos t).le
  have hn₁ : 0 ≤ g₁ t := Real.sqrt_nonneg _
  have hn₄ : 0 ≤ g₄ t := Real.sqrt_nonneg _
  change g₁ t ^ 2 = _ at h₁
  change g₄ t ^ 2 = _ at h₄
  dsimp [harmonicArg, P₁, P₄, a, d, η] at h₁ h₄
  constructor <;> nlinarith

theorem harmonic_lower {t : ℝ} (ht : t ∈ Icc 0 (Real.pi/4)) :
    1 ≤ harmonic 1 η t := by
  have hc : ConcaveOn ℝ (Icc 0 (Real.pi/4)) (harmonic 1 η) :=
    harmonic_concave (fun x hx => harmonic_nonneg (by norm_num)
      (by norm_num [η]) ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  have hl : harmonic 1 η 0 = 1 := by simp [harmonic]
  have hu : 1 ≤ harmonic 1 η (Real.pi/4) := by
    obtain ⟨hh, -, -⟩ := east_quadrant_trig
      (by linarith [Real.pi_pos] : 0 ≤ Real.pi/4) le_rfl
    rw [Real.cos_pi_div_four] at hh
    simp only [harmonic, Real.cos_pi_div_four, Real.sin_pi_div_four]
    dsimp [η]
    linarith
  have hm := hc.min_le_of_mem_Icc
    (left_mem_Icc.mpr (by linarith [Real.pi_pos]))
    (right_mem_Icc.mpr (by linarith [Real.pi_pos])) ht
  rw [hl, min_eq_left hu] at hm
  exact hm

def gapD (t : ℝ) : ℝ :=
  harmonic η (-1) t + harmonicRootD supportRadius P₁ 0 (-2*a) t +
    harmonicRootD supportRadius P₄ (-2*d*η) 0 t

def gapDD (t : ℝ) : ℝ :=
  harmonic (-1) (-η) t + harmonicCurvature supportRadius P₁ 0 (-2*a) t +
    harmonicCurvature supportRadius P₄ (-2*d*η) 0 t

theorem gap_derivative (t : ℝ) : HasDerivAt gap (gapD t) t := by
  convert ((((harmonic_hasDerivAt 1 η t).const_add
    (baseDemand-supportRadius*K)).add (harmonicRoot_deriv (root₁_pos t))).add
      (harmonicRoot_deriv (root₄_pos t))) using 1 <;> rfl

theorem gap_second_derivative (t : ℝ) : HasDerivAt gapD (gapDD t) t := by
  exact ((harmonic_hasDerivAt η (-1) t).add
    (harmonicRoot_second (root₁_pos t))).add (harmonicRoot_second (root₄_pos t))

theorem gap_second_negative {t : ℝ} (ht : t ∈ Icc 0 (Real.pi/4)) :
    gapDD t < 0 := by
  have h₁ := harmonicCurvature_le_quarter (R := supportRadius)
    (by norm_num [supportRadius]) (by norm_num [P₁, a]) (root₁_pos t)
  have h₄ := harmonicCurvature_le_quarter (R := supportRadius)
    (by norm_num [supportRadius]) (by norm_num [P₄, d, η]) (root₄_pos t)
  obtain ⟨hg₁, hg₄⟩ := root_bounds ht
  have hh := harmonic_lower ht
  change _ ≤ supportRadius*g₁ t/4 at h₁
  change _ ≤ supportRadius*g₄ t/4 at h₄
  dsimp [gapDD, harmonic, supportRadius] at *
  linarith

theorem gap_concave : ConcaveOn ℝ (Icc 0 (Real.pi/4)) gap :=
  concave_of_deriv2 (fun t _ => gap_derivative t)
    (fun t _ => gap_second_derivative t) (fun _ ht => (gap_second_negative ht).le)

theorem constant_norm_bound : K < 31/8 := by
  have h₁ : Real.sqrt (a^2+b^2) = 593/480 := by
    have he : a^2+b^2=(593/480:ℝ)^2 := by norm_num [a, b]
    rw [he, Real.sqrt_sq (by norm_num)]
  have h₂ : Real.sqrt (b^2+d^2) < 13223/10000 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num [b, d])
  have h₃ : Real.sqrt (1+η^2) < 13171/10000 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num [η])
  dsimp [K]
  rw [h₁]
  linarith

theorem lower_angle_nonneg : 0 ≤ lowerAngle :=
  Real.arcsin_nonneg.mpr (by norm_num)

theorem lower_angle_sine : Real.sin lowerAngle = 3/10 :=
  Real.sin_arcsin (by norm_num) (by norm_num)

theorem lower_endpoint : 0 < gap lowerAngle := by
  have hs := lower_angle_sine
  have hc₀ : 0 ≤ Real.cos lowerAngle := Real.cos_arcsin_nonneg _
  have hu := Real.sin_sq_add_cos_sq lowerAngle
  rw [hs] at hu
  have hc : 9539/10000 < Real.cos lowerAngle := by nlinarith
  have h₁s := Real.sq_sqrt (root₁_pos lowerAngle).le
  have h₄s := Real.sq_sqrt (root₄_pos lowerAngle).le
  change g₁ lowerAngle ^ 2 = _ at h₁s
  change g₄ lowerAngle ^ 2 = _ at h₄s
  have h₁n : 0 ≤ g₁ lowerAngle := Real.sqrt_nonneg _
  have h₄n : 0 ≤ g₄ lowerAngle := Real.sqrt_nonneg _
  dsimp [harmonicArg, P₁, P₄, a, d, η] at h₁s h₄s
  rw [hs] at h₁s h₄s
  have hg₁ : g₁ lowerAngle < 17/16 := by nlinarith
  have hg₄ : g₄ lowerAngle < 271/1000 := by nlinarith
  have hK := constant_norm_bound
  have hmargin :
      baseDemand+(3/10)*η+9539/10000-
        supportRadius*(31/8+17/16+271/1000) = 124871/105000000 := by
    norm_num [baseDemand, a, b, d, η, supportRadius]
  rw [gap_eq]
  dsimp [spanDemand, totalNorm, baseDemand, a, b, d, η, supportRadius] at *
  rw [hs]
  linarith

theorem upper_endpoint : 0 < gap (Real.pi/4) := by
  have hsqrt := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  have hc : (707/1000:ℝ) < Real.sqrt 2/2 := by nlinarith
  have h₁s := Real.sq_sqrt (root₁_pos (Real.pi/4)).le
  have h₄s := Real.sq_sqrt (root₄_pos (Real.pi/4)).le
  change g₁ (Real.pi/4) ^ 2 = _ at h₁s
  change g₄ (Real.pi/4) ^ 2 = _ at h₄s
  have h₁n : 0 ≤ g₁ (Real.pi/4) := Real.sqrt_nonneg _
  have h₄n : 0 ≤ g₄ (Real.pi/4) := Real.sqrt_nonneg _
  simp only [harmonicArg, Real.sin_pi_div_four, Real.cos_pi_div_four] at h₁s h₄s
  dsimp [P₁, P₄, a, d, η] at h₁s h₄s
  have hg₁ : g₁ (Real.pi/4) < 71/100 := by nlinarith
  have hg₄ : g₄ (Real.pi/4) < 27/40 := by nlinarith
  have hK := constant_norm_bound
  have hmargin :
      baseDemand+(η+1)*(707/1000)-
        supportRadius*(31/8+71/100+27/40) = 13001/10500000 := by
    norm_num [baseDemand, a, b, d, η, supportRadius]
  rw [gap_eq]
  simp only [spanDemand, Real.sin_pi_div_four, Real.cos_pi_div_four]
  dsimp [totalNorm, baseDemand, a, b, d, η, supportRadius] at *
  linarith

theorem gap_positive {t : ℝ} (ht : t ∈ Icc lowerAngle (Real.pi/4)) :
    0 < gap t := by
  have hc : ConcaveOn ℝ (Icc lowerAngle (Real.pi/4)) gap :=
    gap_concave.subset (Icc_subset_Icc lower_angle_nonneg le_rfl) (convex_Icc _ _)
  exact concave_gt_of_endpoints hc ht lower_endpoint upper_endpoint

theorem exclusion {p : FiveCorner} {R : ℝ} (hp : p.spans) (hfit : p.fits R)
    (hq : R ^ 2 ≤ ceiling) (hs : 3/10 ≤ Real.sin p.angle) : False := by
  have h := (spans_iff_spanBounds p).1 hp
  have ht : lowerAngle ≤ p.angle := by
    have hh := Real.arcsin_le_arcsin hs
    rwa [Real.arcsin_sin (by linarith [h.angle_lower, Real.pi_pos])
      (by linarith [h.angle_upper, Real.pi_pos])] at hh
  have hg := gap_positive ⟨ht, h.angle_upper⟩
  have hc := disk_stress (a := a) (b := b) (d := d) (η := η) hp hfit
    (by norm_num [a]) (by norm_num [b]) (by norm_num [d]) (by norm_num [η])
  rw [norm_sum] at hc
  have hR : R < supportRadius := by
    have hsq : supportRadius ^ 2-ceiling=309/6250000 := by
      norm_num [supportRadius, ceiling]
    have hr : 0 < supportRadius := by norm_num [supportRadius]
    nlinarith [hfit.1]
  have hnorm := norm_positive p.angle
  have hm := mul_lt_mul_of_pos_right hR hnorm
  rw [gap_eq] at hg
  linarith

end HighTilt
end SquaresInCircles.Eight.FiveCorner
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.FiveCorner
open GeometricModel

open Set

theorem dot_le_completed_circle {m q : ℝ} {p F : Point}
    (hm : 0 < m) (hp : normSq p ≤ q) :
    dot F p ≤ m*q+normSq F/(4*m) := by
  have hbound := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4*m^2 by positivity)
  have hx := sq_nonneg (F.1-2*m*p.1)
  have hy := sq_nonneg (F.2-2*m*p.2)
  have hmul : (dot F p-m*q)*(4*m) ≤ normSq F := by
    dsimp [normSq, dot] at *
    nlinarith
  have hdiv : dot F p-m*q ≤ normSq F/(4*m) :=
    (le_div_iff₀ (by positivity : 0 < 4*m)).mpr hmul
  linarith

theorem dot_le_completed_circle_or_zero {m q : ℝ} {p F : Point}
    (hm : 0 ≤ m) (hz : m=0 → F=(0,0)) (hp : normSq p ≤ q) :
    dot F p ≤ m*q+normSq F/(4*m) := by
  by_cases hzero : m=0
  · simp [hzero, hz hzero, dot, normSq]
  · exact dot_le_completed_circle (lt_of_le_of_ne hm (Ne.symm hzero)) hp

namespace Nominal

def ceiling : ℝ := 1957767069/500000000
def alpha (s : ℝ) : ℝ := 24/41+(49/100)*s-s^2/20
def beta (s : ℝ) : ℝ := 1-s/20-s^2/6
def delta (s : ℝ) : ℝ := 36/31-(7/10)*s-s^2/16
def epsilon (s : ℝ) : ℝ := 36/31-s+(11/20)*s^2
def mA (s : ℝ) : ℝ := (12/41)/(1+13*s/60)
def mB (s : ℝ) : ℝ := (12/41)/(1-9*s/50)
def mD (s : ℝ) : ℝ := (12/31)/(1+9*s/25)
def mH (s : ℝ) : ℝ := (12/31)/(1+49*s/100)
def mE (s : ℝ) : ℝ := (3*s/10)/(1+4*s/5)
def mass (s : ℝ) : Fin 5 → ℝ := ![mA s,mB s,mD s,mE s,mH s]
def massSum (s : ℝ) : ℝ := ∑ i : Fin 5, mass s i
def forces (t : ℝ) : Fin 5 → Point :=
  spanForces t (alpha (Real.sin t)) (beta (Real.sin t))
    (delta (Real.sin t)) (epsilon (Real.sin t))
def demand (t : ℝ) : ℝ :=
  spanDemand t (alpha (Real.sin t)) (beta (Real.sin t))
    (delta (Real.sin t)) (epsilon (Real.sin t))
def energy (t : ℝ) : ℝ :=
  ∑ i : Fin 5, normSq (forces t i)/(4*mass (Real.sin t) i)
def gap (q t : ℝ) : ℝ := demand t-energy t-q*massSum (Real.sin t)

theorem denominator_bounds {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    0 < 1+13*s/60 ∧ 0 < 1-9*s/50 ∧
    0 < 1+9*s/25 ∧ 0 < 1+49*s/100 ∧ 0 < 1+4*s/5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith [hs.1, hs.2]

theorem weights_pos {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    0 < alpha s ∧ 0 < beta s ∧ 0 < delta s ∧ 0 < epsilon s := by
  have hs₂ : s^2 ≤ 9/100 := by
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  dsimp [alpha, beta, delta, epsilon]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hs.1, hs.2, sq_nonneg s]

theorem mass_nonneg {s : ℝ} (hs : s ∈ Icc 0 (3/10)) (i : Fin 5) :
    0 ≤ mass s i := by
  have hs₀ := hs.1
  obtain ⟨hA, hB, hD, hH, hE⟩ := denominator_bounds hs
  fin_cases i <;> simp only [mass]
  all_goals
    dsimp [mA, mB, mD, mH, mE]
    positivity

theorem mass_pos {s : ℝ} (hs : s ∈ Icc 0 (3/10)) (hs₀ : 0 < s)
    (i : Fin 5) : 0 < mass s i := by
  obtain ⟨hA, hB, hD, hH, hE⟩ := denominator_bounds hs
  fin_cases i <;> simp only [mass]
  all_goals
    dsimp [mA, mB, mD, mH, mE]
    positivity

theorem mass_sum_nonneg {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    0 ≤ massSum s :=
  Finset.sum_nonneg (fun i _ => mass_nonneg hs i)

theorem mass_force_zero {t : ℝ} (ht : t ∈ Icc 0 (Real.pi/4))
    (hs : Real.sin t ∈ Icc 0 (3/10)) (i : Fin 5)
    (hz : mass (Real.sin t) i=0) : forces t i=(0,0) := by
  by_cases hs₀ : Real.sin t=0
  · have hc : Real.cos t=1 := by
      have hunit := Real.sin_sq_add_cos_sq t
      have hc₀ := (angle_trig ht).1
      rw [hs₀] at hunit
      nlinarith
    fin_cases i <;>
      simp [mass, mA, mB, mD, mE, mH, hs₀] at hz
    simp [forces, spanForces, hs₀, hc, delta, epsilon]
  · have hp := mass_pos hs (lt_of_le_of_ne hs.1 (Ne.symm hs₀)) i
    linarith

/-- The nominal stress is valid on arbitrary original point coordinates. -/
theorem gap_nonpos_of_spans {p : FiveCorner} {R : ℝ}
    (hp : p.spans) (hfit : p.fits R) (hs : Real.sin p.angle ≤ 3/10) :
    gap (R^2) p.angle ≤ 0 := by
  have h := (spans_iff_spanBounds p).1 hp
  have ht : p.angle ∈ Icc 0 (Real.pi/4) := ⟨h.angle_lower, h.angle_upper⟩
  have hs' : Real.sin p.angle ∈ Icc 0 (3/10) := ⟨(angle_trig ht).2.2.1, hs⟩
  obtain ⟨ha, hb, hd, he⟩ := weights_pos hs'
  have hspan := weighted_spans hp ha.le hb.le hd.le he.le
  have hcircle := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
    dot_le_completed_circle_or_zero (mass_nonneg hs' i)
      (mass_force_zero ht hs' i) (hfit.2 i))
  change (∑ i : Fin 5, dot (forces p.angle i) (p.point i)) ≤
    ∑ i : Fin 5, (mass (Real.sin p.angle) i*R^2+
      normSq (forces p.angle i)/(4*mass (Real.sin p.angle) i)) at hcircle
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hcircle
  change demand p.angle ≤ ∑ i : Fin 5, dot (forces p.angle i) (p.point i) at hspan
  dsimp [gap, energy, massSum]
  linarith

theorem gap_radius_identity (q r t : ℝ) :
    gap q t=gap r t+(r-q)*massSum (Real.sin t) := by
  dsimp [gap]
  ring

def T4 (x : ℝ) : ℝ := 1-x+x^2-x^3+x^4
def B4 (x : ℝ) : ℝ := 1+x+x^2+x^3+(500/473)*x^4
def massUpper (s : ℝ) : ℝ :=
  (12/41)*(T4 (13*s/60)+B4 (9*s/50)) +
  (12/31)*(T4 (9*s/25)+T4 (49*s/100)) +
  (3*s/10)*T4 (4*s/5)

theorem inverse_le_T4 {x : ℝ} (hx : 0 ≤ x) : 1/(1+x) ≤ T4 x := by
  rw [div_le_iff₀ (by linarith : 0 < 1+x)]
  have hpow := pow_nonneg hx 5
  dsimp [T4]
  nlinarith

theorem inverse_le_B4 {x : ℝ} (hx : x ∈ Icc 0 (27/500)) :
    1/(1-x) ≤ B4 x := by
  rw [div_le_iff₀ (by linarith [hx.2] : 0 < 1-x)]
  have hp := mul_nonneg (pow_nonneg hx.1 4)
    (show 0 ≤ 27-500*x by linarith [hx.2])
  dsimp [B4]
  nlinarith

theorem mass_sum_le_upper {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    massSum s ≤ massUpper s := by
  have hs₀ := hs.1
  have hA := mul_le_mul_of_nonneg_left
    (inverse_le_T4 (show 0 ≤ 13*s/60 by positivity)) (by norm_num : (0:ℝ) ≤ 12/41)
  have hB := mul_le_mul_of_nonneg_left
    (inverse_le_B4 (show 9*s/50 ∈ Icc 0 (27/500) by
      constructor <;> linarith [hs.1, hs.2])) (by norm_num : (0:ℝ) ≤ 12/41)
  have hD := mul_le_mul_of_nonneg_left
    (inverse_le_T4 (show 0 ≤ 9*s/25 by positivity)) (by norm_num : (0:ℝ) ≤ 12/31)
  have hH := mul_le_mul_of_nonneg_left
    (inverse_le_T4 (show 0 ≤ 49*s/100 by positivity)) (by norm_num : (0:ℝ) ≤ 12/31)
  have hE := mul_le_mul_of_nonneg_left
    (inverse_le_T4 (show 0 ≤ 4*s/5 by positivity)) (show 0 ≤ 3*s/10 by positivity)
  simp only [massSum, mass, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mA, mB, mD, mE, mH, massUpper]
  simp only [mul_one_div] at hA hB hD hH hE
  linarith

def chiUpper (s : ℝ) : ℝ := s^2/2+s^4/8+s^6/14

theorem cosine_chord {s c : ℝ} (hs : s ∈ Icc 0 (3/10))
    (hc : 0 ≤ c) (hunit : c^2+s^2=1) : 1-c ≤ chiUpper s := by
  let x := s^2
  let P := 1-x/2-x^2/8-x^3/14
  have hx : x ∈ Icc 0 (9/100) := by
    dsimp [x]
    constructor
    · positivity
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  have hx₂ := pow_le_pow_left₀ hx.1 hx.2 2
  have hx₃ := pow_le_pow_left₀ hx.1 hx.2 3
  have hP : 0 < P := by
    dsimp [P]
    nlinarith [hx.1, hx.2]
  have hbracket : 0 ≤ 56-273*x-56*x^2-16*x^3 := by
    nlinarith [hx.2]
  have hid : 1-x-P^2=x^3*(56-273*x-56*x^2-16*x^3)/3136 := by
    dsimp [P]
    ring
  have hp := div_nonneg (mul_nonneg (pow_nonneg hx.1 3) hbracket)
    (by norm_num : (0:ℝ) ≤ 3136)
  have hPc : P ≤ c := by
    dsimp [x] at hid
    nlinarith
  dsimp [P, x, chiUpper] at hPc ⊢
  nlinarith

def polynomial (s : ℝ) : ℝ :=
  38726637/9929687500-(79/1250)*s+(51/200)*s^2-s^3/100-
    (27/100)*s^4-(3/10)*s^5

/-- Polynomial obtained after the circle-mass and cosine majorants. -/
def lowerPolynomial (s : ℝ) : ℝ :=
  3+2*alpha s+3*beta s+2*delta s+epsilon s+epsilon s*s-ceiling*massUpper s-
  (1+(alpha s)^2-2*alpha s*s)*(41/12)*(1+13*s/60)/4-
  ((beta s)^2+(alpha s)^2)*(41/12)*(1-9*s/50)/4-
  ((delta s)^2+(beta s)^2)*(31/12)*(1+9*s/25)/4-
  ((epsilon s)^2+1)*(31/12)*(1+49*s/100)/4-
  s*(5/6)*(3/10-49*s/80)^2*(1+4*s/5)-
  chiUpper s-
  (5/3)*delta s*epsilon s*(1+4*s/5)*(s/2+s^3/8+s^5/14)

theorem force_norm (t : ℝ) (i : Fin 5) :
    normSq (forces t i) =
      ![1+alpha (Real.sin t)^2-2*alpha (Real.sin t)*Real.sin t,
        beta (Real.sin t)^2+alpha (Real.sin t)^2,
        delta (Real.sin t)^2+beta (Real.sin t)^2,
        (delta (Real.sin t)-epsilon (Real.sin t))^2+
          2*delta (Real.sin t)*epsilon (Real.sin t)*(1-Real.cos t),
        epsilon (Real.sin t)^2+1] i := by
  fin_cases i <;>
    simp only [forces, spanForces, Fin.reduceFinMk, Matrix.cons_val, normSq]
  · linear_combination Real.sin_sq_add_cos_sq t
  · ring
  · linear_combination epsilon (Real.sin t)^2 * Real.sin_sq_add_cos_sq t
  · linear_combination (1+epsilon (Real.sin t)^2) * Real.sin_sq_add_cos_sq t

theorem gap_formula {t : ℝ} (hs : Real.sin t ∈ Icc 0 (3/10))
    (hs₀ : 0 < Real.sin t) :
    gap ceiling t =
      3+2*alpha (Real.sin t)+3*beta (Real.sin t)+2*delta (Real.sin t)+
      epsilon (Real.sin t)+epsilon (Real.sin t)*Real.sin t-
      ceiling*massSum (Real.sin t)-
      (1+alpha (Real.sin t)^2-2*alpha (Real.sin t)*Real.sin t)/(4*mA (Real.sin t))-
      (beta (Real.sin t)^2+alpha (Real.sin t)^2)/(4*mB (Real.sin t))-
      (delta (Real.sin t)^2+beta (Real.sin t)^2)/(4*mD (Real.sin t))-
      (epsilon (Real.sin t)^2+1)/(4*mH (Real.sin t))-
      (delta (Real.sin t)-epsilon (Real.sin t))^2/(4*mE (Real.sin t))-
      (1-Real.cos t)*(1+delta (Real.sin t)*epsilon (Real.sin t)/(2*mE (Real.sin t))) := by
  have hA := ne_of_gt (mass_pos hs hs₀ 0)
  have hB := ne_of_gt (mass_pos hs hs₀ 1)
  have hD := ne_of_gt (mass_pos hs hs₀ 2)
  have hE := ne_of_gt (mass_pos hs hs₀ 3)
  have hH := ne_of_gt (mass_pos hs hs₀ 4)
  change mA (Real.sin t) ≠ 0 at hA
  change mB (Real.sin t) ≠ 0 at hB
  change mD (Real.sin t) ≠ 0 at hD
  change mE (Real.sin t) ≠ 0 at hE
  change mH (Real.sin t) ≠ 0 at hH
  simp only [gap, demand, energy, force_norm, spanDemand,
    Fin.sum_univ_succ, mass, Matrix.cons_val_zero, Matrix.cons_val_succ]
  field_simp [hA, hB, hD, hE, hH]
  ring

theorem lowerPolynomial_bound {t : ℝ} (ht : t ∈ Icc 0 (Real.pi/4))
    (hs : Real.sin t ∈ Icc 0 (3/10)) :
    lowerPolynomial (Real.sin t) ≤ gap ceiling t := by
  by_cases hs₀ : Real.sin t=0
  · have hc : Real.cos t=1 := by
      have hu := Real.sin_sq_add_cos_sq t
      rw [hs₀] at hu
      nlinarith [(angle_trig ht).1]
    norm_num [lowerPolynomial, gap, demand, energy, forces, spanDemand, spanForces,
      massSum, mass, mA, mB, mD, mE, mH, alpha, beta, delta, epsilon,
      chiUpper, massUpper, T4, B4, ceiling, hs₀, hc, Fin.sum_univ_succ, normSq]
  · have hsp : 0 < Real.sin t := lt_of_le_of_ne hs.1 (Ne.symm hs₀)
    have hM := mass_sum_le_upper hs
    have hχ := cosine_chord hs (angle_trig ht).1.le
      (by nlinarith [Real.sin_sq_add_cos_sq t])
    obtain ⟨-, -, hd, he⟩ := weights_pos hs
    have hE : 0 < mE (Real.sin t) := mass_pos hs hsp 3
    have hχc : 0 ≤ 1+delta (Real.sin t)*epsilon (Real.sin t)/(2*mE (Real.sin t)) :=
      by positivity
    have hχm := mul_le_mul_of_nonneg_right hχ hχc
    have hMq := mul_le_mul_of_nonneg_left hM (show 0 ≤ ceiling by norm_num [ceiling])
    have hden := denominator_bounds hs
    have hpoly :
        lowerPolynomial (Real.sin t) =
        3+2*alpha (Real.sin t)+3*beta (Real.sin t)+2*delta (Real.sin t)+
        epsilon (Real.sin t)+epsilon (Real.sin t)*Real.sin t-
        ceiling*massUpper (Real.sin t)-
        (1+alpha (Real.sin t)^2-2*alpha (Real.sin t)*Real.sin t)/(4*mA (Real.sin t))-
        (beta (Real.sin t)^2+alpha (Real.sin t)^2)/(4*mB (Real.sin t))-
        (delta (Real.sin t)^2+beta (Real.sin t)^2)/(4*mD (Real.sin t))-
        (epsilon (Real.sin t)^2+1)/(4*mH (Real.sin t))-
        (delta (Real.sin t)-epsilon (Real.sin t))^2/(4*mE (Real.sin t))-
        chiUpper (Real.sin t)*
          (1+delta (Real.sin t)*epsilon (Real.sin t)/(2*mE (Real.sin t))) := by
      dsimp [lowerPolynomial, mA, mB, mD, mH, mE, chiUpper, delta, epsilon]
      field_simp [hs₀, ne_of_gt hden.1, ne_of_gt hden.2.1,
        ne_of_gt hden.2.2.1, ne_of_gt hden.2.2.2.1, ne_of_gt hden.2.2.2.2]
      ring
    rw [hpoly, gap_formula hs hsp]
    linarith

/-- Exact coefficient comparison for one polynomial on the whole interval.
The coefficients are expanded by ring normalization, not selected by boxes. -/
theorem polynomial_bound {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    polynomial s ≤ lowerPolynomial s := by
  have hs₀ := hs.1
  have hcoeff :
      0 ≤ lowerPolynomial s-polynomial s-
        (s*(26-9*s)/1000000+(27/10000)*s^3+
          (s^4/1000)*(56-132*s-86*s^2-77*s^4)) := by
    dsimp [lowerPolynomial, polynomial, alpha, beta, delta, epsilon,
      massUpper, T4, B4, chiUpper, ceiling]
    ring_nf
    positivity
  have hs₂ : s^2 ≤ 9/100 := by
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  have hs₄ : s^4 ≤ 81/10000 := by
    have hproduct := mul_nonneg (sub_nonneg.mpr hs₂)
      (show 0 ≤ (9/100:ℝ)+s^2 by positivity)
    nlinarith
  have hb : 0 ≤ 56-132*s-86*s^2-77*s^4 := by nlinarith [hs.2]
  have h₁ : 0 ≤ s*(26-9*s)/1000000 := by
    apply div_nonneg (mul_nonneg hs.1 (by linarith [hs.2])) (by norm_num)
  have h₂ : 0 ≤ (27/10000:ℝ)*s^3 := by positivity
  have h₃ : 0 ≤ (s^4/1000)*(56-132*s-86*s^2-77*s^4) := by positivity
  linarith

theorem gap_ge_polynomial {q t : ℝ} (hq : q ≤ ceiling)
    (ht : t ∈ Icc 0 (Real.pi/4)) (hs : Real.sin t ∈ Icc 0 (3/10)) :
    polynomial (Real.sin t) ≤ gap q t := by
  have hp := (polynomial_bound hs).trans (lowerPolynomial_bound ht hs)
  have hm := mul_nonneg (sub_nonneg.mpr hq) (mass_sum_nonneg hs)
  rw [gap_radius_identity q ceiling t]
  linarith

def polynomialD (s : ℝ) : ℝ :=
  -79/1250+(51/100)*s-(3/100)*s^2-(27/25)*s^3-(3/2)*s^4
def polynomialDD (s : ℝ) : ℝ :=
  51/100-(3/50)*s-(81/25)*s^2-6*s^3

theorem polynomial_derivative (s : ℝ) :
    HasDerivAt polynomial (polynomialD s) s := by
  have h := (((((hasDerivAt_const s (38726637/9929687500:ℝ)).sub
      ((hasDerivAt_id s).const_mul (79/1250))).add
      (((hasDerivAt_id s).pow 2).const_mul (51/200))).sub
      (((hasDerivAt_id s).pow 3).div_const 100)).sub
      (((hasDerivAt_id s).pow 4).const_mul (27/100))).sub
      (((hasDerivAt_id s).pow 5).const_mul (3/10))
  convert h using 1
  · funext x
    simp only [polynomial, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id]
  · dsimp [polynomialD]
    ring

theorem polynomial_second (s : ℝ) :
    HasDerivAt polynomialD (polynomialDD s) s := by
  have h := ((((hasDerivAt_const s (-79/1250:ℝ)).add
      ((hasDerivAt_id s).const_mul (51/100))).sub
      (((hasDerivAt_id s).pow 2).const_mul (3/100))).sub
      (((hasDerivAt_id s).pow 3).const_mul (27/25))).sub
      (((hasDerivAt_id s).pow 4).const_mul (3/2))
  convert h using 1
  · funext x
    simp only [polynomialD, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id]
  · dsimp [polynomialDD]
    ring

theorem polynomial_left_positive {s : ℝ} (hs : s ∈ Icc 0 (1/10)) :
    0 < polynomial s := by
  have hmono : AntitoneOn polynomial (Icc 0 (1/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun x _ => (polynomial_derivative x).continuousAt.continuousWithinAt)
      (fun x _ => polynomial_derivative x) (fun x hx => by
        dsimp [polynomialD]
        nlinarith [hx.2, sq_nonneg x, pow_nonneg hx.1.le 3, pow_nonneg hx.1.le 4])
  have hp : 0 < polynomial (1/10) := by norm_num [polynomial]
  exact hp.trans_le (hmono hs (by norm_num) hs.2)

theorem polynomial_curvature_positive {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    0 < polynomialDD s := by
  have hs₂ := pow_le_pow_left₀ hs.1 hs.2 2
  have hs₃ := pow_le_pow_left₀ hs.1 hs.2 3
  dsimp [polynomialDD]
  nlinarith [hs.2]

theorem polynomial_right_positive {s : ℝ} (hs : s ∈ Icc (79/500) (3/10)) :
    0 < polynomial s := by
  have hmonoD : MonotoneOn polynomialD (Icc 0 (3/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (polynomial_second x).continuousAt.continuousWithinAt)
      (fun x _ => polynomial_second x)
      (fun x hx => (polynomial_curvature_positive ⟨hx.1.le, hx.2.le⟩).le)
  have hD₀ : 0 < polynomialD (3/20) := by norm_num [polynomialD]
  have hmono : MonotoneOn polynomial (Icc (3/20) (3/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (polynomial_derivative x).continuousAt.continuousWithinAt)
      (fun x _ => polynomial_derivative x) (fun x hx => by
        have h := hmonoD (by norm_num) ⟨by linarith [hx.1], hx.2.le⟩ hx.1.le
        linarith)
  have hp : 0 < polynomial (79/500) := by norm_num [polynomial]
  exact hp.trans_le (hmono (by norm_num) ⟨by linarith [hs.1], hs.2⟩ hs.1)

theorem sine_localization {p : FiveCorner} {R : ℝ}
    (hp : p.spans) (hfit : p.fits R) (hq : R^2 ≤ ceiling) :
    1/10 < Real.sin p.angle ∧ Real.sin p.angle < 79/500 := by
  have h := (spans_iff_spanBounds p).1 hp
  have ht : p.angle ∈ Icc 0 (Real.pi/4) := ⟨h.angle_lower, h.angle_upper⟩
  have hs₀ := (angle_trig ht).2.2.1
  have hs₁ : Real.sin p.angle < 3/10 := by
    by_contra! hs
    exact HighTilt.exclusion hp hfit
      (hq.trans (by norm_num [ceiling, HighTilt.ceiling])) hs
  have hgap := gap_nonpos_of_spans hp hfit hs₁.le
  have hpoly := gap_ge_polynomial hq ht ⟨hs₀, hs₁.le⟩
  constructor
  · by_contra! hs
    have hh := polynomial_left_positive ⟨hs₀, hs⟩
    linarith
  · by_contra! hs
    have hh := polynomial_right_positive ⟨hs, hs₁.le⟩
    linarith

theorem tilt_localization {p : FiveCorner} {R : ℝ}
    (hp : p.spans) (hfit : p.fits R) (hq : R^2 ≤ ceiling) :
    p.angle ∈ Stationary.FiveCornerGeometry.tiltInterval := by
  have h := (spans_iff_spanBounds p).1 hp
  have ht : p.angle ∈ Icc 0 (Real.pi/4) := ⟨h.angle_lower, h.angle_upper⟩
  obtain ⟨hsl, hsu⟩ := sine_localization hp hfit hq
  have hc := (angle_trig ht).1
  have hu := Real.sin_sq_add_cos_sq p.angle
  have hs₀ : 0 ≤ Real.sin p.angle := by linarith
  have hs₂ : Real.sin p.angle ^ 2 < (79/500:ℝ)^2 := by
    exact Stationary.FiveCornerGeometry.square_strict_mono_nonneg hs₀ hsu
  have htan : Real.sin p.angle / Real.cos p.angle < 1/5 := by
    rw [div_lt_iff₀ hc]
    nlinarith
  have hpos : 0 < p.angle := by
    by_contra! hh
    have he : p.angle=0 := le_antisymm hh h.angle_lower
    rw [he, Real.sin_zero] at hsl
    norm_num at hsl
  refine ⟨hpos, ?_⟩
  by_contra! hh
  have hmem : p.angle ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [h.angle_lower, h.angle_upper, Real.pi_pos]
  have hm := Real.strictMonoOn_tan.monotoneOn
    (Real.arctan_mem_Ioo (1/5:ℝ)) hmem hh
  rw [Real.tan_arctan, Real.tan_eq_sin_div_cos] at hm
  linarith

end Nominal
end SquaresInCircles.Eight.FiveCorner
end
end
end
