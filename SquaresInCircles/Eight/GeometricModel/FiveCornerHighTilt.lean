module

public import SquaresInCircles.Eight.GeometricModel.FiveCornerReduction

/-!
# One support on the complete high-tilt arc

Uncompiled draft of HAND_FIVE_CORNER_MODEL_SELECTION.md, Section 3.
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
    simp only [spanForces, Matrix.cons_val_zero, Matrix.cons_val_succ]
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
    (fun t _ => gap_second_derivative t) (fun t ht => (gap_second_negative ht).le)

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
