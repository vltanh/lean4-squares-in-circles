module

public import SquaresInCircles.Eight.BoundaryReduction
public import SquaresInCircles.Common.Analysis

/-!
# Radius transfer for the seven-square boundary relaxation

Source: `HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md`, §§1–2.

This draft gives an endpoint version of the hand derivative argument. The
identity `(r₂-r₁) * (r₂+r₁+B) = q₂-q₁` gives both increment bounds at once.
The signs of the two projection coefficients are retained. Consequently the
argument applies to **each** initially feasible signed axis, including ties;
it does not choose a new owner after the motion.

All lengths here are Euclidean scalar radii. No product-space norm is used.
These sources have deliberately not been compiled or sent to CI.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Eight.RadiusTransfer

/-- Positive root of the outer-corner containment equation. -/
def outerRadius (q B : ℝ) : ℝ :=
  (Real.sqrt (B ^ 2 + 4 * q - 2) - B) / 2

/-- The entire range of coefficients supplied by a nearest-axis frame. -/
def FrameCoefficient (B : ℝ) : Prop := 1 ≤ B ∧ B ≤ Real.sqrt 2

lemma sqrt_two_lt_three_halves : Real.sqrt 2 < (3 : ℝ) / 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]

lemma coefficient_bounds {B : ℝ} (hB : FrameCoefficient B) :
    1 ≤ B ∧ B < 3 / 2 ∧ 1 ≤ B ^ 2 ∧ B ^ 2 ≤ 2 := by
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  exact ⟨hB.1, hB.2.trans_lt sqrt_two_lt_three_halves,
    by nlinarith [sq_nonneg (B - 1)], by nlinarith [hB.1, hB.2]⟩

lemma discriminant_bounds {q B : ℝ} (hq : q ∈ Set.Icc (5 / 2) 4)
    (hB : FrameCoefficient B) :
    9 ≤ B ^ 2 + 4 * q - 2 ∧ B ^ 2 + 4 * q - 2 ≤ 16 := by
  obtain ⟨_, _, hB₁, hB₂⟩ := coefficient_bounds hB
  constructor <;> linarith [hq.1, hq.2]

lemma root_bounds {q B : ℝ} (hq : q ∈ Set.Icc (5 / 2) 4)
    (hB : FrameCoefficient B) :
    3 ≤ Real.sqrt (B ^ 2 + 4 * q - 2) ∧
      Real.sqrt (B ^ 2 + 4 * q - 2) ≤ 4 := by
  obtain ⟨hl, hu⟩ := discriminant_bounds hq hB
  have hs := Real.sq_sqrt (show 0 ≤ B ^ 2 + 4 * q - 2 by linarith)
  have hn := Real.sqrt_nonneg (B ^ 2 + 4 * q - 2)
  constructor <;> nlinarith

lemma outerRadius_nonneg {q B : ℝ} (hq : q ∈ Set.Icc (5 / 2) 4)
    (hB : FrameCoefficient B) : 0 ≤ outerRadius q B := by
  obtain ⟨hl, _⟩ := root_bounds hq hB
  obtain ⟨_, hB', _, _⟩ := coefficient_bounds hB
  unfold outerRadius
  linarith

lemma outerRadius_equation {q B : ℝ} (hq : q ∈ Set.Icc (5 / 2) 4)
    (hB : FrameCoefficient B) :
    (outerRadius q B) ^ 2 + B * outerRadius q B + 1 / 2 = q := by
  have hd := (discriminant_bounds hq hB).1
  have hs := Real.sq_sqrt (show 0 ≤ B ^ 2 + 4 * q - 2 by linarith)
  unfold outerRadius
  nlinarith

lemma outerRadius_bounds {q B : ℝ} (hq : q ∈ Set.Icc (5 / 2) 4)
    (hB : FrameCoefficient B) :
    4 / 5 < outerRadius q B ∧ outerRadius q B < 3 / 2 := by
  let r := outerRadius q B
  have hr : 0 ≤ r := outerRadius_nonneg hq hB
  have he : r ^ 2 + B * r + 1 / 2 = q := outerRadius_equation hq hB
  obtain ⟨hB₁, hB₂, _, _⟩ := coefficient_bounds hB
  constructor
  · by_contra! h
    have hsq : r ^ 2 ≤ 16 / 25 := by nlinarith [sq_nonneg (r - 4 / 5)]
    have hmul : B * r ≤ (3 / 2) * r := mul_le_mul_of_nonneg_right hB₂.le hr
    nlinarith [hq.1]
  · by_contra! h
    have hmul : r ≤ B * r := by nlinarith [mul_nonneg (sub_nonneg.mpr hB₁) hr]
    nlinarith [hq.2, sq_nonneg (r - 3 / 2)]

lemma outerRadius_unique {q B r : ℝ} (hq : q ∈ Set.Icc (5 / 2) 4)
    (hB : FrameCoefficient B) (hr : 0 ≤ r)
    (he : r ^ 2 + B * r + 1 / 2 = q) : r = outerRadius q B := by
  have hs := outerRadius_equation hq hB
  have hn := outerRadius_nonneg hq hB
  have hf : (r - outerRadius q B) * (r + outerRadius q B + B) = 0 := by
    nlinarith
  have hp : 0 < r + outerRadius q B + B := by linarith [hB.1]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (ne_of_gt hp))

lemma outerRadius_difference_identity {qa qb B : ℝ}
    (ha : qa ∈ Set.Icc (5 / 2) 4) (hb : qb ∈ Set.Icc (5 / 2) 4)
    (hB : FrameCoefficient B) :
    (outerRadius qb B - outerRadius qa B) *
      (outerRadius qb B + outerRadius qa B + B) = qb - qa := by
  nlinarith [outerRadius_equation ha hB, outerRadius_equation hb hB]

lemma secant_denominator_bounds {qa qb B : ℝ}
    (ha : qa ∈ Set.Icc (5 / 2) 4) (hb : qb ∈ Set.Icc (5 / 2) 4)
    (hB : FrameCoefficient B) :
    3 ≤ outerRadius qb B + outerRadius qa B + B ∧
      outerRadius qb B + outerRadius qa B + B ≤ 4 := by
  have h₁ := root_bounds ha hB
  have h₂ := root_bounds hb hB
  dsimp [outerRadius]
  constructor <;> linarith

/-- Both travel estimates, with the original radius retained explicitly. -/
lemma outerRadius_increment {qa qb B : ℝ}
    (ha : qa ∈ Set.Icc (5 / 2) 4) (hb : qb ∈ Set.Icc (5 / 2) 4)
    (hab : qa ≤ qb) (hB : FrameCoefficient B) :
    (qb - qa) / 4 ≤ outerRadius qb B - outerRadius qa B ∧
      outerRadius qb B - outerRadius qa B ≤ (qb - qa) / 3 := by
  have he := outerRadius_difference_identity ha hb hB
  obtain ⟨hl, hu⟩ := secant_denominator_bounds ha hb hB
  have hn : 0 ≤ outerRadius qb B - outerRadius qa B := by
    by_contra! hn
    have hp : 0 < outerRadius qb B + outerRadius qa B + B := by linarith
    have hh := mul_neg_of_neg_of_pos hn hp
    linarith
  have hlo := mul_le_mul_of_nonneg_left hl hn
  have hhi := mul_le_mul_of_nonneg_left hu hn
  constructor <;> nlinarith

lemma outerRadius_monotone {qa qb B : ℝ}
    (ha : qa ∈ Set.Icc (5 / 2) 4) (hb : qb ∈ Set.Icc (5 / 2) 4)
    (hab : qa ≤ qb) (hB : FrameCoefficient B) :
    outerRadius qa B ≤ outerRadius qb B := by
  have h := (outerRadius_increment ha hb hab hB).1
  linarith

lemma outerRadius_hasDerivAt {q B : ℝ}
    (hq : q ∈ Set.Icc (5 / 2) 4) (hB : FrameCoefficient B) :
    HasDerivAt (fun x => outerRadius x B)
      (1 / Real.sqrt (B ^ 2 + 4 * q - 2)) q := by
  have hd : 0 < B ^ 2 + 4 * q - 2 := by
    linarith [(discriminant_bounds hq hB).1]
  have hs := ((((hasDerivAt_id q).const_mul 4).const_add (B ^ 2)).sub_const 2).sqrt
    (ne_of_gt hd)
  have hf := (hs.sub_const B).div_const 2
  convert hf using 1 <;> dsimp [outerRadius] <;> ring

lemma outerRadius_derivative_bounds {q B : ℝ}
    (hq : q ∈ Set.Icc (5 / 2) 4) (hB : FrameCoefficient B) :
    1 / 4 ≤ 1 / Real.sqrt (B ^ 2 + 4 * q - 2) ∧
      1 / Real.sqrt (B ^ 2 + 4 * q - 2) ≤ 1 / 3 := by
  obtain ⟨hl, hu⟩ := root_bounds hq hB
  have hp : 0 < Real.sqrt (B ^ 2 + 4 * q - 2) := by linarith
  constructor
  · exact (div_le_div_iff₀ (by norm_num) hp).2 (by linarith)
  · exact (div_le_div_iff₀ hp (by norm_num)).2 (by linarith)

/-- The nonnegative-coefficient case of an active outer/outer projection. -/
lemma nonnegative_projection_reserve {r s u v : ℝ}
    (hr : r < 3 / 2) (hs : s < 3 / 2)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hfeas : 1 ≤ u * r + v * s) :
    2 / 3 ≤ u + v := by
  have h₁ := mul_le_mul_of_nonneg_left hr.le hu
  have h₂ := mul_le_mul_of_nonneg_left hs.le hv
  nlinarith

/-- The coefficient inequalities are deduced at the original feasible state.
They need not be reproved, or assumed, at intermediate radii. -/
lemma mixed_projection_reserve {r s u v : ℝ}
    (hr : r < 3 / 2) (hs : 4 / 5 < s)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v)
    (hfeas : 1 ≤ u * r - v * s) :
    2 / 3 + 8 / 15 * v ≤ u ∧ v ≤ 5 / 8 ∧ 1 / 24 ≤ u / 4 - v / 3 := by
  have h₁ := mul_le_mul_of_nonneg_left hr.le hu.1
  have h₂ := mul_le_mul_of_nonneg_left hs.le hv
  have h₃ : u * r ≤ 3 / 2 := by nlinarith [hu.2]
  have ha : 2 / 3 + 8 / 15 * v ≤ u := by nlinarith
  have hb : v ≤ 5 / 8 := by nlinarith
  exact ⟨ha, hb, by linarith⟩

/-- Pure scalar transport for every feasible pair projection with two outer
states. The lower and upper increment estimates preserve negative coefficients.
The additional reserve is uniform and is useful at an owner tie. -/
lemma outer_outer_increment {r₁ r₂ dr₁ dr₂ Δ u v : ℝ}
    (hr₁ : 4 / 5 < r₁ ∧ r₁ < 3 / 2)
    (hr₂ : 4 / 5 < r₂ ∧ r₂ < 3 / 2)
    (hΔ : 0 ≤ Δ)
    (hd₁ : Δ / 4 ≤ dr₁ ∧ dr₁ ≤ Δ / 3)
    (hd₂ : Δ / 4 ≤ dr₂ ∧ dr₂ ≤ Δ / 3)
    (hu : -1 ≤ u ∧ u ≤ 1) (hv : -1 ≤ v ∧ v ≤ 1)
    (hf : 1 ≤ u * r₁ + v * r₂) :
    Δ / 24 ≤ u * dr₁ + v * dr₂ := by
  by_cases hu₀ : 0 ≤ u
  · by_cases hv₀ : 0 ≤ v
    · have hsum := nonnegative_projection_reserve hr₁.2 hr₂.2 hu₀ hv₀ hf
      have h₁ := mul_le_mul_of_nonneg_left hd₁.1 hu₀
      have h₂ := mul_le_mul_of_nonneg_left hd₂.1 hv₀
      have h₃ := mul_nonneg (show 0 ≤ u + v - 2 / 3 by linarith) hΔ
      nlinarith
    · have hv' : 0 ≤ -v := by linarith
      obtain ⟨_, _, hreserve⟩ := mixed_projection_reserve hr₁.2 hr₂.1
        ⟨hu₀, hu.2⟩ hv' (by nlinarith : 1 ≤ u * r₁ - (-v) * r₂)
      have h₁ := mul_le_mul_of_nonneg_left hd₁.1 hu₀
      have h₂ := mul_le_mul_of_nonpos_left hd₂.2 (by linarith : v ≤ 0)
      have h₃ := mul_nonneg (show 0 ≤ u / 4 - (-v) / 3 - 1 / 24 by linarith) hΔ
      nlinarith
  · have hu' : 0 ≤ -u := by linarith
    have hv₀ : 0 ≤ v := by
      by_contra! hh
      have h₁ := mul_nonpos_of_nonpos_of_nonneg (by linarith : u ≤ 0)
        (by linarith : 0 ≤ r₁)
      have h₂ := mul_nonpos_of_nonpos_of_nonneg hh.le (by linarith : 0 ≤ r₂)
      linarith
    obtain ⟨_, _, hreserve⟩ := mixed_projection_reserve hr₂.2 hr₁.1
      ⟨hv₀, hv.2⟩ hu' (by nlinarith : 1 ≤ v * r₂ - (-u) * r₁)
    have h₁ := mul_le_mul_of_nonneg_left hd₂.1 hv₀
    have h₂ := mul_le_mul_of_nonpos_left hd₁.2 (by linarith : u ≤ 0)
    have h₃ := mul_nonneg (show 0 ≤ v / 4 - (-u) / 3 - 1 / 24 by linarith) hΔ
    nlinarith

lemma core_outer_projection_reserve {r c u v : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 3 / 2) (hc : 0 ≤ c ∧ c ≤ 4 / 5)
    (hv : v ≤ 1) (hf : 1 ≤ u * r + v * c) : 2 / 15 ≤ u := by
  have hvc : v * c ≤ 4 / 5 := by
    have h := mul_le_mul_of_nonneg_right hv hc.1
    nlinarith [hc.2]
  have hur : 1 / 5 ≤ u * r := by linarith
  have hu : 0 ≤ u := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h.le hr.1
    linarith
  have hmul := mul_le_mul_of_nonneg_left hr.2 hu
  nlinarith

lemma core_outer_increment {r c dr Δ u v : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 3 / 2) (hc : 0 ≤ c ∧ c ≤ 4 / 5)
    (hΔ : 0 ≤ Δ) (hdr : Δ / 4 ≤ dr) (hv : v ≤ 1)
    (hf : 1 ≤ u * r + v * c) : Δ / 30 ≤ u * dr := by
  have hu := core_outer_projection_reserve hr hc hv hf
  have hu₀ : 0 ≤ u := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hdr hu₀
  have h₂ := mul_nonneg (show 0 ≤ u - 2 / 15 by linarith) hΔ
  nlinarith

/-- A radial state retains its kind under radius transfer. The core radius is
part of the state, and is held fixed. Side/corner distinctions are geometric
data upstream and are immaterial to this projection theorem. -/
inductive RadialState where
  | outer (B : ℝ) (frame : FrameCoefficient B)
  | core (r : ℝ) (bounds : 0 ≤ r ∧ r < 4 / 5)

def RadialState.radius (s : RadialState) (q : ℝ) : ℝ :=
  match s with
  | .outer B _ => outerRadius q B
  | .core r _ => r

def RadialState.isOuter : RadialState → Bool
  | .outer .. => true
  | .core .. => false

/-- Every initially feasible signed projection remains feasible. Coefficients
are fixed dot products of the retained unit axis with the two retained rays.
The threshold is the unchanged sum of support half-widths. -/
theorem every_feasible_projection_preserved
    (s₁ s₂ : RadialState) {qa qb u v width : ℝ}
    (ha : qa ∈ Set.Icc (5 / 2) 4) (hb : qb ∈ Set.Icc (5 / 2) 4)
    (hab : qa ≤ qb) (hu : -1 ≤ u ∧ u ≤ 1) (hv : -1 ≤ v ∧ v ≤ 1)
    (hw : 1 ≤ width)
    (hfeas : width ≤ u * s₁.radius qa + v * s₂.radius qa) :
    width ≤ u * s₁.radius qb + v * s₂.radius qb := by
  have hΔ : 0 ≤ qb - qa := sub_nonneg.mpr hab
  cases s₁ with
  | outer B hB =>
    cases s₂ with
    | outer C hC =>
      have h := outer_outer_increment (outerRadius_bounds ha hB)
        (outerRadius_bounds ha hC) hΔ (outerRadius_increment ha hb hab hB)
        (outerRadius_increment ha hb hab hC) hu hv (hw.trans hfeas)
      dsimp [RadialState.radius] at *
      nlinarith
    | core c hc =>
      have hr := outerRadius_bounds ha hB
      have h := core_outer_increment ⟨by linarith, hr.2.le⟩ ⟨hc.1, hc.2.le⟩ hΔ
        (outerRadius_increment ha hb hab hB).1 hv.2 (hw.trans hfeas)
      dsimp [RadialState.radius] at *
      nlinarith
  | core c hc =>
    cases s₂ with
    | outer B hB =>
      have hr := outerRadius_bounds ha hB
      have hf : 1 ≤ v * outerRadius qa B + u * c := by
        dsimp [RadialState.radius] at hfeas
        linarith
      have h := core_outer_increment ⟨by linarith, hr.2.le⟩ ⟨hc.1, hc.2.le⟩ hΔ
        (outerRadius_increment ha hb hab hB).1 hu.2 hf
      dsimp [RadialState.radius] at *
      nlinarith
    | core d hd => exact hfeas

/-- Simultaneous transport makes no finiteness or single-owner assumption on
the family of selected axes. In particular it retains every owner tie. -/
theorem all_axes_preserved {ι : Type*} (s₁ s₂ : RadialState)
    {qa qb : ℝ} (u v width : ι → ℝ)
    (ha : qa ∈ Set.Icc (5 / 2) 4) (hb : qb ∈ Set.Icc (5 / 2) 4)
    (hab : qa ≤ qb) (hu : ∀ i, -1 ≤ u i ∧ u i ≤ 1)
    (hv : ∀ i, -1 ≤ v i ∧ v i ≤ 1) (hw : ∀ i, 1 ≤ width i) :
    ∀ i, width i ≤ u i * s₁.radius qa + v i * s₂.radius qa →
      width i ≤ u i * s₁.radius qb + v i * s₂.radius qb := by
  intro i hi
  exact every_feasible_projection_preserved s₁ s₂ ha hb hab (hu i) (hv i) (hw i) hi

end SquaresInCircles.Eight.RadiusTransfer

namespace SquaresInCircles.Eight

def BoundaryCycle.radius {q : ℝ} (C : BoundaryCycle q) (i : Vertex) : ℝ :=
  Real.sqrt (C.a i^2 + C.b i^2)

def BoundaryCycle.ray {q : ℝ} (C : BoundaryCycle q) (i : Vertex) : Point :=
  (Real.cos (C.beta i), Real.sin (C.beta i))

lemma BoundaryCycle.radius_pos {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    0 < C.radius i := by
  apply Real.sqrt_pos.mpr
  nlinarith [C.a_pos i, sq_nonneg (C.b i)]

lemma BoundaryCycle.radius_sq {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    C.radius i^2 = C.a i^2 + C.b i^2 := Real.sq_sqrt (by positivity)

lemma BoundaryCycle.ray_unit {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    normSq (C.ray i) = 1 := by
  simpa [BoundaryCycle.ray, normSq, add_comm] using Real.sin_sq_add_cos_sq (C.beta i)

lemma BoundaryCycle.center_polar {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    (C.square i).center = scale (C.radius i) (C.ray i) := by
  exact Prod.ext (C.center_cos i) (C.center_sin i)

lemma BoundaryCycle.absolute_coordinates {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    alpha (C.square i) (0, 0) = C.a i ∧ beta (C.square i) (0, 0) = C.b i := by
  have hX : localX (C.square i) (0, 0) = -C.a i := by
    rw [localX, C.center_eq i]
    dsimp [rotate]
    linear_combination -(C.a i) * (C.square i).unit
  have hY : localY (C.square i) (0, 0) = C.sigma i*C.b i := by
    rw [localY, C.center_eq i]
    dsimp [rotate]
    linear_combination C.sigma i*C.b i * (C.square i).unit
  have hσ : |C.sigma i| = 1 := by rcases C.sigma_sign i with h | h <;> simp [h]
  simp [alpha, beta, hX, hY, abs_mul, hσ, abs_of_nonneg (C.a_pos i).le,
    abs_of_nonneg (C.b_nonneg i)]

def BoundaryCycle.radialCoefficient {q : ℝ} (C : BoundaryCycle q) (i : Vertex) : ℝ :=
  (C.a i+C.b i)/C.radius i

lemma BoundaryCycle.radialCoefficient_bounds {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    RadiusTransfer.FrameCoefficient (C.radialCoefficient i) := by
  have hr := C.radius_pos i
  have hr₂ := C.radius_sq i
  have ha := C.a_pos i
  have hb := C.b_nonneg i
  have hsum : C.radius i ≤ C.a i+C.b i := by
    nlinarith [mul_nonneg ha.le hb]
  have hsum' : C.a i+C.b i ≤ Real.sqrt 2*C.radius i := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    have hp := mul_nonneg hn hr.le
    nlinarith [sq_nonneg (C.a i-C.b i)]
  exact ⟨(le_div_iff₀ hr).2 (by simpa using hsum),
    (div_le_iff₀ hr).2 hsum'⟩

lemma BoundaryCycle.core_radius_bound {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hi : C.kind i ≠ .outer) : C.radius i < 4/5 := by
  have hr := (C.radius_pos i).le
  have hr₂ := C.radius_sq i
  have ha := C.a_pos i
  have hb := C.b_nonneg i
  have hab := C.b_le_a i
  have h := C.boundary i
  cases hk : C.kind i with
  | outer => exact (hi hk).elim
  | coreSide =>
    simp only [hk, BoundaryState] at h
    nlinarith [mul_nonneg (show 0 ≤ 1/2-C.b i by linarith) (show 0 ≤ 1/2+C.b i by linarith)]
  | coreCorner =>
    simp only [hk, BoundaryState] at h
    have hsum : C.a i+C.b i-1 < 1/8 := by
      have hsq : (C.a i+C.b i-1)^2 ≤ 1/72 := by
        nlinarith [sq_nonneg (C.a i-C.b i)]
      nlinarith
    nlinarith

def BoundaryCycle.radialState {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    RadiusTransfer.RadialState :=
  if h : C.kind i = .outer then
    .outer (C.radialCoefficient i) (C.radialCoefficient_bounds i)
  else .core (C.radius i) ⟨(C.radius_pos i).le,C.core_radius_bound i h⟩

lemma BoundaryCycle.radialState_source {q : ℝ} (C : BoundaryCycle q)
    (hq : q ∈ Set.Icc (5/2) 4) (i : Vertex) :
    (C.radialState i).radius q = C.radius i := by
  by_cases h : C.kind i = .outer
  · simp only [BoundaryCycle.radialState, dif_pos h, RadiusTransfer.RadialState.radius]
    apply (RadiusTransfer.outerRadius_unique hq (C.radialCoefficient_bounds i)
      (C.radius_pos i).le).symm
    have hb := C.boundary i
    simp only [h, BoundaryState, phi] at hb
    have hr := C.radius_sq i
    have he : C.radialCoefficient i*C.radius i = C.a i+C.b i := by
      simp [BoundaryCycle.radialCoefficient, ne_of_gt (C.radius_pos i)]
    nlinarith
  · simp [BoundaryCycle.radialState,h,RadiusTransfer.RadialState.radius]

def BoundaryCycle.expansionFactor {q : ℝ} (C : BoundaryCycle q) (r : ℝ) (i : Vertex) : ℝ :=
  (C.radialState i).radius r / C.radius i

lemma BoundaryCycle.expansionFactor_core {q r : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (h : C.kind i ≠ .outer) : C.expansionFactor r i = 1 := by
  simp [BoundaryCycle.expansionFactor,BoundaryCycle.radialState,h,
    RadiusTransfer.RadialState.radius,ne_of_gt (C.radius_pos i)]

lemma BoundaryCycle.expansionFactor_ge_one {q r : ℝ} (C : BoundaryCycle q)
    (hq : q ∈ Set.Icc (5/2) 4) (hr : r ∈ Set.Icc (5/2) 4) (hqr : q ≤ r)
    (i : Vertex) : 1 ≤ C.expansionFactor r i := by
  by_cases h : C.kind i = .outer
  · have hm := RadiusTransfer.outerRadius_monotone hq hr hqr (C.radialCoefficient_bounds i)
    have hs := C.radialState_source hq i
    simp only [BoundaryCycle.radialState,dif_pos h,RadiusTransfer.RadialState.radius] at hs
    dsimp [BoundaryCycle.expansionFactor]
    simp only [BoundaryCycle.radialState,dif_pos h,RadiusTransfer.RadialState.radius]
    apply (le_div_iff₀ (C.radius_pos i)).2
    simpa [hs] using hm
  · rw [C.expansionFactor_core i h]

lemma BoundaryCycle.expansionFactor_radius {q r : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    C.expansionFactor r i*C.radius i = (C.radialState i).radius r := by
  simp [BoundaryCycle.expansionFactor,ne_of_gt (C.radius_pos i)]

lemma BoundaryCycle.expanded_sqrt {q r : ℝ} (C : BoundaryCycle q)
    (hq : q ∈ Set.Icc (5/2) 4) (hr : r ∈ Set.Icc (5/2) 4) (hqr : q ≤ r)
    (i : Vertex) :
    Real.sqrt ((C.expansionFactor r i*C.a i)^2+(C.expansionFactor r i*C.b i)^2) =
      C.expansionFactor r i*C.radius i := by
  have hλ := C.expansionFactor_ge_one hq hr hqr i
  apply Real.sqrt_eq_iff_mul_self_eq (by nlinarith [C.radius_pos i]) |>.2
  nlinarith [C.radius_sq i]

lemma BoundaryCycle.expanded_tangent {q r : ℝ} (C : BoundaryCycle q)
    (hq : q ∈ Set.Icc (5/2) 4) (hr : r ∈ Set.Icc (5/2) 4) (hqr : q ≤ r)
    (i : Vertex) :
    C.sigma i*(C.expansionFactor r i*C.b i)/(C.expansionFactor r i*C.a i) = C.tangent i := by
  have hλ : C.expansionFactor r i ≠ 0 := ne_of_gt (by linarith [C.expansionFactor_ge_one hq hr hqr i])
  dsimp [BoundaryCycle.tangent]
  field_simp [hλ,ne_of_gt (C.a_pos i)]
  ring

lemma BoundaryCycle.expanded_boundary {q r : ℝ} (C : BoundaryCycle q)
    (hq : q ∈ Set.Icc (5/2) 4) (hr : r ∈ Set.Icc (5/2) 4) (hqr : q ≤ r)
    (i : Vertex) :
    BoundaryState r (C.kind i) (C.expansionFactor r i*C.a i) (C.expansionFactor r i*C.b i) := by
  cases hk : C.kind i with
  | outer =>
    have he := RadiusTransfer.outerRadius_equation hr (C.radialCoefficient_bounds i)
    have hmul := C.expansionFactor_radius (r := r) i
    simp only [BoundaryCycle.radialState,dif_pos hk,RadiusTransfer.RadialState.radius] at hmul
    have hc : C.radialCoefficient i*C.radius i = C.a i+C.b i := by
      simp [BoundaryCycle.radialCoefficient,ne_of_gt (C.radius_pos i)]
    have hr₂ := C.radius_sq i
    have hprod := congrArg (fun x : ℝ => C.expansionFactor r i*x) hc
    have hsq := congrArg (fun x : ℝ => C.expansionFactor r i^2*x) hr₂
    simp only [hk,BoundaryState,phi]
    nlinarith
  | coreSide =>
    have hλ := C.expansionFactor_core (r := r) i (by simp [hk])
    simpa [hk,hλ,BoundaryState] using C.boundary i
  | coreCorner =>
    have hλ := C.expansionFactor_core (r := r) i (by simp [hk])
    simpa [hk,hλ,BoundaryState] using C.boundary i

lemma BoundaryCycle.expanded_contained {q r : ℝ} (C : BoundaryCycle q)
    (hq : q ∈ Set.Icc (5/2) 4) (hr : r ∈ Set.Icc (5/2) 4) (hqr : q ≤ r)
    (i : Vertex) : SqContained r (radialSquare (C.square i) (C.expansionFactor r i)) := by
  by_cases hk : C.kind i = .outer
  · obtain ⟨hx,hy⟩ := radialSquare_coordinates (C.square i)
      (show 0 ≤ C.expansionFactor r i by linarith [C.expansionFactor_ge_one hq hr hqr i])
    obtain ⟨ha,hb⟩ := C.absolute_coordinates i
    have he := C.expanded_boundary hq hr hqr i
    simp only [hk,BoundaryState] at he
    simpa [SqContained,hx,hy,ha,hb] using he.le
  · rw [C.expansionFactor_core i hk]
    simpa [radialSquare,moveCenter,scale] using (C.contained i).mono hqr

lemma BoundaryCycle.expanded_axis {q r : ℝ} (C : BoundaryCycle q)
    (hq : q ∈ Set.Icc (5/2) 4) (hr : r ∈ Set.Icc (5/2) 4) (hqr : q ≤ r)
    (i : Vertex) (axis : SignedAxis)
    (haxis : axis.Feasible (C.square i) (C.square (next i))) :
    axis.Feasible
      (radialSquare (C.square i) (C.expansionFactor r i))
      (radialSquare (C.square (next i)) (C.expansionFactor r (next i))) := by
  let n := axis.normal (C.square i) (C.square (next i))
  let u := -dot n (C.ray i)
  let v := dot n (C.ray (next i))
  have hunit : normSq n = 1 := signed_normal_unit axis _ _
  have hu : -1 ≤ u ∧ u ≤ 1 := by
    have hh := cauchy_sq n (C.ray i)
    rw [hunit,C.ray_unit] at hh
    dsimp [u]
    constructor <;> nlinarith [sq_nonneg (dot n (C.ray i)+1),sq_nonneg (dot n (C.ray i)-1)]
  have hv : -1 ≤ v ∧ v ≤ 1 := by
    have hh := cauchy_sq n (C.ray (next i))
    rw [hunit,C.ray_unit] at hh
    dsimp [v]
    constructor <;> nlinarith [sq_nonneg (dot n (C.ray (next i))+1),sq_nonneg (dot n (C.ray (next i))-1)]
  have hsource : axis.projection (C.square i) (C.square (next i)) =
      u*(C.radialState i).radius q+v*(C.radialState (next i)).radius q := by
    rw [C.radialState_source hq i,C.radialState_source hq (next i)]
    dsimp [SignedAxis.projection]
    rw [C.center_polar i,C.center_polar (next i)]
    dsimp [u,v,n,dot,sub,scale]
    ring
  have htransport := RadiusTransfer.every_feasible_projection_preserved
    (C.radialState i) (C.radialState (next i)) hq hr hqr hu hv
    (threshold_ge_one (C.square i) (C.square (next i)))
    (by simpa [SignedAxis.Feasible,hsource] using haxis)
  have hnormal := signed_normal_same_frames
    (radialSquare_frame (C.square i) (C.expansionFactor r i))
    (radialSquare_frame (C.square (next i)) (C.expansionFactor r (next i))) axis
  have hthreshold := threshold_same_frames
    (radialSquare_frame (C.square i) (C.expansionFactor r i))
    (radialSquare_frame (C.square (next i)) (C.expansionFactor r (next i)))
  dsimp [SignedAxis.Feasible]
  rw [hthreshold]
  have htarget : axis.projection
      (radialSquare (C.square i) (C.expansionFactor r i))
      (radialSquare (C.square (next i)) (C.expansionFactor r (next i))) =
      u*(C.radialState i).radius r+v*(C.radialState (next i)).radius r := by
    dsimp [SignedAxis.projection]
    rw [hnormal]
    change dot n (sub (scale (C.expansionFactor r (next i)) (C.square (next i)).center)
      (scale (C.expansionFactor r i) (C.square i).center)) = _
    rw [C.center_polar i,C.center_polar (next i)]
    have hi := C.expansionFactor_radius (r := r) i
    have hj := C.expansionFactor_radius (r := r) (next i)
    dsimp [u,v,dot,sub,scale]
    nlinarith [congrArg (fun x : ℝ => x*(C.ray i).1) hi,
      congrArg (fun x : ℝ => x*(C.ray i).2) hi,
      congrArg (fun x : ℝ => x*(C.ray (next i)).1) hj,
      congrArg (fun x : ℝ => x*(C.ray (next i)).2) hj]
  simpa [htarget] using htransport

/-- The actual endpoint configuration. Its full square records, polar rays,
nearest-axis representatives, radial kinds and selected witnesses are retained.
The proof of `feasible` uses the stronger all-axis endpoint transport above. -/
def BoundaryCycle.expand {q r : ℝ} (C : BoundaryCycle q)
    (hq : q ∈ Set.Icc (5/2) 4) (hr : r ∈ Set.Icc (5/2) 4) (hqr : q ≤ r) :
    BoundaryCycle r where
  square i := radialSquare (C.square i) (C.expansionFactor r i)
  contained := C.expanded_contained hq hr hqr
  core i := radialSquare_core (C.core i) (C.expansionFactor_ge_one hq hr hqr i)
  selected := C.selected
  feasible i := C.expanded_axis hq hr hqr i (C.selected i) (C.feasible i)
  kind := C.kind
  a i := C.expansionFactor r i*C.a i
  b i := C.expansionFactor r i*C.b i
  sigma := C.sigma
  a_pos i := mul_pos (by linarith [C.expansionFactor_ge_one hq hr hqr i]) (C.a_pos i)
  b_nonneg i := mul_nonneg (by linarith [C.expansionFactor_ge_one hq hr hqr i]) (C.b_nonneg i)
  b_le_a i := mul_le_mul_of_nonneg_left (C.b_le_a i)
    (by linarith [C.expansionFactor_ge_one hq hr hqr i])
  sigma_sign := C.sigma_sign
  center_eq i := by
    change scale (C.expansionFactor r i) (C.square i).center = _
    rw [C.center_eq i]
    apply Prod.ext <;> dsimp [rotate,radialSquare,moveCenter,scale] <;> ring
  boundary := C.expanded_boundary hq hr hqr
  beta := C.beta
  center_cos i := by
    rw [C.expanded_sqrt hq hr hqr i]
    change C.expansionFactor r i*(C.square i).center.1 = _
    rw [C.center_cos i]
    rfl
  center_sin i := by
    rw [C.expanded_sqrt hq hr hqr i]
    change C.expansionFactor r i*(C.square i).center.2 = _
    rw [C.center_sin i]
    rfl
  frame_cos i := by
    rw [C.expanded_tangent hq hr hqr i]
    exact C.frame_cos i
  frame_sin i := by
    rw [C.expanded_tangent hq hr hqr i]
    exact C.frame_sin i
  gap_pos := C.gap_pos
  gap_lt_pi := C.gap_lt_pi

theorem BoundaryCycle.expand_spec {q r : ℝ} (C : BoundaryCycle q)
    (hq : q ∈ Set.Icc (5/2) 4) (hr : r ∈ Set.Icc (5/2) 4) (hqr : q ≤ r) :
    RadiusExpansion C (C.expand hq hr hqr) := by
  refine ⟨rfl,fun i => ⟨rfl,rfl⟩,rfl,?_,?_⟩
  · funext i
    exact C.expanded_tangent hq hr hqr i
  · exact C.expanded_axis hq hr hqr

theorem radius_expand_boundary_cycle {q r : ℝ} (C : BoundaryCycle q)
    (hq : q ∈ Set.Icc (5/2) 4) (hr : r ∈ Set.Icc (5/2) 4) (hqr : q ≤ r) :
    ∃ D : BoundaryCycle r, RadiusExpansion C D :=
  ⟨C.expand hq hr hqr,C.expand_spec hq hr hqr⟩

end SquaresInCircles.Eight
