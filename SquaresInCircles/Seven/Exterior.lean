import SquaresInCircles.Common.Tangents
import SquaresInCircles.Common.Trigonometry
import SquaresInCircles.Common.ExteriorCharts
import SquaresInCircles.Common.DiskSupport
import SquaresInCircles.Seven.Construction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Seven squares: states, labels, markers and the marker arc

The state of an exterior square is its sorted chart `(a, u)` in the disk of
squared radius `13/4`, an admissible `ExteriorChart`. Its label, the least of an
axial, a side and a capped term, is the angle from the chart phase to the
marker. The centre of an admissible square is within `√3 - 1/2` of the disk
centre, which bounds its support below. The closed square holds the arc of the
unit circle of half-width `1/2` about its label: each of the four edge lines
stays out of the way, the far one trivially. The transverse edges are
controlled by arcsine bounds, and the near edge by an envelope whose curvature
is at most `-1/8`, hence below a parabola through its value and slope at `0`.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

def targetSq : ℝ := 13 / 4
def gap : ℝ := Real.pi / 3
def axial (u : ℝ) : ℝ := 5 * u / 4
def side (a u : ℝ) : ℝ := Real.pi / 6 + (u - 1/2) / 3 + 3 * (1-a) / 4
def label (a u : ℝ) : ℝ := min (min (axial u) (side a u)) (Real.pi / 4)
def remainder (a u : ℝ) : ℝ := 4 - 3*a - 2*u

/-- An admissible state: `1/2 ≤ a`, `0 ≤ u ≤ a` and `φ(a, u) ≤ 13/4`. -/
abbrev Admissible (a u : ℝ) : Prop := ExteriorChart targetSq a u

lemma remainder_identity (a u : ℝ) :
    remainder a u = (a-1)^2 + (u-1/2)^2 + targetSq - phi a u := by
  unfold remainder targetSq phi
  ring

lemma side_identity_transverse (a u : ℝ) :
    side a u = Real.pi/6 + (5/6)*(u-1/2) + remainder a u/4 := by
  unfold side remainder
  ring

lemma side_identity_radial (a u : ℝ) :
    side a u = Real.pi/6 - (5/4)*(a-1) - remainder a u/6 := by
  unfold side remainder
  ring

namespace Admissible
variable {a u : ℝ} (h : Admissible a u)
include h

/-- The tangent half-plane of the circle `φ = 13/4` at the side state `(1, 1/2)`. -/
lemma tangent : 3*a + 2*u ≤ 4 := by
  linarith [tangent_le (u := 1) (v := 1/2) h.phi_le (by norm_num [phi,targetSq])]

lemma remainder_nonneg : 0 ≤ remainder a u := by
  unfold remainder
  linarith [h.tangent]

lemma a_le_sqrt_three_sub_half : a ≤ Real.sqrt 3 - 1/2 :=
  (coordinate_le_of_phi h.u_nonneg h.phi_le).trans_eq (by norm_num [targetSq])

lemma a_lt_five_fourths : a < 5/4 := by
  nlinarith [h.a_le_sqrt_three_sub_half, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
    Real.sqrt_nonneg 3]

lemma sum_lt : a+u < 31/20 := by
  linarith [dot_gt (p := -1) (r := -1) (c := 51/20) h.phi_le (by norm_num)
    (by norm_num [targetSq])]

lemma u_lt : u < 31/40 := by linarith [h.sum_lt, h.u_le]

lemma side_pos : 0 < side a u := by
  have ha := h.a_lt_five_fourths
  have hp := Real.pi_gt_d2
  dsimp [side]
  linarith [h.u_nonneg]

lemma label_nonneg : 0 ≤ label a u :=
  le_min (le_min (by dsimp [axial]; linarith [h.u_nonneg]) h.side_pos.le) (by positivity)

omit h in
lemma label_le_axial (_h : Admissible a u) : label a u ≤ axial u :=
  (min_le_left _ _).trans (min_le_left _ _)

omit h in
lemma label_le_side (_h : Admissible a u) : label a u ≤ side a u :=
  (min_le_left _ _).trans (min_le_right _ _)

omit h in
lemma label_le_quarter (_h : Admissible a u) : label a u ≤ Real.pi/4 := min_le_right _ _

/-- The label lies in `[0, π/4]`. -/
lemma label_mem : 0 ≤ label a u ∧ label a u ≤ Real.pi/4 :=
  ⟨h.label_nonneg, h.label_le_quarter⟩

lemma label_zero_iff : label a u = 0 ↔ u = 0 := by
  constructor
  · intro hl
    by_contra hu
    have hu' : 0 < u := lt_of_le_of_ne h.u_nonneg (Ne.symm hu)
    have hp : 0 < label a u :=
      lt_min (lt_min (by dsimp [axial]; linarith) h.side_pos) (by positivity)
    exact hp.ne' hl
  · rintro rfl
    exact le_antisymm (by simpa [axial] using h.label_le_axial) h.label_nonneg

lemma radial_label_bound : a ≤ 1 + 2*Real.pi/15 - (4/5)*label a u := by
  have ht := h.label_le_side
  rw [side_identity_radial] at ht
  linarith [h.remainder_nonneg]

omit h in
/-- The label is one of its three terms. -/
lemma selected (_h : Admissible a u) :
    label a u = axial u ∨ label a u = side a u ∨ label a u = Real.pi/4 := by
  unfold label
  rcases min_choice (min (axial u) (side a u)) (Real.pi/4) with h | h <;> rw [h]
  · rcases min_choice (axial u) (side a u) with h' | h' <;> simp [h']
  · simp

end Admissible

/-- Projecting the state disk onto the direction `(2, 1)`: `2a + u < 2.532`. -/
lemma Admissible.projection_two_one {a u : ℝ} (h : Admissible a u) : 2*a+u < 2.532 := by
  linarith [dot_gt (p := -2) (r := -1) (c := 4.032) h.phi_le (by norm_num)
    (by norm_num [targetSq])]

lemma side_selected_label_gt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) : (9 : ℝ)/25 < label a u := by
  have hproj := h.projection_two_one
  have hu := h.label_le_axial
  have hs := hsel
  dsimp [axial] at hu
  dsimp [side] at hs
  by_contra hn
  linarith [Real.pi_gt_d2]

/-- At `a ≥ 9/8` the side label forces `u > 0.29`, and the corner
`(9/8, 0.29)` lies outside the disk. -/
lemma side_selected_a_lt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) : a < 9/8 := by
  have hl := side_selected_label_gt h hsel
  have hp := h.phi_le
  rw [hsel] at hl
  dsimp [side] at hl
  dsimp [phi,targetSq] at hp
  by_contra hn
  have hu : (0.29 : ℝ) < u := by linarith [Real.pi_lt_d4]
  nlinarith

lemma side_selected_a_gt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) : (7 : ℝ)/10 < a := by
  have ht := h.label_le_axial
  have hq := h.label_le_quarter
  rw [hsel] at ht hq
  dsimp [side,axial] at ht hq
  linarith [Real.pi_lt_d4]

lemma axial_tie_line {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = axial u) : 9*a+11*u ≤ 2*Real.pi+7 := by
  have hh := h.label_le_side
  rw [hsel] at hh
  dsimp [side,axial] at hh
  linarith

/-- An axial label: `15 (a + u) = (9a + 11u) + 2 (4 - r)` with `9a + 11u ≤ 2π + 7`,
and the remainder `r` vanishes only at the side state `(1, 1/2)`, where the
label is not axial. -/
lemma axial_sum_lt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = axial u) : a+u < 1+2*Real.pi/15 := by
  have ht := axial_tie_line h hsel
  by_contra hn
  have hr : remainder a u ≤ 0 := by unfold remainder; linarith
  have he := remainder_identity a u
  have hp := h.phi_le
  have ha : a = 1 := by nlinarith [sq_nonneg (u-1/2)]
  have hu : u = 1/2 := by nlinarith [sq_nonneg (a-1)]
  rw [ha,hu] at ht
  linarith [Real.pi_lt_d2]

/-- A side label above `π/6` costs a remainder quadratic in the excess. -/
lemma side_remainder_quadratic {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) :
    (9/5)*(label a u-Real.pi/6)^2 ≤ remainder a u := by
  let D := label a u-Real.pi/6
  let W := remainder a u
  have hW : 0 ≤ W := h.remainder_nonneg
  have hD : D ≤ 4/15 := by
    have hh := h.label_le_quarter
    dsimp [D]
    linarith [Real.pi_lt_d4]
  have hx : a-1 = -(4/5)*D-(2/15)*W := by
    have hh := side_identity_radial a u
    rw [← hsel] at hh
    dsimp [D,W]
    linarith
  have hy : u-1/2 = (6/5)*D-(3/10)*W := by
    have hh := side_identity_transverse a u
    rw [← hsel] at hh
    dsimp [D,W]
    linarith
  have hs : (a-1)^2+(u-1/2)^2 ≤ W := by
    have hh := remainder_identity a u
    have hp := h.phi_le
    dsimp [W]
    linarith
  have hid : (a-1)^2+(u-1/2)^2 =
      (52/25)*D^2-(38/75)*D*W+(97/900)*W^2 := by
    rw [hx,hy]
    ring
  have hprod := mul_nonneg hW (show 0 ≤ 4/15-D by linarith)
  change (9/5)*D^2 ≤ W
  linarith [sq_nonneg W,sq_nonneg D]

/-- The marker in an existing square chart. Reflections are not lost. -/
def chartMarker {S : UnitSquare} {o : Point} (C : SquareChart S o) : Direction :=
  chartAngle C.phase C.reversed (label C.a C.b)

lemma sqrt_three_bounds : (1.73 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 1.733 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  constructor <;> nlinarith [Real.sqrt_nonneg (3 : ℝ)]

/-- The centre of an admissible square is within `√3 - 1/2` of the disk centre,
so its support in every direction is at least `1 - √3 > -37/50`. -/
lemma support_lower {a b : ℝ} (h : Admissible a |b|) (z : ℝ) :
    -37/50 < support a b z := by
  have hc : a^2+b^2 ≤ (Real.sqrt 3-1/2)^2 := h.center_sq_le.trans_eq (by norm_num [targetSq])
  linarith [support_ge (by linarith [sqrt_three_bounds.1]) hc z,sqrt_three_bounds.2]

/-- `(5/4) y - arcsin y` increases on `[-3/5, 3/5]` and decreases on `[3/5, 1]`:
its derivative is `5/4 - 1/√(1 - y²)`. -/
lemma asin_line_mono :
    MonotoneOn (fun y => (5/4)*y-Real.arcsin y) (Icc (-3/5) (3/5)) ∧
      AntitoneOn (fun y => (5/4)*y-Real.arcsin y) (Icc (3/5) 1) := by
  have hd (y : ℝ) (hy : y ∈ Ioo (-1) 1) :
      HasDerivAt (fun y => (5/4)*y-Real.arcsin y) (5/4-1/Real.sqrt (1-y^2)) y :=
    ((hasDerivAt_id y).const_mul (5/4)).sub
      (Real.hasDerivAt_arcsin (by linarith [hy.1]) (by linarith [hy.2])) |>.congr_deriv (by simp)
  have hr {y : ℝ} (hy : y ∈ Ioo (-1) 1) : 0 < Real.sqrt (1-y^2) :=
    Real.sqrt_pos.mpr (by nlinarith [hy.1,hy.2])
  have hs {y : ℝ} (hy : y ∈ Ioo (-1) 1) : Real.sqrt (1-y^2)^2 = 1-y^2 :=
    Real.sq_sqrt (by nlinarith [hy.1,hy.2])
  refine ⟨monoOn_of_hasDeriv_nonneg (by fun_prop)
    (fun y hy => hd y ⟨by linarith [hy.1],by linarith [hy.2]⟩) fun y hy => ?_,
    antiOn_of_hasDeriv_nonpos (by fun_prop)
    (fun y hy => hd y ⟨by linarith [hy.1],hy.2⟩) fun y hy => ?_⟩
  · have hy' : y ∈ Ioo (-1) 1 := ⟨by linarith [hy.1],by linarith [hy.2]⟩
    have hlo : 4/5 ≤ Real.sqrt (1-y^2) := by nlinarith [hy.1,hy.2,hr hy',hs hy']
    linarith [(div_le_iff₀ (hr hy')).mpr (show 1 ≤ 5/4*Real.sqrt (1-y^2) by linarith)]
  · have hy' : y ∈ Ioo (-1) 1 := ⟨by linarith [hy.1],hy.2⟩
    have hup : Real.sqrt (1-y^2) ≤ 4/5 := by nlinarith [hy.1,hy.2,hr hy',hs hy']
    linarith [(le_div_iff₀ (hr hy')).mpr (show 5/4*Real.sqrt (1-y^2) ≤ 1 by linarith)]

lemma marker_lower_endpoint {a u : ℝ} (h : Admissible a u) :
    Real.arcsin (u-1/2)+1/2 < label a u := by
  have hasin : Real.arcsin (u-1/2) ≤ u-1/2+(11/40)^3/4 := by
    by_cases h0 : 0 ≤ u-1/2
    · have hb := arcsin_le_cubic h0 (by linarith [h.u_lt])
      have hc : (u-1/2)^3 ≤ (11/40 : ℝ)^3 := pow_le_pow_left₀ h0 (by linarith [h.u_lt]) 3
      linarith
    · linarith [arcsin_le_self_of_nonpos (by linarith [h.u_nonneg]) (le_of_not_ge h0)]
  have hp := Real.pi_gt_d2
  -- the axial term: `(5/4) y - arcsin y` increases from `y = -1/2`
  have hA : Real.pi/6 ≤ axial u-Real.arcsin (u-1/2) := by
    have hm := asin_line_mono.1 (show (-1/2 : ℝ) ∈ Icc (-3/5) (3/5) by norm_num)
      (show u-1/2 ∈ Icc (-3/5) (3/5) by constructor <;> linarith [h.u_nonneg,h.u_lt]) (by linarith [h.u_nonneg])
    beta_reduce at hm
    rw [neg_div,Real.arcsin_neg,asin_half] at hm
    dsimp [axial]
    linarith
  -- the side term, by Cauchy–Schwarz on the disk: `(3/4)(a+1/2)+(2/3)(u+1/2) < 43/24+0.0175`
  have hcs := dot_gt (p := -3/4) (r := -2/3) (c := 43/24+0.0175) h.phi_le (by norm_num)
    (by norm_num [targetSq])
  have hT : Real.arcsin (u-1/2)+1/2 < side a u := by
    dsimp [side]
    linarith
  have hcap : Real.arcsin (u-1/2)+1/2 < Real.pi/4 := by
    linarith [h.u_lt]
  unfold label
  exact lt_min (lt_min (by linarith) hT) hcap

/-- Upper envelope for side label plus arcsine of the near vertical edge. -/
def arcEnvelope (x : ℝ) : ℝ :=
  Real.pi/6+1/24+(1/3)*Real.sqrt (targetSq-(x+1)^2)+Real.arcsin x-3*x/4

def arcEnvelopeDeriv (x : ℝ) : ℝ :=
  1/Real.sqrt (1-x^2)-3/4-(x+1)/(3*Real.sqrt (targetSq-(x+1)^2))

def arcEnvelopeSecond (x : ℝ) : ℝ :=
  x/(Real.sqrt (1-x^2))^3-targetSq/(3*(Real.sqrt (targetSq-(x+1)^2))^3)

lemma arc_radicands {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    0 < 1-x^2 ∧ 0 < targetSq-(x+1)^2 := by
  dsimp [targetSq]
  constructor <;> nlinarith [hx.1,hx.2]

lemma arcEnvelope_hasDeriv {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    HasDerivAt arcEnvelope (arcEnvelopeDeriv x) x := by
  have hp := arc_radicands hx
  have hB : Real.sqrt (targetSq-(x+1)^2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hp.2)
  have hd : HasDerivAt (fun y : ℝ => targetSq-(y+1)^2) (-(2*(x+1))) x := by
    simpa using (((hasDerivAt_id x).add_const 1).pow 2).const_sub targetSq
  have hs := (hd.sqrt (ne_of_gt hp.2)).const_mul (1/3 : ℝ)
  have ha := Real.hasDerivAt_arcsin (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have h := ((hs.const_add (Real.pi/6+1/24)).add ha).sub
    ((hasDerivAt_id x).const_mul (3/4 : ℝ))
  convert h using 1
  · ext y; dsimp [arcEnvelope]; ring
  · dsimp [arcEnvelopeDeriv]
    field_simp
    ring

lemma arcEnvelopeDeriv_hasDeriv {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    HasDerivAt arcEnvelopeDeriv (arcEnvelopeSecond x) x := by
  have hp := arc_radicands hx
  set A := Real.sqrt (1-x^2) with hAdef
  set B := Real.sqrt (targetSq-(x+1)^2) with hBdef
  have hA : 0 < A := Real.sqrt_pos.mpr hp.1
  have hB : 0 < B := Real.sqrt_pos.mpr hp.2
  have hB2 : B^2=targetSq-(x+1)^2 := Real.sq_sqrt hp.2.le
  have dA : HasDerivAt (fun y : ℝ => Real.sqrt (1-y^2)) (-x/A) x := by
    have h1 : HasDerivAt (fun y : ℝ => 1-y^2) (-(2*x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub 1
    have h := h1.sqrt (ne_of_gt hp.1)
    rw [← hAdef] at h
    refine h.congr_deriv ?_
    field_simp
  have dB : HasDerivAt (fun y : ℝ => Real.sqrt (targetSq-(y+1)^2)) (-(x+1)/B) x := by
    have h1 : HasDerivAt (fun y : ℝ => targetSq-(y+1)^2) (-(2*(x+1))) x := by
      simpa using (((hasDerivAt_id x).add_const 1).pow 2).const_sub targetSq
    have h := h1.sqrt (ne_of_gt hp.2)
    rw [← hBdef] at h
    refine h.congr_deriv ?_
    field_simp
  have hi : HasDerivAt (fun y : ℝ => 1/Real.sqrt (1-y^2)) (x/A^3) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).div dA (ne_of_gt hA)
    rw [← hAdef] at h
    refine h.congr_deriv ?_
    field_simp
    ring
  have hj : HasDerivAt (fun y : ℝ => (y+1)/(3*Real.sqrt (targetSq-(y+1)^2)))
      (targetSq/(3*B^3)) x := by
    have h := ((hasDerivAt_id x).add_const 1).div (dB.const_mul 3)
      (by positivity : 3*B ≠ 0)
    rw [← hBdef] at h
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    linarith
  exact (hi.sub_const (3/4 : ℝ)).sub hj

/-- `9(x+1/8)²(9-7x)³` rises up to `x = 123/280` and falls after it; its peak
is below `676`. -/
lemma curvature_peak_lt {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    9*(x+1/8)^2*(9-7*x)^3 < 676 := by
  have hd (y : ℝ) : HasDerivAt (fun y : ℝ => 9*(y+1/8)^2*(9-7*y)^3)
      (9*(y+1/8)*(9-7*y)^2*(123/8-35*y)) y := by
    have h := ((((hasDerivAt_id y).add_const (1/8)).pow 2).const_mul 9).mul
      ((((hasDerivAt_id y).const_mul 7).const_sub 9).pow 3)
    convert h using 1
    · funext z
      simp only [Pi.mul_apply,Pi.pow_apply,id]
    · simp only [Pi.pow_apply,id]
      ring
  have hm := le_at_peak (c := 123/280) (l := 0) (u := 3/4) (by norm_num) hx
    (by fun_prop) hd
    (fun y hy => by
      have : 0 ≤ y+1/8 := by linarith [hy.1]
      have : 0 ≤ 123/8-35*y := by linarith [hy.2]
      positivity)
    (fun y hy => mul_nonpos_of_nonneg_of_nonpos
      (by have : 0 ≤ y+1/8 := by linarith [hy.1]
          positivity) (by linarith [hy.1]))
  norm_num at hm
  linarith

/-- The envelope bends down at rate at least `1/8`: with `A = √(1-x²) ≤ 1` and
`B = √(13/4-(x+1)²)`, this is `12(x+1/8)B³ < 13A³`, which squares to the peak
bound since `4B² ≤ (9-7x)A²`. -/
lemma arcEnvelopeSecond_le {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    arcEnvelopeSecond x ≤ -1/8 := by
  have hp := arc_radicands hx
  let A := Real.sqrt (1-x^2)
  let B := Real.sqrt (targetSq-(x+1)^2)
  have hA : 0 < A := Real.sqrt_pos.mpr hp.1
  have hB : 0 < B := Real.sqrt_pos.mpr hp.2
  have hA2 : A^2=1-x^2 := Real.sq_sqrt hp.1.le
  have hB2 : B^2=targetSq-(x+1)^2 := Real.sq_sqrt hp.2.le
  have hA3 : A^3 ≤ 1 := pow_le_one₀ hA.le (by nlinarith)
  have hratio : 4*B^2 ≤ (9-7*x)*A^2 := by
    rw [hA2,hB2]
    dsimp [targetSq]
    nlinarith [mul_nonneg hx.1 (sq_nonneg (x-5/14))]
  have hcube := pow_le_pow_left₀ (by positivity) hratio 3
  have hpeak := mul_lt_mul_of_pos_right (curvature_peak_lt hx) (pow_pos (pow_pos hA 2) 3)
  have hsq : (12*(x+1/8)*B^3)^2 < (13*A^3)^2 := by
    have hx8 : 0 ≤ (x+1/8)^2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hcube hx8]
  have hlt : 12*(x+1/8)*B^3 < 13*A^3 := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hrepr : arcEnvelopeSecond x+1/8 =
      (12*x*B^3-13*A^3+(3/2)*A^3*B^3)/(12*A^3*B^3) := by
    change x/A^3-targetSq/(3*B^3)+1/8 = _
    dsimp [targetSq]
    field_simp
    ring
  have hnum : 12*x*B^3-13*A^3+(3/2)*A^3*B^3 < 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hA3 (pow_pos hB 3).le]
  have hneg : arcEnvelopeSecond x+1/8 < 0 := by
    rw [hrepr]
    exact div_neg_of_neg_of_pos hnum (by positivity)
  linarith

/-- With value `π/6 + 13/24` and slope `1/36` at `0`, and curvature at most
`-1/8`, the envelope stays below `π/6 + 353/648`, its parabola's top. -/
lemma arcEnvelope_bound {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    arcEnvelope x ≤ Real.pi/6+353/648 := by
  have hdom (y : ℝ) (hy : y ∈ Icc (0 : ℝ) (3/4)) : 0 ≤ y ∧ y ≤ 3/4 := hy
  have ht := curvature_tangent (f := fun y => -arcEnvelope y) (d := fun y => -arcEnvelopeDeriv y)
    (dd := fun y => -arcEnvelopeSecond y) (κ := 1/8) (l := 0) (u := 3/4) (t := 0) hx
    (by norm_num) (fun y hy => (arcEnvelope_hasDeriv (hdom y hy)).neg)
    (fun y hy => (arcEnvelopeDeriv_hasDeriv (hdom y hy)).neg)
    (fun y hy => by linarith [arcEnvelopeSecond_le (hdom y hy)])
  have hs : Real.sqrt (9/4 : ℝ) = 3/2 := by
    rw [show (9/4 : ℝ) = (3/2)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h0 : arcEnvelope 0 = Real.pi/6+13/24 := by
    norm_num [arcEnvelope,targetSq,hs]
    ring
  have h0' : arcEnvelopeDeriv 0 = 1/36 := by norm_num [arcEnvelopeDeriv,targetSq,hs]
  simp only [h0,h0'] at ht
  nlinarith [sq_nonneg (x-2/9)]

lemma marker_vertical_endpoint {a u : ℝ} (h : Admissible a u) :
    label a u+1/2 < Real.arccos (a-1/2) := by
  let x := a-1/2
  have hx : 0 ≤ x ∧ x ≤ 3/4 := by
    dsimp [x]; constructor <;> linarith [h.half_le,h.a_lt_five_fourths]
  have hp := (arc_radicands hx).2
  have hs := Real.sq_sqrt hp.le
  have hu : u+1/2 ≤ Real.sqrt (targetSq-(x+1)^2) := by
    have hh := h.phi_le
    have hn := Real.sqrt_nonneg (targetSq-(x+1)^2)
    dsimp [phi,x] at hh hs hn ⊢
    nlinarith [h.u_nonneg]
  have henv : side a u+Real.arcsin x ≤ arcEnvelope x := by
    dsimp [side,arcEnvelope,x] at *
    linarith
  have hb := arcEnvelope_bound hx
  have hl := h.label_le_side
  have hpi := Real.pi_gt_d2
  change label a u+1/2 < Real.arccos x
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith

lemma marker_horizontal_endpoint {a u : ℝ} (h : Admissible a u) (hu : u ≤ 1/2) :
    label a u+1/2 < Real.arcsin (u+1/2) := by
  have hs : Real.sin (5/8 : ℝ) < 3/5 := by
    have hb := sin_upper_five (x := 5/8) (by norm_num)
    norm_num at hb ⊢
    linarith
  have ha : (5/8 : ℝ) < Real.arcsin (3/5 : ℝ) :=
    (Real.lt_arcsin_iff_sin_lt'
      (show (5/8 : ℝ) ∈ Ico (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [Real.two_le_pi])).mpr hs
  -- `(5/4) y - arcsin y` is largest at `y = 3/5`
  have ht : Real.arcsin (3/5 : ℝ)+(5/4)*(u+1/2-3/5) ≤ Real.arcsin (u+1/2) := by
    rcases le_total (u+1/2) (3/5) with hy | hy
    · have hm := asin_line_mono.1 (show u+1/2 ∈ Icc (-3/5) (3/5) by
        constructor <;> linarith [h.u_nonneg]) (show (3/5 : ℝ) ∈ Icc (-3/5) (3/5) by norm_num) hy
      simp only at hm
      linarith
    · have hm := asin_line_mono.2 (show (3/5 : ℝ) ∈ Icc (3/5) 1 by norm_num)
        (show u+1/2 ∈ Icc (3/5) 1 by constructor <;> linarith) hy
      simp only at hm
      linarith
  have hl := h.label_le_axial
  dsimp [axial] at hl
  linarith

/-- The marker arc: chart angles within `1/2` of the label stay in the
closed square. -/
theorem marker_arc {a u t : ℝ} (h : Admissible a u)
    (ht : |t-label a u| ≤ 1/2) :
    |Real.cos t-a| ≤ 1/2 ∧ |Real.sin t-u| ≤ 1/2 := by
  have hl := marker_lower_endpoint h
  have hv := marker_vertical_endpoint h
  have hP := h.label_nonneg
  rcases abs_le.mp ht with ⟨ht0,ht1⟩
  have hcos0 : -Real.arccos (a-1/2) < t := by linarith
  have hcos1 : t < Real.arccos (a-1/2) := by linarith
  have ha0 : 0 ≤ a-1/2 := by linarith [h.half_le]
  have ha1 : a-1/2 ≤ 1 := by linarith [h.a_lt_five_fourths]
  have hcos : a-1/2 < Real.cos t := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (Real.arccos_le_pi (a-1/2)) (abs_lt.mpr ⟨hcos0,hcos1⟩)
    rw [Real.cos_arccos (by linarith) ha1,Real.cos_abs] at hh
    exact hh
  have htdom : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    have hA : Real.arccos (a-1/2) ≤ Real.pi/2 := Real.arccos_le_pi_div_two.mpr ha0
    constructor <;> linarith
  have hsin0 : u-1/2 < Real.sin t :=
    (Real.arcsin_lt_iff_lt_sin' ⟨htdom.1,htdom.2.le⟩).mp (by linarith)
  have hsin1 : Real.sin t ≤ u+1/2 := by
    by_cases hu : u ≤ 1/2
    · have hh := marker_horizontal_endpoint h hu
      have hs : Real.sin t < u+1/2 :=
        (Real.lt_arcsin_iff_sin_lt' ⟨htdom.1.le,htdom.2⟩).mp (by linarith)
      exact hs.le
    · linarith [Real.sin_le_one t]
  exact ⟨abs_le.mpr ⟨by linarith,by linarith [Real.cos_le_one t,h.half_le]⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩⟩

end SquaresInCircles.Seven
