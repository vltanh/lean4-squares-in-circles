module

public import SquaresInCircles.Common.Basic
public import Mathlib.Tactic

/-!
# Eight squares: the five-corner chain and the parameters of the family

A point of `Coordinates` is a squared radius `q`, a position `y`, the half-angle tangent `z` of
the tilt and the coordinates `x₁, x₂, y₃, x₄` of the chain of squares `A, B, D, E, H` with five
corners on the circle. In a chain (`IsChain`) the first four corners lie on the circle of squared
radius `q`, and the fifth, `h₁ e + h₂ f` on `H`, lies outside it by the `defect`. The inputs are
these algebraic equations, not rounded coordinates. The stationary system `IsStationary` adds
the bounds of the analytic strip, `defect = 0` and the vanishing of the derivatives of the defect
in the position and in the tilt. The position equation is kept separate from the circle
equations: it is the equation needed for the last force balance (`Weights.lean`).

The chain realizes the seven contacts of the optimal packing for every `q`, `y` and `z`
(`HG_contact`, `GA_contact`, `HE_contact`, `standard_contacts`). `EqualityParameters` are the
five parameters of the family, and `Admissible` is its domain, with all weak separation ties and
the half-open interval of the central frame; `InBox` is the box of side `0.002` inside it.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Eight.ExactFamily

def halfAngleCos (z : ℝ) : ℝ := (1 - z ^ 2) / (1 + z ^ 2)
def halfAngleSin (z : ℝ) : ℝ := 2 * z / (1 + z ^ 2)

theorem halfAngle_den_pos (z : ℝ) : 0 < 1 + z ^ 2 := by positivity

theorem halfAngle_unit (z : ℝ) :
    halfAngleCos z ^ 2 + halfAngleSin z ^ 2 = 1 := by
  unfold halfAngleCos halfAngleSin
  field_simp [ne_of_gt (halfAngle_den_pos z)]
  ring

theorem halfAngleCos_pos {z : ℝ} (hz : |z| < 1) : 0 < halfAngleCos z := by
  apply div_pos _ (halfAngle_den_pos z)
  have hz' := abs_lt.mp hz
  nlinarith

theorem halfAngleSin_pos {z : ℝ} (hz : 0 < z) : 0 < halfAngleSin z := by
  exact div_pos (by linarith) (halfAngle_den_pos z)

theorem halfAngleCos_le_one (z : ℝ) : halfAngleCos z ≤ 1 := by
  rw [halfAngleCos, div_le_iff₀ (halfAngle_den_pos z)]
  nlinarith [sq_nonneg z]

/-- Short bounds on the frame throughout the analytic tilt interval. -/
theorem halfAngle_local_bounds {z : ℝ} (hz : 1/20 ≤ z ∧ z ≤ 81/1000) :
    0.986 ≤ halfAngleCos z ∧ halfAngleCos z ≤ 1 ∧
    0.099 ≤ halfAngleSin z ∧ halfAngleSin z ≤ 0.162 := by
  have hz₂ : z^2 ≤ (0.081:ℝ)^2 := by nlinarith only [hz.1,hz.2]
  have hc : 0.986 ≤ halfAngleCos z ∧ halfAngleCos z ≤ 1 := by
    refine ⟨?_,halfAngleCos_le_one z⟩
    rw [halfAngleCos,le_div_iff₀ (halfAngle_den_pos z)]
    nlinarith only [hz₂]
  have hs : 0.099 ≤ halfAngleSin z ∧ halfAngleSin z ≤ 0.162 := by
    constructor
    · rw [halfAngleSin,le_div_iff₀ (halfAngle_den_pos z)]
      nlinarith only [hz.1,hz₂]
    · rw [halfAngleSin,div_le_iff₀ (halfAngle_den_pos z)]
      nlinarith only [hz.2,sq_nonneg z]
  exact ⟨hc.1,hc.2,hs.1,hs.2⟩

/-- The squared radius, the position, the half-angle tangent of the tilt and the four
coordinates of the chain given by successive square roots, of which `x₄` is negative. -/
structure Coordinates where
  q : ℝ
  y : ℝ
  z : ℝ
  x₁ : ℝ
  x₂ : ℝ
  y₃ : ℝ
  x₄ : ℝ

/-- Coordinates from successive circle radicals, with the negative branch for `x₄`. -/
def radicalCoordinates (q y z : ℝ) : Coordinates where
  q := q
  y := y
  z := z
  x₁ := Real.sqrt (q-y^2)
  x₂ := Real.sqrt (q-(y+2)^2)
  y₃ := Real.sqrt (q-(Real.sqrt (q-(y+2)^2)-3)^2)
  x₄ := -Real.sqrt (q-(Real.sqrt (q-(Real.sqrt (q-(y+2)^2)-3)^2)-2)^2)

namespace Coordinates

def c (d : Coordinates) : ℝ := halfAngleCos d.z
def s (d : Coordinates) : ℝ := halfAngleSin d.z
def x₃ (d : Coordinates) : ℝ := d.x₂ - 3
def y₄ (d : Coordinates) : ℝ := d.y₃ - 2
def h₁ (d : Coordinates) : ℝ := d.c * d.x₁ + d.s * d.y - 2 - d.c
def h₂ (d : Coordinates) : ℝ := -d.s * d.x₄ + d.c * d.y₄ - 1 - d.s
def h₂tilt (d : Coordinates) : ℝ := -d.c*(d.x₄+1)-d.s*d.y₄
def defect (d : Coordinates) : ℝ := d.h₁ ^ 2 + d.h₂ ^ 2 - d.q
def y₄deriv (d : Coordinates) : ℝ :=
  d.x₃ * (d.y + 2) / (d.y₃ * d.x₂)
def h₁deriv (d : Coordinates) : ℝ := d.s - d.c * d.y / d.x₁
def h₂deriv (d : Coordinates) : ℝ :=
  (d.c + d.s * d.y₄ / d.x₄) * d.y₄deriv
def positionDerivative (d : Coordinates) : ℝ :=
  2 * (d.h₁ * d.h₁deriv + d.h₂ * d.h₂deriv)
def tiltDerivative (d : Coordinates) : ℝ :=
  2 * (d.h₁ * (-d.s * (d.x₁ - 1) + d.c * d.y) +
       d.h₂ * (-d.c * (d.x₄ + 1) - d.s * d.y₄))

/-- Branch inequalities and the four circle equations. -/
structure IsChain (d : Coordinates) : Prop where
  x₁_pos : 0 < d.x₁
  x₂_pos : 0 < d.x₂
  y₃_pos : 0 < d.y₃
  x₄_neg : d.x₄ < 0
  first_circle : d.x₁ ^ 2 + d.y ^ 2 = d.q
  second_circle : d.x₂ ^ 2 + (d.y + 2) ^ 2 = d.q
  third_circle : d.x₃ ^ 2 + d.y₃ ^ 2 = d.q
  fourth_circle : d.x₄ ^ 2 + d.y₄ ^ 2 = d.q

/-- The stationary system in the analytic strip. It consists of equations and branch
conditions only, with no reference to packings. -/
structure IsStationary (d : Coordinates) : Prop extends IsChain d where
  q_lower : (79 / 40 : ℝ) ^ 2 ≤ d.q
  q_upper : d.q ≤ 9789 / 2500
  y_lower : -1 < d.y
  y_upper : d.y < -(1 / 2)
  y₄_lower : -1 < d.y₄
  y₄_upper : d.y₄ < -(1 / 2)
  position_order : d.y < d.y₄
  z_pos : 0 < d.z
  tilt_range : 2 * d.z / (1 - d.z ^ 2) < 1 / 5
  z_lt_one : d.z < 1
  zero_defect : d.defect = 0
  position_stationary : d.positionDerivative = 0
  tilt_stationary : d.tiltDerivative = 0

theorem unit (d : Coordinates) : d.c ^ 2 + d.s ^ 2 = 1 :=
  halfAngle_unit d.z

theorem IsChain.radicals {d : Coordinates} (h : d.IsChain) :
    d.x₁ = Real.sqrt (d.q - d.y ^ 2) ∧
    d.x₂ = Real.sqrt (d.q - (d.y + 2) ^ 2) ∧
    d.y₃ = Real.sqrt (d.q - d.x₃ ^ 2) ∧
    d.x₄ = -Real.sqrt (d.q - d.y₄ ^ 2) := by
  have h₁ : d.q - d.y ^ 2 = d.x₁ ^ 2 := by linarith [h.first_circle]
  have h₂ : d.q - (d.y + 2) ^ 2 = d.x₂ ^ 2 := by linarith [h.second_circle]
  have h₃ : d.q - d.x₃ ^ 2 = d.y₃ ^ 2 := by linarith [h.third_circle]
  have h₄ : d.q - d.y₄ ^ 2 = d.x₄ ^ 2 := by linarith [h.fourth_circle]
  simp only [h₁, h₂, h₃, h₄, Real.sqrt_sq_eq_abs,
    abs_of_pos h.x₁_pos, abs_of_pos h.x₂_pos, abs_of_pos h.y₃_pos,
    abs_of_neg h.x₄_neg, neg_neg, and_self]

theorem chain_unique_radicals {d e : Coordinates} (hd : d.IsChain) (he : e.IsChain)
    (hq : d.q = e.q) (hy : d.y = e.y) (hz : d.z = e.z) : d = e := by
  have hd' := hd.radicals
  have he' := he.radicals
  have h₁ : d.x₁ = e.x₁ := by rw [hd'.1, he'.1, hq, hy]
  have h₂ : d.x₂ = e.x₂ := by rw [hd'.2.1, he'.2.1, hq, hy]
  have h₃ : d.y₃ = e.y₃ := by rw [hd'.2.2.1, he'.2.2.1, x₃, x₃, hq, h₂]
  have h₄ : d.x₄ = e.x₄ := by rw [hd'.2.2.2, he'.2.2.2, y₄, y₄, hq, h₃]
  cases d
  cases e
  simp only [Coordinates.mk.injEq]
  exact ⟨hq, hy, hz, h₁, h₂, h₃, h₄⟩

def e (d : Coordinates) : Point := (d.c, d.s)
def f (d : Coordinates) : Point := (-d.s, d.c)
def inFrame (d : Coordinates) (a b : ℝ) : Point :=
  (d.c * a - d.s * b, d.s * a + d.c * b)

theorem dot_e_inFrame (d : Coordinates) (a b : ℝ) :
    dot d.e (d.inFrame a b) = a := by
  dsimp [dot, e, inFrame]
  linear_combination a * d.unit

theorem dot_f_inFrame (d : Coordinates) (a b : ℝ) :
    dot d.f (d.inFrame a b) = b := by
  dsimp [dot, f, inFrame]
  linear_combination b * d.unit

theorem normSq_inFrame (d : Coordinates) (a b : ℝ) :
    normSq (d.inFrame a b) = a ^ 2 + b ^ 2 := by
  dsimp [normSq, inFrame]
  linear_combination (a ^ 2 + b ^ 2) * d.unit

theorem inFrame_sub (d : Coordinates) (a b x y : ℝ) :
    sub (d.inFrame a b) (d.inFrame x y) = d.inFrame (a-x) (b-y) := by
  ext <;> dsimp [sub, inFrame] <;> ring

def pA (d : Coordinates) : Point := (d.x₁ - 1/2, d.y + 1/2)
def pB (d : Coordinates) : Point := (d.x₂ - 1/2, d.y + 3/2)
def pD (d : Coordinates) : Point := (d.x₃ + 1/2, d.y₃ - 1/2)
def pE (d : Coordinates) : Point := (d.x₄ + 1/2, d.y₄ + 1/2)
def pH (d : Coordinates) : Point := d.inFrame (d.h₁ + 1/2) (d.h₂ + 1/2)
def pT (d : Coordinates) (z : ℝ) : Point := (d.x₂ - 3/2, z)
def pG (d : Coordinates) (η : ℝ) : Point :=
  d.inFrame (d.h₁ + 3/2) (d.h₂ + 1/2 + η)

def tiltedSquare (d : Coordinates) (p : Point) : UnitSquare where
  center := p
  cosine := d.c
  sine := d.s
  unit := d.unit

def zMax (d : Coordinates) : ℝ :=
  Real.sqrt (d.q - (d.x₂ - 1) ^ 2) - 1/2
def etaMin (d : Coordinates) : ℝ :=
  -d.h₂ - Real.sqrt (d.q - (d.h₁ + 2) ^ 2)
def etaMax (d : Coordinates) : ℝ := -d.h₂ - 13/12

/-- Exterior labels, in the canonical counterclockwise order. -/
def exteriorCenters (d : Coordinates) (z η : ℝ) : Fin 7 → Point :=
  ![d.pH, d.pG η, d.pA, d.pB, d.pT z, d.pD, d.pE]

def exteriorSquares (d : Coordinates) (z η : ℝ) : Fin 7 → UnitSquare :=
  ![d.tiltedSquare d.pH, d.tiltedSquare (d.pG η), axisSquare d.pA,
    axisSquare d.pB, axisSquare (d.pT z), axisSquare d.pD, axisSquare d.pE]

def anchorPoints (d : Coordinates) : Fin 5 → Point :=
  ![(d.x₁,d.y), (d.x₂,d.y+2), (d.x₃,d.y₃), (d.x₄,d.y₄),
    d.inFrame d.h₁ d.h₂]

def anchorCenters (d : Coordinates) : Fin 5 → Point :=
  ![d.pA, d.pB, d.pD, d.pE, d.pH]

def anchorOffsets (d : Coordinates) : Fin 5 → Point :=
  ![(1/2,-1/2), (1/2,1/2), (-1/2,1/2), (-1/2,-1/2),
    d.inFrame (-1/2) (-1/2)]

theorem anchor_vertex (d : Coordinates) (i : Fin 5) :
    add (d.anchorCenters i) (d.anchorOffsets i) = d.anchorPoints i := by
  fin_cases i <;>
    ext <;>
    simp [anchorCenters, anchorOffsets, anchorPoints, pA, pB, pD, pE, pH,
      inFrame, add] <;> ring

theorem anchor_circle {d : Coordinates} (hd : d.IsChain) (hz : d.defect = 0)
    (i : Fin 5) : normSq (d.anchorPoints i) = d.q := by
  fin_cases i
  · simpa [anchorPoints, normSq] using hd.first_circle
  · simpa [anchorPoints, normSq] using hd.second_circle
  · simpa [anchorPoints, normSq] using hd.third_circle
  · simpa [anchorPoints, normSq] using hd.fourth_circle
  · simpa [anchorPoints, d.normSq_inFrame, defect] using (sub_eq_zero.mp hz)

theorem HG_contact (d : Coordinates) (η : ℝ) :
    dot d.e (sub (d.pG η) d.pH) = 1 := by
  rw [pG, pH, d.inFrame_sub, d.dot_e_inFrame]
  ring

theorem GA_contact (d : Coordinates) (η : ℝ) :
    dot d.e (sub d.pA (d.pG η)) = (1+d.c+d.s)/2 := by
  rw [dot_sub_right]
  have hG := d.dot_e_inFrame (d.h₁+3/2) (d.h₂+1/2+η)
  change dot d.e d.pA - dot d.e (d.inFrame (d.h₁+3/2) (d.h₂+1/2+η)) = _
  rw [hG]
  dsimp [dot, e, pA, h₁]
  ring

theorem HA_contact (d : Coordinates) :
    dot d.e (sub d.pA d.pH) = (1+d.c+d.s)/2 + 1 := by
  rw [dot_sub_right, pH, d.dot_e_inFrame]
  dsimp [dot, e, pA, h₁]
  ring

theorem HE_contact (d : Coordinates) :
    dot d.f (sub d.pE d.pH) = (1+d.c+d.s)/2 := by
  rw [dot_sub_right, pH, d.dot_f_inFrame]
  dsimp [dot, f, pE, h₂]
  ring

theorem standard_contacts (d : Coordinates) (z : ℝ) :
    (d.pB).2 - (d.pA).2 = 1 ∧
    (d.pB).1 - (d.pT z).1 = 1 ∧
    (d.pT z).1 - (d.pD).1 = 1 ∧
    (d.pD).2 - (d.pE).2 = 1 := by
  dsimp [pA, pB, pT, pD, pE, x₃, y₄]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end Coordinates

/-- The five parameters of the family: the centre `(x, y)` and the frame parameter `w` of the
central square, the height `z` of the top square `T` and the offset `eta` of `G` along `H`. The
letter `z` also names the half-angle tangent `Coordinates.z`; here it is the height of `T`. -/
structure EqualityParameters where
  x : ℝ
  y : ℝ
  w : ℝ
  z : ℝ
  eta : ℝ

namespace EqualityParameters

def C (p : EqualityParameters) : ℝ := halfAngleCos p.w
def S (p : EqualityParameters) : ℝ := halfAngleSin p.w
def center (p : EqualityParameters) : Point := (p.x,p.y)

def centralSquare (p : EqualityParameters) : UnitSquare where
  center := p.center
  cosine := p.C
  sine := p.S
  unit := halfAngle_unit p.w

def M₀ (p : EqualityParameters) (d : Point) : ℝ :=
  max (max |d.1| |d.2|)
    (max |p.C*d.1+p.S*d.2| |-p.S*d.1+p.C*d.2|)

def Mₜ (p : EqualityParameters) (a : Coordinates) (d : Point) : ℝ :=
  max (max |a.c*d.1+a.s*d.2| |-a.s*d.1+a.c*d.2|)
    (max |p.C*d.1+p.S*d.2| |-p.S*d.1+p.C*d.2|)

def W₀ (p : EqualityParameters) : ℝ := (1+p.C+|p.S|)/2
def Wₜ (p : EqualityParameters) (a : Coordinates) : ℝ :=
  (1+a.c*p.C+a.s*p.S+|a.c*p.S-a.s*p.C|)/2

/-- The admissible parameters: the frame parameter in `[1 - √2, √2 - 1)`, the two sliders in
their closed ranges, the core in the interior of the central square, and the central square
separated from the seven others, with every weak separation tie included. -/
structure Admissible (a : Coordinates) (p : EqualityParameters) : Prop where
  frame_lower : 1-Real.sqrt 2 ≤ p.w
  frame_upper : p.w < Real.sqrt 2-1
  top_lower : 7/12 ≤ p.z
  top_upper : p.z ≤ a.zMax
  tilted_lower : a.etaMin ≤ p.eta
  tilted_upper : p.eta ≤ a.etaMax
  core_first : |p.C*p.x+p.S*p.y| < 5/12
  core_second : |-p.S*p.x+p.C*p.y| < 5/12
  A_sep : p.W₀ ≤ p.M₀ (sub a.pA p.center)
  B_sep : p.W₀ ≤ p.M₀ (sub a.pB p.center)
  D_sep : p.W₀ ≤ p.M₀ (sub a.pD p.center)
  E_sep : p.W₀ ≤ p.M₀ (sub a.pE p.center)
  T_sep : p.W₀ ≤ p.M₀ (sub (a.pT p.z) p.center)
  H_sep : p.Wₜ a ≤ p.Mₜ a (sub a.pH p.center)
  G_sep : p.Wₜ a ≤ p.Mₜ a (sub (a.pG p.eta) p.center)

/-- The rational box `[0.139, 0.141] × [-0.001, 0.001] × [0.099, 0.101] × [1.349, 1.351] ×
[-0.321, -0.319]` of parameters. -/
def InBox (p : EqualityParameters) : Prop :=
  (139/1000 ≤ p.x ∧ p.x ≤ 141/1000) ∧
  (-(1/1000) ≤ p.y ∧ p.y ≤ 1/1000) ∧
  (99/1000 ≤ p.w ∧ p.w ≤ 101/1000) ∧
  (1349/1000 ≤ p.z ∧ p.z ≤ 1351/1000) ∧
  (-(321/1000) ≤ p.eta ∧ p.eta ≤ -(319/1000))

def model (a : Coordinates) (p : EqualityParameters) : Fin 8 → UnitSquare :=
  ![p.centralSquare, a.tiltedSquare a.pH, a.tiltedSquare (a.pG p.eta),
    axisSquare a.pA, axisSquare a.pB, axisSquare (a.pT p.z),
    axisSquare a.pD, axisSquare a.pE]

theorem central_core_coordinates (p : EqualityParameters) :
    alpha p.centralSquare (0,0) = |p.C*p.x+p.S*p.y| ∧
    beta p.centralSquare (0,0) = |-p.S*p.x+p.C*p.y| := by
  constructor
  · change |p.C*(0-p.x)+p.S*(0-p.y)| = _
    convert abs_neg (p.C*p.x+p.S*p.y) using 1
    congr 1
    ring
  · change |-p.S*(0-p.x)+p.C*(0-p.y)| = _
    convert abs_neg (-p.S*p.x+p.C*p.y) using 1
    congr 1
    ring

theorem central_containment {a : Coordinates} {p : EqualityParameters}
    (hp : p.Admissible a) (hq : (121/72 : ℝ) < a.q) :
    phi (alpha p.centralSquare (0,0)) (beta p.centralSquare (0,0)) < a.q := by
  obtain ⟨hx,hy⟩ := p.central_core_coordinates
  rw [hx,hy]
  have h₁ := hp.core_first
  have h₂ := hp.core_second
  have h₃ := abs_nonneg (p.C*p.x+p.S*p.y)
  have h₄ := abs_nonneg (-p.S*p.x+p.C*p.y)
  unfold phi
  nlinarith

end EqualityParameters

/-! ### Bounds from the circle equations -/

open Coordinates

/-- A circle equation bounds a nonnegative coordinate by comparing squared endpoints. -/
theorem circle_coordinate_bounds {q x y l u : ℝ} (h : x^2+y^2=q)
    (hx : 0 ≤ x) (hu : 0 ≤ u) (hl : l^2+y^2 ≤ q) (hh : q ≤ u^2+y^2) :
    l ≤ x ∧ x ≤ u :=
  ⟨le_of_sq_le_sq (by linarith only [h,hl]) hx,
    le_of_sq_le_sq (by linarith only [h,hh]) hu⟩

private theorem sqrt_bracket {r l u : ℝ} (hu : 0 ≤ u) (hl : l^2 ≤ r) (hh : r ≤ u^2) :
    l ≤ Real.sqrt r ∧ Real.sqrt r ≤ u :=
  ⟨Real.le_sqrt_of_sq_le hl,Real.sqrt_le_iff.mpr ⟨hu,hh⟩⟩

/-- Multiply bounds for two nonnegative quantities. -/
theorem positive_product_bounds {x y a b c d : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    a*c ≤ x*y ∧ x*y ≤ b*d :=
  ⟨mul_le_mul hx.1 hy.1 hc (ha.trans hx.1),
    mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans (hx.1.trans hx.2))⟩

/-- Divide nonnegative bounds by positive bounds, reversing the denominator endpoints. -/
theorem positive_quotient_bounds {x y a b c d : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) (ha : 0 ≤ a) (hc : 0 < c) :
    a/d ≤ x/y ∧ x/y ≤ b/c :=
  ⟨div_le_div₀ (ha.trans hx.1) hx.1 (hc.trans_le hy.1) hy.2,
    div_le_div₀ (ha.trans (hx.1.trans hx.2)) hx.2 hc hy.1⟩

namespace Coordinates

/-- Coarse height and circle-coordinate bounds control the frame, without a fine `h₂` bound. -/
theorem frame_bounds_of_coordinates {d : Coordinates}
    (hY : 1.4387 ≤ d.y₃ ∧ d.y₃ ≤ 1.4643)
    (hw : 1.8974 ≤ -d.x₄ ∧ -d.x₄ ≤ 1.9049)
    (hz : 1/20 ≤ d.z ∧ d.z ≤ 81/1000) :
    (0.28 ≤ d.y₄/d.x₄ ∧ d.y₄/d.x₄ ≤ 0.296) ∧
    (1.019 ≤ d.c+d.s*d.y₄/d.x₄ ∧ d.c+d.s*d.y₄/d.x₄ ≤ 1.04) ∧
    (0.93 ≤ d.h₂tilt ∧ d.h₂tilt ≤ 1) := by
  have prod {x y l h l' h' : ℝ} (hx : l ≤ x ∧ x ≤ h) (hy : l' ≤ y ∧ y ≤ h')
      (hl : 0 ≤ l := by norm_num) (hl' : 0 ≤ l' := by norm_num) :=
    positive_product_bounds hx hy hl hl'
  obtain ⟨hcl,hcu,hsl,hsu⟩ := halfAngle_local_bounds hz
  have hc : 0.986 ≤ d.c ∧ d.c ≤ 1 := ⟨hcl,hcu⟩
  have hs : 0.099 ≤ d.s ∧ d.s ≤ 0.162 := ⟨hsl,hsu⟩
  have hv : 0.5357 ≤ -d.y₄ ∧ -d.y₄ ≤ 0.5613 := by
    dsimp only [y₄]; constructor <;> linarith only [hY]
  have hvw₀ := positive_quotient_bounds hv hw (by norm_num) (by norm_num)
  have hvw : 0.28 ≤ d.y₄/d.x₄ ∧ d.y₄/d.x₄ ≤ 0.296 := by
    rw [neg_div_neg_eq] at hvw₀
    constructor <;> linarith only [hvw₀]
  have hframe : d.c+d.s*d.z=1 := by
    dsimp [c,s,halfAngleCos,halfAngleSin]
    field_simp [ne_of_gt (halfAngle_den_pos d.z)]
    ring
  have hdiff : 0.199 ≤ d.y₄/d.x₄-d.z ∧ d.y₄/d.x₄-d.z ≤ 0.246 := by
    constructor <;> linarith only [hvw,hz]
  have hL : 1.019 ≤ d.c+d.s*d.y₄/d.x₄ ∧ d.c+d.s*d.y₄/d.x₄ ≤ 1.04 := by
    have h := prod hs hdiff
    have he : d.c+d.s*d.y₄/d.x₄ = 1+d.s*(d.y₄/d.x₄-d.z) := by
      linear_combination hframe
    rw [he]
    constructor <;> linarith only [h]
  have hw₁ : 0.8974 ≤ -d.x₄-1 ∧ -d.x₄-1 ≤ 0.9049 := by
    constructor <;> linarith only [hw]
  have hE₁ := prod hc hw₁
  have hE₂ := prod hs hv
  have hE : 0.93 ≤ d.h₂tilt ∧ d.h₂tilt ≤ 1 := by
    have he : d.h₂tilt = d.c*(-d.x₄-1)+d.s*(-d.y₄) := by dsimp only [h₂tilt]; ring
    rw [he]
    constructor <;> linarith only [hE₁,hE₂]
  exact ⟨hvw,hL,hE⟩

end Coordinates

/-- Circle and frame bounds throughout the local analytic rectangle. -/
theorem radical_coordinate_bounds {q y z : ℝ}
    (hq : 7831/2000 ≤ q ∧ q ≤ 9789/2500)
    (hy : -937/1000 ≤ y ∧ y ≤ -179/200)
    (hz : 1/20 ≤ z ∧ z ≤ 81/1000) :
    17428/10000 ≤ (radicalCoordinates q y z).x₁ ∧
      (radicalCoordinates q y z).x₁ ≤ 17649/10000 ∧
    16414/10000 ≤ (radicalCoordinates q y z).x₂ ∧
      (radicalCoordinates q y z).x₂ ≤ 16691/10000 ∧
    14387/10000 ≤ (radicalCoordinates q y z).y₃ ∧
      (radicalCoordinates q y z).y₃ ≤ 14643/10000 ∧
    -19049/10000 ≤ (radicalCoordinates q y z).x₄ ∧
      (radicalCoordinates q y z).x₄ ≤ -18974/10000 ∧
    -14263/10000 ≤ (radicalCoordinates q y z).h₁ ∧
      (radicalCoordinates q y z).h₁ ≤ -13198/10000 ∧
    -15316/10000 ≤ (radicalCoordinates q y z).h₂ ∧
      (radicalCoordinates q y z).h₂ ≤ -13202/10000 := by
  let d := radicalCoordinates q y z
  change (17428/10000 ≤ d.x₁ ∧ d.x₁ ≤ 17649/10000 ∧
    16414/10000 ≤ d.x₂ ∧ d.x₂ ≤ 16691/10000 ∧
    14387/10000 ≤ d.y₃ ∧ d.y₃ ≤ 14643/10000 ∧
    -19049/10000 ≤ d.x₄ ∧ d.x₄ ≤ -18974/10000 ∧
    -14263/10000 ≤ d.h₁ ∧ d.h₁ ≤ -13198/10000 ∧
    -15316/10000 ≤ d.h₂ ∧ d.h₂ ≤ -13202/10000)
  have hx₁ : (17428/10000) ≤ d.x₁ ∧ d.x₁ ≤ (17649/10000) :=
    sqrt_bracket (by norm_num) (by nlinarith only [hq.1,hy.1,hy.2])
      (by nlinarith only [hq.2,hy.1,hy.2])
  -- Keep one extra decimal at x₂ before using its circle equation for y₃.
  have hx₂ : 1.64148 ≤ d.x₂ ∧ d.x₂ ≤ 1.66903 :=
    sqrt_bracket (by norm_num) (by nlinarith only [hq.1,hy.1,hy.2])
      (by nlinarith only [hq.2,hy.1,hy.2])
  have hy₃ : (14387/10000) ≤ d.y₃ ∧ d.y₃ ≤ (14643/10000) := by
    change (14387/10000) ≤ Real.sqrt (q-(d.x₂-3)^2) ∧ Real.sqrt (q-(d.x₂-3)^2) ≤ (14643/10000)
    exact sqrt_bracket (by norm_num) (by nlinarith only [hq.1,hx₂.1,hx₂.2])
      (by nlinarith only [hq.2,hx₂.1,hx₂.2])
  have hx₄ : (-19049/10000) ≤ d.x₄ ∧ d.x₄ ≤ (-18974/10000) := by
    have h : 1.8974 ≤ Real.sqrt (q-(d.y₃-2)^2) ∧ Real.sqrt (q-(d.y₃-2)^2) ≤ 1.9049 :=
      sqrt_bracket (by norm_num) (by nlinarith only [hq.1,hy₃.1,hy₃.2])
        (by nlinarith only [hq.2,hy₃.1,hy₃.2])
    change (-19049/10000) ≤ -Real.sqrt (q-(d.y₃-2)^2) ∧ -Real.sqrt (q-(d.y₃-2)^2) ≤ (-18974/10000)
    constructor <;> linarith only [h]
  obtain ⟨hcl,hcu,hsl,hsu⟩ := halfAngle_local_bounds hz
  have hc : 0.986 ≤ d.c ∧ d.c ≤ 1 := ⟨hcl,hcu⟩
  have hs : 0.099 ≤ d.s ∧ d.s ≤ 0.162 := ⟨hsl,hsu⟩
  -- The fifth-corner estimates now use only these coordinate and frame bounds.
  have hdy : d.y = y := rfl
  clear_value d
  -- Use h₁ = c(x₁-1)+sy-2 and h₂ = s(-x₄-1)+c(y₃-2)-1.
  have hcx := positive_product_bounds hc
    (show 0.7428 ≤ d.x₁-1 ∧ d.x₁-1 ≤ 0.7649 by constructor <;> linarith only [hx₁])
    (by norm_num) (by norm_num)
  have hsy := positive_product_bounds hs
    (show 0.895 ≤ -y ∧ -y ≤ 0.937 by constructor <;> linarith only [hy])
    (by norm_num) (by norm_num)
  have hcy := positive_product_bounds hc
    (show 0.5357 ≤ 2-d.y₃ ∧ 2-d.y₃ ≤ 0.5613 by constructor <;> linarith only [hy₃])
    (by norm_num) (by norm_num)
  have hsx := positive_product_bounds hs
    (show 0.8974 ≤ -d.x₄-1 ∧ -d.x₄-1 ≤ 0.9049 by constructor <;> linarith only [hx₄])
    (by norm_num) (by norm_num)
  have hh₁ : (-14263/10000) ≤ d.h₁ ∧ d.h₁ ≤ (-13198/10000) := by
    simp only [h₁,hdy]
    constructor <;> linarith only [hcx,hsy]
  have hh₂ : (-15316/10000) ≤ d.h₂ ∧ d.h₂ ≤ (-13202/10000) := by
    change (-15316/10000) ≤ -d.s*d.x₄+d.c*(d.y₃-2)-1-d.s ∧
      -d.s*d.x₄+d.c*(d.y₃-2)-1-d.s ≤ (-13202/10000)
    constructor <;> linarith only [hcy,hsx]
  exact ⟨hx₁.1,hx₁.2,by linarith only [hx₂.1],by linarith only [hx₂.2],
    hy₃.1,hy₃.2,hx₄.1,hx₄.2,hh₁.1,hh₁.2,hh₂.1,hh₂.2⟩


namespace Coordinates

/-- The four circle coordinates at the left position, independently of tilt. -/
theorem left_circle_bounds {d : Coordinates} (hd : d.IsChain)
    (hq : 3.9155 ≤ d.q ∧ d.q ≤ 3.9156) (hy : d.y = -937/1000) :
    (1.7428 ≤ d.x₁ ∧ d.x₁ ≤ 1.743) ∧
    (1.6689 ≤ d.x₂ ∧ d.x₂ ≤ 1.6691) ∧
    (1.464 ≤ d.y₃ ∧ d.y₃ ≤ 1.4644) ∧
    (1.9047 ≤ -d.x₄ ∧ -d.x₄ ≤ 1.905) := by
  have hr : 1.7428 ≤ d.x₁ ∧ d.x₁ ≤ 1.743 :=
    circle_coordinate_bounds hd.first_circle hd.x₁_pos.le (by norm_num)
      (by rw [hy]; nlinarith only [hq.1]) (by rw [hy]; nlinarith only [hq.2])
  have hU : 1.6689 ≤ d.x₂ ∧ d.x₂ ≤ 1.6691 :=
    circle_coordinate_bounds hd.second_circle hd.x₂_pos.le (by norm_num)
      (by rw [hy]; nlinarith only [hq.1]) (by rw [hy]; nlinarith only [hq.2])
  have hY : 1.464 ≤ d.y₃ ∧ d.y₃ ≤ 1.4644 :=
    circle_coordinate_bounds (q:=d.q) (x:=d.y₃) (y:=d.x₂-3)
      (by simpa only [x₃,add_comm] using hd.third_circle) hd.y₃_pos.le (by norm_num)
      (by nlinarith only [hq.1,hU.1,hU.2]) (by nlinarith only [hq.2,hU.1,hU.2])
  have hw : 1.9047 ≤ -d.x₄ ∧ -d.x₄ ≤ 1.905 :=
    circle_coordinate_bounds (q:=d.q) (x:= -d.x₄) (y:=d.y₃-2)
      (by simpa only [neg_sq,y₄] using hd.fourth_circle) (by linarith only [hd.x₄_neg]) (by norm_num)
      (by nlinarith only [hq.1,hY.1,hY.2]) (by nlinarith only [hq.2,hY.1,hY.2])
  exact ⟨hr,hU,hY,hw⟩

/-- The four circle coordinates at the right position, independently of tilt. -/
theorem right_circle_bounds {d : Coordinates} (hd : d.IsChain)
    (hq : 3.9155 ≤ d.q ∧ d.q ≤ 3.9156) (hy : d.y = -179/200) :
    (1.7647 ≤ d.x₁ ∧ d.x₁ ≤ 1.765) ∧
    (1.6414 ≤ d.x₂ ∧ d.x₂ ≤ 1.6416) ∧
    (1.4386 ≤ d.y₃ ∧ d.y₃ ≤ 1.4389) ∧
    (1.8974 ≤ -d.x₄ ∧ -d.x₄ ≤ 1.8976) := by
  have hr : 1.7647 ≤ d.x₁ ∧ d.x₁ ≤ 1.765 :=
    circle_coordinate_bounds hd.first_circle hd.x₁_pos.le (by norm_num)
      (by rw [hy]; nlinarith only [hq.1]) (by rw [hy]; nlinarith only [hq.2])
  have hU : 1.6414 ≤ d.x₂ ∧ d.x₂ ≤ 1.6416 :=
    circle_coordinate_bounds hd.second_circle hd.x₂_pos.le (by norm_num)
      (by rw [hy]; nlinarith only [hq.1]) (by rw [hy]; nlinarith only [hq.2])
  have hY : 1.4386 ≤ d.y₃ ∧ d.y₃ ≤ 1.4389 :=
    circle_coordinate_bounds (q:=d.q) (x:=d.y₃) (y:=d.x₂-3)
      (by simpa only [x₃,add_comm] using hd.third_circle) hd.y₃_pos.le (by norm_num)
      (by nlinarith only [hq.1,hU.1,hU.2]) (by nlinarith only [hq.2,hU.1,hU.2])
  have hw : 1.8974 ≤ -d.x₄ ∧ -d.x₄ ≤ 1.8976 :=
    circle_coordinate_bounds (q:=d.q) (x:= -d.x₄) (y:=d.y₃-2)
      (by simpa only [neg_sq,y₄] using hd.fourth_circle) (by linarith only [hd.x₄_neg]) (by norm_num)
      (by nlinarith only [hq.1,hY.1,hY.2]) (by nlinarith only [hq.2,hY.1,hY.2])
  exact ⟨hr,hU,hY,hw⟩


/-- At the lower-left corner, the first circle projection dominates the second. -/
theorem lower_corner_position {d : Coordinates} (hd : d.IsChain)
    (hq : 3.9155 ≤ d.q ∧ d.q ≤ 3.9156)
    (hy : d.y = -937/1000) (hz : d.z = 1/20) : d.positionDerivative < 0 := by
  obtain ⟨hr,hU,hY,hw⟩ := left_circle_bounds hd hq hy
  have hc : d.c = 399/401 := by norm_num [c,hz,halfAngleCos]
  have hs : d.s = 40/401 := by norm_num [s,hz,halfAngleSin]
  let K := -d.h₁; let A := d.h₁deriv; let H := -d.h₂
  let p := (-d.x₃)*(d.y+2)/(d.y₃*d.x₂)
  let L := d.c+d.s*d.y₄/d.x₄
  have hK : 1.354 ≤ K := by
    dsimp only [K,h₁]; rw [hc,hs,hy]
    linarith only [hr.2]
  have hratio := positive_quotient_bounds
    (show (399/401:ℝ)*(937/1000) ≤ (399/401)*(937/1000) ∧
      (399/401)*(937/1000) ≤ (399/401)*(937/1000) from ⟨le_rfl,le_rfl⟩) hr (by norm_num) (by norm_num)
  have hA : 0.634 ≤ A := by
    dsimp only [A,h₁deriv]; rw [hc,hs,hy]
    simp only [mul_neg,neg_div] at *
    linarith only [hratio.1]
  have hH : 0 ≤ H ∧ H ≤ 1.444 := by
    dsimp only [H,h₂,y₄]; rw [hc,hs]
    constructor <;> linarith only [hY.1,hY.2,hw.1,hw.2]
  have hV : 1.3309 ≤ -d.x₃ ∧ -d.x₃ ≤ 1.3311 := by
    dsimp only [x₃]; constructor <;> linarith only [hU.1,hU.2]
  have ht : 1.063 ≤ d.y+2 ∧ d.y+2 ≤ 1.063 := by rw [hy]; norm_num
  have hp₀ := positive_quotient_bounds
    (positive_product_bounds hV ht (by norm_num) (by norm_num))
    (positive_product_bounds hY hU (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hp : 0 ≤ p ∧ p ≤ 0.58 := by
    dsimp only [p]; constructor <;> linarith only [hp₀.1,hp₀.2]
  have hv : 0.5356 ≤ -d.y₄ ∧ -d.y₄ ≤ 0.536 := by
    dsimp only [y₄]; constructor <;> linarith only [hY.1,hY.2]
  have hvw := positive_quotient_bounds hv hw (by norm_num) (by norm_num)
  rw [neg_div_neg_eq] at hvw
  have hL : 0 ≤ L ∧ L ≤ 1.024 := by
    dsimp only [L]; rw [hc,hs,mul_div_assoc]
    constructor <;> linarith only [hvw.1,hvw.2]
  have hleft := mul_le_mul hK hA (by norm_num : (0:ℝ) ≤ 0.634) (by linarith only [hK] : 0 ≤ K)
  have hright := (positive_product_bounds (positive_product_bounds hH hp (by norm_num) (by norm_num)) hL (by norm_num) (by norm_num)).2
  have heq : d.positionDerivative = 2*(H*p*L-K*A) := by
    dsimp only [positionDerivative,h₂deriv,y₄deriv,H,p,L,K,A]
    ring
  rw [heq]
  linarith only [hleft,hright]

/-- At the upper-right corner, the second circle projection dominates the first. -/
theorem upper_corner_position {d : Coordinates} (hd : d.IsChain)
    (hq : 3.9155 ≤ d.q ∧ d.q ≤ 3.9156)
    (hy : d.y = -179/200) (hz : d.z = 81/1000) : 0 < d.positionDerivative := by
  obtain ⟨hr,hU,hY,hw⟩ := right_circle_bounds hd hq hy
  have hc : d.c = 993439/1006561 := by norm_num [c,hz,halfAngleCos]
  have hs : d.s = 162000/1006561 := by norm_num [s,hz,halfAngleSin]
  let K := -d.h₁; let A := d.h₁deriv; let H := -d.h₂
  let p := (-d.x₃)*(d.y+2)/(d.y₃*d.x₂)
  let L := d.c+d.s*d.y₄/d.x₄
  have hK : 0 ≤ K ∧ K ≤ 1.39 := by
    dsimp only [K,h₁]; rw [hc,hs,hy]
    constructor <;> linarith only [hr.1,hr.2]
  have hratio := positive_quotient_bounds
    (show (993439/1006561:ℝ)*(179/200) ≤ (993439/1006561)*(179/200) ∧
      (993439/1006561)*(179/200) ≤ (993439/1006561)*(179/200) from ⟨le_rfl,le_rfl⟩) hr (by norm_num) (by norm_num)
  have hA : 0 ≤ A ∧ A ≤ 0.662 := by
    dsimp only [A,h₁deriv]; rw [hc,hs,hy]
    simp only [mul_neg,neg_div] at *
    constructor <;> linarith only [hratio.1,hratio.2]
  have hH : 1.408 ≤ H := by
    dsimp only [H,h₂,y₄]; rw [hc,hs]
    linarith only [hY.1,hY.2,hw.1,hw.2]
  have hV : 1.3584 ≤ -d.x₃ ∧ -d.x₃ ≤ 1.3586 := by
    dsimp only [x₃]; constructor <;> linarith only [hU.1,hU.2]
  have ht : 1.105 ≤ d.y+2 ∧ d.y+2 ≤ 1.105 := by rw [hy]; norm_num
  have hp₀ := positive_quotient_bounds
    (positive_product_bounds hV ht (by norm_num) (by norm_num))
    (positive_product_bounds hY hU (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  have hp : 0.635 ≤ p := by
    dsimp only [p]; linarith only [hp₀.1]
  have hv : 0.5611 ≤ -d.y₄ ∧ -d.y₄ ≤ 0.5614 := by
    dsimp only [y₄]; constructor <;> linarith only [hY.1,hY.2]
  have hvw := positive_quotient_bounds hv hw (by norm_num) (by norm_num)
  rw [neg_div_neg_eq] at hvw
  have hL : 1.034 ≤ L := by
    dsimp only [L]; rw [hc,hs,mul_div_assoc]
    linarith only [hvw.1]
  have hleft := (positive_product_bounds hK hA (by norm_num) (by norm_num)).2
  have hHp := mul_le_mul hH hp (by norm_num : (0:ℝ) ≤ 0.635) (by linarith only [hH] : 0 ≤ H)
  have hright := mul_le_mul hHp hL (by norm_num : (0:ℝ) ≤ 1.034)
    (by positivity : 0 ≤ H*p)
  have heq : d.positionDerivative = 2*(H*p*L-K*A) := by
    dsimp only [positionDerivative,h₂deriv,y₄deriv,H,p,L,K,A]
    ring
  rw [heq]
  linarith only [hleft,hright]

end Coordinates

end SquaresInCircles.Eight.ExactFamily
