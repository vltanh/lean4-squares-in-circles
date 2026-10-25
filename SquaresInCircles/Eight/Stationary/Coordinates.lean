module

public import Mathlib.Tactic
public import SquaresInCircles.Common.Basic

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
namespace SquaresInCircles.Eight.Stationary

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

namespace Coordinates

def c (d : Coordinates) : ℝ := halfAngleCos d.z
def s (d : Coordinates) : ℝ := halfAngleSin d.z
def x₃ (d : Coordinates) : ℝ := d.x₂ - 3
def y₄ (d : Coordinates) : ℝ := d.y₃ - 2
def h₁ (d : Coordinates) : ℝ := d.c * d.x₁ + d.s * d.y - 2 - d.c
def h₂ (d : Coordinates) : ℝ := -d.s * d.x₄ + d.c * d.y₄ - 1 - d.s
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

end SquaresInCircles.Eight.Stationary
