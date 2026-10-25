module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import SquaresInCircles.Common.Basic
public import SquaresInCircles.Eight.Arithmetic.ClosedCover
public import SquaresInCircles.Eight.Boundary.Reduction

/-!
# Eight squares: fixed-point interval evaluation of formulas

An interval `DI` is a pair of integers `lo, hi`, read as `[lo / 2 ^ p, hi / 2 ^ p]`, and every
operation rounds outwards to that scale. One pass of `eval` over a `Formula` of `Expression.lean`
encloses its value at every point of a box of such intervals (`eval_sound`). Square roots and
reciprocals are accepted only for arguments with a positive lower end, so a successful pass also
shows that the formula is regular on the box (`Formula.RegularAt`). Every intermediate number is
an integer at the fixed scale `2 ^ p`, so no denominators accumulate along the formula.

On a rational box the Boolean tests `bounded` and `regular` run one pass; their success gives the
bounds, and the regularity, at every real point of the box (`bounded_sound`, `regular_sound`).
`inside` tests that one box lies in another. The generated module
`Generated/LocalStationaryBounds.lean` decides these tests with `decide +kernel`; its generator
runs the same integer arithmetic (`fx_eval` in `scripts/eight/generate_stationary.py`) before it
writes a bound.
-/

section
/-!
## The five-corner chain and the parameters of the family

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
end
end
end

section
/-!
## The contact and circle weights of the chain

From the coordinates of a chain, the module defines five circle weights `mu`, one for each corner
on the circle, normalized to add up to `1` (`WeightDomain.mu_sum`), and seven contact weights `lam`,
one for each contact of the cycle. They are positive on the sign domain `WeightDomain`, which holds
at every point of the stationary system (`IsStationary.weightDomain`). With these weights the
forces on the squares balance: at each of `A`, `B`, `D`, `E` and `H` the contact forces cancel the
corner force `2 μ P` (`force_balance`), and on `T` and `G` they cancel each other
(`slider_forces_zero`). The vertical balance at `E` is not an assumption on the weights; it follows
from the position equation `positionDerivative = 0` (`last_force_residual`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.Stationary
namespace Coordinates

def rawMuA (d : Coordinates) : ℝ := d.c / (2*d.x₁)
def rawAlpha (d : Coordinates) : ℝ := d.s-d.c*d.y/d.x₁
def rawMuB (d : Coordinates) : ℝ := d.rawAlpha/(2*(d.y+2))
def rawBeta (d : Coordinates) : ℝ := d.rawAlpha*d.x₂/(d.y+2)
def rawMuD (d : Coordinates) : ℝ := -d.rawBeta/(2*d.x₃)
def rawDelta (d : Coordinates) : ℝ := 2*d.rawMuD*d.y₃
def rawMuH (d : Coordinates) : ℝ := -1/(2*d.h₁)
def rawEpsilon (d : Coordinates) : ℝ := d.h₂/d.h₁
def rawMuE (d : Coordinates) : ℝ := -d.s*d.rawEpsilon/(2*d.x₄)

def rawMu (d : Coordinates) : Fin 5 → ℝ :=
  ![d.rawMuA,d.rawMuB,d.rawMuD,d.rawMuE,d.rawMuH]
def weightMass (d : Coordinates) : ℝ := ∑ i : Fin 5, d.rawMu i
def mu (d : Coordinates) (i : Fin 5) : ℝ := d.rawMu i/d.weightMass

/-- Contact order AB, TB, DT, ED, GA, HG, HE. -/
def rawLambda (d : Coordinates) : Fin 7 → ℝ :=
  ![d.rawAlpha,d.rawBeta,d.rawBeta,d.rawDelta,1,1,d.rawEpsilon]
def lam (d : Coordinates) (i : Fin 7) : ℝ := d.rawLambda i/d.weightMass

/-- The sign conditions under which the weights are positive. The adaptive comparison uses them
at every tilt; they assert neither stationarity nor optimality. -/
structure WeightDomain (d : Coordinates) : Prop where
  x₁_pos : 0 < d.x₁
  x₂_pos : 0 < d.x₂
  y₃_pos : 0 < d.y₃
  x₃_neg : d.x₃ < 0
  x₄_neg : d.x₄ < 0
  y_neg : d.y < 0
  y_add_two_pos : 0 < d.y+2
  c_pos : 0 < d.c
  s_pos : 0 < d.s
  h₁_neg : d.h₁ < 0
  h₂_neg : d.h₂ < 0

theorem IsStationary.weightDomain {d : Coordinates} (hd : d.IsStationary) :
    d.WeightDomain := by
  have hc : 0 < d.c := halfAngleCos_pos (abs_lt.mpr ⟨by linarith [hd.z_pos], hd.z_lt_one⟩)
  have hs : 0 < d.s := halfAngleSin_pos hd.z_pos
  have hc1 : d.c ≤ 1 := halfAngleCos_le_one d.z
  have hs1 : d.s ≤ 1 := by nlinarith [d.unit, sq_nonneg d.c]
  have hy0 : d.y < 0 := by linarith [hd.y_upper]
  have hy42 : d.y₄ < 0 := by linarith [hd.y₄_upper]
  have hy1 : d.y ^ 2 < 1 := by nlinarith [hd.y_lower, hd.y_upper]
  have hx11 : 1 < d.x₁ := by
    nlinarith [hd.q_lower, hd.first_circle, hd.x₁_pos]
  have hx12 : d.x₁ < 2 := by
    nlinarith [hd.q_upper, hd.first_circle, sq_nonneg d.y]
  have hx22 : d.x₂ < 2 := by
    nlinarith [hd.q_upper, hd.second_circle, sq_nonneg (d.y+2)]
  have hx42 : -2 < d.x₄ := by
    nlinarith [hd.q_upper, hd.fourth_circle, sq_nonneg d.y₄]
  have h₁ : d.h₁ < 0 := by
    have hcx : d.c*(d.x₁-1) < 1 := by
      have h := mul_le_mul_of_nonneg_right hc1 (by linarith : 0 ≤ d.x₁-1)
      nlinarith
    have hsy : d.s*d.y < 0 := mul_neg_of_pos_of_neg hs hy0
    dsimp [h₁]
    nlinarith
  have h₂ : d.h₂ < 0 := by
    have hsy : d.s*(-d.x₄-1) < d.s := by nlinarith
    have hcy : d.c*d.y₄ < 0 := mul_neg_of_pos_of_neg hc hy42
    dsimp [h₂]
    nlinarith
  exact ⟨hd.x₁_pos, hd.x₂_pos, hd.y₃_pos, by dsimp [x₃]; linarith,
    hd.x₄_neg, hy0, by linarith [hd.y_lower], hc, hs, h₁, h₂⟩

theorem WeightDomain.rawAlpha_pos {d : Coordinates} (h : d.WeightDomain) :
    0 < d.rawAlpha := by
  have hcy : d.c*d.y/d.x₁ < 0 := div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg h.c_pos h.y_neg) h.x₁_pos
  dsimp [rawAlpha]
  linarith [h.s_pos]

theorem WeightDomain.rawBeta_pos {d : Coordinates} (h : d.WeightDomain) :
    0 < d.rawBeta := div_pos (mul_pos h.rawAlpha_pos h.x₂_pos) h.y_add_two_pos

theorem WeightDomain.rawMu_pos {d : Coordinates} (h : d.WeightDomain) (i : Fin 5) :
    0 < d.rawMu i := by
  have hA : 0 < d.rawMuA := div_pos h.c_pos (by linarith [h.x₁_pos])
  have hB : 0 < d.rawMuB := div_pos h.rawAlpha_pos (by linarith [h.y_add_two_pos])
  have hD : 0 < d.rawMuD := div_pos_of_neg_of_neg (by linarith [h.rawBeta_pos])
    (by linarith [h.x₃_neg])
  have hH : 0 < d.rawMuH := div_pos_of_neg_of_neg (by norm_num)
    (by linarith [h.h₁_neg])
  have hε : 0 < d.rawEpsilon := div_pos_of_neg_of_neg h.h₂_neg h.h₁_neg
  have hE : 0 < d.rawMuE := div_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (by linarith [h.s_pos]) hε) (by linarith [h.x₄_neg])
  fin_cases i <;> simp only [rawMu] <;> assumption

theorem WeightDomain.weightMass_pos {d : Coordinates} (h : d.WeightDomain) :
    0 < d.weightMass := by
  exact Finset.sum_pos (fun i _ => h.rawMu_pos i) Finset.univ_nonempty

theorem WeightDomain.mu_pos {d : Coordinates} (h : d.WeightDomain) (i : Fin 5) :
    0 < d.mu i := div_pos (h.rawMu_pos i) h.weightMass_pos

theorem WeightDomain.mu_sum {d : Coordinates} (h : d.WeightDomain) :
    ∑ i : Fin 5, d.mu i = 1 := by
  simp only [mu]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt h.weightMass_pos)

theorem WeightDomain.rawLambda_pos {d : Coordinates} (h : d.WeightDomain) (i : Fin 7) :
    0 < d.rawLambda i := by
  have hα : 0 < d.rawAlpha := h.rawAlpha_pos
  have hβ : 0 < d.rawBeta := h.rawBeta_pos
  have hδ : 0 < d.rawDelta := mul_pos
    (mul_pos (by norm_num) (h.rawMu_pos 2)) h.y₃_pos
  have hε : 0 < d.rawEpsilon := div_pos_of_neg_of_neg h.h₂_neg h.h₁_neg
  fin_cases i <;> simp only [rawLambda, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> first | assumption | norm_num

theorem WeightDomain.lam_pos {d : Coordinates} (h : d.WeightDomain) (i : Fin 7) :
    0 < d.lam i := div_pos (h.rawLambda_pos i) h.weightMass_pos

/-- The scalar identity behind the E vertical balance. -/
theorem last_force_residual {d : Coordinates} (h : d.WeightDomain) :
    2*d.rawMuE*d.y₄+d.rawDelta-d.c*d.rawEpsilon =
      -d.positionDerivative/(2*d.h₁*d.y₄deriv) := by
  have hx₁ := ne_of_gt h.x₁_pos
  have hx₂ := ne_of_gt h.x₂_pos
  have hy₃ := ne_of_gt h.y₃_pos
  have hx₃ := ne_of_lt h.x₃_neg
  have hx₄ := ne_of_lt h.x₄_neg
  have hy := ne_of_gt h.y_add_two_pos
  have hh₁ := ne_of_lt h.h₁_neg
  dsimp [rawMuE, rawEpsilon, rawDelta, rawMuD, rawBeta, rawAlpha,
    positionDerivative, h₁deriv, h₂deriv, y₄deriv]
  field_simp [hx₁,hx₂,hy₃,hx₃,hx₄,hy,hh₁]
  ring

/-- The unnormalized centre forces, in the order `A, B, D, E, H, T, G`. -/
def rawForces (d : Coordinates) : Fin 7 → Point :=
  ![(-d.c, d.rawAlpha-d.s),
    (-d.rawBeta,-d.rawAlpha),
    (d.rawBeta,-d.rawDelta),
    (d.rawEpsilon*d.s,d.rawDelta-d.rawEpsilon*d.c),
    (d.c-d.rawEpsilon*d.s,d.s+d.rawEpsilon*d.c),
    (0,0),(0,0)]

theorem raw_force_balance {d : Coordinates} (h : d.WeightDomain)
    (hstation : d.positionDerivative = 0) (i : Fin 5) :
    add (scale (2*d.rawMu i) (d.anchorPoints i)) (d.rawForces i.castSucc.castSucc) = (0,0) := by
  have hx₁ := ne_of_gt h.x₁_pos
  have hx₃ := ne_of_lt h.x₃_neg
  have hx₄ := ne_of_lt h.x₄_neg
  have hy := ne_of_gt h.y_add_two_pos
  have hh₁ := ne_of_lt h.h₁_neg
  have hE : 2*d.rawMuE*d.y₄+d.rawDelta-d.c*d.rawEpsilon = 0 := by
    rw [last_force_residual h, hstation]
    simp
  fin_cases i
  all_goals
    ext <;> simp only [rawMu, rawForces, anchorPoints, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.reduceCastSucc, Matrix.cons_val, add, scale]
  all_goals
    first
    | linear_combination hE
    | dsimp [rawMuA,rawMuB,rawMuD,rawMuE,rawMuH,rawAlpha,rawBeta,
        rawDelta,rawEpsilon,inFrame]
      field_simp [hx₁,hx₃,hx₄,hy,hh₁]
      ring

def forces (d : Coordinates) (i : Fin 7) : Point :=
  scale (1/d.weightMass) (d.rawForces i)

theorem force_balance {d : Coordinates} (h : d.WeightDomain)
    (hstation : d.positionDerivative = 0) (i : Fin 5) :
    d.forces i.castSucc.castSucc =
      scale (-2*d.mu i) (d.anchorPoints i) := by
  have hf := raw_force_balance h hstation i
  have hx := congrArg Prod.fst hf
  have hy := congrArg Prod.snd hf
  ext <;> dsimp [forces,mu,add,scale] at hx hy ⊢
  · linear_combination (1/d.weightMass)*hx
  · linear_combination (1/d.weightMass)*hy

theorem slider_forces_zero (d : Coordinates) :
    d.forces 5 = (0,0) ∧ d.forces 6 = (0,0) := by
  simp [forces,rawForces,scale]

end Coordinates
end SquaresInCircles.Eight.Stationary
end
end
end

section
/-!
## Completing the square at the centres, and the stationary identity

The identity `center_square_difference` completes the square: the difference of
`μ |p + o|²` and `μ |r + o|²`, corrected by the first-order term at `r`, is `μ |p - r|²`.

The stationary identity (`OriginalDual`) applies the weights of a stationary chain to seven centres
with zero frame errors: the weighted sum of the five corner constraints less the weighted gaps
along the normals of the model equals `q` plus the weighted squared distances of the five anchored
centres from those of the model (`OriginalDual.exact_identity`). All these identities hold for
arbitrary centres; nothing assumes that a centre is near a moved one or inside a slider range. So
if the five anchored corners lie in the disk of squared radius `q` and the gaps are nonnegative,
the five anchors are those of the model and every gap vanishes
(`OriginalDual.original_centers_rigid`), and the two sliders lie on their lines
(`OriginalDual.slider_coordinates`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight
open Stationary

theorem center_square_difference (μ : ℝ) (p r o : Point) :
    μ*normSq (add p o)-μ*normSq (add r o)+
      dot (scale (-2*μ) (add r o)) (sub p r) =
      μ*normSq (sub p r) := by
  dsimp [normSq,add,dot,scale,sub]
  ring

theorem zero_normSq_iff (p : Point) : normSq p = 0 ↔ p = (0,0) := by
  constructor
  · intro hp
    have hx := sq_nonneg p.1
    have hy := sq_nonneg p.2
    ext <;> dsimp [normSq] at hp <;> nlinarith
  · rintro rfl
    norm_num [normSq]

namespace OriginalDual
open Stationary.Coordinates

/-- Centres indexed by `A, B, D, E, H, T, G`. The permutation `cycleIndex` passes from the
order `H, G, A, B, T, D, E` of the cycle. -/
abbrev Positions := Fin 7 → Point

def cycleIndex : Fin 7 → Fin 7 := ![2,3,5,6,0,4,1]
def ofCycle (p : Fin 7 → Point) : Positions := fun i => p (cycleIndex i)

def reference (d : Coordinates) (Z η : ℝ) : Positions :=
  ![d.pA,d.pB,d.pD,d.pE,d.pH,d.pT Z,d.pG η]

def gap (d : Coordinates) (p : Positions) : Fin 7 → ℝ :=
  ![(p 1).2-(p 0).2-1,
    (p 1).1-(p 5).1-1,
    (p 5).1-(p 2).1-1,
    (p 2).2-(p 3).2-1,
    dot d.e (sub (p 0) (p 6))-(1+d.c+d.s)/2,
    dot d.e (sub (p 6) (p 4))-1,
    dot d.f (sub (p 3) (p 4))-(1+d.c+d.s)/2]

def value (d : Coordinates) (p : Positions) : ℝ :=
  (∑ i : Fin 5, d.mu i*normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i)))-
  ∑ e : Fin 7, d.lam e*gap d p e

theorem reference_gap (d : Coordinates) (Z η : ℝ) (e : Fin 7) :
    gap d (reference d Z η) e = 0 := by
  have hstandard := d.standard_contacts Z
  fin_cases e
  · simpa [gap,reference] using sub_eq_zero.mpr hstandard.1
  · simpa [gap,reference] using sub_eq_zero.mpr hstandard.2.1
  · simpa [gap,reference] using sub_eq_zero.mpr hstandard.2.2.1
  · simpa [gap,reference] using sub_eq_zero.mpr hstandard.2.2.2
  · simpa [gap,reference] using sub_eq_zero.mpr (d.GA_contact η)
  · simpa [gap,reference] using sub_eq_zero.mpr (d.HG_contact η)
  · simpa [gap,reference] using sub_eq_zero.mpr d.HE_contact

theorem weighted_gap_difference (d : Coordinates) (p r : Positions) :
    -(∑ e : Fin 7, d.lam e*gap d p e)+
       (∑ e : Fin 7, d.lam e*gap d r e) =
      ∑ i : Fin 7, dot (d.forces i) (sub (p i) (r i)) := by
  simp [Fin.sum_univ_succ,gap,lam,rawLambda,forces,rawForces,
    dot,sub,scale,Coordinates.e,Coordinates.f]
  ring

theorem reference_value {d : Coordinates} (hd : d.IsChain)
    (hw : d.WeightDomain) (hz : d.defect = 0) (Z η : ℝ) :
    value d (reference d Z η) = d.q := by
  have href (i : Fin 5) : reference d Z η i.castSucc.castSucc = d.anchorCenters i := by
    fin_cases i <;> rfl
  simp only [value,reference_gap,mul_zero,Finset.sum_const_zero,sub_zero,href,d.anchor_vertex]
  simp only [d.anchor_circle hd hz]
  rw [← Finset.sum_mul,hw.mu_sum,one_mul]

theorem exact_identity {d : Coordinates} (hd : d.IsChain) (hw : d.WeightDomain)
    (hz : d.defect = 0) (hstation : d.positionDerivative = 0)
    (p : Positions) :
    value d p = d.q+
      ∑ i : Fin 5, d.mu i*normSq (sub (p i.castSucc.castSucc) (d.anchorCenters i)) := by
  let r := reference d 0 0
  have href (i : Fin 5) : r i.castSucc.castSucc = d.anchorCenters i := by
    fin_cases i <;> rfl
  have hforce (i : Fin 5) : d.forces i.castSucc.castSucc =
      scale (-2*d.mu i) (add (r i.castSucc.castSucc) (d.anchorOffsets i)) := by
    rw [href,d.anchor_vertex]
    exact d.force_balance hw hstation i
  have hsum (i : Fin 5) := center_square_difference (d.mu i)
    (p i.castSucc.castSucc) (r i.castSucc.castSucc) (d.anchorOffsets i)
  have hsum' := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => hsum i)
  have hgap := weighted_gap_difference d p r
  have hzero := d.slider_forces_zero
  have hrefl : value d r = d.q := reference_value hd hw hz 0 0
  have hforces : (∑ i : Fin 7, dot (d.forces i) (sub (p i) (r i))) =
      ∑ i : Fin 5, dot (d.forces i.castSucc.castSucc)
        (sub (p i.castSucc.castSucc) (r i.castSucc.castSucc)) := by
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    have h5 : d.forces (Fin.last 5).castSucc = (0,0) := hzero.1
    have h6 : d.forces (Fin.last 6) = (0,0) := hzero.2
    rw [h5,h6]
    simp [dot]
  rw [hforces] at hgap
  simp only [hforce] at hgap
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hsum'
  dsimp only [value] at hrefl ⊢
  simp only [href] at hsum' hgap hrefl
  linarith

theorem value_le {d : Coordinates} (hw : d.WeightDomain) {p : Positions} {q : ℝ}
    (hc : ∀ i : Fin 5, normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i)) ≤ q)
    (hg : ∀ e : Fin 7, 0 ≤ gap d p e) : value d p ≤ q := by
  have hvertices := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
    mul_le_mul_of_nonneg_left (hc i) (hw.mu_pos i).le)
  have hgaps : 0 ≤ ∑ e : Fin 7, d.lam e*gap d p e :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hw.lam_pos e).le (hg e))
  rw [← Finset.sum_mul,hw.mu_sum,one_mul] at hvertices
  dsimp [value]
  linarith

/-- The original centres are rigid: if the five anchored corners lie in the disk of squared
radius `q` and the seven gaps are nonnegative, the anchors are the centres of the model and the
gaps vanish. Nothing is assumed about displacements or about the positions of the sliders. -/
theorem original_centers_rigid {d : Coordinates} (hd : d.IsChain)
    (hw : d.WeightDomain) (hz : d.defect = 0) (hstation : d.positionDerivative = 0)
    {p : Positions}
    (hc : ∀ i : Fin 5, normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i)) ≤ d.q)
    (hg : ∀ e : Fin 7, 0 ≤ gap d p e) :
    (∀ i : Fin 5, p i.castSucc.castSucc = d.anchorCenters i) ∧
    (∀ e : Fin 7, gap d p e = 0) := by
  have hdual := value_le hw hc hg
  have hid := exact_identity hd hw hz hstation p
  have hsnonneg : 0 ≤ ∑ i : Fin 5,
      d.mu i*normSq (sub (p i.castSucc.castSucc) (d.anchorCenters i)) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw.mu_pos i).le (normSq_nonneg _))
  have hs : (∑ i : Fin 5,
      d.mu i*normSq (sub (p i.castSucc.castSucc) (d.anchorCenters i))) = 0 := by linarith
  have hcenters (i : Fin 5) : p i.castSucc.castSucc = d.anchorCenters i := by
    have hone := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
        mul_nonneg (hw.mu_pos j).le (normSq_nonneg
          (sub (p j.castSucc.castSucc) (d.anchorCenters j)))) (Finset.mem_univ i)
    rw [hs] at hone
    have hnorm : normSq (sub (p i.castSucc.castSucc) (d.anchorCenters i)) = 0 := by
      nlinarith [hw.mu_pos i,normSq_nonneg (sub (p i.castSucc.castSucc) (d.anchorCenters i))]
    have hpoint := (zero_normSq_iff _).mp hnorm
    ext <;> have hh := congrArg Prod.fst hpoint <;>
      have hh' := congrArg Prod.snd hpoint <;> dsimp [sub] at hh hh' <;> linarith
  have hvalue : value d p = d.q := by rw [hid,hs,add_zero]
  have hgapSum : (∑ e : Fin 7, d.lam e*gap d p e) = 0 := by
    have hvert : (∑ i : Fin 5,
        d.mu i*normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i))) = d.q := by
      simp only [hcenters,d.anchor_vertex,d.anchor_circle hd hz]
      rw [← Finset.sum_mul,hw.mu_sum,one_mul]
    dsimp [value] at hvalue
    linarith
  refine ⟨hcenters,fun e => ?_⟩
  have hone := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 7))) =>
      mul_nonneg (hw.lam_pos j).le (hg j)) (Finset.mem_univ e)
  rw [hgapSum] at hone
  nlinarith [hw.lam_pos e,hg e]

theorem frame_reconstruction (d : Coordinates) (p : Point) :
    d.inFrame (dot d.e p) (dot d.f p) = p := by
  ext <;> dsimp [Coordinates.inFrame,Coordinates.e,Coordinates.f,dot]
  · linear_combination p.1*d.unit
  · linear_combination p.2*d.unit

theorem slider_coordinates {d : Coordinates} {p : Positions}
    (hB : p 1 = d.pB) (hH : p 4 = d.pH)
    (hTB : gap d p 1 = 0) (hHG : gap d p 5 = 0) :
    ∃ Z η : ℝ, p 5 = d.pT Z ∧ p 6 = d.pG η := by
  refine ⟨(p 5).2,dot d.f (p 6)-d.h₂-1/2,?_,?_⟩
  · have h := hTB
    simp only [gap,Matrix.cons_val_zero,Matrix.cons_val_one,hB,
      Coordinates.pB] at h
    ext <;> dsimp [Coordinates.pT]
    linarith
  · have h := hHG
    simp only [gap,hH,dot_sub_right,Coordinates.pH,d.dot_e_inFrame] at h
    have hx : dot d.e (p 6) = d.h₁+3/2 := by
      simp at h
      linarith
    conv_lhs => rw [← frame_reconstruction d (p 6)]
    rw [hx,Coordinates.pG]
    congr 1
    ring

end OriginalDual
end SquaresInCircles.Eight
end
end
end

section
/-!
## The parameters of the central square

Every unit square is, as a set of points, the central square of parameters with the same centre
and with the frame parameter `w` in the half-open interval `[1 - √2, √2 - 1)`
(`central_parameters_exist`). One of the four quarter turns of its frame makes an angle in
`[-π/4, π/4)` with the horizontal (`halfopen_quarter_exists`), and for that frame `(c, s)` the
parameter is recovered algebraically as `w = s/(1 + c)` (`halfAngle_recover`,
`halfAngle_halfopen`). The lower end of the interval is included and the upper end excluded, as in
the admissible domain, so a frame along a diagonal gets only one parameter.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Stationary
open Coordinates EqualityParameters

theorem halfopen_quarter_exists (K : UnitSquare) :
    ∃ k : Fin 4, 0<(turnSquare k K).cosine ∧
      -(turnSquare k K).cosine≤(turnSquare k K).sine ∧
      (turnSquare k K).sine<(turnSquare k K).cosine := by
  by_cases hc : 0<K.cosine
  · by_cases hs : K.sine < -K.cosine
    · refine ⟨1,?_⟩
      norm_num [turnSquare]
      exact ⟨by linarith,by linarith,by linarith⟩
    · have hsl : -K.cosine≤K.sine := le_of_not_gt hs
      by_cases hsu : K.sine<K.cosine
      · exact ⟨0,by simpa [turnSquare] using And.intro hc ⟨hsl,hsu⟩⟩
      · refine ⟨3,?_⟩
        have hh : K.cosine≤K.sine := le_of_not_gt hsu
        norm_num [turnSquare]
        exact ⟨by linarith,by linarith,by linarith⟩
  · have hc' : K.cosine≤0 := le_of_not_gt hc
    by_cases hs : 0<K.sine
    · by_cases hu : -K.cosine<K.sine
      · refine ⟨3,?_⟩
        norm_num [turnSquare]
        exact ⟨hs,by linarith,hu⟩
      · refine ⟨2,?_⟩
        have hh : K.sine≤ -K.cosine := le_of_not_gt hu
        norm_num [turnSquare]
        exact ⟨by linarith,by linarith,by linarith⟩
    · have hs' : K.sine≤0 := le_of_not_gt hs
      by_cases hcs : K.cosine<K.sine
      · refine ⟨2,?_⟩
        norm_num [turnSquare]
        exact ⟨by linarith,by linarith,by linarith⟩
      · have hsc : K.sine≤K.cosine := le_of_not_gt hcs
        have hsneg : K.sine<0 := by
          by_contra! hn
          have hsz : K.sine=0 := by linarith
          have hcz : K.cosine=0 := by linarith
          nlinarith [K.unit]
        refine ⟨1,?_⟩
        norm_num [turnSquare]
        exact ⟨by linarith,hsc,by linarith⟩

theorem halfAngle_recover {c s : ℝ} (hu : c^2+s^2=1) (hc : 0<c) :
    halfAngleCos (s/(1+c))=c ∧ halfAngleSin (s/(1+c))=s := by
  have hd : 0<1+c := by linarith
  have hD : 1+(s/(1+c))^2=2/(1+c) := by
    field_simp [ne_of_gt hd]
    nlinarith
  have hN : 1-(s/(1+c))^2=2*c/(1+c) := by
    field_simp [ne_of_gt hd]
    nlinarith
  constructor
  · rw [halfAngleCos,hD,hN]
    field_simp [ne_of_gt hd]
  · rw [halfAngleSin,hD]
    field_simp [ne_of_gt hd]

theorem halfAngle_halfopen {c s : ℝ} (hu : c^2+s^2=1)
    (hc : 0<c) (hlo : -c≤ s) (hhi : s<c) :
    1-Real.sqrt 2≤ s/(1+c) ∧ s/(1+c)<Real.sqrt 2-1 := by
  let w := s/(1+c)
  have hw := halfAngle_recover hu hc
  have hD := halfAngle_den_pos w
  have hDc : (1+w^2)*c=1-w^2 := by
    rw [← hw.1]
    dsimp [halfAngleCos,w]
    field_simp [ne_of_gt (halfAngle_den_pos (s/(1+c)))]
  have hDs : (1+w^2)*s=2*w := by
    rw [← hw.2]
    dsimp [halfAngleSin,w]
    field_simp [ne_of_gt (halfAngle_den_pos (s/(1+c)))]
  have hl := mul_le_mul_of_nonneg_left hlo hD.le
  have hh := mul_lt_mul_of_pos_left hhi hD
  have hlpoly : (w-1)^2≤2 := by nlinarith
  have hhpoly : (w+1)^2<2 := by nlinarith
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  constructor
  · change 1-Real.sqrt 2≤w
    by_contra! h
    have hp := mul_pos (by linarith : 0<1-w-Real.sqrt 2)
      (by linarith : 0<1-w+Real.sqrt 2)
    nlinarith
  · change w<Real.sqrt 2-1
    by_contra! h
    have hp := mul_nonneg (by linarith : 0≤w+1-Real.sqrt 2)
      (by linarith : 0≤w+1+Real.sqrt 2)
    nlinarith

private theorem centralParameters_unitSquare_eq {K L : UnitSquare} (h1 : K.center=L.center)
    (h2 : K.cosine=L.cosine) (h3 : K.sine=L.sine) : K=L := by
  cases K; cases L
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem central_parameters_exist (K : UnitSquare) (Z η : ℝ) :
    ∃ p : EqualityParameters, SameSquare p.centralSquare K ∧
      p.centralSquare.center=K.center ∧
      (1-Real.sqrt 2≤p.w ∧ p.w<Real.sqrt 2-1) ∧ p.z=Z ∧ p.eta=η := by
  obtain ⟨k,hc,hl,hu⟩ := halfopen_quarter_exists K
  let L := turnSquare k K
  let p : EqualityParameters :=
    ⟨K.center.1,K.center.2,L.sine/(1+L.cosine),Z,η⟩
  have hw := halfAngle_recover L.unit hc
  have hframe := halfAngle_halfopen L.unit hc hl hu
  have hL : p.centralSquare=L := by
    refine centralParameters_unitSquare_eq ?_ ?_ ?_
    · rfl
    · show halfAngleCos (L.sine/(1+L.cosine))=L.cosine
      exact hw.1
    · show halfAngleSin (L.sine/(1+L.cosine))=L.sine
      exact hw.2
  refine ⟨p,?_,?_,hframe,rfl,rfl⟩
  · rw [hL]
    exact turnSquare_sameSquare k K
  · rfl

end SquaresInCircles.Eight.Stationary
end
end
end

section
/-!
## Formulas and their derivatives

A `Formula` is a real expression in `n` variables built from rational constants, sums,
negation, products, inverses, square roots and powers. `Formula.diff` is its symbolic partial
derivative, assembled with `plus`, `minus`, `times`, `power`, `reciprocal` and `quotient`, which
simplify rational constants. Where every radicand is positive and every inverted value nonzero
(`Formula.RegularAt`), the value of a formula along a differentiable curve has the derivative
`Formula.directional` (`Formula.hasDerivAt_curve`), the sum of the symbolic partial derivatives
against the velocity (`Formula.directional_eq_partials`); in particular `Formula.diff` gives the
partial derivatives (`Formula.hasDerivAt_partial`). `FixedEval.lean` bounds formulas on boxes.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.Stationary
open Arithmetic

inductive Formula (n : ℕ)
  | const (q : ℚ)
  | var (i : Fin n)
  | add (a b : Formula n)
  | neg (a : Formula n)
  | mul (a b : Formula n)
  | inv (a : Formula n)
  | sqrt (a : Formula n)
  | pow (a : Formula n) (k : ℕ)
  deriving DecidableEq

namespace Formula

def eval {n : ℕ} (env : Fin n → ℝ) : Formula n → ℝ
  | .const q => q
  | .var i => env i
  | .add a b => eval env a+eval env b
  | .neg a => -eval env a
  | .mul a b => eval env a*eval env b
  | .inv a => (eval env a)⁻¹
  | .sqrt a => Real.sqrt (eval env a)
  | .pow a k => (eval env a)^k

def plus {n : ℕ} (a b : Formula n) : Formula n :=
  if a = .const 0 then b else if b = .const 0 then a else
    match a,b with
    | .const p,.const q => .const (p+q)
    | a,b => .add a b

def minus {n : ℕ} (a : Formula n) : Formula n :=
  match a with
  | .const q => .const (-q)
  | .neg a => a
  | a => .neg a

def times {n : ℕ} (a b : Formula n) : Formula n :=
  if a = .const 0 ∨ b = .const 0 then .const 0 else
    if a = .const 1 then b else if b = .const 1 then a else
      match a,b with
      | .const p,.const q => .const (p*q)
      | a,b => .mul a b

def power {n : ℕ} (a : Formula n) (k : ℕ) : Formula n :=
  if k=0 then .const 1 else if k=1 then a else .pow a k

def reciprocal {n : ℕ} (a : Formula n) : Formula n :=
  match a with
  | .const q => .const q⁻¹
  | a => .inv a

def quotient {n : ℕ} (a b : Formula n) : Formula n := times a (reciprocal b)

@[simp] theorem eval_plus {n : ℕ} (env : Fin n → ℝ) (a b : Formula n) :
    (plus a b).eval env = a.eval env+b.eval env := by
  unfold plus
  split_ifs with ha hb
  · subst ha; simp [eval]
  · subst hb; simp [eval]
  · split <;> simp [eval]

@[simp] theorem eval_minus {n : ℕ} (env : Fin n → ℝ) (a : Formula n) :
    (minus a).eval env = -a.eval env := by cases a <;> simp [minus,eval]

@[simp] theorem eval_times {n : ℕ} (env : Fin n → ℝ) (a b : Formula n) :
    (times a b).eval env = a.eval env*b.eval env := by
  unfold times
  split_ifs with h hA hB
  · rcases h with rfl | rfl <;> simp [eval]
  · subst a; simp [eval]
  · subst b; simp [eval]
  · cases a <;> cases b <;> simp [eval]

@[simp] theorem eval_power {n : ℕ} (env : Fin n → ℝ) (a : Formula n) (k : ℕ) :
    (power a k).eval env = (a.eval env)^k := by
  unfold power
  split_ifs <;> simp_all [eval]

@[simp] theorem eval_reciprocal {n : ℕ} (env : Fin n → ℝ) (a : Formula n) :
    (reciprocal a).eval env = (a.eval env)⁻¹ := by cases a <;> simp [reciprocal,eval]

@[simp] theorem eval_quotient {n : ℕ} (env : Fin n → ℝ) (a b : Formula n) :
    (quotient a b).eval env = a.eval env/b.eval env := by
  simp [quotient,div_eq_mul_inv]

/-- Symbolic partial derivative, with exact rational constant simplification. -/
def diff {n : ℕ} (i : Fin n) : Formula n → Formula n
  | .const _ => .const 0
  | .var j => .const (if i=j then 1 else 0)
  | .add a b => plus (diff i a) (diff i b)
  | .neg a => minus (diff i a)
  | .mul a b => plus (times (diff i a) b) (times a (diff i b))
  | .inv a => minus (quotient (diff i a) (.pow a 2))
  | .sqrt a => quotient (diff i a) (times (.const 2) (.sqrt a))
  | .pow a k => times (.const k) (times (power a (k-1)) (diff i a))

/-- Strict positive radicands and nonzero denominators justify derivatives. -/
def RegularAt {n : ℕ} (env : Fin n → ℝ) : Formula n → Prop
  | .const _ => True
  | .var _ => True
  | .add a b => RegularAt env a ∧ RegularAt env b
  | .neg a => RegularAt env a
  | .mul a b => RegularAt env a ∧ RegularAt env b
  | .inv a => RegularAt env a ∧ a.eval env ≠ 0
  | .sqrt a => RegularAt env a ∧ 0 < a.eval env
  | .pow a _ => RegularAt env a

def directional {n : ℕ} (env v : Fin n → ℝ) : Formula n → ℝ
  | .const _ => 0
  | .var i => v i
  | .add a b => directional env v a+directional env v b
  | .neg a => -directional env v a
  | .mul a b => directional env v a*b.eval env+a.eval env*directional env v b
  | .inv a => -directional env v a/(a.eval env)^2
  | .sqrt a => directional env v a/(2*Real.sqrt (a.eval env))
  | .pow a k => k*(a.eval env)^(k-1)*directional env v a

theorem directional_eq_partials {n : ℕ} (a : Formula n) (env v : Fin n → ℝ) :
    a.directional env v = ∑ i : Fin n, (a.diff i).eval env*v i := by
  induction a with
  | const q => simp [directional,diff,eval]
  | var j => simp [directional,diff,eval,apply_ite (fun x : ℚ => (x : ℝ)),ite_mul]
  | add a b ha hb => simp [directional,diff,ha,hb,Finset.sum_add_distrib,add_mul]
  | neg a ha => simp [directional,diff,ha,Finset.sum_neg_distrib]
  | mul a b ha hb =>
      simp only [directional,diff,eval_plus,eval_times,ha,hb,Finset.sum_mul,Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
  | inv a ha =>
      simp only [directional,diff,eval_minus,eval_quotient,eval,ha,neg_div,Finset.sum_div,
        ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
  | sqrt a ha =>
      simp only [directional,diff,eval_quotient,eval_times,eval,ha,Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)
  | pow a k ha =>
      simp only [directional,diff,eval_times,eval_power,eval,ha,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)

theorem hasDerivAt_curve {n : ℕ} (a : Formula n) {env : ℝ → Fin n → ℝ}
    {t : ℝ} {v : Fin n → ℝ} (hv : ∀ i, HasDerivAt (fun s => env s i) (v i) t)
    (h : a.RegularAt (env t)) :
    HasDerivAt (fun s => a.eval (env s)) (a.directional (env t) v) t := by
  induction a with
  | const q => simpa [eval,directional] using hasDerivAt_const t (q:ℝ)
  | var i => exact hv i
  | add a b ha hb => exact (ha h.1).fun_add (hb h.2)
  | neg a ha => exact (ha h).fun_neg
  | mul a b ha hb => exact (ha h.1).fun_mul (hb h.2)
  | inv a ha => exact (ha h.1).fun_inv h.2
  | sqrt a ha => exact (ha h.1).sqrt (ne_of_gt h.2)
  | pow a k ha => exact (ha h).fun_pow k

theorem hasDerivAt_partial {n : ℕ} (a : Formula n) (i : Fin n)
    (env : Fin n → ℝ) (h : a.RegularAt env) :
    HasDerivAt (fun t => a.eval (Function.update env i t)) ((a.diff i).eval env) (env i) := by
  induction a with
  | const q => simpa [eval,diff] using hasDerivAt_const (env i) (q:ℝ)
  | var j =>
      by_cases hij : i=j
      · subst hij
        simpa [eval,diff] using hasDerivAt_id' (env i)
      · simpa [eval,diff,hij,Function.update_of_ne (Ne.symm hij)] using
          hasDerivAt_const (env i) (env j)
  | add a b ha hb =>
      simpa [eval,diff] using (ha h.1).fun_add (hb h.2)
  | neg a ha => simpa [eval,diff] using (ha h).fun_neg
  | mul a b ha hb =>
      simpa [eval,diff] using (ha h.1).fun_mul (hb h.2)
  | inv a ha =>
      simpa [eval,diff,neg_div] using (ha h.1).fun_inv (by simpa using h.2)
  | sqrt a ha =>
      simpa [eval,diff] using (ha h.1).sqrt (by simpa using ne_of_gt h.2)
  | pow a k ha =>
      simpa [eval,diff,mul_assoc] using (ha h).fun_pow k

end Formula

end SquaresInCircles.Eight.Stationary
end
end
end

section
@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Stationary.FixedEval
open Arithmetic

/-- The scale `2 ^ p`, as an integer. -/
def scale (p : ℕ) : Int := ((2 ^ p : ℕ) : Int)

theorem scale_pos (p : ℕ) : 0 < scale p := by
  unfold scale
  exact_mod_cast Nat.pos_of_ne_zero (pow_ne_zero p (by norm_num))

theorem scale_real (p : ℕ) : ((scale p : Int) : ℝ) = 2 ^ p := by
  simp [scale]

theorem two_pow_pos (p : ℕ) : (0 : ℝ) < 2 ^ p := by positivity

/-- `⌊a / 2 ^ p⌋`. -/
def down (p : ℕ) (a : Int) : Int := a / scale p

/-- `⌈a / 2 ^ p⌉`. -/
def up (p : ℕ) (a : Int) : Int := -((-a) / scale p)

/-- `⌊a / d⌋ * d ≤ a` for a positive integer `d`, in the reals. -/
theorem ediv_mul_le_real (a : Int) {d : Int} (hd : 0 < d) : ((a / d : Int) : ℝ) * d ≤ a := by
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hd)

/-- `a ≤ ⌈a / d⌉ * d` for a positive integer `d`, in the reals. -/
theorem le_neg_ediv_mul_real (a : Int) {d : Int} (hd : 0 < d) :
    (a : ℝ) ≤ ((-((-a) / d) : Int) : ℝ) * d := by
  have h := ediv_mul_le_real (-a) hd
  push_cast at h ⊢
  linarith

theorem down_mul_le (p : ℕ) (a : Int) : (down p a : ℝ) * 2 ^ p ≤ a := by
  rw [← scale_real]
  exact ediv_mul_le_real a (scale_pos p)

theorem le_up_mul (p : ℕ) (a : Int) : (a : ℝ) ≤ (up p a : ℝ) * 2 ^ p := by
  rw [← scale_real]
  exact le_neg_ediv_mul_real a (scale_pos p)

/-- An interval `[lo / 2 ^ p, hi / 2 ^ p]` with integer ends; the scale `p` is a parameter of
the operations. -/
structure DI where
  lo : Int
  hi : Int

namespace DI

/-- `x` lies in the interval at the scale `2 ^ p`, stated without division. -/
def Mem (p : ℕ) (I : DI) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x * 2 ^ p ∧ x * 2 ^ p ≤ (I.hi : ℝ)

def add (I J : DI) : DI := ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : DI) : DI := ⟨-I.hi, -I.lo⟩

/-- The product: the least and the greatest corner product, rounded down and up to the scale. -/
def mul (p : ℕ) (I J : DI) : DI :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  ⟨down p (min (min a b) (min c d)), up p (max (max a b) (max c d))⟩

/-- The reciprocal `[⌊2 ^ (2p) / hi⌋, ⌈2 ^ (2p) / lo⌉]` of an interval with positive lower end;
it encloses the reciprocals (`mem_inv`). -/
def inv (p : ℕ) (I : DI) : DI := ⟨scale (2 * p) / I.hi, -((-scale (2 * p)) / I.lo)⟩

/-- The square root `[⌊√(lo 2 ^ p)⌋, ⌊√(hi 2 ^ p)⌋ + 1]` of an interval with nonnegative ends; it
encloses the square roots when the lower end is positive (`mem_sqrt`). -/
def sqrt (p : ℕ) (I : DI) : DI :=
  ⟨((Nat.sqrt (I.lo.toNat * 2 ^ p) : ℕ) : Int), ((Nat.sqrt (I.hi.toNat * 2 ^ p) + 1 : ℕ) : Int)⟩

/-- The point `1`. -/
def one (p : ℕ) : DI := ⟨scale p, scale p⟩

/-- Powers, by repeated multiplication. -/
def pow (p : ℕ) (I : DI) : ℕ → DI
  | 0 => one p
  | k + 1 => mul p (pow p I k) I

/-- An outward enclosure of a rational number. -/
def ofRat (p : ℕ) (q : ℚ) : DI := ⟨(q.num * scale p) / q.den, -((-(q.num * scale p)) / q.den)⟩

theorem mem_add {p : ℕ} {I J : DI} {x y : ℝ} (hx : I.Mem p x) (hy : J.Mem p y) :
    (I.add J).Mem p (x + y) := by
  unfold Mem add at *
  push_cast
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {p : ℕ} {I : DI} {x : ℝ} (hx : I.Mem p x) : I.neg.Mem p (-x) := by
  unfold Mem neg at *
  push_cast
  constructor <;> nlinarith [hx.1, hx.2]

theorem mem_mul {p : ℕ} {I J : DI} {x y : ℝ} (hx : I.Mem p x) (hy : J.Mem p y) :
    (I.mul p J).Mem p (x * y) := by
  have h2 := two_pow_pos p
  set X := x * 2 ^ p
  set Y := y * 2 ^ p
  have hXY : X * Y = (x * y) * 2 ^ p * 2 ^ p := by ring
  obtain ⟨hl, hu⟩ := QInterval.product_between_corners (x := X) (y := Y) hx hy
    (m := min (min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi)) (min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi)))
    (M := max (max ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi)) (max ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi)))
    ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
    ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hmin : (((min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)) : Int)) : ℝ) =
      min (min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi)) (min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi)) := by
    push_cast; rfl
  have hmax : (((max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)) : Int)) : ℝ) =
      max (max ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi)) (max ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi)) := by
    push_cast; rfl
  have hd := down_mul_le p (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)))
  have hu' := le_up_mul p (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))
  rw [hmin] at hd
  rw [hmax] at hu'
  constructor
  · show ((down p _ : Int) : ℝ) ≤ x * y * 2 ^ p
    have : ((down p (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))) : Int) : ℝ)
        * 2 ^ p ≤ x * y * 2 ^ p * 2 ^ p := by linarith
    exact le_of_mul_le_mul_right this h2
  · show x * y * 2 ^ p ≤ ((up p _ : Int) : ℝ)
    have : x * y * 2 ^ p * 2 ^ p ≤ ((up p (max (max (I.lo * J.lo) (I.lo * J.hi))
        (max (I.hi * J.lo) (I.hi * J.hi))) : Int) : ℝ) * 2 ^ p := by linarith
    exact le_of_mul_le_mul_right this h2

/-- For a positive lower end the reciprocal interval encloses `x⁻¹`, and `x` is positive. -/
theorem mem_inv {p : ℕ} {I : DI} {x : ℝ} (hx : I.Mem p x) (hpos : 0 < I.lo) :
    (I.inv p).Mem p x⁻¹ ∧ 0 < x := by
  have h2 := two_pow_pos p
  have hlo : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hX : 0 < x * 2 ^ p := hlo.trans_le hx.1
  have hx0 : 0 < x := by
    by_contra h; push Not at h
    nlinarith
  have hhi : (0 : ℝ) < I.hi := hX.trans_le hx.2
  have hhi' : (0 : Int) < I.hi := by exact_mod_cast hhi
  have hS : ((scale (2 * p) : Int) : ℝ) = 2 ^ p * 2 ^ p := by rw [scale_real]; ring
  refine ⟨⟨?_, ?_⟩, hx0⟩
  · -- `⌊2^(2p) / hi⌋ ≤ 2^(2p) / hi ≤ x⁻¹ 2^p`
    have h := ediv_mul_le_real (scale (2 * p)) hhi'
    rw [hS] at h
    show ((scale (2 * p) / I.hi : Int) : ℝ) ≤ x⁻¹ * 2 ^ p
    have hq : ((scale (2 * p) / I.hi : Int) : ℝ) ≤ 2 ^ p * 2 ^ p / I.hi := by
      rw [le_div_iff₀ hhi]; exact h
    have hq2 : 2 ^ p * 2 ^ p / (I.hi : ℝ) ≤ x⁻¹ * 2 ^ p := by
      rw [div_le_iff₀ hhi]
      have : x * 2 ^ p ≤ I.hi := hx.2
      field_simp
      nlinarith
    exact hq.trans hq2
  · have h := le_neg_ediv_mul_real (scale (2 * p)) hpos
    rw [hS] at h
    show x⁻¹ * 2 ^ p ≤ ((-((-scale (2 * p)) / I.lo) : Int) : ℝ)
    have hq : 2 ^ p * 2 ^ p / (I.lo : ℝ) ≤ ((-((-scale (2 * p)) / I.lo) : Int) : ℝ) := by
      rw [div_le_iff₀ hlo]; exact h
    have hq2 : x⁻¹ * 2 ^ p ≤ 2 ^ p * 2 ^ p / (I.lo : ℝ) := by
      rw [le_div_iff₀ hlo]
      have : (I.lo : ℝ) ≤ x * 2 ^ p := hx.1
      field_simp
      nlinarith
    exact hq2.trans hq

/-- For a positive lower end the square-root interval encloses `√x`, and `x` is positive. -/
theorem mem_sqrt {p : ℕ} {I : DI} {x : ℝ} (hx : I.Mem p x) (hpos : 0 < I.lo) :
    (I.sqrt p).Mem p (Real.sqrt x) ∧ 0 < x := by
  have h2 := two_pow_pos p
  have hlo : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hX : 0 < x * 2 ^ p := hlo.trans_le hx.1
  have hx0 : 0 < x := by
    by_contra h; push Not at h
    nlinarith
  have hhi : (0 : ℝ) < I.hi := hX.trans_le hx.2
  have hlo_nat : ((I.lo.toNat : ℕ) : ℝ) = I.lo := by
    have := Int.toNat_of_nonneg hpos.le
    exact_mod_cast this
  have hhi_nat : ((I.hi.toNat : ℕ) : ℝ) = I.hi := by
    have := Int.toNat_of_nonneg (show (0 : Int) ≤ I.hi by exact_mod_cast hhi.le)
    exact_mod_cast this
  -- `√x · 2^p = √(x 2^p · 2^p)`
  have hkey : Real.sqrt x * 2 ^ p = Real.sqrt (x * 2 ^ p * 2 ^ p) := by
    rw [show x * 2 ^ p * 2 ^ p = x * (2 ^ p) ^ 2 by ring, Real.sqrt_mul hx0.le,
      Real.sqrt_sq h2.le]
  refine ⟨⟨?_, ?_⟩, hx0⟩
  · -- `⌊√(lo 2^p)⌋ ≤ √(lo 2^p) ≤ √(x 2^p 2^p)`
    set N := I.lo.toNat * 2 ^ p
    have hs := Nat.sqrt_le' N
    have hN : (N : ℝ) = I.lo * 2 ^ p := by simp [N, hlo_nat]
    show (((Nat.sqrt N : ℕ) : Int) : ℝ) ≤ Real.sqrt x * 2 ^ p
    rw [hkey]
    have hs' : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ x * 2 ^ p * 2 ^ p := by
      have : ((Nat.sqrt N ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hs
      push_cast at this
      rw [hN] at this
      nlinarith [hx.1]
    push_cast
    exact Real.le_sqrt_of_sq_le hs'
  · set N := I.hi.toNat * 2 ^ p
    have hs := Nat.lt_succ_sqrt' N
    have hN : (N : ℝ) = I.hi * 2 ^ p := by simp [N, hhi_nat]
    show Real.sqrt x * 2 ^ p ≤ (((Nat.sqrt N + 1 : ℕ) : Int) : ℝ)
    rw [hkey]
    have hs' : x * 2 ^ p * 2 ^ p ≤ ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
      have : (N : ℝ) < ((Nat.succ (Nat.sqrt N) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hs
      push_cast at this
      rw [hN] at this
      nlinarith [hx.2]
    push_cast
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hs'⟩

theorem mem_pow {p : ℕ} {I : DI} {x : ℝ} (hx : I.Mem p x) : ∀ k, (I.pow p k).Mem p (x ^ k)
  | 0 => by
    unfold Mem pow one
    rw [scale_real]
    simp
  | k + 1 => by
    rw [pow_succ]
    exact mem_mul (mem_pow hx k) hx

theorem mem_ofRat (p : ℕ) (q : ℚ) : (ofRat p q).Mem p q := by
  have hd : (0 : Int) < q.den := by exact_mod_cast q.den_pos
  have hdR : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hq : (q : ℝ) = (q.num : ℝ) / q.den := by exact_mod_cast (Rat.num_div_den q).symm
  have h1 := ediv_mul_le_real (q.num * scale p) hd
  have h2 := le_neg_ediv_mul_real (q.num * scale p) hd
  push_cast at h1 h2
  rw [scale_real] at h1 h2
  unfold Mem ofRat
  rw [hq]
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hdR]
    push_cast; linarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ hdR]
    push_cast; linarith

end DI

/-- One pass of outward-rounded interval arithmetic over a formula, with the intervals `B` for
the variables; `none` when a reciprocal or a square root meets a lower end that is not
positive. -/
def eval {n : ℕ} (p : ℕ) (B : Fin n → DI) : Formula n → Option DI
  | .const q => some (DI.ofRat p q)
  | .var i => some (B i)
  | .add a b => match eval p B a, eval p B b with
    | some x, some y => some (x.add y)
    | _, _ => none
  | .neg a => match eval p B a with
    | some x => some x.neg
    | none => none
  | .mul a b => match eval p B a, eval p B b with
    | some x, some y => some (x.mul p y)
    | _, _ => none
  | .inv a => match eval p B a with
    | some x => if 0 < x.lo then some (x.inv p) else none
    | none => none
  | .sqrt a => match eval p B a with
    | some x => if 0 < x.lo then some (x.sqrt p) else none
    | none => none
  | .pow a k => match eval p B a with
    | some x => some (x.pow p k)
    | none => none

/-- If every variable lies in its interval, a successful pass encloses the value of the formula,
and the formula is regular there. -/
theorem eval_sound {n p : ℕ} {B : Fin n → DI} {env : Fin n → ℝ}
    (hB : ∀ i, (B i).Mem p (env i)) :
    ∀ (f : Formula n) {I : DI}, eval p B f = some I → I.Mem p (f.eval env) ∧ f.RegularAt env := by
  intro f
  induction f with
  | const q =>
    intro I h
    simp only [eval, Option.some.injEq] at h
    subst h
    exact ⟨DI.mem_ofRat p q, trivial⟩
  | var i =>
    intro I h
    simp only [eval, Option.some.injEq] at h
    subst h
    exact ⟨hB i, trivial⟩
  | add a b ha hb =>
    intro I h
    cases hx : eval p B a <;> cases hy : eval p B b <;> simp [eval, hx, hy] at h
    subst h
    obtain ⟨h1, r1⟩ := ha hx
    obtain ⟨h2, r2⟩ := hb hy
    exact ⟨DI.mem_add h1 h2, r1, r2⟩
  | neg a ha =>
    intro I h
    cases hx : eval p B a <;> simp [eval, hx] at h
    subst h
    obtain ⟨h1, r1⟩ := ha hx
    exact ⟨DI.mem_neg h1, r1⟩
  | mul a b ha hb =>
    intro I h
    cases hx : eval p B a <;> cases hy : eval p B b <;> simp [eval, hx, hy] at h
    subst h
    obtain ⟨h1, r1⟩ := ha hx
    obtain ⟨h2, r2⟩ := hb hy
    exact ⟨DI.mem_mul h1 h2, r1, r2⟩
  | inv a ha =>
    intro I h
    cases hx : eval p B a with
    | none => simp [eval, hx] at h
    | some x =>
      simp only [eval, hx] at h
      split_ifs at h with hpos
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, r1⟩ := ha hx
      obtain ⟨hm, hp⟩ := DI.mem_inv h1 hpos
      exact ⟨hm, r1, ne_of_gt hp⟩
  | sqrt a ha =>
    intro I h
    cases hx : eval p B a with
    | none => simp [eval, hx] at h
    | some x =>
      simp only [eval, hx] at h
      split_ifs at h with hpos
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, r1⟩ := ha hx
      obtain ⟨hm, hp⟩ := DI.mem_sqrt h1 hpos
      exact ⟨hm, r1, hp⟩
  | pow a k ha =>
    intro I h
    cases hx : eval p B a <;> simp [eval, hx] at h
    subst h
    obtain ⟨h1, r1⟩ := ha hx
    exact ⟨DI.mem_pow h1 k, r1⟩

/-- The outward fixed-point enclosure of a rational box. -/
def ofBox {n : ℕ} (p : ℕ) (B : QBox n) (i : Fin n) : DI :=
  ⟨(DI.ofRat p (B i).lo).lo, (DI.ofRat p (B i).hi).hi⟩

theorem mem_ofBox {n p : ℕ} {B : QBox n} {env : Fin n → ℝ} (he : B.Mem env) (i : Fin n) :
    (ofBox p B i).Mem p (env i) := by
  have h2 := two_pow_pos p
  have hl := (DI.mem_ofRat p (B i).lo).1
  have hu := (DI.mem_ofRat p (B i).hi).2
  exact ⟨hl.trans (mul_le_mul_of_nonneg_right (he i).1 h2.le),
    (mul_le_mul_of_nonneg_right (he i).2 h2.le).trans hu⟩

/-- The test that one pass on `B` encloses `f` in `[lo, hi]`, with `lo` and `hi` rounded
inwards. -/
def bounded {n : ℕ} (p : ℕ) (B : QBox n) (f : Formula n) (lo hi : ℚ) : Bool :=
  match eval p (ofBox p B) f with
  | some I => decide ((DI.ofRat p lo).hi ≤ I.lo ∧ I.hi ≤ (DI.ofRat p hi).lo)
  | none => false

/-- The test that one pass over `f` on `B` succeeds. -/
def regular {n : ℕ} (p : ℕ) (B : QBox n) (f : Formula n) : Bool :=
  (eval p (ofBox p B) f).isSome

/-- If `bounded` succeeds, `lo ≤ f ≤ hi` at every real point of the box. -/
theorem bounded_sound {n p : ℕ} {B : QBox n} {f : Formula n} {lo hi : ℚ}
    (h : bounded p B f lo hi = true) {env : Fin n → ℝ} (he : B.Mem env) :
    (lo : ℝ) ≤ f.eval env ∧ f.eval env ≤ hi := by
  have h2 := two_pow_pos p
  cases hI : eval p (ofBox p B) f with
  | none => simp [bounded, hI] at h
  | some I =>
    have hc : (DI.ofRat p lo).hi ≤ I.lo ∧ I.hi ≤ (DI.ofRat p hi).lo := by
      simpa [bounded, hI] using h
    have hm := (eval_sound (mem_ofBox he) f hI).1
    have hl : ((DI.ofRat p lo).hi : ℝ) ≤ I.lo := by exact_mod_cast hc.1
    have hu : (I.hi : ℝ) ≤ (DI.ofRat p hi).lo := by exact_mod_cast hc.2
    have hlo := (DI.mem_ofRat p lo).2
    have hhi := (DI.mem_ofRat p hi).1
    constructor
    · exact le_of_mul_le_mul_right (hlo.trans (hl.trans hm.1)) h2
    · exact le_of_mul_le_mul_right (hm.2.trans (hu.trans hhi)) h2

/-- If `regular` succeeds, `f` is regular at every real point of the box. -/
theorem regular_sound {n p : ℕ} {B : QBox n} {f : Formula n} (h : regular p B f = true)
    {env : Fin n → ℝ} (he : B.Mem env) : f.RegularAt env := by
  cases hI : eval p (ofBox p B) f with
  | none => simp [regular, hI] at h
  | some I => exact (eval_sound (mem_ofBox he) f hI).2

/-- The test that the box `B` lies in `target`, with weak inequalities in every coordinate. -/
def inside (B target : QBox 3) : Bool :=
  decide (∀ i, (target i).lo ≤ (B i).lo ∧ (B i).hi ≤ (target i).hi)

end SquaresInCircles.Eight.Stationary.FixedEval
end
end
end
