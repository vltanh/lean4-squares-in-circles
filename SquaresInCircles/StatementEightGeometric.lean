module

public import SquaresInCircles.Geometry
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-!
# Pure geometric statement of the eight-square model

Uncompiled source draft, written without running Lean or lake.

The sharp radius is the infimum of the nonnegative radii admitting five
points with five prescribed projection spans. Existence, attainment and
uniqueness are downstream theorems. No numerical radius bracket, stationary
equation, generated certificate, or packing theorem occurs in this definition.

All distances use `normSq`, the Euclidean squared distance. The norm instance
on `ℝ × ℝ` is not used for the enclosing circle.

The five point indices are A, B, D, E, H, in that order. Angles are real
representatives; the square itself is unchanged by a quarter turn.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles
namespace Eight.GeometricModel

def e (t : ℝ) : Point := (Real.cos t, Real.sin t)
def f (t : ℝ) : Point := (-Real.sin t, Real.cos t)

/-- The scalar projection used by the proof-independent statement layer. -/
def projection (n p : Point) : ℝ := n.1 * p.1 + n.2 * p.2

def square (p : Point) (t : ℝ) : UnitSquare where
  center := p
  cosine := Real.cos t
  sine := Real.sin t
  unit := by simpa only [add_comm] using Real.sin_sq_add_cos_sq t

/-- The exact squared distance of a square's farthest vertex from zero. -/
def containmentCost (p : Point) (t : ℝ) : ℝ :=
  (|projection (e t) p| + 1 / 2) ^ 2 +
    (|projection (f t) p| + 1 / 2) ^ 2

def supportWidth (t : ℝ) (n : Point) : ℝ :=
  (|projection (e t) n| + |projection (f t) n|) / 2

/-- All four candidate unsigned separating axes share this support sum. -/
def separationWidth (a b : ℝ) : ℝ :=
  (1 + |Real.cos (a - b)| + |Real.sin (a - b)|) / 2

def separationMargin (a b : ℝ) (d : Point) : ℝ :=
  max (max |projection (e a) d| |projection (f a) d|)
      (max |projection (e b) d| |projection (f b) d|) - separationWidth a b

structure FiveCorner where
  angle : ℝ
  point : Fin 5 → Point
  deriving Inhabited

namespace FiveCorner

/-- Five projected spans and the complete natural tilt interval. The order
of the last two spans is E/H followed by A/H, matching the contact weights. -/
def spans (d : FiveCorner) : Prop :=
  0 ≤ d.angle ∧ d.angle ≤ Real.pi / 4 ∧
  2 ≤ (d.point 1).2 - (d.point 0).2 ∧
  3 ≤ (d.point 1).1 - (d.point 2).1 ∧
  2 ≤ (d.point 2).2 - (d.point 3).2 ∧
  1 + Real.sin d.angle ≤ projection (f d.angle) (sub (d.point 3) (d.point 4)) ∧
  2 + Real.cos d.angle ≤ projection (e d.angle) (sub (d.point 0) (d.point 4))

def fits (d : FiveCorner) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ i : Fin 5, normSq (d.point i) ≤ R ^ 2

def feasibleRadii : Set ℝ := {R | ∃ d : FiveCorner, d.spans ∧ d.fits R}

/-- The geometric sharp radius. Downstream proofs show that the infimum is
attained by exactly one five-point configuration in the chosen frame. -/
def radius : ℝ := sInf feasibleRadii

def IsMinimizer (d : FiveCorner) : Prop := d.spans ∧ d.fits radius

def selected : FiveCorner := Classical.epsilon IsMinimizer

end FiveCorner

/-- The two-height expression obtained from the upper chord of width three. -/
def twoHeightRadiusSq (u v : ℝ) : ℝ :=
  ((9 + (u - v) ^ 2) * (9 + (4 - u - v) ^ 2)) / 36

def upperRightFromHeights (u v : ℝ) : ℝ :=
  (9 + (u - v) * (4 - u - v)) / 6

def upperLeftFromHeights (u v : ℝ) : ℝ :=
  (9 - (u - v) * (4 - u - v)) / 6

/-- Reflection in the diagonal, kept in the proof-independent model layer. -/
def reflectSquare (K : UnitSquare) : UnitSquare where
  center := (K.center.2, K.center.1)
  cosine := K.sine
  sine := K.cosine
  unit := by linarith [K.unit]

namespace FiveCorner

/-- The order of the five anchor centers is `A,B,D,E,H`. -/
def anchorCenter (d : FiveCorner) : Fin 5 → Point :=
  ![((d.point 0).1-1/2,(d.point 0).2+1/2),
    ((d.point 1).1-1/2,(d.point 1).2-1/2),
    ((d.point 2).1+1/2,(d.point 2).2-1/2),
    ((d.point 3).1+1/2,(d.point 3).2+1/2),
    ((d.point 4).1+((e d.angle).1+(f d.angle).1)/2,
      (d.point 4).2+((e d.angle).2+(f d.angle).2)/2)]

/-- The middle upper square moves on the vertical rail one unit left of B. -/
def topCenter (d : FiveCorner) (z : ℝ) : Point :=
  ((d.anchorCenter 1).1-1,z)

/-- The lower tilted square moves along the side direction of H. -/
def tiltedCenter (d : FiveCorner) (η : ℝ) : Point :=
  ((d.anchorCenter 4).1+(e d.angle).1+η*(f d.angle).1,
    (d.anchorCenter 4).2+(e d.angle).2+η*(f d.angle).2)

/-- Exterior labels retain their counterclockwise order `H,G,A,B,T,D,E`. -/
def exteriorCenter (d : FiveCorner) (z η : ℝ) : Fin 7 → Point :=
  ![d.anchorCenter 4,d.tiltedCenter η,d.anchorCenter 0,d.anchorCenter 1,
    d.topCenter z,d.anchorCenter 2,d.anchorCenter 3]

def exteriorAngle (d : FiveCorner) : Fin 7 → ℝ :=
  ![d.angle,d.angle,0,0,0,0,0]

def exteriorSquare (d : FiveCorner) (z η : ℝ) (i : Fin 7) : UnitSquare :=
  square (d.exteriorCenter z η i) (d.exteriorAngle i)

end FiveCorner

/-- Five real freedoms, expressed using the actual central angle. -/
structure Parameters where
  center : Point
  angle : ℝ
  top : ℝ
  tilted : ℝ

namespace Parameters

def centralSquare (p : Parameters) : UnitSquare := square p.center p.angle

def model (d : FiveCorner) (p : Parameters) : Fin 8 → UnitSquare :=
  Fin.cons p.centralSquare (d.exteriorSquare p.top p.tilted)

/-- A half-open representative of a square frame, rather than an orientation
of a marked edge.  The corresponding square is unchanged by a quarter turn. -/
def AngleRepresentative (θ : ℝ) : Prop :=
  -Real.pi/4 ≤ θ ∧ θ < Real.pi/4

/-- Exact geometric conditions, with all weak rail and separation contacts. -/
structure Admissible (d : FiveCorner) (p : Parameters) : Prop where
  angle_mem : AngleRepresentative p.angle
  top_contained : containmentCost (d.topCenter p.top) 0 ≤ FiveCorner.radius^2
  tilted_contained :
    containmentCost (d.tiltedCenter p.tilted) d.angle ≤ FiveCorner.radius^2
  top_above_axis : 1/2 ≤ p.top
  tilted_below_axis :
    (d.tiltedCenter p.tilted).2 +
      (|Real.cos d.angle|+|Real.sin d.angle|)/2 ≤ 0
  central_first : |projection (e p.angle) p.center| < 1/2
  central_second : |projection (f p.angle) p.center| < 1/2
  central_separated : ∀ i : Fin 7,
    0 ≤ separationMargin p.angle (d.exteriorAngle i)
      (sub (d.exteriorCenter p.top p.tilted i) p.center)

end Parameters

/-- Both chiral copies are retained.  Arbitrary rigid motions and relabelings
are applied by the surrounding equality classification, as in `Congruent`. -/
def reflectedModel (reflected : Bool) (p : Parameters) : Fin 8 → UnitSquare :=
  if reflected then fun i => reflectSquare (p.model FiveCorner.selected i)
  else p.model FiveCorner.selected

def models : Set (Fin 8 → UnitSquare) :=
  {M | ∃ reflected : Bool, ∃ p : Parameters,
    p.Admissible FiveCorner.selected ∧ M=reflectedModel reflected p}

end Eight.GeometricModel
end SquaresInCircles
