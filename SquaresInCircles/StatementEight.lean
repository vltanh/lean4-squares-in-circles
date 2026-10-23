module

public import SquaresInCircles.Geometry
public import Mathlib.Tactic

/-!
# Pure statement data for eight squares

This module contains only explicit real formulas, finite records, and
ordinary classical selection. It imports no eight-square proof module.
`selected` is defined by the displayed stationary predicate; its existence,
uniqueness, and identification with the analytically selected root are
proved downstream in `Eight/ExactFamily/StatementLink.lean`.

The five-parameter domain includes weak contact inequalities, the half-open
central-frame interval, and both reflected and unreflected model branches.
These definitions are copied into the Mathlib-only `Challenge.lean` by the
source-only `scripts/sync-challenge.py` helper.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles
namespace EightStatement

def halfAngleCos (z : ℝ) : ℝ := (1-z^2)/(1+z^2)
def halfAngleSin (z : ℝ) : ℝ := 2*z/(1+z^2)

theorem halfAngle_unit (z : ℝ) : halfAngleCos z^2+halfAngleSin z^2=1 := by
  have hd : 0<1+z^2 := by positivity
  unfold halfAngleCos halfAngleSin
  field_simp [ne_of_gt hd]
  ring

/-- The seven real coordinates in the explicit stationary system. The
branch conditions below select the four successive circle radicals. -/
structure Root where
  q : ℝ
  y : ℝ
  z : ℝ
  x₁ : ℝ
  x₂ : ℝ
  y₃ : ℝ
  x₄ : ℝ
  deriving Inhabited

namespace Root

def c (d : Root) : ℝ := halfAngleCos d.z
def s (d : Root) : ℝ := halfAngleSin d.z
def x₃ (d : Root) : ℝ := d.x₂-3
def y₄ (d : Root) : ℝ := d.y₃-2
def h₁ (d : Root) : ℝ := d.c*d.x₁+d.s*d.y-2-d.c
def h₂ (d : Root) : ℝ := -d.s*d.x₄+d.c*d.y₄-1-d.s
def defect (d : Root) : ℝ := d.h₁^2+d.h₂^2-d.q
def y₄deriv (d : Root) : ℝ := d.x₃*(d.y+2)/(d.y₃*d.x₂)
def h₁deriv (d : Root) : ℝ := d.s-d.c*d.y/d.x₁
def h₂deriv (d : Root) : ℝ := (d.c+d.s*d.y₄/d.x₄)*d.y₄deriv
def positionDerivative (d : Root) : ℝ := 2*(d.h₁*d.h₁deriv+d.h₂*d.h₂deriv)
def tiltDerivative (d : Root) : ℝ :=
  2*(d.h₁*(-d.s*(d.x₁-1)+d.c*d.y)+d.h₂*(-d.c*(d.x₄+1)-d.s*d.y₄))

structure IsChain (d : Root) : Prop where
  x₁_pos : 0<d.x₁
  x₂_pos : 0<d.x₂
  y₃_pos : 0<d.y₃
  x₄_neg : d.x₄<0
  first_circle : d.x₁^2+d.y^2=d.q
  second_circle : d.x₂^2+(d.y+2)^2=d.q
  third_circle : d.x₃^2+d.y₃^2=d.q
  fourth_circle : d.x₄^2+d.y₄^2=d.q

/-- Circle equations, branch inequalities, and the two exact derivative
equations in the broad analytic strip. No optimality or packing assertion
is part of this selection predicate. -/
structure IsStationary (d : Root) : Prop extends IsChain d where
  q_lower : (79/40 : ℝ)^2≤d.q
  q_upper : d.q≤9789/2500
  y_lower : -1<d.y
  y_upper : d.y< -(1/2)
  y₄_lower : -1<d.y₄
  y₄_upper : d.y₄< -(1/2)
  position_order : d.y<d.y₄
  z_pos : 0<d.z
  tilt_range : 2*d.z/(1-d.z^2)<1/5
  z_lt_one : d.z<1
  zero_defect : d.defect=0
  position_stationary : d.positionDerivative=0
  tilt_stationary : d.tiltDerivative=0

def inFrame (d : Root) (a b : ℝ) : Point :=
  (d.c*a-d.s*b,d.s*a+d.c*b)

def pA (d : Root) : Point := (d.x₁-1/2,d.y+1/2)
def pB (d : Root) : Point := (d.x₂-1/2,d.y+3/2)
def pD (d : Root) : Point := (d.x₃+1/2,d.y₃-1/2)
def pE (d : Root) : Point := (d.x₄+1/2,d.y₄+1/2)
def pH (d : Root) : Point := d.inFrame (d.h₁+1/2) (d.h₂+1/2)
def pT (d : Root) (Z : ℝ) : Point := (d.x₂-3/2,Z)
def pG (d : Root) (η : ℝ) : Point := d.inFrame (d.h₁+3/2) (d.h₂+1/2+η)

def tiltedSquare (d : Root) (p : Point) : UnitSquare where
  center := p
  cosine := d.c
  sine := d.s
  unit := halfAngle_unit d.z

def zMax (d : Root) : ℝ := Real.sqrt (d.q-(d.x₂-1)^2)-1/2
def etaMin (d : Root) : ℝ := -d.h₂-Real.sqrt (d.q-(d.h₁+2)^2)
def etaMax (d : Root) : ℝ := -d.h₂-13/12

end Root

/-- Ordinary Hilbert choice from the explicit stationary system. The proof
module establishes that this predicate has exactly one solution, so the
selection has no dependence on an arbitrary choice of branch or witness. -/
def selected : Root := Classical.epsilon Root.IsStationary

/-- The exact squared radius, characterized by `Root.IsStationary`. -/
def qStar : ℝ := selected.q

/-- The radius of the containing disk for eight squares. -/
def radius : ℝ := Real.sqrt qStar

structure Parameters where
  x : ℝ
  y : ℝ
  w : ℝ
  z : ℝ
  eta : ℝ

namespace Parameters

def C (p : Parameters) : ℝ := halfAngleCos p.w
def S (p : Parameters) : ℝ := halfAngleSin p.w
def center (p : Parameters) : Point := (p.x,p.y)

def centralSquare (p : Parameters) : UnitSquare where
  center := p.center
  cosine := p.C
  sine := p.S
  unit := halfAngle_unit p.w

def M₀ (p : Parameters) (v : Point) : ℝ :=
  max (max |v.1| |v.2|) (max |p.C*v.1+p.S*v.2| |-p.S*v.1+p.C*v.2|)

def Mₜ (p : Parameters) (d : Root) (v : Point) : ℝ :=
  max (max |d.c*v.1+d.s*v.2| |-d.s*v.1+d.c*v.2|)
    (max |p.C*v.1+p.S*v.2| |-p.S*v.1+p.C*v.2|)

def W₀ (p : Parameters) : ℝ := (1+p.C+|p.S|)/2
def Wₜ (p : Parameters) (d : Root) : ℝ :=
  (1+d.c*p.C+d.s*p.S+|d.c*p.S-d.s*p.C|)/2

/-- The full equality domain. All separation and slider inequalities are
weak; the central core inequalities are strict and its frame interval is
half open. -/
structure Admissible (d : Root) (p : Parameters) : Prop where
  frame_lower : 1-Real.sqrt 2≤p.w
  frame_upper : p.w<Real.sqrt 2-1
  top_lower : 7/12≤p.z
  top_upper : p.z≤d.zMax
  tilted_lower : d.etaMin≤p.eta
  tilted_upper : p.eta≤d.etaMax
  core_first : |p.C*p.x+p.S*p.y|<5/12
  core_second : |-p.S*p.x+p.C*p.y|<5/12
  A_sep : p.W₀≤p.M₀ (sub d.pA p.center)
  B_sep : p.W₀≤p.M₀ (sub d.pB p.center)
  D_sep : p.W₀≤p.M₀ (sub d.pD p.center)
  E_sep : p.W₀≤p.M₀ (sub d.pE p.center)
  T_sep : p.W₀≤p.M₀ (sub (d.pT p.z) p.center)
  H_sep : p.Wₜ d≤p.Mₜ d (sub d.pH p.center)
  G_sep : p.Wₜ d≤p.Mₜ d (sub (d.pG p.eta) p.center)

def model (d : Root) (p : Parameters) : Fin 8 → UnitSquare :=
  ![p.centralSquare,d.tiltedSquare d.pH,d.tiltedSquare (d.pG p.eta),
    axisSquare d.pA,axisSquare d.pB,axisSquare (d.pT p.z),axisSquare d.pD,axisSquare d.pE]

end Parameters

def reflectSquare (K : UnitSquare) : UnitSquare where
  center := (K.center.2,K.center.1)
  cosine := K.sine
  sine := K.cosine
  unit := by linarith [K.unit]

def reflectedModel (reflected : Bool) (p : Parameters) : Fin 8 → UnitSquare :=
  if reflected then fun i=>reflectSquare (p.model selected i) else p.model selected

def models : Set (Fin 8 → UnitSquare) :=
  {M | ∃ reflected : Bool,∃ p : Parameters,
    p.Admissible selected ∧ M=reflectedModel reflected p}

end EightStatement
end SquaresInCircles
