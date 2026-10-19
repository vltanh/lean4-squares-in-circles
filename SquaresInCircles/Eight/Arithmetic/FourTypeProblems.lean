module

public import SquaresInCircles.Eight.Arithmetic.PairCover
public import SquaresInCircles.Eight.Frames

/-!
# The problems of the four-type pair tables

The five analytic charts of the four geometric types, and the pair problem of an ordered pair of
charts, signs and a source axis (`fourTypeProblem`): its ends carry the actual charts, tangent
ranges and signed labels, with rational brackets of the constants `√(Q₀ - 1/4)`, `√(Q₀/2)` and
`π`. A pair table (`Generated/Pairs`) defines its problems as the images of `fourTypeCases`
under `fourTypeProblem`, so `FourTypePairs` finds each problem in its table without comparing
rationals.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic.FourType

open PairCover

/-- Five analytic charts for the four geometric types.  The two core
charts have the same label and the same matrix index. -/
inductive Branch | coreSide | coreCorner | low | middle | high

def Branch.type : Branch → Fin 4
  | .coreSide | .coreCorner => 0
  | .low => 1 | .middle => 2 | .high => 3

def gammaQ (s t : Branch) : ℚ := handGammaNumerator s.type t.type/10000

/-- Rational brackets of `√(Q₀ - 1/4)`, `√(Q₀/2)` and `π`. -/
def rootA0Lo : ℚ := 191457567100389113870 / 10 ^ 20
def rootA0Hi : ℚ := 191457567100389113871 / 10 ^ 20
def rootC0Lo : ℚ := 139921406510940991183 / 10 ^ 20
def rootC0Hi : ℚ := 139921406510940991184 / 10 ^ 20
def piLo : ℚ := 3141592653589793238 / 10 ^ 18
def piHi : ℚ := 3141592653589793239 / 10 ^ 18

/-- The positive label of a branch, with a rational bracket of its constant. -/
def branchQuad : Branch → QuadLabel
  | .coreSide | .coreCorner => ⟨7506931/1000000*(7/12), 7506931/1000000*(7/12), -(7506931/1000000),
      269343/250000, 0, 0⟩
  | .low => ⟨-(3231/8000)*(rootA0Hi-1/2), -(3231/8000)*(rootA0Lo-1/2), 3231/8000, 217813/200000,
      0, 0⟩
  | .middle => ⟨-85723/40000, -85723/40000, 1489593/1000000, 1580219/1000000, 0, 0⟩
  | .high => ⟨piLo/4+(8898/15625-195443/500000)*(rootC0Lo-1/2),
      piHi/4+(8898/15625-195443/500000)*(rootC0Hi-1/2), -(8898/15625), 195443/500000, 0, 0⟩

/-- The chart and the tangent range of a branch. -/
def Branch.outer : Branch → Bool
  | .low | .middle | .high => true
  | .coreSide | .coreCorner => false

def Branch.side : Branch → Bool
  | .coreSide => true
  | _ => false

def Branch.range : Branch → QInterval
  | .coreSide => ⟨0, 6/7⟩
  | .coreCorner => ⟨6/7, 1⟩
  | .low => ⟨0, 1/4⟩
  | .middle => ⟨1/4, 3/7⟩
  | .high => ⟨3/7, 1⟩

/-- The end of a pair at a vertex of the branch `s` and sign `σ`. -/
def branchEnd (s : Branch) (σ : Bool) : PairEnd :=
  ⟨s.outer, s.side, σ, s.range, (branchQuad s).signed σ⟩

/-- The six halves `(k, r, u⁺)` of `φ ∈ [-1, 4]`, with `u⁺` over `10⁸`. -/
def fourTypeHalves : List (ℕ × Bool × ℕ) :=
  [(0, false, 100000000), (0, true, 80000000), (1, false, 80000000), (1, true, 80000000),
    (2, false, 80000000), (2, true, 86000000)]

/-- The pair problem of the branches `s`, `t`, the signs `σ`, `τ` and the source axis. -/
def fourTypeProblem (s t : Branch) (σ τ four : Bool) : PairProblem :=
  ⟨branchEnd s σ, branchEnd t τ, if four then .four else .one, 9/50, gammaQ s t, fourTypeHalves⟩

/-- The signs `σ`, `τ` and the source axis (four or one) of the problems of a pair table, in the
order of its problems. -/
def fourTypeCases : List (Bool × Bool × Bool) :=
  [false, true] ×ˢ [false, true] ×ˢ [false, true]

theorem mem_fourTypeCases (c : Bool × Bool × Bool) : c ∈ fourTypeCases := by
  obtain ⟨σ, τ, four⟩ := c
  cases σ <;> cases τ <;> cases four <;> decide

end SquaresInCircles.Eight.Arithmetic.FourType
