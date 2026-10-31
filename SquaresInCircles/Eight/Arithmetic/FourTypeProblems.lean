module

public import SquaresInCircles.Eight.Arithmetic.PairCover
public import SquaresInCircles.Eight.Boundary.Frames

/-!
# Eight squares: the problems of the four-type pair tables

The four-type pair bounds (`FourTypePairs.lean`) use five charts (`Branch`): the core side and
the core corner, which share a label and the type `0`, and the low, middle and high ranges
`[0, 1/4]`, `[1/4, 3/7]` and `[3/7, 1]` of the tangent `b / a` on the outer circle, of the types
`1`, `2` and `3`. The pair problem of an ordered pair of branches, two signs and a source axis,
four or one (`fourTypeProblem`), has the ends of the two branches (`branchEnd`): their charts,
tangent ranges and signed labels (`branchQuad`), the constants of the labels with `√(Q₀ - 1/4)`,
`√(Q₀/2)` and `π` given by rational brackets. Its charge is `9/50`, its target is the entry of
the four-type matrix `handGamma` (`Boundary/Frames.lean`) for the types of the branches (`gammaQ`), and it
is posed on the six halves of `φ ∈ [-1, 4]` (`fourTypeHalves`).

A pair table of `Generated/Pairs/` defines its problems as `fourTypeProblem s t` mapped over
`fourTypeCases`, so that `FourTypePairs.lean` finds each problem in its table without comparing
rationals (`fourTypeProblem_mem`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic.FourType

open PairCover

/-- The five charts of the four-type pair bounds: the core side, the core corner, and the low,
middle and high ranges of the tangent on the outer circle. The two core charts have the same
label and the same type. -/
inductive Branch | coreSide | coreCorner | low | middle | high

/-- The type of a branch: `0` for the core, `1`, `2` and `3` for the low, middle and high
ranges. -/
def Branch.type : Branch → Fin 4
  | .coreSide | .coreCorner => 0
  | .low => 1 | .middle => 2 | .high => 3

/-- The target of a pair of branches: the entry of `handGammaNumerator` for their types, over
`10⁴`. -/
def gammaQ (s t : Branch) : ℚ := handGammaNumerator s.type t.type/10000

/-- Rational brackets of `√(Q₀ - 1/4)` and `√(Q₀/2)` of width `10⁻²⁰`, and of `π` of width
`10⁻¹⁸`. -/
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

/-- The branch lies on the outer circle. -/
def Branch.outer : Branch → Bool
  | .low | .middle | .high => true
  | .coreSide | .coreCorner => false

/-- The branch is the core side. -/
def Branch.side : Branch → Bool
  | .coreSide => true
  | _ => false

/-- The tangent range of a branch. -/
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

/-- The pair problem of the branches `s`, `t`, the signs `σ`, `τ` and the source axis (four if
`four`, else one), with the charge `9/50` and the target `gammaQ s t`. -/
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
