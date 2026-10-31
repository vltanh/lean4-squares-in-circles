module

public import SquaresInCircles.Eight.ExactFamily.Expression
public meta import SquaresInCircles.Eight.ExactFamily.FormulaData

/-!
# The stationary equations as named formulas

The four radicals follow the five-corner chain. The half-angle formulas give the tilt,
and `FFormula` is the fifth corner's squared distance minus the squared radius.
Partial derivatives are computed once as formula data, then identified by kernel proofs.
-/

set_option maxRecDepth 100000
@[expose] public section
namespace SquaresInCircles.Eight.ExactFamily.Generated
local instance : Add (Formula 3) := ⟨Formula.plus⟩
local instance : Neg (Formula 3) := ⟨Formula.minus⟩
local instance : Sub (Formula 3) := ⟨fun a b => Formula.plus a (Formula.minus b)⟩
local instance : Mul (Formula 3) := ⟨Formula.times⟩
local instance : Div (Formula 3) := ⟨Formula.quotient⟩
local instance : Pow (Formula 3) Nat := ⟨Formula.power⟩
local instance (n : Nat) : OfNat (Formula 3) n := ⟨.const n⟩

def squaredRadius : Formula 3 := .var 0
def position : Formula 3 := .var 1
def halfTilt : Formula 3 := .var 2

def xOneFormula : Formula 3 := eval% .sqrt (squaredRadius - position^2)
def xTwoFormula : Formula 3 := eval% .sqrt (squaredRadius - (position+2)^2)
def yThreeFormula : Formula 3 := eval% .sqrt (squaredRadius - (xTwoFormula-3)^2)
def xFourFormula : Formula 3 := eval% -(.sqrt (squaredRadius - (yThreeFormula-2)^2))
def cosineFormula : Formula 3 := eval% (1-halfTilt^2)/(1+halfTilt^2)
def sineFormula : Formula 3 := eval% (2*halfTilt)/(1+halfTilt^2)
def hOneFormula : Formula 3 := eval% cosineFormula*xOneFormula+sineFormula*position-2-cosineFormula
def hTwoFormula : Formula 3 := eval% -(sineFormula*xFourFormula)+cosineFormula*(yThreeFormula-2)-1-sineFormula
def FFormula : Formula 3 := eval% hOneFormula^2+hTwoFormula^2-squaredRadius

def FqFormula : Formula 3 := eval% FFormula.diff 0
def FyFormula : Formula 3 := eval% FFormula.diff 1
def FzFormula : Formula 3 := eval% FFormula.diff 2
def FyyFormula : Formula 3 := eval% FyFormula.diff 1
def FyzFormula : Formula 3 := eval% FyFormula.diff 2
def FzzFormula : Formula 3 := eval% FzFormula.diff 2

theorem Fq_diff : FFormula.diff 0 = FqFormula := by decide +kernel
theorem Fy_diff : FFormula.diff 1 = FyFormula := by decide +kernel
theorem Fz_diff : FFormula.diff 2 = FzFormula := by decide +kernel
theorem Fyy_diff : FyFormula.diff 1 = FyyFormula := by decide +kernel
theorem Fyz_diff : FyFormula.diff 2 = FyzFormula := by decide +kernel
theorem Fzz_diff : FzFormula.diff 2 = FzzFormula := by decide +kernel

noncomputable def scalarF (q y z : ℝ) : ℝ := FFormula.eval ![q,y,z]
theorem F_eval (q y z : ℝ) : FFormula.eval ![q,y,z] = scalarF q y z := rfl

noncomputable def scalarFy (q y z : ℝ) : ℝ := FyFormula.eval ![q,y,z]
theorem Fy_eval (q y z : ℝ) : FyFormula.eval ![q,y,z] = scalarFy q y z := rfl

noncomputable def scalarFz (q y z : ℝ) : ℝ := FzFormula.eval ![q,y,z]
theorem Fz_eval (q y z : ℝ) : FzFormula.eval ![q,y,z] = scalarFz q y z := rfl

noncomputable def scalarxOne (q y z : ℝ) : ℝ := xOneFormula.eval ![q,y,z]
theorem xOne_eval (q y z : ℝ) : xOneFormula.eval ![q,y,z] = scalarxOne q y z := rfl

noncomputable def scalarxTwo (q y z : ℝ) : ℝ := xTwoFormula.eval ![q,y,z]
theorem xTwo_eval (q y z : ℝ) : xTwoFormula.eval ![q,y,z] = scalarxTwo q y z := rfl

noncomputable def scalaryThree (q y z : ℝ) : ℝ := yThreeFormula.eval ![q,y,z]
theorem yThree_eval (q y z : ℝ) : yThreeFormula.eval ![q,y,z] = scalaryThree q y z := rfl

noncomputable def scalarxFour (q y z : ℝ) : ℝ := xFourFormula.eval ![q,y,z]
theorem xFour_eval (q y z : ℝ) : xFourFormula.eval ![q,y,z] = scalarxFour q y z := rfl

noncomputable def scalarcosine (q y z : ℝ) : ℝ := cosineFormula.eval ![q,y,z]
theorem cosine_eval (q y z : ℝ) : cosineFormula.eval ![q,y,z] = scalarcosine q y z := rfl

noncomputable def scalarsine (q y z : ℝ) : ℝ := sineFormula.eval ![q,y,z]
theorem sine_eval (q y z : ℝ) : sineFormula.eval ![q,y,z] = scalarsine q y z := rfl

noncomputable def scalarhOne (q y z : ℝ) : ℝ := hOneFormula.eval ![q,y,z]
theorem hOne_eval (q y z : ℝ) : hOneFormula.eval ![q,y,z] = scalarhOne q y z := rfl

noncomputable def scalarhTwo (q y z : ℝ) : ℝ := hTwoFormula.eval ![q,y,z]
theorem hTwo_eval (q y z : ℝ) : hTwoFormula.eval ![q,y,z] = scalarhTwo q y z := rfl

/-- The mixed partials agree, by the product and chain rules and commutativity of real arithmetic. -/
theorem mixed_partials (env : Fin 3 → ℝ) :
    (FzFormula.diff 1).eval env = FyzFormula.eval env := by
  norm_num [FzFormula, FyzFormula, Formula.diff, Formula.plus, Formula.minus, Formula.times,
    Formula.power, Formula.reciprocal, Formula.quotient, Formula.eval]
  ring

end SquaresInCircles.Eight.ExactFamily.Generated
