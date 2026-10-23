module

public import SquaresInCircles.Eight.TableFree.SoleNegativeTScalarModel
public import SquaresInCircles.Eight.TableFree.SolePositiveTPolynomials

/-!
# Whole-interval enclosure formulas for all negative-T scalar endpoints

Uncompiled source. The same global septic radical majorant and rigorous
polynomial arithmetic used for positive T are applied to the 34 intrinsic
one-dimensional cases. The polynomial is elevated to Bernstein degree 32
on its entire interval; the second tensor variable is unused. The exact
coefficient/error comparisons below have deliberately not been run.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleNegativeTPolynomials
open TensorPolynomialEnclosure TensorWholeIntervalPolynomial
open SoleTScalarModel SolePositiveTPolynomials SoleNegativeTScalarModel

def parameter (r : Row) : Enclosure :=
  add (constant ((SoleNegativeTScalarModel.left r+SoleNegativeTScalarModel.right r)/2))
    (mul (constant ((SoleNegativeTScalarModel.right r-SoleNegativeTScalarModel.left r)/2)) outerVariable)

def xParameter (s : Case) : Enclosure := if s.atG then parameter s.row else constant 0
def eParameter (s : Case) : Enclosure := if s.atG then constant 0 else parameter s.row
def angleParameter (s : Case) : Enclosure :=
  if shifted s.row then sub (parameter s.row) (constant (3/10)) else constant 0

def variables (s : Case) : Fin 11 → Enclosure :=
  ![parameter s.row,constant 0,sine (xParameter s),cosine (xParameter s),constant 0,constant 1,
    sine (eParameter s),cosine (eParameter s),sine (angleParameter s),cosine (angleParameter s),
    sine (mul (eParameter s) (constant (1/2)))]

def rootExpression (s : Case) (i : Fin 7) : Expr :=
  Expression.sqrtUpper (variables s) (rootSquare (scalar s) i)

def baseExpression (s : Case) : Expr :=
  kE (family s.row)*(1+2*cx+(1+2*gE (family s.row))*sx)+
    3*cE (family s.row)+2*ellE (family s.row)-
    lit SoleTScalarModel.radiusUpper*kE (family s.row)*sx*rootExpression s 4

def eExpression (s : Case) : Expr :=
  if tiltedE (family s.row) then
    1+2*ce+(1+2*epsilonE (family s.row))*se-
      lit SoleTScalarModel.radiusUpper*se*rootExpression s 6
  else if isDE (family s.row) then
    1+lit (1/2)*ce+lit (1-SoleTScalarModel.axisUpper)*se+lit (3/2)*lit (5/4)
  else 3+se-lit (2*SoleTScalarModel.radiusUpper)*shalf

def correctionE (s : Case) : Expr :=
  if family s.row=.ehMiddle ∨ family s.row=.ehHigh then
    lit (8/25)*(cE (family s.row)-pE (scalar s))^2 else 0
def removedE (s : Case) : Expr := if shifted s.row then lit (3/10) else tE
def coefficientE (s : Case) : Expr :=
  if index s.row=3 then cE (family s.row) else nuE (scalar s)

def expression (s : Case) : Expr :=
  ((((baseExpression s+eExpression s+correctionE s+
    lit (21/20)*cE (family s.row)*removedE s+coefficientE s*(ct-1))-
      lit SoleTScalarModel.radiusUpper*rootExpression s 0)-
        lit SoleTScalarModel.radiusUpper*rootExpression s 1)-
          lit SoleTScalarModel.radiusUpper*rootExpression s 2)-
            lit SoleTScalarModel.radiusUpper*rootExpression s 3

def enclosure (s : Case) : Enclosure := Expression.enclose (variables s) (expression s)
def polynomial (s : Case) : Bivar := (enclosure s).polynomial
def lower (s : Case) : ℚ :=
  Finset.univ.inf' Finset.univ_nonempty (fun ij : Fin 33 × Fin 33 =>
    TensorWholeIntervalBernstein.coefficient 32 (polynomial s) ij.1 ij.2)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem seeds_positive (s : Case) (i : Fin 7) :
    0<rootSeed (Expression.enclose (variables s) (rootSquare (scalar s) i)) := by
  rcases s with ⟨r,b⟩
  cases r <;> cases b <;> fin_cases i <;> try (rename_i j; fin_cases j)
  all_goals decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem polynomial_identity (s : Case) :
    polynomial s=TensorWholeIntervalBernstein.expansion 32 (polynomial s) := by
  rcases s with ⟨r,b⟩
  cases r <;> cases b <;> try (rename_i j; fin_cases j)
  all_goals decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem partition :
    (∑ i : Fin 33,∑ j : Fin 33,TensorWholeIntervalBernstein.basis 32 i j)=1 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem reserve (s : Case) : (enclosure s).error<lower s := by
  rcases s with ⟨r,b⟩
  cases r <;> cases b <;> try (rename_i j; fin_cases j)
  all_goals decide

theorem lower_le (s : Case) (i j : Fin 33) :
    lower s≤TensorWholeIntervalBernstein.coefficient 32 (polynomial s) i j :=
  Finset.inf'_le _ (Finset.mem_univ (i,j))

noncomputable section
open Set

def parameterValue (r : Row) (X : ℝ) : ℝ :=
  ((SoleNegativeTScalarModel.left r:ℝ)+(SoleNegativeTScalarModel.right r:ℝ))/2+
    ((SoleNegativeTScalarModel.right r:ℝ)-(SoleNegativeTScalarModel.left r:ℝ))/2*X

def inputs (s : Case) (t : ℝ) : Fin 11 → ℝ :=
  ![t,0,Real.sin (x (scalar s) t 0),Real.cos (x (scalar s) t 0),0,1,
    Real.sin (e (scalar s) t 0),Real.cos (e (scalar s) t 0),
    Real.sin (SoleNegativeTScalarModel.angle s.row t),Real.cos (SoleNegativeTScalarModel.angle s.row t),
    Real.sin (e (scalar s) t 0/2)]

theorem parameter_mem (r : Row) {X : ℝ} (hX : |X|≤1) :
    parameterValue r X∈SoleNegativeTScalarModel.domain r := by
  have h := abs_le.mp hX
  cases r <;> norm_num [parameterValue,SoleNegativeTScalarModel.domain,
    SoleNegativeTScalarModel.left,SoleNegativeTScalarModel.right] <;>
    constructor <;> linarith [h.1,h.2]

theorem parameter_contains (r : Row) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    Contains (parameter r) X Y (parameterValue r X) := by
  have hh := (contains_constant
    ((SoleNegativeTScalarModel.left r+SoleNegativeTScalarModel.right r)/2) X Y).add
      ((contains_constant
        ((SoleNegativeTScalarModel.right r-SoleNegativeTScalarModel.left r)/2) X Y).mul
          (contains_outer X Y) hX hY)
  simpa [parameter,parameterValue] using hh

theorem variables_contain (s : Case) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    ∀ i,Contains (variables s i) X Y (inputs s (parameterValue s.row X) i) := by
  let t := parameterValue s.row X
  have ht := parameter_mem s.row hX
  have hf := family_mem ht
  have htz := angles ht
  have hz : (0:ℝ)∈Icc 0 t := ⟨le_rfl,htz.1.1⟩
  have htc : Contains (parameter s.row) X Y t := parameter_contains s.row hX hY
  have hxc : Contains (xParameter s) X Y (x (scalar s) t 0) := by
    cases hb : s.atG
    · simpa [xParameter,x,scalar,hb] using contains_constant 0 X Y
    · simpa [xParameter,x,scalar,hb] using htc
  have hec : Contains (eParameter s) X Y (e (scalar s) t 0) := by
    cases hb : s.atG
    · simpa [eParameter,e,scalar,hb] using htc
    · simpa [eParameter,e,scalar,hb] using contains_constant 0 X Y
  have hwc : Contains (angleParameter s) X Y (SoleNegativeTScalarModel.angle s.row t) := by
    dsimp [angleParameter,SoleNegativeTScalarModel.angle]
    split_ifs
    · exact htc.sub (contains_constant (3/10) X Y)
    · exact contains_constant 0 X Y
  have hx := (split_angles (scalar s) hf hz).2.1
  have he := (split_angles (scalar s) hf hz).2.2
  have hhalf : e (scalar s) t 0/2∈Icc 0 frameCap :=
    ⟨by linarith [he.1],by linarith [he.1,he.2]⟩
  have hhc := (hec.mul (contains_constant (1/2) X Y) hX hY).sine hX hY
    (by simpa only [div_eq_mul_inv] using hhalf)
  intro i
  fin_cases i
  · simpa [variables,inputs] using htc
  · simpa [variables,inputs] using contains_constant 0 X Y
  · simpa [variables,inputs] using hxc.sine hX hY hx
  · simpa [variables,inputs] using hxc.cosine hX hY hx
  · simpa [variables,inputs] using contains_constant 0 X Y
  · simpa [variables,inputs] using contains_constant 1 X Y
  · simpa [variables,inputs] using hec.sine hX hY he
  · simpa [variables,inputs] using hec.cosine hX hY he
  · simpa [variables,inputs] using hwc.sine hX hY htz.2.1
  · simpa [variables,inputs] using hwc.cosine hX hY htz.2.1
  · simpa [variables,inputs,div_eq_mul_inv] using hhc

theorem model_positive (s : Case) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    0<Expression.value (inputs s (parameterValue s.row X)) (expression s) := by
  have hp := TensorWholeIntervalBernstein.lower_on_square (polynomial_identity s) partition
    (lower_le s) hX hY
  have hc := Expression.contains (expression s) (variables_contain s hX hY) hX hY
  have hr : ((enclosure s).error:ℝ)<(lower s:ℝ) := by exact_mod_cast reserve s
  have hb := (abs_le.mp hc.2).1
  change -((enclosure s).error:ℝ)≤_ at hb
  change (lower s:ℝ)≤evaluate X Y (enclosure s).polynomial at hp
  linarith

end SquaresInCircles.Eight.TableFree.SoleNegativeTPolynomials
