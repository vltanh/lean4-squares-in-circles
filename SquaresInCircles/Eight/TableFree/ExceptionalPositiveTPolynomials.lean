module

public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTScalarModel
public import SquaresInCircles.Eight.TableFree.TensorPolynomialEnclosure
public import SquaresInCircles.Eight.TableFree.TensorWholeIntervalBernstein

/-!
# Whole-square scalar formulas for an unaligned E contact and positive T

Uncompiled transcription of the outside-critical-strip certificate. Each
of the four intrinsic intervals is mapped to one complete square, with
z=t(1+Y)/2. The additional H choice is precisely the p charge required by
the unaligned actual EH witness. All roots use the displayed septic
majorant and the same total-degree-14 arithmetic as the hand proof.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTPolynomials
open TensorPolynomialEnclosure TensorWholeIntervalPolynomial
open ExceptionalPositiveTScalarModel

abbrev Expr := Expression (Fin 10)
abbrev lit (r : ℚ) : Expr := .literal r
abbrev var (i : Fin 10) : Expr := .variable i

def tE : Expr := var 0
def zE : Expr := var 1
def sx : Expr := var 2
def cx : Expr := var 3
def sz : Expr := var 4
def cz : Expr := var 5
def se : Expr := var 6
def ce : Expr := var 7
def st : Expr := var 8
def ct : Expr := var 9

def KE : Family → Expr
  | .lowZero | .lowAfter => lit (17253/20000)+lit (67/100)*tE+lit (27/100)*tE^2
  | .middle | .high => 1
def LE : Family → Expr
  | .lowZero | .lowAfter => lit (50521/100000)+lit (21/25)*tE+tE^2*lit (1/2)
  | .middle => lit (551/1000)+lit (67/100)*tE+lit (21/100)*tE^2
  | .high => lit (7/10)+lit (8/25)*tE
def CE : Family → Expr
  | .lowZero | .lowAfter => lit (17253/20000)+lit (18/25)*tE+lit (3/10)*tE^2
  | .middle => lit (891/1000)+lit (16/25)*tE+tE^2*lit (1/50)
  | .high => lit (113/100)
def etaE : Family → Expr
  | .lowZero | .lowAfter => lit (131/500)+lit (19/100)*tE+lit (2/25)*tE^2
  | .middle => lit (61/200)-tE*lit (1/50)+lit (7/200)*tE^2
  | .high => lit (27/100)+lit (2/25)*tE
def kE (f : Family) : Expr := KE f+lit (3/50)*zE
def ellE (f : Family) : Expr := LE f-lit (23/100)*zE
def cE (f : Family) : Expr := CE f-lit (53/100)*zE
def nE (s : ScalarCase) : Expr := kE s.family*(cx+etaE s.family*sx)
def mE (s : ScalarCase) : Expr := cE s.family*(cz+etaE s.family*sz)
def pE (s : ScalarCase) : Expr := ce+etaE s.family*se
def firstE (s : ScalarCase) : Fin 4 → Expr := ![pE s,kE s.family,ellE s.family,1]
def secondE (s : ScalarCase) : Fin 4 → Expr :=
  ![nE s,ellE s.family,if s.td then mE s else cE s.family,
    if s.td then cE s.family else mE s]
def nuE (s : ScalarCase) : Expr :=
  ![if s.hCoefficient then pE s else nE s,ellE s.family,
    if s.td then mE s+(if s.family=.high then lit (3/100) else 0) else ellE s.family,
    if s.td then cE s.family else mE s] s.negative
def squareE (s : ScalarCase) (i : Fin 4) : Expr :=
  firstE s i^2+secondE s i^2-
    if i=s.negative then 2*firstE s i*secondE s i*st else 0
def rootSquare (s : ScalarCase) (i : Fin 5) : Expr :=
  if hi : i.val<4 then squareE s ⟨i.val,hi⟩ else 1+etaE s.family^2

def parameter (f : Family) : Enclosure :=
  add (constant ((left f+right f)/2))
    (mul (constant ((right f-left f)/2)) outerVariable)
def secondParameter (f : Family) : Enclosure :=
  mul (mul (parameter f) (add (constant 1) innerVariable)) (constant (1/2))
def xParameter (s : ScalarCase) : Enclosure :=
  if s.atG then sub (parameter s.family) (secondParameter s.family) else constant 0
def eParameter (s : ScalarCase) : Enclosure :=
  if s.atG then constant 0 else sub (parameter s.family) (secondParameter s.family)
def variables (s : ScalarCase) : Fin 10 → Enclosure :=
  ![parameter s.family,secondParameter s.family,sine (xParameter s),cosine (xParameter s),
    sine (secondParameter s.family),cosine (secondParameter s.family),
    sine (eParameter s),cosine (eParameter s),sine (parameter s.family),
    cosine (parameter s.family)]
def rootExpression (s : ScalarCase) (i : Fin 5) : Expr :=
  Expression.sqrtUpper (variables s) (rootSquare s i)
def baseExpression (s : ScalarCase) : Expr :=
  kE s.family*(1+2*cx+(1+2*etaE s.family)*sx)+
    cE s.family*(1+2*cz+(1+2*etaE s.family)*sz)+2*ellE s.family+
    1+2*ce+(1+2*etaE s.family)*se-
    lit radiusUpper*(kE s.family*sx+cE s.family*sz+se)*rootExpression s 4
def expression (s : ScalarCase) : Expr :=
  ((((baseExpression s+nuE s*(ct-1))-
    lit radiusUpper*rootExpression s 0)-lit radiusUpper*rootExpression s 1)-
      lit radiusUpper*rootExpression s 2)-lit radiusUpper*rootExpression s 3
def enclosure (s : ScalarCase) : Enclosure := Expression.enclose (variables s) (expression s)
def polynomial (s : ScalarCase) : Bivar := (enclosure s).polynomial

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem seeds_positive (s : ScalarCase) (i : Fin 5) :
    0<rootSeed (Expression.enclose (variables s) (rootSquare s i)) := by
  rcases s with ⟨f,td,atG,j,h⟩
  cases f <;> cases td <;> cases atG <;> fin_cases j <;> cases h <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem polynomial_identity (s : ScalarCase) :
    polynomial s=TensorWholeIntervalBernstein.expansion 16 (polynomial s) := by
  rcases s with ⟨f,td,atG,j,h⟩
  cases f <;> cases td <;> cases atG <;> fin_cases j <;> cases h <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem basis_partition :
    (∑ i : Fin 17,∑ j : Fin 17,TensorWholeIntervalBernstein.basis 16 i j)=1 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_reserve (s : ScalarCase) (i j : Fin 17) :
    (13/100000:ℚ)<TensorWholeIntervalBernstein.coefficient 16 (polynomial s) i j := by
  rcases s with ⟨f,td,atG,k,h⟩
  cases f <;> cases td <;> cases atG <;> fin_cases k <;> cases h <;>
    fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem error_reserve (s : ScalarCase) :
    0≤(enclosure s).error ∧ (enclosure s).error<53/1000000 := by
  rcases s with ⟨f,td,atG,j,h⟩
  cases f <;> cases td <;> cases atG <;> fin_cases j <;> cases h <;> decide

noncomputable section

def parameterValue (f : Family) (X : ℝ) : ℝ :=
  ((left f:ℝ)+(right f:ℝ))/2+((right f:ℝ)-(left f:ℝ))/2*X
def secondValue (f : Family) (X Y : ℝ) : ℝ := parameterValue f X*(1+Y)/2
def inputs (s : ScalarCase) (t z : ℝ) : Fin 10 → ℝ :=
  ![t,z,Real.sin (x s t z),Real.cos (x s t z),Real.sin z,Real.cos z,
    Real.sin (e s t z),Real.cos (e s t z),Real.sin t,Real.cos t]

theorem parameter_mem (f : Family) {X : ℝ} (hX : |X|≤1) :
    parameterValue f X∈domain f := by
  have h := abs_le.mp hX
  cases f <;> norm_num [parameterValue,domain,left,right] <;>
    constructor <;> linarith [h.1,h.2]
theorem second_mem (f : Family) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    secondValue f X Y∈Set.Icc 0 (parameterValue f X) := by
  have ht := (angle (parameter_mem f hX)).1
  have hy := abs_le.mp hY
  have hp := mul_nonneg ht (show 0≤1+Y by linarith)
  have hu := mul_nonneg ht (show 0≤1-Y by linarith)
  dsimp [secondValue]
  constructor <;> nlinarith
theorem parameter_contains (f : Family) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    Contains (parameter f) X Y (parameterValue f X) := by
  have h := (contains_constant ((left f+right f)/2) X Y).add
    ((contains_constant ((right f-left f)/2) X Y).mul (contains_outer X Y) hX hY)
  simpa [parameter,parameterValue] using h
theorem variables_contain (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    ∀ i,Contains (variables s i) X Y
      (inputs s (parameterValue s.family X) (secondValue s.family X Y) i) := by
  let t := parameterValue s.family X
  let z := secondValue s.family X Y
  have ht := parameter_mem s.family hX
  have hz := second_mem s.family hX hY
  have htc : Contains (parameter s.family) X Y t := parameter_contains s.family hX hY
  have hzc : Contains (secondParameter s.family) X Y z := by
    have h := (htc.mul ((contains_constant 1 X Y).add (contains_inner X Y)) hX hY).mul
      (contains_constant (1/2) X Y) hX hY
    simpa [secondParameter,secondValue,z,t,div_eq_mul_inv] using h
  have hxc : Contains (xParameter s) X Y (x s t z) := by
    dsimp [xParameter,x]
    split_ifs
    · exact htc.sub hzc
    · exact contains_constant 0 X Y
  have hec : Contains (eParameter s) X Y (e s t z) := by
    dsimp [eParameter,e]
    split_ifs
    · exact contains_constant 0 X Y
    · exact htc.sub hzc
  obtain ⟨hz',hx,he⟩ := split_angles s ht hz
  intro i
  fin_cases i
  · simpa [variables,inputs] using htc
  · simpa [variables,inputs] using hzc
  · simpa [variables,inputs] using hxc.sine hX hY hx
  · simpa [variables,inputs] using hxc.cosine hX hY hx
  · simpa [variables,inputs] using hzc.sine hX hY hz'
  · simpa [variables,inputs] using hzc.cosine hX hY hz'
  · simpa [variables,inputs] using hec.sine hX hY he
  · simpa [variables,inputs] using hec.cosine hX hY he
  · simpa [variables,inputs] using htc.sine hX hY (angle ht)
  · simpa [variables,inputs] using htc.cosine hX hY (angle ht)

theorem model_positive (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    (77/1000000:ℝ)<Expression.value
      (inputs s (parameterValue s.family X) (secondValue s.family X Y)) (expression s) := by
  have hp := TensorWholeIntervalBernstein.lower_on_square (polynomial_identity s)
    basis_partition (fun i j => (coefficient_reserve s i j).le) hX hY
  have hc := Expression.contains (expression s) (variables_contain s hX hY) hX hY
  have he : ((enclosure s).error:ℝ)<(53/1000000:ℝ) := by
    exact_mod_cast (error_reserve s).2
  have hb := (abs_le.mp hc.2).1
  change -((enclosure s).error:ℝ)≤_ at hb
  change (13/100000:ℝ)≤evaluate X Y (enclosure s).polynomial at hp
  nlinarith

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTPolynomials
