module

public import SquaresInCircles.Eight.TableFree.SoleTScalarModel
public import SquaresInCircles.Eight.TableFree.TensorPolynomialEnclosure
public import SquaresInCircles.Eight.TableFree.TensorWholeIntervalBernstein

/-!
# Whole-square rational formulas for positive T and a sole E primary

Uncompiled source. Each intrinsic family interval is parameterized by
one full square, with `z=t(1+Y)/2`. The only finite choices are the five
coefficient families, the two actual T rows, the two primary-split
endpoints and the four negative indices. Every coefficient reserve is
an exact rational reduction of the displayed expression recipe.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SolePositiveTPolynomials
open TensorPolynomialEnclosure TensorWholeIntervalPolynomial
open SoleTScalarModel

abbrev Expr := Expression (Fin 11)
abbrev lit (r : ℚ) : Expr := .literal r
abbrev var (i : Fin 11) : Expr := .variable i

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
def shalf : Expr := var 10

def KE : Family → Expr
  | .ehLow => lit (17253/20000)+lit (11/20)*tE+lit (3/10)*tE^2
  | .ehMiddle => lit (983/1000)+lit (1/10)*(tE-lit (1/5))-lit (3/10)*(tE-lit (1/5))^2
  | .ehHigh => lit (1017/1000)-lit (1/50)*tE
  | .deLow => lit (53/50)-lit (1/10)*tE
  | .deHigh => lit (107/100)-lit (3/25)*tE

def LE : Family → Expr
  | .ehLow => lit (50521/100000)+lit (823/1000)*tE+lit (7/10)*tE^2
  | .ehMiddle => lit (349/500)+lit (9/10)*(tE-lit (1/5))-(tE-lit (1/5))^2
  | .ehHigh => lit (7/10)+lit (9/25)*tE
  | .deLow => lit (113/200)+lit (3/4)*tE
  | .deHigh => lit (77/100)+lit (1/5)*tE

def CE : Family → Expr
  | .ehLow => KE .ehLow+lit (3/10)*tE
  | .ehMiddle => lit (209/200)+lit (13/20)*(tE-lit (1/5))-lit (3/2)*(tE-lit (1/5))^2
  | .ehHigh | .deHigh => lit (113/100)
  | .deLow => lit (903/1000)+lit (13/20)*tE

def gE : Family → Expr
  | .ehLow | .deLow => lit (8/25)
  | .ehMiddle => lit (31/100)
  | .ehHigh => lit (27/100)+lit (2/25)*tE
  | .deHigh => lit (3/10)+lit (1/20)*tE

def epsilonE : Family → Expr
  | .ehLow => lit (131/500)+lit (267/1000)*tE+lit (1/10)*tE^2
  | .ehMiddle => lit (319/1000)+lit (1/5)*(tE-lit (1/5))
  | _ => 0

def kE (f : Family) : Expr := KE f+lit (3/50)*zE
def ellE (f : Family) : Expr := LE f-lit (23/100)*zE
def cE (f : Family) : Expr := CE f-lit (53/100)*zE
def etaE : Expr := lit (1/4)+lit (33/100)*tE
def lambdaE (f : Family) : Expr := if isDE f then lit (5/4) else 1
def nE (s : ScalarCase) : Expr := kE s.family*(cx+gE s.family*sx)
def mE (s : ScalarCase) : Expr := cE s.family*(cz+etaE*sz)
def pE (s : ScalarCase) : Expr := if tiltedE s.family then ce+epsilonE s.family*se else 1

def firstE (s : ScalarCase) : Fin 4 → Expr :=
  ![lambdaE s.family,kE s.family,ellE s.family,pE s]
def secondE (s : ScalarCase) : Fin 4 → Expr :=
  ![nE s,ellE s.family,if s.td then mE s else cE s.family,
    if s.td then cE s.family else mE s]
def nuE (s : ScalarCase) : Expr :=
  ![if isDE s.family then lit (5/4) else nE s,ellE s.family,
    if s.td then mE s else ellE s.family,lit (1131/1000)] s.negative

def squareE (s : ScalarCase) (i : Fin 4) : Expr :=
  firstE s i^2+secondE s i^2-
    if i=s.negative then 2*firstE s i*secondE s i*st else 0

def rootSquare (s : ScalarCase) (i : Fin 7) : Expr :=
  if hi : i.val<4 then squareE s ⟨i.val,hi⟩
  else if i.val=4 then 1+gE s.family^2
  else if i.val=5 then 1+etaE^2 else 1+epsilonE s.family^2

def parameter (f : Family) : Enclosure :=
  add (constant ((left f+right f)/2))
    (mul (constant ((right f-left f)/2)) outerVariable)

def secondParameter (f : Family) : Enclosure :=
  mul (mul (parameter f) (add (constant 1) innerVariable)) (constant (1/2))

def xParameter (s : ScalarCase) : Enclosure :=
  if s.atG then sub (parameter s.family) (secondParameter s.family) else constant 0

def eParameter (s : ScalarCase) : Enclosure :=
  if s.atG then constant 0 else sub (parameter s.family) (secondParameter s.family)

def variables (s : ScalarCase) : Fin 11 → Enclosure :=
  ![parameter s.family,secondParameter s.family,sine (xParameter s),cosine (xParameter s),
    sine (secondParameter s.family),cosine (secondParameter s.family),
    sine (eParameter s),cosine (eParameter s),sine (parameter s.family),
    cosine (parameter s.family),sine (mul (eParameter s) (constant (1/2)))]

def rootExpression (s : ScalarCase) (i : Fin 7) : Expr :=
  Expression.sqrtUpper (variables s) (rootSquare s i)

def baseExpression (s : ScalarCase) : Expr :=
  kE s.family*(1+2*cx+(1+2*gE s.family)*sx)+
    cE s.family*(1+2*cz+(1+2*etaE)*sz)+2*ellE s.family-
    lit radiusUpper*(kE s.family*sx*rootExpression s 4+
      cE s.family*sz*rootExpression s 5)

def eExpression (s : ScalarCase) : Expr :=
  if tiltedE s.family then
    1+2*ce+(1+2*epsilonE s.family)*se-lit radiusUpper*se*rootExpression s 6
  else if isDE s.family then
    1+lit (1/2)*ce+lit (1-axisUpper)*se+lit (3/2)*lit (5/4)
  else 3+se-lit (2*radiusUpper)*shalf

def expression (s : ScalarCase) : Expr :=
  ((((baseExpression s+eExpression s+nuE s*(ct-1))-
    lit radiusUpper*rootExpression s 0)-lit radiusUpper*rootExpression s 1)-
      lit radiusUpper*rootExpression s 2)-lit radiusUpper*rootExpression s 3

def enclosure (s : ScalarCase) : Enclosure := Expression.enclose (variables s) (expression s)
def polynomial (s : ScalarCase) : Bivar := (enclosure s).polynomial

/- Exact reductions of one expression recipe. No precomputed coefficient
array, angle subdivision, or external arithmetic result is imported. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem seeds_positive (s : ScalarCase) (i : Fin 7) :
    0<rootSeed (Expression.enclose (variables s) (rootSquare s i)) := by
  rcases s with ⟨f,td,atG,j⟩
  cases f <;> cases td <;> cases atG <;> fin_cases j <;> fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem polynomial_identity (s : ScalarCase) :
    polynomial s=TensorWholeIntervalBernstein.expansion 16 (polynomial s) := by
  rcases s with ⟨f,td,atG,j⟩
  cases f <;> cases td <;> cases atG <;> fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem basis_partition :
    (∑ i : Fin 17,∑ j : Fin 17,TensorWholeIntervalBernstein.basis 16 i j)=1 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_reserve (s : ScalarCase) (i j : Fin 17) :
    (1/6250:ℚ)<TensorWholeIntervalBernstein.coefficient 16 (polynomial s) i j := by
  rcases s with ⟨f,td,atG,k⟩
  cases f <;> cases td <;> cases atG <;> fin_cases k <;> fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem error_reserve (s : ScalarCase) :
    0≤(enclosure s).error ∧ (enclosure s).error<7/500000 := by
  rcases s with ⟨f,td,atG,j⟩
  cases f <;> cases td <;> cases atG <;> fin_cases j <;> decide

noncomputable section

def parameterValue (f : Family) (X : ℝ) : ℝ :=
  ((left f:ℝ)+(right f:ℝ))/2+((right f:ℝ)-(left f:ℝ))/2*X
def secondValue (f : Family) (X Y : ℝ) : ℝ := parameterValue f X*(1+Y)/2

def inputs (s : ScalarCase) (t z : ℝ) : Fin 11 → ℝ :=
  ![t,z,Real.sin (x s t z),Real.cos (x s t z),Real.sin z,Real.cos z,
    Real.sin (e s t z),Real.cos (e s t z),Real.sin t,Real.cos t,Real.sin (e s t z/2)]

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
  have htc : Contains (parameter s.family) X Y t := by
    have h := (contains_constant ((left s.family+right s.family)/2) X Y).add
      ((contains_constant ((right s.family-left s.family)/2) X Y).mul
        (contains_outer X Y) hX hY)
    simpa [parameter,parameterValue,t] using h
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
  have hhalf : e s t z/2∈Set.Icc 0 frameCap :=
    ⟨by linarith [he.1],by linarith [he.1,he.2]⟩
  have hh := (hec.mul (contains_constant (1/2) X Y) hX hY).sine hX hY
    (by simpa [div_eq_mul_inv] using hhalf)
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
  · simpa [variables,inputs,div_eq_mul_inv] using hh

theorem model_positive (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    (1/10000:ℝ)<Expression.value
      (inputs s (parameterValue s.family X) (secondValue s.family X Y)) (expression s) := by
  have hp := TensorWholeIntervalBernstein.lower_on_square (polynomial_identity s)
    basis_partition (fun i j => (coefficient_reserve s i j).le) hX hY
  have hc := Expression.contains (expression s) (variables_contain s hX hY) hX hY
  have he : ((enclosure s).error:ℝ)<(7/500000:ℝ) := by
    exact_mod_cast (error_reserve s).2
  have hb := (abs_le.mp hc.2).1
  change -((enclosure s).error:ℝ)≤_ at hb
  change (1/6250:ℝ)≤evaluate X Y (enclosure s).polynomial at hp
  norm_num at hp
  nlinarith

end SquaresInCircles.Eight.TableFree.SolePositiveTPolynomials
