module

public import Mathlib.Algebra.Order.Ring.Star
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTScalar

/-!
# Eight squares: coefficient correlations of the positive-T contact blocks

The ranges of the coefficients on the whole square, with the H ratio that an unaligned contact
requires (`ratio_lower`, `pair_upper`, `larger_lower`, `smaller_lower`). Every comparison is an
exact polynomial reduction; the cases are the coefficient families and the block indices, and the
thirty-one tests are checked on packed Taylor models (`tests_nonnegative`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTCoefficients
open ExceptionalPositiveTScalarModel ExceptionalPositiveTPolynomials
open TensorPolynomialEnclosure TensorWholeIntervalPolynomial

def cap : Family → ℚ
  | .lowZero | .lowAfter => 21/20
  | .middle => 559/500
  | .high => 1131/1000
def largeFloor : Family → ℚ
  | .lowZero | .lowAfter => 431/500
  | .middle => 911/1000
  | .high => 0
def smallFloor (f : Family) (i : Fin 4) : ℚ :=
  match f with
  | .middle => if i=0 ∨ i=3 then 911/1000 else 0
  | .high => 731/1000
  | _ => 0
def ratioE (f : Family) (i : Fin 4) : Expr :=
  match f with
  | .lowZero | .lowAfter => if i=0 then lit (41/50)
      else if i=2 then lit (117/200)+lit (1/5)*tE else lit (117/200)
  | .middle => if i=1 then lit (31/50) else if i=2 then lit (2/3) else lit (71/100)
  | .high => lit (71/100)
def witnessE (s : ScalarCase) (i : Fin 4) : Expr :=
  if i=0 ∨ i=2 then secondE s i else firstE s i

inductive Test where
  | ratioFirst (i : Fin 4) | ratioSecond (i : Fin 4)
  | upperFirst (i : Fin 4) | upperSecond (i : Fin 4)
  | larger (i : Fin 4) | smallerFirst (i : Fin 4) | smallerSecond (i : Fin 4)
  | middleAUpper | middleALower | mixedB
  deriving DecidableEq

instance : Fintype Test where
  elems := {.middleAUpper, .middleALower, .mixedB} ∪
    Finset.univ.image Test.ratioFirst ∪
    Finset.univ.image Test.ratioSecond ∪
    Finset.univ.image Test.upperFirst ∪
    Finset.univ.image Test.upperSecond ∪
    Finset.univ.image Test.larger ∪
    Finset.univ.image Test.smallerFirst ∪
    Finset.univ.image Test.smallerSecond
  complete x := by cases x <;> simp
def test (s : ScalarCase) : Test → Expr
  | .ratioFirst i => firstE s i-ratioE s.family i*secondE s i
  | .ratioSecond i => secondE s i-ratioE s.family i*firstE s i
  | .upperFirst i => lit (cap s.family)-firstE s i
  | .upperSecond i => lit (cap s.family)-secondE s i
  | .larger i => witnessE s i-lit (largeFloor s.family)
  | .smallerFirst i => firstE s i-lit (smallFloor s.family i)
  | .smallerSecond i => secondE s i-lit (smallFloor s.family i)
  | .middleAUpper => if s.family=.middle then lit (203/250)*kE s.family-ellE s.family else 0
  | .middleALower => if s.family=.middle then ellE s.family-lit (159/250) else 0
  | .mixedB => mE s+(if s.family=.high then lit (3/100) else 0)-ellE s.family
def canonical (s : ScalarCase) : ScalarCase := {s with negative:=0,hCoefficient:=false}
def testEnclosure (s : ScalarCase) (j : Test) : Enclosure :=
  Expression.enclose («variables» (canonical s)) (test (canonical s) j)

theorem identity (f : Family) (td atG : Bool) (j : Test) :
    (testEnclosure ⟨f,td,atG,0,false⟩ j).polynomial=
      TensorWholeIntervalBernstein.expansion 16 (testEnclosure ⟨f,td,atG,0,false⟩ j).polynomial :=
  r54_expansion ((r54_enclose_bounded (r54_variables_bounded _) _).mono (by norm_num))
/-! ### The packed certificate

Each test is mirrored by an `IE` expression, evaluated by the packed Taylor models of
`ExceptionalPositiveTPolynomials`, and the kernel checks that its degree-10 Bernstein coefficients
are nonnegative, in natural-number arithmetic. -/

section packed
open PackedModels

def capI : Family → IExpr
  | .lowZero | .lowAfter => lq 21 20
  | .middle => lq 559 500
  | .high => lq 1131 1000
def largeFloorI : Family → IExpr
  | .lowZero | .lowAfter => lq 431 500
  | .middle => lq 911 1000
  | .high => .lit (.num 0)
def smallFloorI (f : Family) (i : Fin 4) : IExpr :=
  match f with
  | .middle => if i=0 ∨ i=3 then lq 911 1000 else .lit (.num 0)
  | .high => lq 731 1000
  | _ => .lit (.num 0)
def ratioI (f : Family) (i : Fin 4) : IExpr :=
  match f with
  | .lowZero | .lowAfter => if i=0 then lq 41 50
      else if i=2 then lq 117 200+lq 1 5*tI else lq 117 200
  | .middle => if i=1 then lq 31 50 else if i=2 then lq 2 3 else lq 71 100
  | .high => lq 71 100
def witnessI (f : Family) (td : Bool) (i : Fin 4) : IExpr :=
  if i=0 ∨ i=2 then secondI f td i else firstI f i
def testI (f : Family) (td : Bool) : Test → IExpr
  | .ratioFirst i => firstI f i-ratioI f i*secondI f td i
  | .ratioSecond i => secondI f td i-ratioI f i*firstI f i
  | .upperFirst i => capI f-firstI f i
  | .upperSecond i => capI f-secondI f td i
  | .larger i => witnessI f td i-largeFloorI f
  | .smallerFirst i => firstI f i-smallFloorI f i
  | .smallerSecond i => secondI f td i-smallFloorI f i
  | .middleAUpper => if f=.middle then lq 203 250*kI f-ellI f else 0
  | .middleALower => if f=.middle then ellI f-lq 159 250 else 0
  | .mixedB => mI f+(if f=.high then lq 3 100 else 0)-ellI f

theorem testI_eq (f : Family) (td atG : Bool) (j : Test) :
    (testI f td j).toExpressionWith inputFormulas=test ⟨f,td,atG,0,false⟩ j := by
  cases f <;> cases td <;> rcases j with (i|i|i|i|i|i|i|_|_|_) <;> (try fin_cases i) <;> rfl

/-- The thirty-one tests. -/
def allTests : List Test :=
  ([0,1,2,3] : List (Fin 4)).flatMap (fun i => [.ratioFirst i,.ratioSecond i,.upperFirst i,
    .upperSecond i,.larger i,.smallerFirst i,.smallerSecond i])++
    [.middleAUpper,.middleALower,.mixedB]

theorem mem_allTests (j : Test) : j∈allTests := by
  rcases j with (i|i|i|i|i|i|i|_|_|_) <;> (try fin_cases i) <;> decide

/-- The models of the inputs (the roots do not occur). -/
def testModels (f : Family) (atG : Bool) : Fin 10 ⊕ Fin 5 → Model :=
  Sum.elim (inputModels f atG) fun _ => zeroModel config

/-- Everything the kernel checks for one test. -/
def testCheck (f : Family) (td atG : Bool) (j : Test) : Bool :=
  check config 10 (testModels f atG) (testI f td j) 0 1 false && (testI f td j).poly &&
    (testI f td j).seedFree

theorem tests_check (f : Family) (td atG : Bool) : allTests.all (testCheck f td atG)=true := by
  cases f <;> cases td <;> cases atG <;> decide +kernel

theorem reserve (f : Family) (td atG : Bool) (j : Test) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    0≤Expression.value (inputs ⟨f,td,atG,0,false⟩ (parameterValue f X) (secondValue f X Y))
      (test ⟨f,td,atG,0,false⟩ j) := by
  have hc := List.all_eq_true.mp (tests_check f td atG) j (mem_allTests j)
  simp only [testCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨hm,hp⟩,hf⟩ := hc
  set v := inputs ⟨f,td,atG,0,false⟩ (parameterValue f X) (secondValue f X Y)
  have hw : ∀ k,(testModels f atG k).Contains config X Y ((inputFormulas k).value v) := by
    rintro (k|k)
    · exact inputModels_contain ⟨f,td,atG,0,false⟩ hX hY k
    · show (zeroModel config).Contains config X Y (Expression.value v 0)
      rw [value_zero]
      exact zeroModel_contains config X Y
  have h := check_le config_valid hm hX hY hw (IE.seedsOK_of_seedFree _ hf)
  rw [← testI_eq f td atG j,IE.value_toExpressionWith _ _ _ (IE.isPoly_of_poly _ hp)]
  simpa using h

end packed

open ExceptionalPositiveTScalar

section r54_value
variable {ι : Type*} (v : ι → ℝ) (a b : Expression ι)
@[simp] private theorem r54_value_add :
    Expression.value v (a+b)=Expression.value v a+Expression.value v b := rfl
@[simp] private theorem r54_value_neg : Expression.value v (-a)=-Expression.value v a := rfl
@[simp] private theorem r54_value_sub :
    Expression.value v (a-b)=Expression.value v a-Expression.value v b := by
  show Expression.value v a+-Expression.value v b=_
  ring
@[simp] private theorem r54_value_mul :
    Expression.value v (a*b)=Expression.value v a*Expression.value v b := rfl
@[simp] private theorem r54_value_zero : Expression.value v (0 : Expression ι)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  norm_num
@[simp] private theorem r54_value_ite (P : Prop) [Decidable P] :
    Expression.value v (if P then a else b)=
      if P then Expression.value v a else Expression.value v b := by
  split_ifs <;> rfl
end r54_value

@[simp] private theorem r54_value_lit (w : Fin 10 → ℝ) (r : ℚ) :
    Expression.value w (lit r)=(r:ℝ) := rfl
@[simp] private theorem r54_value_var (w : Fin 10 → ℝ) (i : Fin 10) :
    Expression.value w (var i)=w i := rfl
@[simp] private theorem r54_inputs_0 (s : ScalarCase) (t z : ℝ) : inputs s t z 0=t := rfl

def ratio (f : Family) (t : ℝ) (i : Fin 4) : ℝ :=
  match f with
  | .lowZero | .lowAfter => if i=0 then 41/50
      else if i=2 then 117/200+1/5*t else 117/200
  | .middle => if i=1 then 31/50 else if i=2 then 2/3 else 71/100
  | .high => 71/100
@[simp] theorem ratioE_value (s : ScalarCase) (f : Family) (t z : ℝ) (i : Fin 4) :
    Expression.value (inputs s t z) (ratioE f i)=ratio f t i := by
  cases f <;> simp [ratioE,ratio,tE]

theorem tests_nonnegative (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (j : Test) :
    0≤Expression.value (inputs s t z) (test s j) := by
  obtain ⟨X,Y,hX,hY,htX,hzY⟩ := square_coordinates s ht hz
  have h := reserve s.family s.td s.atG j hX hY
  have hinput : inputs ⟨s.family,s.td,s.atG,0,false⟩ t z=inputs s t z := rfl
  have htest : test ⟨s.family,s.td,s.atG,0,false⟩ j=test s j := by cases j <;> rfl
  rw [htX,hzY,hinput,htest] at h
  exact h

theorem ratio_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    ratio s.family t i*max (first s t z i) (second s t z i)≤
      min (first s t z i) (second s t z i) := by
  have h1 := tests_nonnegative s ht hz (.ratioFirst i)
  have h2 := tests_nonnegative s ht hz (.ratioSecond i)
  simp only [test,r54_value_sub,r54_value_mul,firstE_value,secondE_value,ratioE_value] at h1 h2
  rcases le_total (first s t z i) (second s t z i) with h | h
  · rw [max_eq_right h,min_eq_left h]
    linarith
  · rw [max_eq_left h,min_eq_right h]
    linarith
theorem pair_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    max (first s t z i) (second s t z i)≤(cap s.family:ℝ) := by
  have h1 := tests_nonnegative s ht hz (.upperFirst i)
  have h2 := tests_nonnegative s ht hz (.upperSecond i)
  simp only [test,r54_value_sub,r54_value_lit,firstE_value,secondE_value] at h1 h2
  exact max_le (by linarith) (by linarith)
theorem larger_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    (largeFloor s.family:ℝ)≤ max (first s t z i) (second s t z i) := by
  have h := tests_nonnegative s ht hz (.larger i)
  simp only [test,witnessE,r54_value_sub,r54_value_lit,r54_value_ite] at h
  split_ifs at h
  · rw [secondE_value] at h
    exact (by linarith : (largeFloor s.family:ℝ) ≤ second s t z i).trans (le_max_right _ _)
  · rw [firstE_value] at h
    exact (by linarith : (largeFloor s.family:ℝ) ≤ first s t z i).trans (le_max_left _ _)
theorem smaller_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    (smallFloor s.family i:ℝ)≤ min (first s t z i) (second s t z i) := by
  have h1 := tests_nonnegative s ht hz (.smallerFirst i)
  have h2 := tests_nonnegative s ht hz (.smallerSecond i)
  simp only [test,r54_value_sub,r54_value_lit,firstE_value,secondE_value] at h1 h2
  exact le_min (by linarith) (by linarith)
theorem scalar_B_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    max (ell s.family t z) (m s t z)≤ m s t z+(if s.family=.high then 3/100 else 0) := by
  have h := tests_nonnegative s ht hz .mixedB
  simp [test] at h
  apply max_le (by linarith)
  split_ifs <;> linarith
theorem middle_A (s : ScalarCase) {t z : ℝ} (hf : s.family=.middle)
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    (159/250:ℝ)≤ell s.family t z ∧ ell s.family t z≤(203/250)*k s.family t z := by
  have h1 := tests_nonnegative s ht hz .middleALower
  have h2 := tests_nonnegative s ht hz .middleAUpper
  simp [test,hf] at h1 h2
  rw [hf]
  exact ⟨by linarith,by linarith⟩
theorem half_ratio (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    max (first s t z i) (second s t z i)≤2*min (first s t z i) (second s t z i) := by
  have hr := ratio_lower s ht hz i
  have hpos := (weights_positive s ht hz).2.2.2.1 i
  have hmax : 0 < max (first s t z i) (second s t z i) := hpos.trans_le (le_max_left _ _)
  have hratio : (1/2:ℝ)≤ratio s.family t i := by
    have ht0 := (angle ht).1
    cases s.family <;> dsimp [ratio] <;> first | (split_ifs <;> linarith) | linarith
  have hh := mul_le_mul_of_nonneg_right hratio hmax.le
  linarith

end SquaresInCircles.Eight.ExceptionalPositiveTCoefficients
