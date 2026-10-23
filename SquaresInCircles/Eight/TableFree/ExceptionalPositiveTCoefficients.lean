module

public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTScalar

/-!
# Coefficient correlations for the actual positive-T contact blocks

Uncompiled source. This is the full-square range recipe in section 8
of the outside-strip proof, with the H ratio required by the unaligned
contact. Every comparison is an exact rational polynomial reduction;
the choices are coefficient families and physical block indices.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTCoefficients
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
  deriving DecidableEq, Fintype
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
  Expression.enclose (variables (canonical s)) (test (canonical s) j)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem identity (f : Family) (td atG : Bool) (j : Test) :
    (testEnclosure ⟨f,td,atG,0,false⟩ j).polynomial=
      TensorWholeIntervalBernstein.expansion 16 (testEnclosure ⟨f,td,atG,0,false⟩ j).polynomial := by
  cases f <;> cases td <;> cases atG <;> cases j <;>
    first | decide | (rename_i i; fin_cases i <;> decide)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem reserve (f : Family) (td atG : Bool) (j : Test) :
    ∀ i k : Fin 17,(testEnclosure ⟨f,td,atG,0,false⟩ j).error≤
      TensorWholeIntervalBernstein.coefficient 16
        (testEnclosure ⟨f,td,atG,0,false⟩ j).polynomial i k := by
  cases f <;> cases td <;> cases atG <;> cases j <;>
    first | decide | (rename_i i; fin_cases i <;> decide)

noncomputable section
open ExceptionalPositiveTScalar

def ratio (f : Family) (t : ℝ) (i : Fin 4) : ℝ :=
  match f with
  | .lowZero | .lowAfter => if i=0 then 41/50
      else if i=2 then 117/200+1/5*t else 117/200
  | .middle => if i=1 then 31/50 else if i=2 then 2/3 else 71/100
  | .high => 71/100
@[simp] theorem ratioE_value (s : ScalarCase) (f : Family) (t z : ℝ) (i : Fin 4) :
    Expression.value (inputs s t z) (ratioE f i)=ratio f t i := by
  cases f <;> simp [ratioE,ratio,Expression.value,tE,inputs]

theorem tests_nonnegative (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (j : Test) :
    0≤Expression.value (inputs s t z) (test s j) := by
  obtain ⟨X,Y,hX,hY,htX,hzY⟩ := square_coordinates s ht hz
  have hc := Expression.contains (test (canonical s) j)
    (variables_contain (canonical s) hX hY) hX hY
  have hp := TensorWholeIntervalBernstein.lower_on_square
    (identity s.family s.td s.atG j) basis_partition
    (reserve s.family s.td s.atG j) hX hY
  have hb := (abs_le.mp hc.2).1
  have hinput : inputs (canonical s) t z=inputs s t z := rfl
  have htest : test (canonical s) j=test s j := by cases j <;> rfl
  have htX' : parameterValue (canonical s).family X=t := htX
  have hzY' : secondValue (canonical s).family X Y=z := hzY
  rw [htX',hzY',hinput,htest] at hb
  change ((testEnclosure s j).error:ℝ)≤
    evaluate X Y (testEnclosure s j).polynomial at hp
  change -((testEnclosure s j).error:ℝ)≤
    Expression.value (inputs s t z) (test s j)-
      evaluate X Y (testEnclosure s j).polynomial at hb
  linarith

theorem ratio_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    ratio s.family t i*max (first s t z i) (second s t z i)≤
      min (first s t z i) (second s t z i) := by
  have h1 := tests_nonnegative s ht hz (.ratioFirst i)
  have h2 := tests_nonnegative s ht hz (.ratioSecond i)
  simp only [test,Expression.value,firstE_value,secondE_value,ratioE_value] at h1 h2
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
  simp only [test,Expression.value,firstE_value,secondE_value] at h1 h2
  exact max_le (by linarith) (by linarith)
theorem larger_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    (largeFloor s.family:ℝ)≤max (first s t z i) (second s t z i) := by
  have h := tests_nonnegative s ht hz (.larger i)
  simp only [test,witnessE,Expression.value] at h
  split_ifs at h
  · rw [secondE_value] at h
    exact (by linarith : (largeFloor s.family:ℝ)≤second s t z i).trans (le_max_right _ _)
  · rw [firstE_value] at h
    exact (by linarith : (largeFloor s.family:ℝ)≤first s t z i).trans (le_max_left _ _)
theorem smaller_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    (smallFloor s.family i:ℝ)≤min (first s t z i) (second s t z i) := by
  have h1 := tests_nonnegative s ht hz (.smallerFirst i)
  have h2 := tests_nonnegative s ht hz (.smallerSecond i)
  simp only [test,Expression.value,firstE_value,secondE_value] at h1 h2
  exact le_min (by linarith) (by linarith)
theorem scalar_B_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    max (ell s.family t z) (m s t z)≤m s t z+(if s.family=.high then 3/100 else 0) := by
  have h := tests_nonnegative s ht hz .mixedB
  simp [test,Expression.value] at h
  apply max_le (by linarith)
  split_ifs <;> linarith
theorem middle_A (s : ScalarCase) {t z : ℝ} (hf : s.family=.middle)
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    (159/250:ℝ)≤ell s.family t z ∧ ell s.family t z≤(203/250)*k s.family t z := by
  have h1 := tests_nonnegative s ht hz .middleALower
  have h2 := tests_nonnegative s ht hz .middleAUpper
  simp [test,hf,Expression.value] at h1 h2
  exact ⟨by linarith,by linarith⟩
theorem half_ratio (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    max (first s t z i) (second s t z i)≤2*min (first s t z i) (second s t z i) := by
  have hr := ratio_lower s ht hz i
  have hpos := (weights_positive s ht hz).2.2.2.1 i
  have hmax : 0<max (first s t z i) (second s t z i) := hpos.trans_le (le_max_left _ _)
  have hratio : (1/2:ℝ)≤ratio s.family t i := by
    have ht0 := (angle ht).1
    cases s.family <;> dsimp [ratio] <;> split_ifs <;> linarith
  have hh := mul_le_mul_of_nonneg_right hratio hmax.le
  linarith

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTCoefficients
