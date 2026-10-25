module

public import SquaresInCircles.Eight.Owners.Sole.NormGain

/-!
# Eight squares: the negative-T endpoint scalars at the common radius

Every radical majorant holds on the whole range, and every polynomial coefficient that is dropped
is counted in the error of the enclosure (`model_le_actual`). The intervals, both endpoints
included, are mapped onto the whole parameter square (`parameter_surjective`), and the scalars are
positive at every common radius `q ≤ qTrial` (`actual_radius_positive`). These are scalar
statements; no geometry of a negative T enters.
-/

section
/-!
## Whole-interval enclosure formulas for all negative-T scalar endpoints

The same global septic radical majorant and rigorous
polynomial arithmetic used for positive T are applied to the 34 intrinsic
one-dimensional cases. The polynomial is elevated to Bernstein degree 32
on its entire interval; the second tensor variable is unused. The exact
coefficient and error comparisons are decided by the kernel (`row_check`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleNegativeTPolynomials
section r63_bernstein
open Polynomial Finset TensorWholeIntervalPolynomial

/-! Degree-`D` Bernstein re-expansion of a bivariate polynomial whose degrees in both
variables are at most `D`, and the degree bound `14` of every enclosure polynomial. -/

section generic
variable {R : Type*} [CommRing R]

end generic

/-! Every enclosure polynomial has degree at most 14 in each variable. -/

end r63_bernstein

section r63_constant
open Polynomial TensorWholeIntervalPolynomial TensorPolynomialEnclosure

/-- The constant coefficient of a tensor polynomial. -/
private def r63κ : Bivar →+* ℚ :=
  (Polynomial.constantCoeff : ℚ[X] →+* ℚ).comp (Polynomial.constantCoeff : Bivar →+* ℚ[X])

private theorem r63κ_scalar (c : ℚ) : r63κ (scalar c)=c := by
  simp [r63κ,scalar]

private theorem r63κ_X : r63κ X=0 := by simp [r63κ]

private theorem r63κ_CX : r63κ (C X)=0 := by simp [r63κ]

private theorem r63κ_monomial (c : ℚ) (i j : ℕ) :
    r63κ (scalar c*X^i*(C X)^j)=c*0^i*0^j := by
  rw [map_mul,map_mul,map_pow,map_pow,r63κ_scalar,r63κ_X,r63κ_CX]

private theorem r63κ_truncate (p : Bivar) : r63κ (truncate p)=r63κ p := by
  unfold truncate
  rw [map_sum,Finset.sum_eq_single (0 : Fin 15)]
  · rw [map_sum,Finset.sum_eq_single (0 : Fin 15)]
    · simp only [Fin.val_zero,add_zero,zero_le,↓reduceIte,pow_zero,mul_one]
      simp [r63κ,scalar]
    · intro j _ hj
      have hj' : j.val≠0 := fun h => hj (Fin.ext h)
      split_ifs
      · rw [r63κ_monomial,zero_pow hj',mul_zero]
      · exact map_zero _
    · simp
  · intro i _ hi
    have hi' : i.val≠0 := fun h => hi (Fin.ext h)
    rw [map_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    split_ifs
    · rw [r63κ_monomial,zero_pow hi',mul_zero,zero_mul]
    · exact map_zero _
  · simp

private theorem r63κ_mul (a b : Enclosure) :
    r63κ (TensorPolynomialEnclosure.mul a b).polynomial=r63κ a.polynomial*r63κ b.polynomial := by
  show r63κ (truncate (a.polynomial*b.polynomial))=_
  rw [r63κ_truncate,map_mul]

private theorem r63κ_constant (c : ℚ) : r63κ (constant c).polynomial=c := r63κ_scalar c

private theorem r63κ_power (a : Enclosure) (n : ℕ) :
    r63κ (TensorPolynomialEnclosure.power a n).polynomial=r63κ a.polynomial^n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [TensorPolynomialEnclosure.power]
    by_cases hn : n=0
    · subst hn
      simp [r63κ_constant]
    · simp only [hn,↓reduceIte]
      have hh := ih (n/2) (by omega)
      by_cases he : n%2=0
      · simp only [he,↓reduceIte,r63κ_mul,hh,← pow_add]
        congr 1
        omega
      · simp only [he,↓reduceIte,r63κ_mul,hh,← pow_add,← pow_succ]
        congr 1
        omega

private theorem r63κ_enclose {ι : Type*} (w : ι → Enclosure) (e : Expression ι) :
    (r63κ (Expression.enclose w e).polynomial:ℝ)=
      Expression.value (fun i => (r63κ (w i).polynomial:ℝ)) e := by
  induction e with
  | literal r => simp [Expression.enclose,Expression.value,r63κ_constant]
  | «variable» i => rfl
  | add a b ha hb =>
    simp only [Expression.enclose,Expression.value,TensorPolynomialEnclosure.add,map_add,
      Rat.cast_add,ha,hb]
  | neg a ha =>
    simp only [Expression.enclose,Expression.value,TensorPolynomialEnclosure.neg,map_neg,
      Rat.cast_neg,ha]
  | mul a b ha hb =>
    simp only [Expression.enclose,Expression.value,r63κ_mul,Rat.cast_mul,ha,hb]
  | power a n ha =>
    simp only [Expression.enclose,Expression.value,r63κ_power,Rat.cast_pow,ha]

private theorem r63κ_sine (a : Enclosure) :
    (r63κ (sine a).polynomial:ℝ)=HighOrderTaylor.S13 (r63κ a.polynomial:ℝ) := by
  rw [← sine_sum]
  simp only [sine,widen,TensorPolynomialEnclosure.sum,map_sum,r63κ_mul,r63κ_power,
    r63κ_constant,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Rat.cast_div]

private theorem r63κ_cosine (a : Enclosure) :
    (r63κ (cosine a).polynomial:ℝ)=HighOrderTaylor.C14 (r63κ a.polynomial:ℝ) := by
  rw [← cosine_sum]
  simp only [cosine,widen,TensorPolynomialEnclosure.sum,map_sum,r63κ_mul,r63κ_power,
    r63κ_constant,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Rat.cast_div]

private theorem r63_rootSeed_eq (a : Enclosure) : rootSeed a=nearestRoot (r63κ a.polynomial) := by
  simp [rootSeed,r63κ]

private theorem r63_nearestRoot_pos {r : ℚ} (hr : 1/100≤r) : 0<nearestRoot r := by
  have hr0 : 0<r := by linarith
  have hnum : 0<r.num := Rat.num_pos.mpr hr0
  have hden : (0:ℚ)<r.den := by exact_mod_cast r.den_pos
  have hcross : (r.den:ℚ)≤r.num*10000000000000000 := by
    have h := Rat.num_div_den r
    rw [← h] at hr
    rw [le_div_iff₀ hden] at hr
    linarith
  have hN : 1≤r.num.natAbs*10000000000000000/r.den := by
    rw [Nat.one_le_div_iff r.den_pos]
    have h1 : ((r.num.natAbs:ℤ):ℚ)=r.num := by
      rw [Int.natAbs_of_nonneg hnum.le]
    have h2 : ((r.den:ℕ):ℚ)≤((r.num.natAbs*10000000000000000:ℕ):ℚ) := by
      push_cast
      rw [show ((r.num.natAbs:ℕ):ℚ)=((r.num.natAbs:ℤ):ℚ) from (Int.cast_natCast _).symm,h1]
      exact hcross
    exact_mod_cast h2
  have hn : 1≤Nat.sqrt (r.num.natAbs*10000000000000000/r.den) :=
    Nat.le_sqrt.mpr (by simpa using hN)
  unfold nearestRoot
  dsimp only
  apply div_pos _ (by norm_num)
  split_ifs
  · exact_mod_cast hn
  · exact_mod_cast (Nat.succ_pos _)

private theorem r63_taylor_bounds {y : ℝ} (h0 : 0≤y) (h1 : y≤21/40) :
    0≤HighOrderTaylor.S13 y ∧ HighOrderTaylor.S13 y≤3/5 ∧ 1/2≤HighOrderTaylor.C14 y := by
  have hs := HighOrderTaylor.sin_le_S13 h0
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_three])
  have hs15 := HighOrderTaylor.S15_le_sin h0
  have hsl := Real.sin_le h0
  have hc := HighOrderTaylor.cos_le_C16 h0
  have hc1 := Real.one_sub_sq_div_two_le_cos (x := y)
  have hp15 : y^15≤1 := pow_le_one₀ h0 (by linarith)
  have hp16 : y^16≤1 := pow_le_one₀ h0 (by linarith)
  have hy2 : y^2≤1/2 := by nlinarith
  simp only [HighOrderTaylor.S15,HighOrderTaylor.C16] at hs15 hc
  refine ⟨by linarith,by linarith,by linarith⟩

section r63_value
variable {ι : Type*} (v : ι → ℝ) (a b : Expression ι)
@[simp] private theorem r63_value_add :
    Expression.value v (a+b)=Expression.value v a+Expression.value v b := rfl
@[simp] private theorem r63_value_neg : Expression.value v (-a)=-Expression.value v a := rfl
@[simp] private theorem r63_value_sub :
    Expression.value v (a-b)=Expression.value v a-Expression.value v b := by
  show Expression.value v a+-Expression.value v b=_
  ring
@[simp] private theorem r63_value_mul :
    Expression.value v (a*b)=Expression.value v a*Expression.value v b := rfl
@[simp] private theorem r63_value_pow (n : ℕ) :
    Expression.value v (a^n)=Expression.value v a^n := rfl
@[simp] private theorem r63_value_one : Expression.value v (1 : Expression ι)=1 := by
  show (((1:ℕ):ℚ):ℝ)=1
  norm_num
@[simp] private theorem r63_value_two : Expression.value v (2 : Expression ι)=2 := by
  show (((2:ℕ):ℚ):ℝ)=2
  norm_num
@[simp] private theorem r63_value_zero : Expression.value v (0 : Expression ι)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  norm_num
@[simp] private theorem r63_value_ite (P : Prop) [Decidable P] :
    Expression.value v (if P then a else b)=
      if P then Expression.value v a else Expression.value v b := by
  split_ifs <;> rfl
@[simp] private theorem r63_value_literal (r : ℚ) :
    Expression.value v (Expression.literal r : Expression ι)=(r:ℝ) := rfl
@[simp] private theorem r63_value_variable (i : ι) :
    Expression.value v (Expression.variable i : Expression ι)=v i := rfl
end r63_value

end r63_constant


open TensorPolynomialEnclosure TensorWholeIntervalPolynomial
open SoleTScalarModel SolePositiveTPolynomials SoleNegativeTScalarModel



def parameter (r : Row) : Enclosure :=
  TensorPolynomialEnclosure.add (constant ((SoleNegativeTScalarModel.left r+SoleNegativeTScalarModel.right r)/2))
    (mul (constant ((SoleNegativeTScalarModel.right r-SoleNegativeTScalarModel.left r)/2)) outerVariable)

def xParameter (s : Case) : Enclosure := if s.atG then parameter s.row else constant 0
def eParameter (s : Case) : Enclosure := if s.atG then constant 0 else parameter s.row
def angleParameter (s : Case) : Enclosure :=
  if shifted s.row then TensorPolynomialEnclosure.sub (parameter s.row) (constant (3/10)) else constant 0

def «variables» (s : Case) : Fin 11 → Enclosure :=
  ![parameter s.row,constant 0,sine (xParameter s),cosine (xParameter s),constant 0,constant 1,
    sine (eParameter s),cosine (eParameter s),sine (angleParameter s),cosine (angleParameter s),
    sine (mul (eParameter s) (constant (1/2)))]

def rootExpression (s : Case) (i : Fin 7) : Expr :=
  Expression.sqrtUpper («variables» s) (rootSquare (scalar s) i)

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

def enclosure (s : Case) : Enclosure := Expression.enclose («variables» s) (expression s)
def polynomial (s : Case) : Bivar := (enclosure s).polynomial
def lower (s : Case) : ℚ :=
  Finset.univ.inf' Finset.univ_nonempty (fun ij : Fin 33 × Fin 33 =>
    TensorWholeIntervalBernstein.coefficient 32 (polynomial s) ij.1 ij.2)

/-- The constant coefficients of the eleven input enclosures. -/
private def r63v (s : Case) : Fin 11 → ℝ := fun j => (r63κ («variables» s j).polynomial:ℝ)

private theorem r63κ_parameter (r : Row) :
    r63κ (parameter r).polynomial=(SoleNegativeTScalarModel.left r+
      SoleNegativeTScalarModel.right r)/2 := by
  simp [parameter,TensorPolynomialEnclosure.add,r63κ_mul,r63κ_constant,outerVariable,r63κ_X]

private theorem r63_parameter_range (r : Row) :
    0≤((SoleNegativeTScalarModel.left r:ℝ)+(SoleNegativeTScalarModel.right r:ℝ))/2 ∧
      ((SoleNegativeTScalarModel.left r:ℝ)+(SoleNegativeTScalarModel.right r:ℝ))/2≤21/40 := by
  cases r <;> norm_num [SoleNegativeTScalarModel.left,SoleNegativeTScalarModel.right]

private theorem r63v_bounds (s : Case) :
    r63v s 0=((SoleNegativeTScalarModel.left s.row:ℝ)+(SoleNegativeTScalarModel.right s.row:ℝ))/2 ∧
    r63v s 1=0 ∧ 0≤r63v s 6 ∧ 1/2≤r63v s 7 ∧ 0≤r63v s 8 ∧ r63v s 8≤3/5 := by
  obtain ⟨h0,h1⟩ := r63_parameter_range s.row
  have hP : (r63κ (parameter s.row).polynomial:ℝ)=
      ((SoleNegativeTScalarModel.left s.row:ℝ)+(SoleNegativeTScalarModel.right s.row:ℝ))/2 := by
    rw [r63κ_parameter]
    push_cast
    ring
  have he : (r63κ (eParameter s).polynomial:ℝ)∈Set.Icc 0 (21/40) := by
    unfold eParameter
    split_ifs
    · simp only [r63κ_constant,Rat.cast_zero,Set.mem_Icc,le_refl,true_and]
      norm_num
    · rw [hP]
      exact ⟨h0,h1⟩
  have ha : (r63κ (angleParameter s).polynomial:ℝ)∈Set.Icc 0 (21/40) := by
    unfold angleParameter
    split_ifs with hsh
    · simp only [TensorPolynomialEnclosure.sub,TensorPolynomialEnclosure.add,
        TensorPolynomialEnclosure.neg,map_add,map_neg,Rat.cast_add,Rat.cast_neg,hP,
        r63κ_constant]
      cases hr : s.row <;> simp [hr,SoleNegativeTScalarModel.shifted] at hsh <;>
        norm_num [SoleNegativeTScalarModel.left,SoleNegativeTScalarModel.right]
    · simp only [r63κ_constant,Rat.cast_zero,Set.mem_Icc,le_refl,true_and]
      norm_num
  have hE := r63_taylor_bounds he.1 he.2
  have hA := r63_taylor_bounds ha.1 ha.2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact hP
  · simp [r63v,«variables»,r63κ_constant]
  · simpa [r63v,«variables»,r63κ_sine] using hE.1
  · simpa [r63v,«variables»,r63κ_cosine] using hE.2.2
  · simpa [r63v,«variables»,r63κ_sine] using hA.1
  · simpa [r63v,«variables»,r63κ_sine] using hA.2.1

private theorem r63_first_lower (s : Case) (j : Fin 4) :
    3/10≤Expression.value (r63v s) (firstE (SoleNegativeTScalarModel.scalar s) j) := by
  obtain ⟨h0,h1,h6,h7,h8,h8'⟩ := r63v_bounds s
  fin_cases j
  · show 3/10≤Expression.value (r63v s) (lambdaE (family s.row))
    unfold lambdaE
    split_ifs <;> norm_num
  · show 3/10≤Expression.value (r63v s) (kE (family s.row))
    cases hr : s.row <;> rw [hr] at h0 <;>
      simp [kE,KE,SolePositiveTPolynomials.tE,zE,h0,h1,family,SoleNegativeTScalarModel.left,
        SoleNegativeTScalarModel.right] <;> norm_num
  · show 3/10≤Expression.value (r63v s) (ellE (family s.row))
    cases hr : s.row <;> rw [hr] at h0 <;>
      simp [ellE,SolePositiveTPolynomials.LE,SolePositiveTPolynomials.tE,zE,h0,h1,family,
        SoleNegativeTScalarModel.left,SoleNegativeTScalarModel.right] <;> norm_num
  · show 3/10≤Expression.value (r63v s) (pE (SoleNegativeTScalarModel.scalar s))
    have heps : 0≤Expression.value (r63v s) (epsilonE (family s.row)) := by
      cases hr : s.row <;> rw [hr] at h0 <;>
        simp [epsilonE,SolePositiveTPolynomials.tE,h0,family,SoleNegativeTScalarModel.left,
          SoleNegativeTScalarModel.right] <;> norm_num
    have heps' : 0≤Expression.value (r63v s)
        (epsilonE (SoleNegativeTScalarModel.scalar s).family) := heps
    unfold pE
    split_ifs
    · simp only [r63_value_add,r63_value_mul,ce,se,r63_value_variable]
      have := mul_nonneg heps' h6
      linarith
    · norm_num

private theorem r63_rootSquare_lower (s : Case) (i : Fin 7) :
    1/100≤Expression.value (r63v s) (rootSquare (SoleNegativeTScalarModel.scalar s) i) := by
  obtain ⟨h0,h1,h6,h7,h8,h8'⟩ := r63v_bounds s
  unfold rootSquare
  split_ifs with hi
  · have hA := r63_first_lower s ⟨i.val,hi⟩
    simp only [squareE,r63_value_sub,r63_value_add,r63_value_pow,r63_value_ite,r63_value_mul,
      r63_value_two,r63_value_zero,st,r63_value_variable]
    set A := Expression.value (r63v s) (firstE (SoleNegativeTScalarModel.scalar s) ⟨i.val,hi⟩)
    set B := Expression.value (r63v s) (secondE (SoleNegativeTScalarModel.scalar s) ⟨i.val,hi⟩)
    set S := r63v s 8
    have hS2 : S^2≤9/25 := by nlinarith
    have hA2 : 9/100≤A^2 := by nlinarith
    have key : 9/100*(16/25)≤A^2*(1-S^2) :=
      mul_le_mul hA2 (by linarith) (by norm_num) (by positivity)
    split_ifs
    · nlinarith [sq_nonneg (B-A*S),key]
    · nlinarith [sq_nonneg B]
  · simp only [r63_value_add,r63_value_one,r63_value_pow]
    nlinarith [sq_nonneg (Expression.value (r63v s) (gE (family s.row)))]
  · simp only [r63_value_add,r63_value_one,r63_value_pow]
    nlinarith [sq_nonneg (Expression.value (r63v s) etaE)]
  · simp only [r63_value_add,r63_value_one,r63_value_pow]
    nlinarith [sq_nonneg (Expression.value (r63v s) (epsilonE (family s.row)))]

theorem seeds_positive (s : Case) (i : Fin 7) :
    0<rootSeed (Expression.enclose («variables» s) (rootSquare (scalar s) i)) := by
  rw [r63_rootSeed_eq]
  apply r63_nearestRoot_pos
  have h := r63_rootSquare_lower s i
  rw [show Expression.value (r63v s) (rootSquare (SoleNegativeTScalarModel.scalar s) i)=
    (r63κ (Expression.enclose («variables» s)
      (rootSquare (SoleNegativeTScalarModel.scalar s) i)).polynomial:ℝ) from
      (r63κ_enclose _ _).symm] at h
  have h' : (((1/100:ℚ)):ℝ)≤(r63κ (Expression.enclose («variables» s)
      (rootSquare (SoleNegativeTScalarModel.scalar s) i)).polynomial:ℝ) := by
    push_cast
    linarith
  exact Rat.cast_le.mp h'

open Set

def parameterValue (r : Row) (X : ℝ) : ℝ :=
  ((SoleNegativeTScalarModel.left r:ℝ)+(SoleNegativeTScalarModel.right r:ℝ))/2+
    ((SoleNegativeTScalarModel.right r:ℝ)-(SoleNegativeTScalarModel.left r:ℝ))/2*X

def inputs (s : Case) (t : ℝ) : Fin 11 → ℝ :=
  ![t,0,Real.sin (x (scalar s) t 0),Real.cos (x (scalar s) t 0),0,1,
    Real.sin (SoleTScalarModel.e (scalar s) t 0),Real.cos (SoleTScalarModel.e (scalar s) t 0),
    Real.sin (SoleNegativeTScalarModel.angle s.row t),Real.cos (SoleNegativeTScalarModel.angle s.row t),
    Real.sin (SoleTScalarModel.e (scalar s) t 0/2)]

theorem parameter_mem (r : Row) {X : ℝ} (hX : |X|≤1) :
    parameterValue r X∈SoleNegativeTScalarModel.domain r := by
  have h := abs_le.mp hX
  cases r <;> norm_num [parameterValue,SoleNegativeTScalarModel.domain,
    SoleNegativeTScalarModel.left,SoleNegativeTScalarModel.right] <;>
    constructor <;> linarith [h.1,h.2]

/-! ### The packed certificate

The expression is mirrored by an `IE` expression (with the formulas of
`SolePositiveTPolynomials`) whose seven roots are extra variables. The roots and then the whole
expression are evaluated by the packed Taylor models of `PackedModels`, and the kernel checks the
degree-10 Bernstein coefficients in natural-number arithmetic. The root seeds are checked the
same way at the center of the interval. -/

section packed
open PackedModels

def rowBaseI (s : Case) : IExpr :=
  kI (family s.row)*(1+2*cxI+(1+2*gI (family s.row))*sxI)+
    3*cI (family s.row)+2*ellI (family s.row)-
    radiusI*kI (family s.row)*sxI*rootI 4
def rowEI (s : Case) : IExpr :=
  if tiltedE (family s.row) then
    1+2*ceI+(1+2*epsilonI (family s.row))*seI-radiusI*seI*rootI 6
  else if isDE (family s.row) then
    1+lq 1 2*ceI+.lit (.sub (.num 1) (.q 1914558470771 1000000000000))*seI+lq 3 2*lq 5 4
  else 3+seI-.lit (.mul (.num 2) (.q 989385433 500000000))*shalfI
def rowCorrectionI (s : Case) : IExpr :=
  if family s.row=.ehMiddle ∨ family s.row=.ehHigh then
    lq 8 25*(cI (family s.row)-pI (family s.row))^2 else 0
def rowRemovedI (s : Case) : IExpr := if shifted s.row then lq 3 10 else tI
def rowCoefficientI (s : Case) : IExpr :=
  if index s.row=3 then cI (family s.row) else nuI (scalar s)
/-- The expression with its roots as variables. -/
def rowSkeleton (s : Case) : IExpr :=
  ((((rowBaseI s+rowEI s+rowCorrectionI s+
    lq 21 20*cI (family s.row)*rowRemovedI s+rowCoefficientI s*(ctI-1))-
      radiusI*rootI 0)-
        radiusI*rootI 1)-
          radiusI*rootI 2)-
            radiusI*rootI 3

/-- The formulas of the variables: the inputs and the roots. -/
def rowFormulas (s : Case) : Fin 11 ⊕ Fin 7 → Expr :=
  Sum.elim Expression.variable (rootExpression s)

theorem rowSkeleton_eq (s : Case) : (rowSkeleton s).toExpressionWith (rowFormulas s)=expression s := by
  rcases s with ⟨r,atG⟩
  rcases r with _|_|i|i|_|i|i <;> (try fin_cases i) <;> rfl

/-- The models work at scale `2 ^ 48` with total degree `8`; the seeds use constant models. -/
def rowConfig : Config := ⟨48,8,116⟩
def rowSeedConfig : Config := ⟨48,1,116⟩

theorem rowConfig_valid : rowConfig.Valid := ⟨by decide,by decide⟩
theorem rowSeedConfig_valid : rowSeedConfig.Valid := ⟨by decide,by decide⟩

/-- The center and the half-width of a row's interval. -/
def rowCenter : Row → ℕ × ℕ
  | .ehLowDiagonal => (1,10) | .ehMiddleDiagonal => (1,4) | .deLowDiagonal => (3,20)
  | .ehMiddleShifted _ | .deLowShifted _ => (13,40)
  | .ehHighShifted _ | .deHighShifted _ => (21,40)
def rowHalfWidth : Row → ℕ × ℕ
  | .ehLowDiagonal => (1,10) | .ehMiddleDiagonal => (1,20) | .deLowDiagonal => (3,20)
  | .ehMiddleShifted _ | .deLowShifted _ => (1,40)
  | .ehHighShifted _ | .deHighShifted _ => (7,40)

theorem rowCenter_eq (r : Row) :
    (((rowCenter r).1:ℤ):ℝ)/(rowCenter r).2=
      ((SoleNegativeTScalarModel.left r:ℝ)+(SoleNegativeTScalarModel.right r:ℝ))/2 := by
  cases r <;> norm_num [rowCenter,SoleNegativeTScalarModel.left,SoleNegativeTScalarModel.right]
theorem rowHalfWidth_eq (r : Row) :
    (((rowHalfWidth r).1:ℤ):ℝ)/(rowHalfWidth r).2=
      ((SoleNegativeTScalarModel.right r:ℝ)-(SoleNegativeTScalarModel.left r:ℝ))/2 := by
  cases r <;> norm_num [rowHalfWidth,SoleNegativeTScalarModel.left,SoleNegativeTScalarModel.right]

def rowTModel (r : Row) : Model :=
  Model.add rowConfig (Model.lit rowConfig (rowCenter r).1 (rowCenter r).2)
    (Model.mul rowConfig (Model.lit rowConfig (rowHalfWidth r).1 (rowHalfWidth r).2) (Model.X rowConfig))

/-- The models of the eleven inputs on the interval. -/
def rowInputModels (r : Row) (atG : Bool) : Fin 11 → Model :=
  let c := rowConfig
  let t := rowTModel r
  let x := if atG then t else zeroModel c
  let e := if atG then zeroModel c else t
  let a := if shifted r then Model.add c t (Model.neg (Model.lit c 3 10)) else zeroModel c
  ![t,zeroModel c,Model.sin c x,Model.cos c x,zeroModel c,Model.one c,Model.sin c e,Model.cos c e,
    Model.sin c a,Model.cos c a,Model.sin c (Model.mul c e (Model.lit c 1 2))]

/-- The constant models of the constant coefficients of the input enclosures, and zero. -/
def rowPointModels (r : Row) (atG : Bool) : Fin 11 ⊕ Fin 7 → Model :=
  let c := rowSeedConfig
  let t := Model.lit c (rowCenter r).1 (rowCenter r).2
  let x := if atG then t else zeroModel c
  let e := if atG then zeroModel c else t
  let a := if shifted r then Model.add c t (Model.neg (Model.lit c 3 10)) else zeroModel c
  Sum.elim ![t,zeroModel c,Model.sinPoly c x,Model.cosPoly c x,zeroModel c,Model.one c,
    Model.sinPoly c e,Model.cosPoly c e,Model.sinPoly c a,Model.cosPoly c a,
    Model.sinPoly c (Model.mul c e (Model.lit c 1 2))] fun _ => zeroModel c

/-- Whether root `i` carries the negative cross term. -/
def rowNegative (s : Case) (i : Fin 7) : Bool := decide (i.val=(index s.row).val)

/-- The root seeds, `10 ^ 8 · rootSeed`, found from the point models. -/
def rowSeed (r : Row) (atG : Bool) (i : Fin 7) (neg : Bool) : ℕ :=
  seedOf rowSeedConfig (rowPointModels r atG) (rootSquareI (family r) true i neg)

/-- The model of a root on the interval. -/
def rowRootModel (r : Row) (atG : Bool) (i : Fin 7) (neg : Bool) : Model :=
  (IE.sqrtUpper 0 (rowSeed r atG i neg) (rootSquareI (family r) true i neg)).eval rowConfig
    (Sum.elim (rowInputModels r atG) fun _ => zeroModel rowConfig)

/-- The checks of a root. -/
def rowRootCheck (r : Row) (atG : Bool) (i : Fin 7) (neg : Bool) : Bool :=
  seedCheck rowSeedConfig (rowPointModels r atG) (rootSquareI (family r) true i neg)
      (rowSeed r atG i neg) &&
    (rootSquareI (family r) true i neg).seedFree && (rootSquareI (family r) true i neg).poly &&
    (IE.sqrtUpper 0 (rowSeed r atG i neg) (rootSquareI (family r) true i neg)).poly

/-- The models of the inputs and of the roots of a case. -/
def rowModels (s : Case) : Fin 11 ⊕ Fin 7 → Model :=
  Sum.elim (rowInputModels s.row s.atG) fun i =>
    if i.val=(index s.row).val then rowRootModel s.row s.atG i true
    else rowRootModel s.row s.atG i false

/-- Everything the kernel checks for one case. -/
def rowCheck (s : Case) : Bool :=
  check rowConfig 10 (rowModels s) (rowSkeleton s) 0 1 true && (rowSkeleton s).poly &&
    (rowSkeleton s).seedFree &&
    ([0,1,2,3,4,5,6] : List (Fin 7)).all fun i =>
      if i.val=(index s.row).val then rowRootCheck s.row s.atG i true
      else rowRootCheck s.row s.atG i false

theorem row_check (r : Row) : allBool (fun atG => rowCheck ⟨r,atG⟩)=true := by
  rcases r with _|_|i|i|_|i|i <;> (try fin_cases i) <;> decide +kernel

theorem case_check (s : Case) : rowCheck s=true := allBool_eq (row_check s.row) s.atG

theorem rowInputModels_contain (s : Case) {X : ℝ} (hX : |X|≤1) (Y : ℝ) (hY : |Y|≤1) :
    ∀ i,(rowInputModels s.row s.atG i).Contains rowConfig X Y (inputs s (parameterValue s.row X) i) := by
  have hc := rowConfig_valid
  set t := parameterValue s.row X
  have ht : t∈SoleNegativeTScalarModel.domain s.row := parameter_mem s.row hX
  have hf := SoleNegativeTScalarModel.family_mem ht
  have htz := SoleNegativeTScalarModel.angles ht
  have hz : (0:ℝ)∈Set.Icc 0 t := ⟨le_rfl,htz.1.1⟩
  have htm : (rowTModel s.row).Contains rowConfig X Y t := by
    have h := Model.contains_add hc (Model.contains_lit rowConfig (rowCenter s.row).1 (rowCenter s.row).2)
      (Model.contains_mul hc hX hY
        (Model.contains_lit rowConfig (rowHalfWidth s.row).1 (rowHalfWidth s.row).2)
        (Model.contains_X hc X Y))
    rw [rowCenter_eq,rowHalfWidth_eq] at h
    exact h
  have h0 := zeroModel_contains rowConfig X Y
  have hxv : SoleTScalarModel.x (scalar s) t 0=if s.atG then t else 0 := by
    simp [SoleTScalarModel.x,SoleNegativeTScalarModel.scalar]
  have hev : SoleTScalarModel.e (scalar s) t 0=if s.atG then 0 else t := by
    simp [SoleTScalarModel.e,SoleNegativeTScalarModel.scalar]
  have hxm : (if s.atG then rowTModel s.row else zeroModel rowConfig).Contains rowConfig X Y
      (SoleTScalarModel.x (scalar s) t 0) := by
    rw [hxv]; split_ifs; exacts [htm,h0]
  have hem : (if s.atG then zeroModel rowConfig else rowTModel s.row).Contains rowConfig X Y
      (SoleTScalarModel.e (scalar s) t 0) := by
    rw [hev]; split_ifs; exacts [h0,htm]
  have ham : (if shifted s.row then Model.add rowConfig (rowTModel s.row)
      (Model.neg (Model.lit rowConfig 3 10)) else zeroModel rowConfig).Contains rowConfig X Y
      (SoleNegativeTScalarModel.angle s.row t) := by
    unfold SoleNegativeTScalarModel.angle
    split_ifs
    · have h := Model.contains_add hc htm (Model.contains_neg (Model.contains_lit rowConfig 3 10
        (x := X) (y := Y)))
      have e : t-3/10=t+-(((3:ℤ):ℝ)/((10:ℕ):ℝ)) := by push_cast; ring
      rw [e]; exact h
    · exact h0
  have hx := (SoleTScalarModel.split_angles (scalar s) hf hz).2.1
  have he := (SoleTScalarModel.split_angles (scalar s) hf hz).2.2
  have hhalf : SoleTScalarModel.e (scalar s) t 0/2∈Set.Icc 0 frameCap :=
    ⟨by linarith [he.1],by have h2 := he.2; simp only [frameCap] at h2 ⊢; linarith [he.1]⟩
  intro i
  fin_cases i
  · exact htm
  · exact h0
  · exact Model.contains_sin hc hX hY hxm hx
  · exact Model.contains_cos hc hX hY hxm hx
  · exact h0
  · exact Model.contains_one rowConfig X Y
  · exact Model.contains_sin hc hX hY hem he
  · exact Model.contains_cos hc hX hY hem he
  · exact Model.contains_sin hc hX hY ham htz.2.1
  · exact Model.contains_cos hc hX hY ham htz.2.1
  · exact Model.contains_sin hc hX hY (half_contains hc hX hY hem) hhalf

/-- The point models contain the constant coefficients of the input enclosures. -/
private theorem rowPointModels_contain (s : Case) :
    ∀ k,(rowPointModels s.row s.atG k).Contains rowSeedConfig 0 0 ((inputFormulas k).value (r63v s)) := by
  have hc := rowSeedConfig_valid
  have h0 : |(0:ℝ)|≤1 := by simp
  set M : ℝ := ((SoleNegativeTScalarModel.left s.row:ℝ)+(SoleNegativeTScalarModel.right s.row:ℝ))/2
    with hM
  have hP : (r63κ (parameter s.row).polynomial:ℝ)=M := by
    rw [r63κ_parameter]; push_cast; ring
  have h0κ : (r63κ (constant 0).polynomial:ℝ)=0 := by simp [r63κ_constant]
  have h1κ : (r63κ (constant 1).polynomial:ℝ)=1 := by simp [r63κ_constant]
  have htm : (Model.lit rowSeedConfig (rowCenter s.row).1 (rowCenter s.row).2).Contains
      rowSeedConfig 0 0 M := by
    have h := Model.contains_lit rowSeedConfig (rowCenter s.row).1 (rowCenter s.row).2
      (x := 0) (y := 0)
    rwa [rowCenter_eq] at h
  have hz := zeroModel_contains rowSeedConfig 0 0
  have hxm : (if s.atG then Model.lit rowSeedConfig (rowCenter s.row).1 (rowCenter s.row).2
      else zeroModel rowSeedConfig).Contains rowSeedConfig 0 0 (r63κ (xParameter s).polynomial:ℝ) := by
    unfold xParameter
    split_ifs
    · rw [hP]; exact htm
    · rw [h0κ]; exact hz
  have hem : (if s.atG then zeroModel rowSeedConfig
      else Model.lit rowSeedConfig (rowCenter s.row).1 (rowCenter s.row).2).Contains
      rowSeedConfig 0 0 (r63κ (eParameter s).polynomial:ℝ) := by
    unfold eParameter
    split_ifs
    · rw [h0κ]; exact hz
    · rw [hP]; exact htm
  have ham : (if shifted s.row then Model.add rowSeedConfig
      (Model.lit rowSeedConfig (rowCenter s.row).1 (rowCenter s.row).2)
      (Model.neg (Model.lit rowSeedConfig 3 10)) else zeroModel rowSeedConfig).Contains
      rowSeedConfig 0 0 (r63κ (angleParameter s).polynomial:ℝ) := by
    unfold angleParameter
    split_ifs
    · have h := Model.contains_add hc htm (Model.contains_neg (Model.contains_lit rowSeedConfig 3 10
        (x := 0) (y := 0)))
      have e : (r63κ (TensorPolynomialEnclosure.sub (parameter s.row) (constant (3/10))).polynomial:ℝ)=
          M+-(((3:ℤ):ℝ)/((10:ℕ):ℝ)) := by
        simp only [TensorPolynomialEnclosure.sub,TensorPolynomialEnclosure.add,
          TensorPolynomialEnclosure.neg,map_add,map_neg,Rat.cast_add,Rat.cast_neg,hP,r63κ_constant]
        push_cast; ring
      rw [e]; exact h
    · rw [h0κ]; exact hz
  have hhm := half_contains hc h0 h0 hem
  have hH : (r63κ (mul (eParameter s) (constant (1/2))).polynomial:ℝ)=
      (r63κ (eParameter s).polynomial:ℝ)/2 := by
    rw [r63κ_mul,r63κ_constant]; push_cast; ring
  rintro (j|j)
  · fin_cases j
    · show (Model.lit rowSeedConfig ((rowCenter s.row).1:ℤ) (rowCenter s.row).2).Contains
        rowSeedConfig 0 0 (r63κ (parameter s.row).polynomial:ℝ)
      rw [hP]; exact htm
    · show (zeroModel rowSeedConfig).Contains rowSeedConfig 0 0 (r63κ (constant 0).polynomial:ℝ)
      rw [h0κ]; exact hz
    · show (Model.sinPoly rowSeedConfig _).Contains rowSeedConfig 0 0
        (r63κ (sine (xParameter s)).polynomial:ℝ)
      rw [r63κ_sine]; exact Model.contains_sinPoly hc h0 h0 hxm
    · show (Model.cosPoly rowSeedConfig _).Contains rowSeedConfig 0 0
        (r63κ (cosine (xParameter s)).polynomial:ℝ)
      rw [r63κ_cosine]; exact Model.contains_cosPoly hc h0 h0 hxm
    · show (zeroModel rowSeedConfig).Contains rowSeedConfig 0 0 (r63κ (constant 0).polynomial:ℝ)
      rw [h0κ]; exact hz
    · show (Model.one rowSeedConfig).Contains rowSeedConfig 0 0 (r63κ (constant 1).polynomial:ℝ)
      rw [h1κ]; exact Model.contains_one rowSeedConfig 0 0
    · show (Model.sinPoly rowSeedConfig _).Contains rowSeedConfig 0 0
        (r63κ (sine (eParameter s)).polynomial:ℝ)
      rw [r63κ_sine]; exact Model.contains_sinPoly hc h0 h0 hem
    · show (Model.cosPoly rowSeedConfig _).Contains rowSeedConfig 0 0
        (r63κ (cosine (eParameter s)).polynomial:ℝ)
      rw [r63κ_cosine]; exact Model.contains_cosPoly hc h0 h0 hem
    · show (Model.sinPoly rowSeedConfig _).Contains rowSeedConfig 0 0
        (r63κ (sine (angleParameter s)).polynomial:ℝ)
      rw [r63κ_sine]; exact Model.contains_sinPoly hc h0 h0 ham
    · show (Model.cosPoly rowSeedConfig _).Contains rowSeedConfig 0 0
        (r63κ (cosine (angleParameter s)).polynomial:ℝ)
      rw [r63κ_cosine]; exact Model.contains_cosPoly hc h0 h0 ham
    · show (Model.sinPoly rowSeedConfig _).Contains rowSeedConfig 0 0
        (r63κ (sine (mul (eParameter s) (constant (1/2)))).polynomial:ℝ)
      rw [r63κ_sine,hH]; exact Model.contains_sinPoly hc h0 h0 hhm
  · show (zeroModel rowSeedConfig).Contains rowSeedConfig 0 0 (Expression.value (r63v s) 0)
    rw [value_zero]
    exact hz

theorem rowRootCheck_eq (s : Case) (i : Fin 7) :
    rowRootCheck s.row s.atG i (rowNegative s i)=true := by
  have hc := case_check s
  simp only [rowCheck,Bool.and_eq_true,List.all_eq_true] at hc
  have h := hc.2 i (by fin_cases i <;> simp)
  unfold rowNegative
  split_ifs at h with hi
  · rw [decide_eq_true hi]; exact h
  · rw [decide_eq_false hi]; exact h

theorem rowSeed_eq (s : Case) (i : Fin 7) :
    rootSeed (Expression.enclose («variables» s) (rootSquare (scalar s) i))=
      (rowSeed s.row s.atG i (rowNegative s i):ℚ)/100000000 := by
  have h := rowRootCheck_eq s i
  simp only [rowRootCheck,Bool.and_eq_true] at h
  obtain ⟨⟨⟨hs,hf⟩,hp⟩,-⟩ := h
  have hval : Expression.value (r63v s) (rootSquare (scalar s) i)=
      (r63κ (Expression.enclose («variables» s) (rootSquare (scalar s) i)).polynomial:ℝ) :=
    (r63κ_enclose _ _).symm
  have hI : (rootSquareI (family s.row) true i (rowNegative s i)).value
      (fun k => (inputFormulas k).value (r63v s))=Expression.value (r63v s) (rootSquare (scalar s) i) := by
    have ha : (rootSquareI (family s.row) true i (rowNegative s i)).toExpressionWith inputFormulas=
        rootSquare (scalar s) i := SolePositiveTPolynomials.rootSquareI_eq (scalar s) i
    rw [← ha,IE.value_toExpressionWith _ _ _ (IE.isPoly_of_poly _ hp)]
  rw [r63_rootSeed_eq]
  apply seedCheck_sound rowSeedConfig_valid hs (rowPointModels_contain s)
    (IE.seedsOK_of_seedFree _ hf) (by rw [hI,hval])
  have h := r63_rootSquare_lower s i
  rw [hval] at h
  have h' : (0:ℝ)≤(r63κ (Expression.enclose («variables» s) (rootSquare (scalar s) i)).polynomial:ℝ) := by
    linarith
  exact_mod_cast h'

/-- The root models contain the roots on the interval. -/
theorem rowRootModel_contains (s : Case) {X : ℝ} (hX : |X|≤1) (Y : ℝ) (hY : |Y|≤1) (i : Fin 7) :
    (rowRootModel s.row s.atG i (rowNegative s i)).Contains rowConfig X Y
      (Expression.value (inputs s (parameterValue s.row X)) (rootExpression s i)) := by
  set v := inputs s (parameterValue s.row X)
  have h := rowRootCheck_eq s i
  simp only [rowRootCheck,Bool.and_eq_true] at h
  obtain ⟨⟨⟨-,hf⟩,-⟩,hp⟩ := h
  have hw : ∀ k,((Sum.elim (rowInputModels s.row s.atG) fun _ => zeroModel rowConfig) k).Contains
      rowConfig X Y ((inputFormulas k).value v) := by
    rintro (k|k)
    · exact rowInputModels_contain s hX Y hY k
    · show (zeroModel rowConfig).Contains rowConfig X Y (Expression.value v 0)
      rw [value_zero]; exact zeroModel_contains rowConfig X Y
  set a := rootSquareI (family s.row) true i (rowNegative s i)
  have ha : a.toExpressionWith inputFormulas=rootSquare (scalar s) i :=
    SolePositiveTPolynomials.rootSquareI_eq (scalar s) i
  have hs : (IE.sqrtUpper (rootSeed (Expression.enclose («variables» s) (rootSquare (scalar s) i)))
      (rowSeed s.row s.atG i (rowNegative s i)) a).SeedsOK :=
    IE.seedsOK_sqrtUpper (rowSeed_eq s i) (IE.seedsOK_of_seedFree _ hf)
  have hc := IE.eval_sound rowConfig_valid hX hY hw _ hs
  have hpoly : (IE.sqrtUpper (rootSeed (Expression.enclose («variables» s) (rootSquare (scalar s) i)))
      (rowSeed s.row s.atG i (rowNegative s i)) a).IsPoly :=
    IE.isPoly_of_poly _ hp
  have hv := IE.value_toExpressionWith v inputFormulas _ hpoly
  have he : (IE.sqrtUpper (rootSeed (Expression.enclose («variables» s) (rootSquare (scalar s) i)))
      (rowSeed s.row s.atG i (rowNegative s i)) a).toExpressionWith inputFormulas=
      rootExpression s i := by
    rw [rootExpression,← ha]
    exact IE.toExpressionWith_sqrtUpper _ _ _ _
  rw [he] at hv
  rw [hv]
  rw [IE.eval_sqrtUpper rowConfig _ _ 0] at hc
  exact hc

theorem rowModels_contain (s : Case) {X : ℝ} (hX : |X|≤1) (Y : ℝ) (hY : |Y|≤1) :
    ∀ k,(rowModels s k).Contains rowConfig X Y ((rowFormulas s k).value (inputs s (parameterValue s.row X))) := by
  rintro (k|i)
  · exact rowInputModels_contain s hX Y hY k
  · have h := rowRootModel_contains s hX Y hY i
    show (if i.val=(index s.row).val then rowRootModel s.row s.atG i true
      else rowRootModel s.row s.atG i false).Contains rowConfig X Y _
    unfold rowNegative at h
    split_ifs with hi
    · rw [decide_eq_true hi] at h; exact h
    · rw [decide_eq_false hi] at h; exact h

end packed

theorem model_positive (s : Case) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    0<Expression.value (inputs s (parameterValue s.row X)) (expression s) := by
  have hc := case_check s
  simp only [rowCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hm,hp⟩,hf⟩,-⟩ := hc
  have h := PackedModels.check_lt rowConfig_valid hm hX hY (rowModels_contain s hX Y hY)
    (PackedModels.IE.seedsOK_of_seedFree _ hf)
  rw [← rowSkeleton_eq,PackedModels.IE.value_toExpressionWith _ _ _ (PackedModels.IE.isPoly_of_poly _ hp)]
  simpa using h

end SquaresInCircles.Eight.SoleNegativeTPolynomials
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleNegativeTScalar
open SoleTScalarModel SolePositiveTPolynomials SoleNegativeTScalarModel
open SoleNegativeTPolynomials TensorPolynomialEnclosure

section r64_value
variable {ι : Type*} (v : ι → ℝ) (a b : Expression ι)
@[simp] private theorem r64_value_add :
    Expression.value v (a+b)=Expression.value v a+Expression.value v b := rfl
@[simp] private theorem r64_value_neg : Expression.value v (-a)=-Expression.value v a := rfl
@[simp] private theorem r64_value_sub :
    Expression.value v (a-b)=Expression.value v a-Expression.value v b := by
  show Expression.value v a+-Expression.value v b=_
  ring
@[simp] private theorem r64_value_mul :
    Expression.value v (a*b)=Expression.value v a*Expression.value v b := rfl
@[simp] private theorem r64_value_pow (n : ℕ) :
    Expression.value v (a^n)=Expression.value v a^n := rfl
@[simp] private theorem r64_value_one : Expression.value v (1 : Expression ι)=1 := by
  show (((1:ℕ):ℚ):ℝ)=1
  norm_num
@[simp] private theorem r64_value_two : Expression.value v (2 : Expression ι)=2 := by
  show (((2:ℕ):ℚ):ℝ)=2
  norm_num
@[simp] private theorem r64_value_three : Expression.value v (3 : Expression ι)=3 := by
  show (((3:ℕ):ℚ):ℝ)=3
  norm_num
@[simp] private theorem r64_value_zero : Expression.value v (0 : Expression ι)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  norm_num
@[simp] private theorem r64_value_ite (P : Prop) [Decidable P] :
    Expression.value v (if P then a else b)=
      if P then Expression.value v a else Expression.value v b := by
  split_ifs <;> rfl
end r64_value

@[simp] private theorem r64_value_lit (w : Fin 11 → ℝ) (r : ℚ) :
    Expression.value w (lit r)=(r:ℝ) := rfl
@[simp] private theorem r64_value_var (w : Fin 11 → ℝ) (i : Fin 11) :
    Expression.value w (var i)=w i := rfl
section r64_inputs
variable (s : Case) (t : ℝ)
@[simp] private theorem r64_inputs_0 : SoleNegativeTPolynomials.inputs s t 0=t := rfl
@[simp] private theorem r64_inputs_1 : SoleNegativeTPolynomials.inputs s t 1=0 := rfl
@[simp] private theorem r64_inputs_2 :
    SoleNegativeTPolynomials.inputs s t 2=Real.sin (x (scalar s) t 0) := rfl
@[simp] private theorem r64_inputs_3 :
    SoleNegativeTPolynomials.inputs s t 3=Real.cos (x (scalar s) t 0) := rfl
@[simp] private theorem r64_inputs_4 : SoleNegativeTPolynomials.inputs s t 4=0 := rfl
@[simp] private theorem r64_inputs_5 : SoleNegativeTPolynomials.inputs s t 5=1 := rfl
@[simp] private theorem r64_inputs_6 :
    SoleNegativeTPolynomials.inputs s t 6=Real.sin (SoleTScalarModel.e (scalar s) t 0) := rfl
@[simp] private theorem r64_inputs_7 :
    SoleNegativeTPolynomials.inputs s t 7=Real.cos (SoleTScalarModel.e (scalar s) t 0) := rfl
@[simp] private theorem r64_inputs_8 :
    SoleNegativeTPolynomials.inputs s t 8=Real.sin (SoleNegativeTScalarModel.angle s.row t) := rfl
@[simp] private theorem r64_inputs_9 :
    SoleNegativeTPolynomials.inputs s t 9=Real.cos (SoleNegativeTScalarModel.angle s.row t) := rfl
@[simp] private theorem r64_inputs_10 :
    SoleNegativeTPolynomials.inputs s t 10=Real.sin (SoleTScalarModel.e (scalar s) t 0/2) := rfl
end r64_inputs
@[simp] private theorem r64_scalar_family (s : Case) : (scalar s).family=family s.row := rfl
@[simp] private theorem r64_scalar_td (s : Case) : (scalar s).td=true := rfl
@[simp] private theorem r64_scalar_atG (s : Case) : (scalar s).atG=s.atG := rfl
@[simp] private theorem r64_scalar_negative (s : Case) : (scalar s).negative=index s.row := rfl

@[simp] theorem kE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (kE f)=k f t 0 := by
  cases f <;> norm_num [kE,k,KE,K,tE,zE]
@[simp] theorem ellE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (ellE f)=ell f t 0 := by
  cases f <;> norm_num [ellE,ell,SolePositiveTPolynomials.LE,L,tE,zE]
@[simp] theorem cE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (cE f)=c f t 0 := by
  cases f <;> norm_num [cE,c,CE,SoleTScalarModel.C,KE,K,tE,zE]
@[simp] theorem gE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (gE f)=g f t := by
  cases f <;> norm_num [gE,g,tE]
@[simp] theorem epsilonE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (epsilonE f)=epsilon f t := by
  cases f <;> norm_num [epsilonE,epsilon,tE]
@[simp] theorem etaE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) etaE=eta t := by
  norm_num [etaE,eta,tE]
@[simp] theorem lambdaE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (lambdaE f)=lambda f := by
  unfold lambdaE lambda
  split_ifs <;> norm_num
@[simp] theorem nE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (nE (scalar s))=n (scalar s) t 0 := by
  simp [nE,n,cx,sx]
@[simp] theorem mE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (mE (scalar s))=m (scalar s) t 0 := by
  simp [mE,m,cz,sz]
@[simp] theorem pE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (pE (scalar s))=p (scalar s) t 0 := by
  unfold pE p
  split_ifs <;> simp [ce,se]
@[simp] theorem firstE_value (s : Case) (t : ℝ) (i : Fin 4) :
    Expression.value (inputs s t) (firstE (scalar s) i)=first (scalar s) t 0 i := by
  fin_cases i <;> simp [firstE,first]
@[simp] theorem secondE_value (s : Case) (t : ℝ) (i : Fin 4) :
    Expression.value (inputs s t) (secondE (scalar s) i)=second (scalar s) t 0 i := by
  fin_cases i <;> simp [secondE,second]
@[simp] theorem nuE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (nuE (scalar s))=nu (scalar s) t 0 := by
  unfold nuE nu
  generalize (scalar s).negative=j
  fin_cases j <;> simp
  split_ifs <;> norm_num
@[simp] theorem squareE_value (s : Case) (t : ℝ) (i : Fin 4) :
    Expression.value (inputs s t) (squareE (scalar s) i)=SoleNegativeTScalarModel.square s t i := by
  unfold squareE SoleNegativeTScalarModel.square
  simp only [r64_value_sub,r64_value_add,r64_value_pow,firstE_value,secondE_value]
  split_ifs <;> simp_all [st]
@[simp] theorem correctionE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (correctionE s)=correction s t := by
  unfold correctionE correction
  split_ifs <;> simp
@[simp] theorem removedE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (removedE s)=removed s.row t := by
  unfold removedE removed
  split_ifs <;> norm_num [tE]
@[simp] theorem coefficientE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (coefficientE s)=coefficient s t := by
  unfold coefficientE coefficient
  split_ifs <;> simp

def rootArgument (s : Case) (t : ℝ) (i : Fin 7) : ℝ :=
  if hi : i.val<4 then SoleNegativeTScalarModel.square s t ⟨i.val,hi⟩
  else if i.val=4 then 1+(g (family s.row) t)^2
  else if i.val=5 then 1+(eta t)^2 else 1+(epsilon (family s.row) t)^2

@[simp] theorem rootSquare_value (s : Case) (t : ℝ) (i : Fin 7) :
    Expression.value (inputs s t) (rootSquare (scalar s) i)=rootArgument s t i := by
  unfold rootSquare rootArgument
  split_ifs <;> simp

def upper (s : Case) (t : ℝ) (i : Fin 7) : ℝ :=
  Expression.value (inputs s t) (SoleNegativeTPolynomials.rootExpression s i)

theorem root_lower (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) (i : Fin 7) :
    Real.sqrt (rootArgument s t i)≤upper s t i := by
  have hnon : 0≤rootArgument s t i := by
    dsimp [rootArgument]
    split_ifs
    · exact SoleNegativeTScalarModel.square_nonneg s ht _
    all_goals positivity
  have hh := Expression.sqrt_le_value (inputs s t) («variables» s) (rootSquare (scalar s) i)
    (by simpa using hnon) (seeds_positive s i)
  simpa only [rootSquare_value,upper,SoleNegativeTPolynomials.rootExpression] using hh

def upperETerm (s : Case) (t : ℝ) : ℝ :=
  if tiltedE (family s.row) then
    1+2*Real.cos (SoleTScalarModel.e (scalar s) t 0)+(1+2*epsilon (family s.row) t)*Real.sin (SoleTScalarModel.e (scalar s) t 0)-
      (radiusUpper:ℝ)*Real.sin (SoleTScalarModel.e (scalar s) t 0)*upper s t 6
  else if isDE (family s.row) then
    1+Real.cos (SoleTScalarModel.e (scalar s) t 0)/2+(1-(axisUpper:ℝ))*Real.sin (SoleTScalarModel.e (scalar s) t 0)+3/2*(5/4)
  else 3+Real.sin (SoleTScalarModel.e (scalar s) t 0)-2*(radiusUpper:ℝ)*Real.sin (SoleTScalarModel.e (scalar s) t 0/2)

theorem expression_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (expression s)=
      k (family s.row) t 0*(1+2*Real.cos (x (scalar s) t 0)+
        (1+2*g (family s.row) t)*Real.sin (x (scalar s) t 0))+
      3*c (family s.row) t 0+2*ell (family s.row) t 0-
        (radiusUpper:ℝ)*k (family s.row) t 0*Real.sin (x (scalar s) t 0)*upper s t 4+
      upperETerm s t+correction s t+(21/20)*c (family s.row) t 0*removed s.row t+
        coefficient s t*(Real.cos (SoleNegativeTScalarModel.angle s.row t)-1)-
          (radiusUpper:ℝ)*(upper s t 0+upper s t 1+upper s t 2+upper s t 3) := by
  have hU : ∀ i,Expression.value (inputs s t) (SoleNegativeTPolynomials.rootExpression s i)=
      upper s t i := fun _ => rfl
  unfold SoleNegativeTPolynomials.expression SoleNegativeTPolynomials.baseExpression
    SoleNegativeTPolynomials.eExpression upperETerm
  split_ifs <;>
  simp only [hU,r64_value_sub,r64_value_add,r64_value_mul,
    r64_value_one,r64_value_two,r64_value_three,r64_value_lit,r64_value_var,cx,sx,ce,se,ct,shalf,
    r64_inputs_2,r64_inputs_3,r64_inputs_6,r64_inputs_7,r64_inputs_9,r64_inputs_10,kE_value,
    gE_value,cE_value,ellE_value,epsilonE_value,correctionE_value,removedE_value,
    coefficientE_value] <;> push_cast <;> ring

theorem model_le_actual (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    Expression.value (inputs s t) (expression s)≤
      SoleNegativeTScalarModel.value s (radiusUpper:ℝ) (axisUpper:ℝ) t := by
  have hf := family_mem ht
  have hz : (0:ℝ)∈Set.Icc 0 t := ⟨le_rfl,(angles ht).1.1⟩
  have hk := (coefficient_positive hf hz).1
  have hx := (split_angles (scalar s) hf hz).2.1
  have he := (split_angles (scalar s) hf hz).2.2
  have hR : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hG : Real.sqrt (1+(g (family s.row) t)^2)≤upper s t 4 := by
    simpa [rootArgument] using root_lower s ht 4
  have hE : Real.sqrt (1+(epsilon (family s.row) t)^2)≤upper s t 6 := by
    simpa [rootArgument] using root_lower s ht 6
  have hGp := mul_le_mul_of_nonneg_left hG
    (mul_nonneg (mul_nonneg hR hk.le) (transport_trig hx).2.2.1)
  have hEp := mul_le_mul_of_nonneg_left hE (mul_nonneg hR (transport_trig he).2.2.1)
  have h0 : Real.sqrt (SoleNegativeTScalarModel.square s t 0)≤upper s t 0 := by
    simpa [rootArgument] using root_lower s ht 0
  have h1 : Real.sqrt (SoleNegativeTScalarModel.square s t 1)≤upper s t 1 := by
    simpa [rootArgument] using root_lower s ht 1
  have h2 : Real.sqrt (SoleNegativeTScalarModel.square s t 2)≤upper s t 2 := by
    simpa [rootArgument] using root_lower s ht 2
  have h3 : Real.sqrt (SoleNegativeTScalarModel.square s t 3)≤upper s t 3 := by
    simpa [rootArgument] using root_lower s ht 3
  have hsum := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) hR
  rw [expression_value]
  simp only [SoleNegativeTScalarModel.value,upperETerm,eTerm,primaryCoefficient,
    Fin.sum_univ_four,r64_scalar_family]
  by_cases hT : tiltedE (family s.row)=true <;> by_cases hD : isDE (family s.row)=true <;>
    simp only [hT,hD,Bool.false_eq_true,↓reduceIte] <;> linarith

theorem parameter_surjective (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    ∃ X : ℝ,|X|≤1 ∧ parameterValue s.row X=t := by
  obtain ⟨a,ha⟩ : ∃ a : ℝ,a=(SoleNegativeTScalarModel.left s.row:ℝ) := ⟨_,rfl⟩
  obtain ⟨b,hb⟩ : ∃ b : ℝ,b=(SoleNegativeTScalarModel.right s.row:ℝ) := ⟨_,rfl⟩
  have hab : a<b := by
    rw [ha,hb]
    exact_mod_cast (SoleNegativeTScalarModel.interval_order s.row).2.1
  have hgap : 0<b-a := by linarith
  have ht' : a≤t ∧ t≤b := by
    rw [ha,hb]
    exact ht
  refine ⟨(2*t-a-b)/(b-a),?_,?_⟩
  · apply abs_le.mpr
    constructor
    · rw [le_div_iff₀ hgap]
      linarith [ht'.1]
    · rw [div_le_iff₀ hgap]
      linarith [ht'.2]
  · rw [SoleNegativeTPolynomials.parameterValue,← ha,← hb]
    field_simp
    ring

theorem conservative_positive (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    0<SoleNegativeTScalarModel.value s (radiusUpper:ℝ) (axisUpper:ℝ) t := by
  obtain ⟨X,hX,hXt⟩ := parameter_surjective s ht
  have hh := model_positive s hX (show |(0:ℝ)|≤1 by norm_num)
  rw [hXt] at hh
  exact hh.trans_le (model_le_actual s ht)

theorem antitone_parameters (s : Case) {t R R' M M' : ℝ}
    (ht : t∈SoleNegativeTScalarModel.domain s.row) (hR : R≤R') (hM : M≤M') :
    SoleNegativeTScalarModel.value s R' M' t≤SoleNegativeTScalarModel.value s R M t := by
  have hf := family_mem ht
  have hz : (0:ℝ)∈Set.Icc 0 t := ⟨le_rfl,(angles ht).1.1⟩
  have hk := (coefficient_positive hf hz).1
  have hx := (split_angles (scalar s) hf hz).2.1
  have he := (split_angles (scalar s) hf hz).2.2
  have hhalf : SoleTScalarModel.e (scalar s) t 0/2∈Set.Icc 0 frameCap := by
    have he' := he
    simp only [frameCap,Set.mem_Icc] at he' ⊢
    constructor <;> linarith [he'.1,he'.2]
  have hG := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg (mul_nonneg hk.le (transport_trig hx).2.2.1)
      (Real.sqrt_nonneg (1+(g (family s.row) t)^2)))
  have hE := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg (transport_trig he).2.2.1 (Real.sqrt_nonneg (1+(epsilon (family s.row) t)^2)))
  have hhalf' := mul_nonneg (sub_nonneg.mpr hR) (transport_trig hhalf).2.2.1
  have haxis := mul_nonneg (sub_nonneg.mpr hM) (transport_trig he).2.2.1
  have hsum : 0≤∑i : Fin 4,Real.sqrt (SoleNegativeTScalarModel.square s t i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hnorm := mul_nonneg (sub_nonneg.mpr hR) hsum
  simp only [SoleNegativeTScalarModel.value,eTerm,primaryCoefficient,r64_scalar_family]
  by_cases hT : tiltedE (family s.row)=true <;> by_cases hD : isDE (family s.row)=true <;>
    simp only [hT,hD,Bool.false_eq_true,↓reduceIte] <;> nlinarith

theorem actual_radius_positive (s : Case) {q t : ℝ}
    (hq : q≤qTrial) (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    0<SoleNegativeTScalarModel.value s (Real.sqrt q) (Real.sqrt (q-1/4)) t := by
  have hR := (Real.sqrt_le_sqrt hq).trans SoleTScalarModel.radius_upper.le
  have hM := (Real.sqrt_le_sqrt (sub_le_sub_right hq (1/4))).trans SoleTScalarModel.axis_upper.le
  exact (conservative_positive s ht).trans_le (antitone_parameters s ht hR hM)

end SquaresInCircles.Eight.SoleNegativeTScalar
end
end
end
