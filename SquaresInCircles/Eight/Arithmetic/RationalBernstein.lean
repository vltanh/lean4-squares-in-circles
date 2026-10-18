module

public import SquaresInCircles.Eight.Arithmetic.IntervalPolynomial

/-!
# Decidable rational polynomial identities

The expansion identity can be checked as equality in `Polynomial ℚ`, then
transported through evaluation into ℝ.  This avoids emitting thousands of
digits of duplicated Bernstein coefficients for each large-table row.  All
arithmetic still enters through ordinary Lean equality proofs.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.Arithmetic

def QPoly.toPolynomial : QPoly → Polynomial ℚ
  | [] => 0
  | a::p => Polynomial.C a+Polynomial.X*QPoly.toPolynomial p

def QPoly.evalRat : QPoly → ℚ → ℚ
  | [],_ => 0 | a::p,x => a+x*QPoly.evalRat p x

theorem QPoly.evalRat_cast (p : QPoly) (x : ℚ) : (p.evalRat x : ℝ) = p.eval x := by
  induction p <;> simp [evalRat,eval, *]

theorem QPoly.eval_toPolynomial (p : QPoly) (x : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) x p.toPolynomial = p.eval x := by
  induction p <;> simp [toPolynomial,eval, *]

def rationalBernstein (n : ℕ) (b : ℕ → ℚ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (n+1), Polynomial.C (b i*(n.choose i : ℚ))*
    Polynomial.X^i*(1-Polynomial.X)^(n-i)

theorem rationalBernstein_eval (n : ℕ) (b : ℕ → ℚ) (x : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) x (rationalBernstein n b) = bernsteinEval n b x := by
  simp only [rationalBernstein,bernsteinEval,bernsteinBasis,Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_natCast,Polynomial.eval₂_pow,
    Polynomial.eval₂_sub,Polynomial.eval₂_one,Polynomial.eval₂_X,map_mul,map_natCast,
    Rat.coe_castHom]
  ring

def BernsteinRow.AlgebraicIdentity (r : BernsteinRow) : Prop :=
  r.polynomial.toPolynomial.comp
    (Polynomial.C r.interval.lo+Polynomial.C (r.interval.hi-r.interval.lo)*Polynomial.X) =
      rationalBernstein r.degree r.coefficient

instance (r : BernsteinRow) : Decidable r.AlgebraicIdentity := by
  unfold BernsteinRow.AlgebraicIdentity; infer_instance

theorem BernsteinRow.expansion_of_algebraic {r : BernsteinRow} (hr : r.AlgebraicIdentity) (t : ℝ) :
    r.polynomial.eval ((r.interval.lo : ℝ)+(r.interval.hi-r.interval.lo : ℚ)*t) =
      bernsteinEval r.degree r.coefficient t := by
  have he := congrArg (fun p : Polynomial ℚ => Polynomial.eval₂ (Rat.castHom ℝ) t p) hr
  simpa [AlgebraicIdentity,Polynomial.eval₂_comp,QPoly.eval_toPolynomial,rationalBernstein_eval] using he

def transformedCoefficient (p : QPoly) (n : ℕ) (lo hi : ℚ) (j : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n+1), if j ≤ i then
    p.getD i 0*(i.choose j : ℚ)*lo^(i-j)*(hi-lo)^j else 0

def convertedCoefficient (p : QPoly) (n : ℕ) (lo hi : ℚ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k+1), transformedCoefficient p n lo hi j*
    (k.choose j : ℚ)/(n.choose j : ℚ)

def makeBernsteinRow (p : QPoly) (I : QInterval) : BernsteinRow :=
  let n := p.length-1
  { interval := I, polynomial := p, degree := n,
    coefficients := List.ofFn (fun i : Fin (n+1) => convertedCoefficient p n I.lo I.hi i) }

def BernsteinRow.StrictCheck (r : BernsteinRow) : Prop :=
  if r.interval.lo = r.interval.hi then 0 < r.polynomial.evalRat r.interval.lo
  else r.interval.lo < r.interval.hi ∧ r.AlgebraicIdentity ∧
    (∀ i : Fin (r.degree+1), 0 < r.coefficient i)

def BernsteinRow.WeakCheck (r : BernsteinRow) : Prop :=
  if r.interval.lo = r.interval.hi then 0 ≤ r.polynomial.evalRat r.interval.lo
  else r.interval.lo < r.interval.hi ∧ r.AlgebraicIdentity ∧
    (∀ i : Fin (r.degree+1), 0 ≤ r.coefficient i)

instance (r : BernsteinRow) : Decidable r.StrictCheck := by
  unfold BernsteinRow.StrictCheck; infer_instance
instance (r : BernsteinRow) : Decidable r.WeakCheck := by
  unfold BernsteinRow.WeakCheck; infer_instance

theorem BernsteinRow.strictCheck_sound {r : BernsteinRow} (hr : r.StrictCheck)
    {x : ℝ} (hx : r.interval.Mem x) : 0 < r.polynomial.eval x := by
  by_cases he : r.interval.lo=r.interval.hi
  · have hp : 0 < r.polynomial.evalRat r.interval.lo := by simpa [StrictCheck,he] using hr
    have hxe : x=(r.interval.lo : ℝ) := by
      apply le_antisymm
      · simpa [← he] using hx.2
      · exact hx.1
    rw [hxe,← QPoly.evalRat_cast]
    exact_mod_cast hp
  · have hp : r.interval.lo < r.interval.hi ∧ r.AlgebraicIdentity ∧
        (∀ i : Fin (r.degree+1), 0 < r.coefficient i) := by simpa [StrictCheck,he] using hr
    have hd : (0 : ℝ) < (r.interval.hi-r.interval.lo : ℚ) := by exact_mod_cast sub_pos.mpr hp.1
    let t := (x-r.interval.lo)/(r.interval.hi-r.interval.lo : ℚ)
    have ht : 0 ≤ t ∧ t ≤ 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hx.1) hd.le
      · apply (div_le_one hd).mpr
        push_cast
        linarith [hx.2]
    have hident : (r.interval.lo : ℝ)+(r.interval.hi-r.interval.lo : ℚ)*t=x := by
      dsimp [t]
      field_simp [ne_of_gt hd]
      ring
    have hb : ∀ i, i ≤ r.degree → 0 < r.coefficient i :=
      fun i hi => hp.2.2 ⟨i,Nat.lt_succ_of_le hi⟩
    have hh := bernstein_positive ht hb
    rw [← r.expansion_of_algebraic hp.2.1 t,hident] at hh
    exact hh

theorem BernsteinRow.weakCheck_sound {r : BernsteinRow} (hr : r.WeakCheck)
    {x : ℝ} (hx : r.interval.Mem x) : 0 ≤ r.polynomial.eval x := by
  by_cases he : r.interval.lo=r.interval.hi
  · have hp : 0 ≤ r.polynomial.evalRat r.interval.lo := by simpa [WeakCheck,he] using hr
    have hxe : x=(r.interval.lo : ℝ) := by
      apply le_antisymm
      · simpa [← he] using hx.2
      · exact hx.1
    rw [hxe,← QPoly.evalRat_cast]
    exact_mod_cast hp
  · have hp : r.interval.lo < r.interval.hi ∧ r.AlgebraicIdentity ∧
        (∀ i : Fin (r.degree+1), 0 ≤ r.coefficient i) := by simpa [WeakCheck,he] using hr
    have hd : (0 : ℝ) < (r.interval.hi-r.interval.lo : ℚ) := by exact_mod_cast sub_pos.mpr hp.1
    let t := (x-r.interval.lo)/(r.interval.hi-r.interval.lo : ℚ)
    have ht : 0 ≤ t ∧ t ≤ 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hx.1) hd.le
      · apply (div_le_one hd).mpr
        push_cast
        linarith [hx.2]
    have hident : (r.interval.lo : ℝ)+(r.interval.hi-r.interval.lo : ℚ)*t=x := by
      dsimp [t]
      field_simp [ne_of_gt hd]
      ring
    have hb : ∀ i, i ≤ r.degree → 0 ≤ r.coefficient i :=
      fun i hi => hp.2.2 ⟨i,Nat.lt_succ_of_le hi⟩
    have hh := bernstein_lower ht hb
    rw [← r.expansion_of_algebraic hp.2.1 t,hident] at hh
    exact_mod_cast hh

def ParamPoly.strictCheck {n : ℕ} (boxes : QBox n) (I : QInterval) (p : ParamPoly n) : Prop :=
  p.Valid boxes ∧ (makeBernsteinRow (IntervalPoly.lower (p.compile boxes)) I).StrictCheck

def ParamPoly.weakCheck {n : ℕ} (boxes : QBox n) (I : QInterval) (p : ParamPoly n) : Prop :=
  p.Valid boxes ∧ (makeBernsteinRow (IntervalPoly.lower (p.compile boxes)) I).WeakCheck

instance {n : ℕ} (boxes : QBox n) (I : QInterval) (p : ParamPoly n) :
    Decidable (p.strictCheck boxes I) := by unfold ParamPoly.strictCheck; infer_instance

instance {n : ℕ} (boxes : QBox n) (I : QInterval) (p : ParamPoly n) :
    Decidable (p.weakCheck boxes I) := by unfold ParamPoly.weakCheck; infer_instance

theorem ParamPoly.strictCheck_sound {n : ℕ} {boxes : QBox n} {I : QInterval} {p : ParamPoly n}
    (hp : p.strictCheck boxes I) {env : Fin n → ℝ} (henv : boxes.Mem env)
    {x : ℝ} (hx : I.Mem x) (hx0 : 0 ≤ x) : 0 < p.eval env x :=
  (BernsteinRow.strictCheck_sound hp.2 hx).trans_le (p.sound boxes hp.1 env henv hx0).1

theorem ParamPoly.weakCheck_sound {n : ℕ} {boxes : QBox n} {I : QInterval} {p : ParamPoly n}
    (hp : p.weakCheck boxes I) {env : Fin n → ℝ} (henv : boxes.Mem env)
    {x : ℝ} (hx : I.Mem x) (hx0 : 0 ≤ x) : 0 ≤ p.eval env x :=
  (BernsteinRow.weakCheck_sound hp.2 hx).trans (p.sound boxes hp.1 env henv hx0).1

end SquaresInCircles.Eight.Arithmetic
