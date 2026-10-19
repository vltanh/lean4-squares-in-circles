module

public import SquaresInCircles.Eight.Arithmetic.ClosedCover

/-!
# Eight squares: formulas, derivatives and interval certificates

A `Formula` is a real expression in `n` variables built from rational constants, sums,
negation, products, inverses, square roots and powers. `Formula.diff` is its symbolic partial
derivative, and where every radicand is positive and every inverted value nonzero
(`Formula.RegularAt`) it is the partial derivative of its value, by the ordinary rules of real
differentiation (`Formula.hasDerivAt_partial`).

An interval expression `ScalarExpr` carries rational brackets; erasing them gives a formula with the
same value (`erase`, `erase_eval`), so the brackets do not change the expression whose bound is
proved. A `FormulaCertificate` for a target formula is an interval expression that erases to it;
when it is valid on a box, the target takes its values in the computed interval on the whole box
(`FormulaCertificate.sound`). `StrictValid` adds strict positivity of every radicand and inverted
value, which makes the formula regular on the box (`strictValid_regular`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.ExactFamily
open Arithmetic

inductive Formula (n : ℕ)
  | const (q : ℚ)
  | var (i : Fin n)
  | add (a b : Formula n)
  | neg (a : Formula n)
  | mul (a b : Formula n)
  | inv (a : Formula n)
  | sqrt (a : Formula n)
  | pow (a : Formula n) (k : ℕ)
  deriving DecidableEq

namespace Formula

def eval {n : ℕ} (env : Fin n → ℝ) : Formula n → ℝ
  | .const q => q
  | .var i => env i
  | .add a b => eval env a+eval env b
  | .neg a => -eval env a
  | .mul a b => eval env a*eval env b
  | .inv a => (eval env a)⁻¹
  | .sqrt a => Real.sqrt (eval env a)
  | .pow a k => (eval env a)^k

def plus {n : ℕ} (a b : Formula n) : Formula n :=
  if a = .const 0 then b else if b = .const 0 then a else
    match a,b with
    | .const p,.const q => .const (p+q)
    | a,b => .add a b

def minus {n : ℕ} (a : Formula n) : Formula n :=
  match a with
  | .const q => .const (-q)
  | .neg a => a
  | a => .neg a

def times {n : ℕ} (a b : Formula n) : Formula n :=
  if a = .const 0 ∨ b = .const 0 then .const 0 else
    if a = .const 1 then b else if b = .const 1 then a else
      match a,b with
      | .const p,.const q => .const (p*q)
      | a,b => .mul a b

def power {n : ℕ} (a : Formula n) (k : ℕ) : Formula n :=
  if k=0 then .const 1 else if k=1 then a else .pow a k

def reciprocal {n : ℕ} (a : Formula n) : Formula n :=
  match a with
  | .const q => .const q⁻¹
  | a => .inv a

def quotient {n : ℕ} (a b : Formula n) : Formula n := times a (reciprocal b)

@[simp] theorem eval_plus {n : ℕ} (env : Fin n → ℝ) (a b : Formula n) :
    (plus a b).eval env = a.eval env+b.eval env := by
  unfold plus
  split_ifs with ha hb
  · subst ha; simp [eval]
  · subst hb; simp [eval]
  · split <;> simp [eval]

@[simp] theorem eval_minus {n : ℕ} (env : Fin n → ℝ) (a : Formula n) :
    (minus a).eval env = -a.eval env := by cases a <;> simp [minus,eval]

@[simp] theorem eval_times {n : ℕ} (env : Fin n → ℝ) (a b : Formula n) :
    (times a b).eval env = a.eval env*b.eval env := by
  unfold times
  split_ifs with h hA hB
  · rcases h with rfl | rfl <;> simp [eval]
  · subst a; simp [eval]
  · subst b; simp [eval]
  · cases a <;> cases b <;> simp [eval]

@[simp] theorem eval_power {n : ℕ} (env : Fin n → ℝ) (a : Formula n) (k : ℕ) :
    (power a k).eval env = (a.eval env)^k := by
  unfold power
  split_ifs <;> simp_all [eval]

@[simp] theorem eval_reciprocal {n : ℕ} (env : Fin n → ℝ) (a : Formula n) :
    (reciprocal a).eval env = (a.eval env)⁻¹ := by cases a <;> simp [reciprocal,eval]

@[simp] theorem eval_quotient {n : ℕ} (env : Fin n → ℝ) (a b : Formula n) :
    (quotient a b).eval env = a.eval env/b.eval env := by
  simp [quotient,div_eq_mul_inv]

/-- Symbolic partial derivative, with exact rational constant simplification. -/
def diff {n : ℕ} (i : Fin n) : Formula n → Formula n
  | .const _ => .const 0
  | .var j => .const (if i=j then 1 else 0)
  | .add a b => plus (diff i a) (diff i b)
  | .neg a => minus (diff i a)
  | .mul a b => plus (times (diff i a) b) (times a (diff i b))
  | .inv a => minus (quotient (diff i a) (.pow a 2))
  | .sqrt a => quotient (diff i a) (times (.const 2) (.sqrt a))
  | .pow a k => times (.const k) (times (power a (k-1)) (diff i a))

/-- Strict positive radicands and nonzero denominators justify derivatives. -/
def RegularAt {n : ℕ} (env : Fin n → ℝ) : Formula n → Prop
  | .const _ => True
  | .var _ => True
  | .add a b => RegularAt env a ∧ RegularAt env b
  | .neg a => RegularAt env a
  | .mul a b => RegularAt env a ∧ RegularAt env b
  | .inv a => RegularAt env a ∧ a.eval env ≠ 0
  | .sqrt a => RegularAt env a ∧ 0 < a.eval env
  | .pow a _ => RegularAt env a

def directional {n : ℕ} (env v : Fin n → ℝ) : Formula n → ℝ
  | .const _ => 0
  | .var i => v i
  | .add a b => directional env v a+directional env v b
  | .neg a => -directional env v a
  | .mul a b => directional env v a*b.eval env+a.eval env*directional env v b
  | .inv a => -directional env v a/(a.eval env)^2
  | .sqrt a => directional env v a/(2*Real.sqrt (a.eval env))
  | .pow a k => k*(a.eval env)^(k-1)*directional env v a

theorem directional_eq_partials {n : ℕ} (a : Formula n) (env v : Fin n → ℝ) :
    a.directional env v = ∑ i : Fin n, (a.diff i).eval env*v i := by
  induction a with
  | const q => simp [directional,diff,eval]
  | var j => simp [directional,diff,eval,apply_ite (fun x : ℚ => (x : ℝ)),ite_mul]
  | add a b ha hb => simp [directional,diff,ha,hb,Finset.sum_add_distrib,add_mul]
  | neg a ha => simp [directional,diff,ha,Finset.sum_neg_distrib]
  | mul a b ha hb =>
      simp only [directional,diff,eval_plus,eval_times,ha,hb,Finset.sum_mul,Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
  | inv a ha =>
      simp only [directional,diff,eval_minus,eval_quotient,eval,ha,neg_div,Finset.sum_div,
        ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
  | sqrt a ha =>
      simp only [directional,diff,eval_quotient,eval_times,eval,ha,Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)
  | pow a k ha =>
      simp only [directional,diff,eval_times,eval_power,eval,ha,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)

theorem hasDerivAt_curve {n : ℕ} (a : Formula n) {env : ℝ → Fin n → ℝ}
    {t : ℝ} {v : Fin n → ℝ} (hv : ∀ i, HasDerivAt (fun s => env s i) (v i) t)
    (h : a.RegularAt (env t)) :
    HasDerivAt (fun s => a.eval (env s)) (a.directional (env t) v) t := by
  induction a with
  | const q => simpa [eval,directional] using hasDerivAt_const t (q:ℝ)
  | var i => exact hv i
  | add a b ha hb => exact (ha h.1).fun_add (hb h.2)
  | neg a ha => exact (ha h).fun_neg
  | mul a b ha hb => exact (ha h.1).fun_mul (hb h.2)
  | inv a ha => exact (ha h.1).fun_inv h.2
  | sqrt a ha => exact (ha h.1).sqrt (ne_of_gt h.2)
  | pow a k ha => exact (ha h).fun_pow k

theorem hasDerivAt_partial {n : ℕ} (a : Formula n) (i : Fin n)
    (env : Fin n → ℝ) (h : a.RegularAt env) :
    HasDerivAt (fun t => a.eval (Function.update env i t)) ((a.diff i).eval env) (env i) := by
  induction a with
  | const q => simpa [eval,diff] using hasDerivAt_const (env i) (q:ℝ)
  | var j =>
      by_cases hij : i=j
      · subst hij
        simpa [eval,diff] using hasDerivAt_id' (env i)
      · simpa [eval,diff,hij,Function.update_of_ne (Ne.symm hij)] using
          hasDerivAt_const (env i) (env j)
  | add a b ha hb =>
      simpa [eval,diff] using (ha h.1).fun_add (hb h.2)
  | neg a ha => simpa [eval,diff] using (ha h).fun_neg
  | mul a b ha hb =>
      simpa [eval,diff] using (ha h.1).fun_mul (hb h.2)
  | inv a ha =>
      simpa [eval,diff,neg_div] using (ha h.1).fun_inv (by simpa using h.2)
  | sqrt a ha =>
      simpa [eval,diff] using (ha h.1).sqrt (by simpa using ne_of_gt h.2)
  | pow a k ha =>
      simpa [eval,diff,mul_assoc] using (ha h).fun_pow k

end Formula

end SquaresInCircles.Eight.ExactFamily
