module

public import SquaresInCircles.Eight.Arithmetic.ClosedCover

/-!
# Differential semantics for the stationary interval certificates

The unannotated formula is independent of the rational interval brackets.
Erasing an enclosure does not erase the expression whose bound is proved.
The derivative interpreter is justified by ordinary real derivative rules.
No external evaluator or native-decide axiom is used.
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
  deriving DecidableEq, Repr

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
  split_ifs <;> subst_vars <;> simp_all [eval]
  cases a <;> cases b <;> simp [eval]

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
  | var j => simp [directional,diff,eval]
  | add a b ha hb => simp [directional,diff,ha,hb,Finset.sum_add_distrib,add_mul]
  | neg a ha => simp [directional,diff,ha,Finset.sum_neg_distrib]
  | mul a b ha hb =>
      simp [directional,diff,ha,hb,Finset.sum_add_distrib,Finset.sum_mul,
        Finset.mul_sum,add_mul,mul_assoc,mul_comm,mul_left_comm]
  | inv a ha =>
      simp [directional,diff,ha,Finset.sum_mul,Finset.sum_neg_distrib,
        div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
  | sqrt a ha =>
      simp [directional,diff,ha,Finset.sum_mul,div_eq_mul_inv,
        mul_assoc,mul_comm,mul_left_comm]
  | pow a k ha =>
      simp [directional,diff,ha,eval,Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm]

theorem hasDerivAt_curve {n : ℕ} (a : Formula n) {env : ℝ → Fin n → ℝ}
    {t : ℝ} {v : Fin n → ℝ} (hv : ∀ i, HasDerivAt (fun s => env s i) (v i) t)
    (h : a.RegularAt (env t)) :
    HasDerivAt (fun s => a.eval (env s)) (a.directional (env t) v) t := by
  induction a with
  | const q => simpa [eval,directional] using hasDerivAt_const t (q:ℝ)
  | var i => exact hv i
  | add a b ha hb => exact (ha h.1).add (hb h.2)
  | neg a ha => exact (ha h).neg
  | mul a b ha hb => exact (ha h.1).mul (hb h.2)
  | inv a ha => simpa [directional,eval] using (ha h.1).inv h.2
  | sqrt a ha => simpa [directional,eval] using (ha h.1).sqrt (ne_of_gt h.2)
  | pow a k ha => simpa [directional,eval,mul_assoc] using (ha h).pow k

theorem hasDerivAt_partial {n : ℕ} (a : Formula n) (i : Fin n)
    (env : Fin n → ℝ) (h : a.RegularAt env) :
    HasDerivAt (fun t => a.eval (Function.update env i t)) ((a.diff i).eval env) (env i) := by
  induction a with
  | const q => simpa [eval,diff] using hasDerivAt_const (env i) (q:ℝ)
  | var j =>
      by_cases hij : i=j
      · subst j
        simpa [eval,diff] using hasDerivAt_id (env i)
      · simpa [eval,diff,hij,Ne.symm hij,Function.update_of_ne (Ne.symm hij)] using
          hasDerivAt_const (env i) (env j)
  | add a b ha hb =>
      simpa [eval,diff] using (ha h.1).add (hb h.2)
  | neg a ha => simpa [eval,diff] using (ha h).neg
  | mul a b ha hb =>
      simpa [eval,diff] using (ha h.1).mul (hb h.2)
  | inv a ha => simpa [eval,diff,div_eq_mul_inv] using (ha h.1).inv h.2
  | sqrt a ha =>
      simpa [eval,diff] using (ha h.1).sqrt (ne_of_gt h.2)
  | pow a k ha =>
      simpa [eval,diff,Nat.cast_ofNat,mul_assoc,mul_comm,mul_left_comm] using (ha h).pow k

end Formula

def erase {n : ℕ} : ScalarExpr n → Formula n
  | .const q => .const q
  | .var i => .var i
  | .add a b => .add (erase a) (erase b)
  | .neg a => .neg (erase a)
  | .mul a b => .mul (erase a) (erase b)
  | .inv a => .inv (erase a)
  | .sqrt a _ => .sqrt (erase a)
  | .pow a k => .pow (erase a) k
  | .enclose a _ => erase a

theorem erase_eval {n : ℕ} (a : ScalarExpr n) (env : Fin n → ℝ) :
    (erase a).eval env = a.eval env := by
  induction a <;> simp_all [erase,Formula.eval,ScalarExpr.eval]

/-- Positivity of radicands is explicit and independent of the ordinary weak
square-root enclosure predicate. -/
def StrictValid {n : ℕ} (box : QBox n) : ScalarExpr n → Prop
  | .const _ => True
  | .var _ => True
  | .add a b => StrictValid box a ∧ StrictValid box b
  | .neg a => StrictValid box a
  | .mul a b => StrictValid box a ∧ StrictValid box b
  | .inv a => StrictValid box a ∧ 0 < (a.range box).lo
  | .sqrt a _ => StrictValid box a ∧ 0 < (a.range box).lo
  | .pow a _ => StrictValid box a
  | .enclose a _ => StrictValid box a

instance strictValidDecidable {n : ℕ} (box : QBox n) (a : ScalarExpr n) :
    Decidable (StrictValid box a) := by
  induction a <;> simp only [StrictValid] <;> infer_instance

theorem strictValid_regular {n : ℕ} (box : QBox n) (a : ScalarExpr n)
    (hv : a.Valid box) (hs : StrictValid box a) {env : Fin n → ℝ} (he : box.Mem env) :
    (erase a).RegularAt env := by
  induction a with
  | const q => trivial
  | var i => trivial
  | add a b ha hb => exact ⟨ha hv.1 hs.1,hb hv.2 hs.2⟩
  | neg a ha => exact ha hv hs
  | mul a b ha hb => exact ⟨ha hv.1 hs.1,hb hv.2 hs.2⟩
  | inv a ha =>
      refine ⟨ha hv.1 hs.1,?_⟩
      rw [erase_eval]
      exact ne_of_gt (ScalarExpr.positive box a hv.1 hs.2 env he)
  | sqrt a J ha =>
      refine ⟨ha hv.1 hs.1,?_⟩
      rw [erase_eval]
      exact ScalarExpr.positive box a hv.1 hs.2 env he
  | pow a k ha => exact ha hv hs
  | enclose a J ha => exact ha hv.1 hs

/-- An exact interval certificate also fixes the entire expression syntax. -/
structure FormulaCertificate (n : ℕ) where
  expression : ScalarExpr n
  deriving DecidableEq, Repr

def FormulaCertificate.Valid {n : ℕ} (c : FormulaCertificate n)
    (box : QBox n) (target : Formula n) : Prop :=
  erase c.expression = target ∧ c.expression.Valid box

instance {n : ℕ} (c : FormulaCertificate n) (box : QBox n) (target : Formula n) :
    Decidable (c.Valid box target) := by unfold FormulaCertificate.Valid; infer_instance

theorem FormulaCertificate.sound {n : ℕ} {c : FormulaCertificate n}
    {box : QBox n} {target : Formula n} (hc : c.Valid box target)
    {env : Fin n → ℝ} (he : box.Mem env) :
    (c.expression.range box).Mem (target.eval env) := by
  rw [← hc.1,erase_eval]
  exact ScalarExpr.sound box c.expression hc.2 env he

end SquaresInCircles.Eight.ExactFamily
