module

public import SquaresInCircles.Eight.Arithmetic.Bernstein
public import SquaresInCircles.Eight.Arithmetic.ScalarExpr
public import SquaresInCircles.Eight.Arithmetic.ClosedCover

/-!
# Coefficient interval propagation

Real coefficients may depend on an angle (Taylor remainder witnesses do).
At each fixed angle the coefficient relation below is sufficient; no
derivative or continuity of those coefficients is used.  Multiplication is
the actual polynomial convolution, with four-corner interval multiplication
at every coefficient product.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

namespace RealPoly
abbrev T := List ℝ
def eval : T → ℝ → ℝ
  | [],_ => 0 | a::p,x => a+x*eval p x
def add : T → T → T
  | [],q => q | p,[] => p | a::p,b::q => (a+b)::add p q
def neg (p : T) : T := p.map (-·)
def scale (a : ℝ) (p : T) : T := p.map (a*·)
def mul : T → T → T
  | [],_ => [] | a::p,q => add (scale a q) (0::mul p q)
def pow (p : T) : ℕ → T
  | 0 => [1] | k+1 => mul (pow p k) p

theorem eval_add (p q : T) (x : ℝ) : eval (add p q) x = eval p x+eval q x := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih => cases q <;> simp [add,eval,ih] <;> ring

theorem eval_neg (p : T) (x : ℝ) : eval (neg p) x = -eval p x := by
  induction p with
  | nil => simp [neg,eval]
  | cons a p ih =>
      simp only [neg,List.map_cons,eval] at ih ⊢
      rw [ih]
      ring

theorem eval_scale (a : ℝ) (p : T) (x : ℝ) : eval (scale a p) x = a*eval p x := by
  induction p with
  | nil => simp [scale,eval]
  | cons b p ih =>
      simp only [scale,List.map_cons,eval] at ih ⊢
      rw [ih]
      ring

theorem eval_mul (p q : T) (x : ℝ) : eval (mul p q) x = eval p x*eval q x := by
  induction p <;> simp [mul,eval,eval_add,eval_scale, *] <;> ring

theorem eval_pow (p : T) (n : ℕ) (x : ℝ) : eval (pow p n) x = (eval p x)^n := by
  induction n <;> simp [pow,eval,eval_mul,pow_succ, *]
end RealPoly

namespace IntervalPoly
abbrev T := List QInterval
def add : T → T → T
  | [],q => q | p,[] => p | a::p,b::q => a.add b::add p q
def neg (p : T) : T := p.map QInterval.neg
def scale (a : QInterval) (p : T) : T := p.map (QInterval.mul a)
def mul : T → T → T
  | [],_ => [] | a::p,q => add (scale a q) (QInterval.point 0::mul p q)
def pow (p : T) : ℕ → T
  | 0 => [QInterval.point 1] | k+1 => mul (pow p k) p
def lower (p : T) : QPoly := p.map QInterval.lo
def upper (p : T) : QPoly := p.map QInterval.hi
def Rel (p : T) (a : RealPoly.T) : Prop := List.Forall₂ QInterval.Mem p a

theorem rel_add {p q : T} {a b : RealPoly.T} (hp : Rel p a) (hq : Rel q b) :
    Rel (add p q) (RealPoly.add a b) := by
  induction hp generalizing q b with
  | nil => simpa [add,RealPoly.add] using hq
  | @cons I x p a hx hp ih =>
      cases hq with
      | nil => simpa [add,RealPoly.add,Rel] using List.Forall₂.cons hx hp
      | cons hy hq => exact List.Forall₂.cons (QInterval.mem_add hx hy) (ih hq)

theorem rel_neg {p : T} {a : RealPoly.T} (hp : Rel p a) :
    Rel (neg p) (RealPoly.neg a) := by
  induction hp with
  | nil => exact List.Forall₂.nil
  | cons hx hp ih => exact List.Forall₂.cons (QInterval.mem_neg hx) ih

theorem rel_scale {I : QInterval} {x : ℝ} {p : T} {a : RealPoly.T}
    (hI : I.Mem x) (hp : Rel p a) : Rel (scale I p) (RealPoly.scale x a) := by
  induction hp with
  | nil => exact List.Forall₂.nil
  | cons hx hp ih => exact List.Forall₂.cons (QInterval.mem_mul hI hx) ih

theorem rel_mul {p q : T} {a b : RealPoly.T} (hp : Rel p a) (hq : Rel q b) :
    Rel (mul p q) (RealPoly.mul a b) := by
  induction hp with
  | nil => exact List.Forall₂.nil
  | cons hx hp ih =>
      exact rel_add (rel_scale hx hq)
        (List.Forall₂.cons (by simpa using QInterval.mem_point (0 : ℚ)) ih)

theorem rel_pow {p : T} {a : RealPoly.T} (hp : Rel p a) (n : ℕ) :
    Rel (pow p n) (RealPoly.pow a n) := by
  induction n with
  | zero => exact List.Forall₂.cons (by simpa using QInterval.mem_point (1 : ℚ)) List.Forall₂.nil
  | succ n ih => exact rel_mul ih hp

theorem lower_upper {p : T} {a : RealPoly.T} (hp : Rel p a) {x : ℝ} (hx : 0 ≤ x) :
    (lower p).eval x ≤ RealPoly.eval a x ∧ RealPoly.eval a x ≤ (upper p).eval x := by
  induction hp with
  | nil => exact ⟨le_rfl,le_rfl⟩
  | cons hhead htail ih =>
      have hlow := mul_le_mul_of_nonneg_left ih.1 hx
      have hupp := mul_le_mul_of_nonneg_left ih.2 hx
      simp only [lower,upper,List.map_cons,QPoly.eval,RealPoly.eval] at hlow hupp ⊢
      constructor <;> linarith [hhead.1,hhead.2]
end IntervalPoly

/-- A polynomial in the angle whose coefficients are real scalar expressions.
Scalar leaves may include algebraic endpoints, pi brackets supplied as input,
and pointwise sine/cosine remainder coefficients. -/
inductive ParamPoly (n : ℕ)
  | scalar (e : ScalarExpr n)
  | angle
  | add (a b : ParamPoly n)
  | neg (a : ParamPoly n)
  | mul (a b : ParamPoly n)
  | pow (a : ParamPoly n) (exponent : ℕ)
  deriving DecidableEq, Repr

namespace ParamPoly
def sub {n : ℕ} (a b : ParamPoly n) : ParamPoly n := add a (neg b)
def constant {n : ℕ} (q : ℚ) : ParamPoly n := scalar (.const q)
def scale {n : ℕ} (q : ℚ) (p : ParamPoly n) : ParamPoly n := mul (constant q) p

def eval {n : ℕ} (env : Fin n → ℝ) (x : ℝ) : ParamPoly n → ℝ
  | .scalar e => e.eval env | .angle => x
  | .add a b => eval env x a+eval env x b
  | .neg a => -eval env x a
  | .mul a b => eval env x a*eval env x b
  | .pow a k => (eval env x a)^k

def actual {n : ℕ} (env : Fin n → ℝ) : ParamPoly n → RealPoly.T
  | .scalar e => [e.eval env] | .angle => [0,1]
  | .add a b => RealPoly.add (actual env a) (actual env b)
  | .neg a => RealPoly.neg (actual env a)
  | .mul a b => RealPoly.mul (actual env a) (actual env b)
  | .pow a k => RealPoly.pow (actual env a) k

def compile {n : ℕ} (boxes : QBox n) : ParamPoly n → IntervalPoly.T
  | .scalar e => [e.range boxes] | .angle => [QInterval.point 0,QInterval.point 1]
  | .add a b => IntervalPoly.add (compile boxes a) (compile boxes b)
  | .neg a => IntervalPoly.neg (compile boxes a)
  | .mul a b => IntervalPoly.mul (compile boxes a) (compile boxes b)
  | .pow a k => IntervalPoly.pow (compile boxes a) k

def Valid {n : ℕ} (boxes : QBox n) : ParamPoly n → Prop
  | .scalar e => e.Valid boxes | .angle => True
  | .add a b => Valid boxes a ∧ Valid boxes b
  | .neg a => Valid boxes a
  | .mul a b => Valid boxes a ∧ Valid boxes b
  | .pow a _ => Valid boxes a

instance validDecidable {n : ℕ} (boxes : QBox n) (p : ParamPoly n) :
    Decidable (p.Valid boxes) := by
  induction p with
  | scalar e => exact inferInstanceAs (Decidable (e.Valid boxes))
  | angle => exact isTrue True.intro
  | add a b ha hb => exact @instDecidableAnd _ _ ha hb
  | neg a ha => exact ha
  | mul a b ha hb => exact @instDecidableAnd _ _ ha hb
  | pow a k ha => exact ha

theorem actual_eval {n : ℕ} (env : Fin n → ℝ) (x : ℝ) (p : ParamPoly n) :
    RealPoly.eval (p.actual env) x = p.eval env x := by
  induction p <;>
    simp [actual,eval,RealPoly.eval,RealPoly.eval_add,RealPoly.eval_neg,
      RealPoly.eval_mul,RealPoly.eval_pow, *]

theorem compile_rel {n : ℕ} (boxes : QBox n) (p : ParamPoly n)
    (hp : p.Valid boxes) (env : Fin n → ℝ) (henv : boxes.Mem env) :
    IntervalPoly.Rel (p.compile boxes) (p.actual env) := by
  induction p with
  | scalar e => exact List.Forall₂.cons (ScalarExpr.sound boxes e hp env henv) List.Forall₂.nil
  | angle =>
      exact List.Forall₂.cons (by simpa using QInterval.mem_point (0 : ℚ))
        (List.Forall₂.cons (by simpa using QInterval.mem_point (1 : ℚ)) List.Forall₂.nil)
  | add a b ha hb => exact IntervalPoly.rel_add (ha hp.1) (hb hp.2)
  | neg a ha => exact IntervalPoly.rel_neg (ha hp)
  | mul a b ha hb => exact IntervalPoly.rel_mul (ha hp.1) (hb hp.2)
  | pow a k ha => exact IntervalPoly.rel_pow (ha hp) k

theorem sound {n : ℕ} (boxes : QBox n) (p : ParamPoly n)
    (hp : p.Valid boxes) (env : Fin n → ℝ) (henv : boxes.Mem env)
    {x : ℝ} (hx : 0 ≤ x) :
    (IntervalPoly.lower (p.compile boxes)).eval x ≤ p.eval env x ∧
    p.eval env x ≤ (IntervalPoly.upper (p.compile boxes)).eval x := by
  simpa [actual_eval] using IntervalPoly.lower_upper (compile_rel boxes p hp env henv) hx

/-- A proved finite Bernstein certificate for the compiled lower polynomial
therefore proves the full real parametric expression on its closed interval. -/
theorem positive_of_bernstein {n : ℕ} {boxes : QBox n} {p : ParamPoly n}
    (hp : p.Valid boxes) {r : BernsteinRow} {margin : ℚ} (hr : r.Valid margin)
    (hm : 0 < margin) (hpoly : r.polynomial = IntervalPoly.lower (p.compile boxes))
    (env : Fin n → ℝ) (henv : boxes.Mem env) {x : ℝ}
    (hx : r.interval.Mem x) (hx0 : 0 ≤ x) : 0 < p.eval env x := by
  have h := hr.positive hm hx
  rw [hpoly] at h
  exact h.trans_le (sound boxes p hp env henv hx0).1
end ParamPoly

end SquaresInCircles.Eight.Arithmetic
