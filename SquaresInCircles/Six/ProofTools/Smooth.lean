import SquaresInCircles.Six.ProofTools.Certificate
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differentiation with an explicit regularity certificate

Only smooth operations are admitted in this syntax. Constant subexpressions
are recognized structurally and need no spurious nonzero-radicand premise.
Every variable-dependent reciprocal or square root has an explicit regularity
guard. The soundness theorem proves HasDerivAt from those real guards; an
interval derivative calculation alone is never treated as differentiability.
-/

namespace SquaresInCircles.Six.ProofTools

inductive Smooth (n : ℕ) where
  | var : Fin n → Smooth n
  | rat : ℚ → Smooth n
  | pi : Smooth n
  | add : Smooth n → Smooth n → Smooth n
  | neg : Smooth n → Smooth n
  | mul : Smooth n → Smooth n → Smooth n
  | inv : Smooth n → Smooth n
  | sqrt : Smooth n → Smooth n
  | sin : Smooth n → Smooth n
  | cos : Smooth n → Smooth n
  deriving DecidableEq, Repr

namespace Smooth

instance {n : ℕ} : Add (Smooth n) := ⟨Smooth.add⟩
instance {n : ℕ} : Neg (Smooth n) := ⟨Smooth.neg⟩
instance {n : ℕ} : Sub (Smooth n) := ⟨fun a b => .add a (.neg b)⟩
instance {n : ℕ} : Mul (Smooth n) := ⟨Smooth.mul⟩
instance {n : ℕ} : Div (Smooth n) := ⟨fun a b => .mul a (.inv b)⟩
instance {n k : ℕ} : OfNat (Smooth n) k := ⟨.rat k⟩

def expr {n : ℕ} : Smooth n → Expr n
  | .var i => .var i
  | .rat q => .rat q
  | .pi => .pi
  | .add a b => .add a.expr b.expr
  | .neg a => .neg a.expr
  | .mul a b => .mul a.expr b.expr
  | .inv a => .inv a.expr
  | .sqrt a => .sqrt a.expr
  | .sin a => .sin a.expr
  | .cos a => .cos a.expr

noncomputable def value {n : ℕ} (e : Smooth n) (x : Fin n → ℝ) : ℝ := Expr.denote e.expr x

def depends {n : ℕ} (i : Fin n) : Smooth n → Bool
  | .var j => decide (j=i)
  | .rat _ => false
  | .pi => false
  | .add a b => depends i a || depends i b
  | .neg a => depends i a
  | .mul a b => depends i a || depends i b
  | .inv a => depends i a
  | .sqrt a => depends i a
  | .sin a => depends i a
  | .cos a => depends i a

/-- Structural differentiation. A constant subexpression has derivative zero,
even when written using inverses or square roots. -/
def derivative {n : ℕ} (i : Fin n) (e : Smooth n) : Smooth n :=
  if depends i e then
    match e with
    | .var _ => 1
    | .rat _ => 0
    | .pi => 0
    | .add a b => derivative i a+derivative i b
    | .neg a => -derivative i a
    | .mul a b => derivative i a*b+a*derivative i b
    | .inv a => -derivative i a/(a*a)
    | .sqrt a => derivative i a/(2*.sqrt a)
    | .sin a => .cos a*derivative i a
    | .cos a => -.sin a*derivative i a
  else 0

/-- Sufficient conditions for each variable-dependent operation to be smooth.
These are formulas about actual real values, not numerical flags. -/
def regular {n : ℕ} (i : Fin n) (e : Smooth n) : Formula n :=
  if depends i e then
    match e with
    | .var _ => .top
    | .rat _ => .top
    | .pi => .top
    | .add a b => .conj (regular i a) (regular i b)
    | .neg a => regular i a
    | .mul a b => .conj (regular i a) (regular i b)
    | .inv a => .conj (regular i a) (.disj (.lt 0 a.expr) (.lt a.expr 0))
    | .sqrt a => .conj (regular i a) (.lt 0 a.expr)
    | .sin a => regular i a
    | .cos a => regular i a
  else .top

lemma value_update_of_free {n : ℕ} (i : Fin n) (e : Smooth n)
    (h : depends i e=false) (x : Fin n → ℝ) (t : ℝ) :
    e.value (Function.update x i t)=e.value x := by
  induction e with
  | var j =>
    have hji : j≠i := by simpa [depends] using h
    simp [value,expr,Expr.denote,hji]
  | rat q => rfl
  | pi => rfl
  | add a b ha hb =>
    have hh : depends i a=false ∧ depends i b=false := by simpa [depends] using h
    change a.value (Function.update x i t)+b.value (Function.update x i t)=a.value x+b.value x
    rw [ha hh.1,hb hh.2]
  | neg a ha =>
    change -a.value (Function.update x i t)= -a.value x
    rw [ha h]
  | mul a b ha hb =>
    have hh : depends i a=false ∧ depends i b=false := by simpa [depends] using h
    change a.value (Function.update x i t)*b.value (Function.update x i t)=a.value x*b.value x
    rw [ha hh.1,hb hh.2]
  | inv a ha =>
    change 1/a.value (Function.update x i t)=1/a.value x
    rw [ha h]
  | sqrt a ha =>
    change Real.sqrt (a.value (Function.update x i t))=Real.sqrt (a.value x)
    rw [ha h]
  | sin a ha =>
    change Real.sin (a.value (Function.update x i t))=Real.sin (a.value x)
    rw [ha h]
  | cos a ha =>
    change Real.cos (a.value (Function.update x i t))=Real.cos (a.value x)
    rw [ha h]

private lemma free_hasDerivAt {n : ℕ} (i : Fin n) (e : Smooth n)
    (h : depends i e=false) (x : Fin n → ℝ) :
    HasDerivAt (fun t => e.value (Function.update x i t)) ((derivative i e).value x) (x i) := by
  have hf : (fun t => e.value (Function.update x i t))=fun _ => e.value x := by
    funext t
    exact value_update_of_free i e h x t
  rw [hf,derivative,h]
  exact hasDerivAt_const (x i) (e.value x)

/-- The symbolic derivative is a real derivative whenever the regularity
formula holds. The proof is structural and does not call an external solver. -/
theorem hasDerivAt {n : ℕ} (i : Fin n) (e : Smooth n) (x : Fin n → ℝ)
    (hreg : Formula.Holds (regular i e) x) :
    HasDerivAt (fun t => e.value (Function.update x i t)) ((derivative i e).value x) (x i) := by
  induction e with
  | var j =>
    by_cases hji : j=i
    · subst j
      simpa [value,expr,Expr.denote,derivative,depends] using hasDerivAt_id (x i)
    · exact free_hasDerivAt i (.var j) (by simp [depends,hji]) x
  | rat q => exact free_hasDerivAt i (.rat q) rfl x
  | pi => exact free_hasDerivAt i .pi rfl x
  | add a b ha hb =>
    by_cases hd : depends i (.add a b)=false
    · exact free_hasDerivAt i (.add a b) hd x
    · have ht : depends i (.add a b)=true := Bool.eq_true_of_not_eq_false hd
      have h : Formula.Holds (regular i a) x ∧ Formula.Holds (regular i b) x := by
        simpa only [regular,ht,if_true,Formula.Holds] using hreg
      simpa only [derivative,ht,if_true,value,expr,Expr.denote] using (ha h.1).add (hb h.2)
  | neg a ha =>
    by_cases hd : depends i (.neg a)=false
    · exact free_hasDerivAt i (.neg a) hd x
    · have ht : depends i (.neg a)=true := Bool.eq_true_of_not_eq_false hd
      have h : Formula.Holds (regular i a) x := by
        simpa only [regular,ht,if_true] using hreg
      simpa only [derivative,ht,if_true,value,expr,Expr.denote] using (ha h).neg
  | mul a b ha hb =>
    by_cases hd : depends i (.mul a b)=false
    · exact free_hasDerivAt i (.mul a b) hd x
    · have ht : depends i (.mul a b)=true := Bool.eq_true_of_not_eq_false hd
      have h : Formula.Holds (regular i a) x ∧ Formula.Holds (regular i b) x := by
        simpa only [regular,ht,if_true,Formula.Holds] using hreg
      simpa [derivative,ht,value,expr,Expr.denote] using (ha h.1).mul (hb h.2)
  | inv a ha =>
    by_cases hd : depends i (.inv a)=false
    · exact free_hasDerivAt i (.inv a) hd x
    · have ht : depends i (.inv a)=true := Bool.eq_true_of_not_eq_false hd
      have h : Formula.Holds (regular i a) x ∧ (0<a.value x ∨ a.value x<0) := by
        simpa only [regular,ht,if_true,Formula.Holds,value,expr,Expr.denote] using hreg
      have hn : a.value (Function.update x i (x i))≠0 := by
        simp only [Function.update_eq_self]
        rcases h.2 with h | h <;> linarith
      have hf := (hasDerivAt_const (x i) (1:ℝ)).div (ha h.1) hn
      simpa [derivative,ht,value,expr,Expr.denote,pow_two] using hf
  | sqrt a ha =>
    by_cases hd : depends i (.sqrt a)=false
    · exact free_hasDerivAt i (.sqrt a) hd x
    · have ht : depends i (.sqrt a)=true := Bool.eq_true_of_not_eq_false hd
      have h : Formula.Holds (regular i a) x ∧ 0<a.value x := by
        simpa only [regular,ht,if_true,Formula.Holds,value,expr,Expr.denote] using hreg
      have hn : a.value (Function.update x i (x i))≠0 := by
        simpa using ne_of_gt h.2
      simpa [derivative,ht,value,expr,Expr.denote] using (ha h.1).sqrt hn
  | sin a ha =>
    by_cases hd : depends i (.sin a)=false
    · exact free_hasDerivAt i (.sin a) hd x
    · have ht : depends i (.sin a)=true := Bool.eq_true_of_not_eq_false hd
      have h : Formula.Holds (regular i a) x := by
        simpa only [regular,ht,if_true] using hreg
      simpa [derivative,ht,value,expr,Expr.denote,mul_comm] using (ha h).sin
  | cos a ha =>
    by_cases hd : depends i (.cos a)=false
    · exact free_hasDerivAt i (.cos a) hd x
    · have ht : depends i (.cos a)=true := Bool.eq_true_of_not_eq_false hd
      have h : Formula.Holds (regular i a) x := by
        simpa only [regular,ht,if_true] using hreg
      simpa [derivative,ht,value,expr,Expr.denote,mul_comm] using (ha h).cos

/-- A checked derivative claim includes regularity, not just a numerical bound. -/
def derivativeClaim {n : ℕ} (i : Fin n) (e : Smooth n) (margin : ℚ) : Formula n :=
  .conj (regular i e) (.lt (.rat margin) (derivative i e).expr)

lemma checked_derivative {n : ℕ} (i : Fin n) (e : Smooth n) (margin : ℚ)
    (weights : Fin n → ℚ) (start : Fin n) (fuel : ℕ) (B : RBox n)
    (hc : certify (derivativeClaim i e margin) weights start fuel B=true)
    {x : Fin n → ℝ} (hx : B.Mem x) :
    HasDerivAt (fun t => e.value (Function.update x i t)) ((derivative i e).value x) (x i) ∧
      (margin:ℝ)<(derivative i e).value x := by
  have hh := certify_sound (derivativeClaim i e margin) weights start fuel hc hx
  exact ⟨hasDerivAt i e x hh.1,hh.2⟩

end Smooth
end SquaresInCircles.Six.ProofTools
