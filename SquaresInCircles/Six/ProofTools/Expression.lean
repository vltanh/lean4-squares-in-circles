module
public import SquaresInCircles.Six.ProofTools.TrigInterval

@[expose] public section

/-!
# Reified real scalar expressions

`eval_sound` connects exact rational evaluation to the real expression.
Conditional evaluation selects a branch only after a certified comparison of
whole intervals; an undecided comparison encloses BOTH branches. This is
needed for the exact cap/vertex support and never equates dominance with the
cap condition. Failed roots or reciprocal evaluations propagate as `none`.
-/

namespace SquaresInCircles.Six.ProofTools

abbrev RBox (n : ℕ) := Fin n → RInterval

def RBox.Mem {n : ℕ} (B : RBox n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (B i).Mem (x i)

inductive Expr (n : ℕ) where
  | var : Fin n → Expr n
  | rat : ℚ → Expr n
  | pi : Expr n
  | add : Expr n → Expr n → Expr n
  | neg : Expr n → Expr n
  | mul : Expr n → Expr n → Expr n
  | inv : Expr n → Expr n
  | sqrt : Expr n → Expr n
  | sin : Expr n → Expr n
  | cos : Expr n → Expr n
  | abs : Expr n → Expr n
  | min : Expr n → Expr n → Expr n
  | max : Expr n → Expr n → Expr n
  | sq : Expr n → Expr n
  | pow : Expr n → ℕ → Expr n
  | iteLe : Expr n → Expr n → Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

namespace Expr

instance {n : ℕ} : Add (Expr n) := ⟨Expr.add⟩
instance {n : ℕ} : Neg (Expr n) := ⟨Expr.neg⟩
instance {n : ℕ} : Sub (Expr n) := ⟨fun a b => .add a (.neg b)⟩
instance {n : ℕ} : Mul (Expr n) := ⟨Expr.mul⟩
instance {n : ℕ} : Div (Expr n) := ⟨fun a b => .mul a (.inv b)⟩
instance {n : ℕ} : Pow (Expr n) ℕ := ⟨Expr.pow⟩
instance {n k : ℕ} : OfNat (Expr n) k := ⟨.rat k⟩

noncomputable def denote {n : ℕ} : Expr n → (Fin n → ℝ) → ℝ
  | .var i, x => x i
  | .rat q, _ => q
  | .pi, _ => Real.pi
  | .add a b, x => denote a x + denote b x
  | .neg a, x => -denote a x
  | .mul a b, x => denote a x * denote b x
  | .inv a, x => 1 / denote a x
  | .sqrt a, x => Real.sqrt (denote a x)
  | .sin a, x => Real.sin (denote a x)
  | .cos a, x => Real.cos (denote a x)
  | .abs a, x => |denote a x|
  | .min a b, x => min (denote a x) (denote b x)
  | .max a b, x => max (denote a x) (denote b x)
  | .sq a, x => (denote a x)^2
  | .pow a k, x => (denote a x)^k
  | .iteLe a b f g, x => if denote a x ≤ denote b x then denote f x else denote g x

private def map1 (f : RInterval → RInterval) : Option RInterval → Option RInterval
  | none => none
  | some a => some (f a)

private def map2 (f : RInterval → RInterval → RInterval) :
    Option RInterval → Option RInterval → Option RInterval
  | some a, some b => some (f a b)
  | _, _ => none

private def bind1 (f : RInterval → Option RInterval) : Option RInterval → Option RInterval
  | none => none
  | some a => f a

private def selectLe : Option RInterval → Option RInterval →
    Option RInterval → Option RInterval → Option RInterval
  | some a, some b, f, g =>
      if a.hi ≤ b.lo then f else if b.hi < a.lo then g else map2 RInterval.hull f g
  | _, _, f, g => map2 RInterval.hull f g

private lemma map1_eq_some {f : RInterval → RInterval} {a : Option RInterval} {c : RInterval}
    (h : map1 f a = some c) : ∃ A, a = some A ∧ c = f A := by
  cases a with
  | none => cases h
  | some A => exact ⟨A,rfl,(Option.some.inj h).symm⟩

private lemma map2_eq_some {f : RInterval → RInterval → RInterval}
    {a b : Option RInterval} {c : RInterval} (h : map2 f a b = some c) :
    ∃ A B, a = some A ∧ b = some B ∧ c = f A B := by
  cases a with
  | none => cases h
  | some A =>
    cases b with
    | none => cases h
    | some B => exact ⟨A,B,rfl,rfl,(Option.some.inj h).symm⟩

private lemma bind1_eq_some {f : RInterval → Option RInterval}
    {a : Option RInterval} {c : RInterval} (h : bind1 f a = some c) :
    ∃ A, a = some A ∧ f A = some c := by
  cases a with
  | none => cases h
  | some A => exact ⟨A,rfl,h⟩

private lemma hull_if_sound {F G : Option RInterval} {f g a b : ℝ} {I : RInterval}
    (hf : ∀ J, F=some J → J.Mem f) (hg : ∀ J, G=some J → J.Mem g)
    (h : map2 RInterval.hull F G=some I) : I.Mem (if a≤b then f else g) := by
  obtain ⟨A,B,hA,hB,rfl⟩ := map2_eq_some h
  by_cases hab : a≤b
  · rw [if_pos hab]
    exact RInterval.mem_hull_left (hf A hA)
  · rw [if_neg hab]
    exact RInterval.mem_hull_right (hg B hB)

private lemma selectLe_sound {A B F G : Option RInterval} {a b f g : ℝ} {I : RInterval}
    (ha : ∀ J, A=some J → J.Mem a) (hb : ∀ J, B=some J → J.Mem b)
    (hf : ∀ J, F=some J → J.Mem f) (hg : ∀ J, G=some J → J.Mem g)
    (h : selectLe A B F G=some I) : I.Mem (if a≤b then f else g) := by
  cases A with
  | none => exact hull_if_sound hf hg h
  | some A =>
    cases B with
    | none => exact hull_if_sound hf hg h
    | some B =>
      have hA := ha A rfl
      have hB := hb B rfl
      simp only [selectLe] at h
      split_ifs at h with hab hba
      · have hc : (A.hi:ℝ) ≤ B.lo := by exact_mod_cast hab
        rw [if_pos (show a≤b by linarith [hA.2,hB.1])]
        exact hf I h
      · have hc : (B.hi:ℝ) < A.lo := by exact_mod_cast hba
        rw [if_neg (show ¬a≤b by linarith [hB.2,hA.1])]
        exact hg I h
      · exact hull_if_sound hf hg h

def eval {n : ℕ} : Expr n → RBox n → Option RInterval
  | .var i, B => some (B i)
  | .rat q, _ => some (RInterval.point q)
  | .pi, _ => some RInterval.piInterval
  | .add a b, B => map2 RInterval.add (eval a B) (eval b B)
  | .neg a, B => map1 RInterval.neg (eval a B)
  | .mul a b, B => map2 RInterval.mul (eval a B) (eval b B)
  | .inv a, B => bind1 RInterval.inverse (eval a B)
  | .sqrt a, B => bind1 RInterval.root (eval a B)
  | .sin a, B => map1 RInterval.sine (eval a B)
  | .cos a, B => map1 RInterval.cosine (eval a B)
  | .abs a, B => map1 RInterval.absolute (eval a B)
  | .min a b, B => map2 RInterval.minimum (eval a B) (eval b B)
  | .max a b, B => map2 RInterval.maximum (eval a B) (eval b B)
  | .sq a, B => map1 RInterval.square (eval a B)
  | .pow a k, B => map1 (fun I => RInterval.power I k) (eval a B)
  | .iteLe a b f g, B => selectLe (eval a B) (eval b B) (eval f B) (eval g B)

/-- Every successful evaluation encloses the real expression throughout the box. -/
theorem eval_sound {n : ℕ} (e : Expr n) {B : RBox n} {x : Fin n → ℝ}
    (hx : B.Mem x) {I : RInterval} (h : eval e B = some I) : I.Mem (denote e x) := by
  induction e generalizing I with
  | var i => cases h; exact hx i
  | rat q => cases h; exact RInterval.mem_point q
  | pi => cases h; exact RInterval.mem_piInterval
  | add a b ha hb =>
    obtain ⟨A,B,hA,hB,rfl⟩ := map2_eq_some h
    exact RInterval.mem_add (ha hA) (hb hB)
  | neg a ha =>
    obtain ⟨A,hA,rfl⟩ := map1_eq_some h
    exact RInterval.mem_neg (ha hA)
  | mul a b ha hb =>
    obtain ⟨A,B,hA,hB,rfl⟩ := map2_eq_some h
    exact RInterval.mem_mul (ha hA) (hb hB)
  | inv a ha =>
    obtain ⟨A,hA,hI⟩ := bind1_eq_some h
    exact RInterval.mem_inverse (ha hA) hI
  | sqrt a ha =>
    obtain ⟨A,hA,hI⟩ := bind1_eq_some h
    exact RInterval.mem_root (ha hA) hI
  | sin a ha =>
    obtain ⟨A,hA,rfl⟩ := map1_eq_some h
    exact RInterval.mem_sine (ha hA)
  | cos a ha =>
    obtain ⟨A,hA,rfl⟩ := map1_eq_some h
    exact RInterval.mem_cosine (ha hA)
  | abs a ha =>
    obtain ⟨A,hA,rfl⟩ := map1_eq_some h
    exact RInterval.mem_absolute (ha hA)
  | min a b ha hb =>
    obtain ⟨A,B,hA,hB,rfl⟩ := map2_eq_some h
    exact RInterval.mem_minimum (ha hA) (hb hB)
  | max a b ha hb =>
    obtain ⟨A,B,hA,hB,rfl⟩ := map2_eq_some h
    exact RInterval.mem_maximum (ha hA) (hb hB)
  | sq a ha =>
    obtain ⟨A,hA,rfl⟩ := map1_eq_some h
    exact RInterval.mem_square (ha hA)
  | pow a k ha =>
    obtain ⟨A,hA,rfl⟩ := map1_eq_some h
    exact RInterval.mem_power (ha hA) k
  | iteLe a b f g ha hb hf hg =>
    exact selectLe_sound (fun _ h => ha h) (fun _ h => hb h)
      (fun _ h => hf h) (fun _ h => hg h) h

end Expr
end SquaresInCircles.Six.ProofTools
