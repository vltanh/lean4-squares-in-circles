import SquaresInCircles.Six.ProofTools.Expression

/-!
# Finite rational covers produce proofs of real formulas

Unknown comparisons and failed expression evaluations never count as success.
A split covers its parent because every real coordinate lies on one side of
the rational midpoint. `certify_sound` is proved by induction on the finite
fuel, independently of any numerical run. Applications must prove the concrete
Boolean check equals true; a log or an externally supplied success flag cannot
replace that proof.
-/

namespace SquaresInCircles.Six.ProofTools

inductive Verdict where
  | yes | no | unknown
  deriving DecidableEq, Repr

inductive Formula (n : ℕ) where
  | top | bottom
  | lt : Expr n → Expr n → Formula n
  | le : Expr n → Expr n → Formula n
  | neg : Formula n → Formula n
  | conj : Formula n → Formula n → Formula n
  | disj : Formula n → Formula n → Formula n
  | imp : Formula n → Formula n → Formula n
  deriving DecidableEq, Repr

namespace Formula

noncomputable def Holds {n : ℕ} : Formula n → (Fin n → ℝ) → Prop
  | .top, _ => True
  | .bottom, _ => False
  | .lt a b, x => Expr.denote a x < Expr.denote b x
  | .le a b, x => Expr.denote a x ≤ Expr.denote b x
  | .neg a, x => ¬ Holds a x
  | .conj a b, x => Holds a x ∧ Holds b x
  | .disj a b, x => Holds a x ∨ Holds b x
  | .imp a b, x => Holds a x → Holds b x

def all {n : ℕ} (fs : List (Formula n)) : Formula n := fs.foldr Formula.conj .top
def any {n : ℕ} (fs : List (Formula n)) : Formula n := fs.foldr Formula.disj .bottom

def negVerdict : Verdict → Verdict
  | .yes => .no
  | .no => .yes
  | .unknown => .unknown

def conjVerdict : Verdict → Verdict → Verdict
  | .no, _ => .no
  | _, .no => .no
  | .yes, .yes => .yes
  | _, _ => .unknown

def disjVerdict : Verdict → Verdict → Verdict
  | .yes, _ => .yes
  | _, .yes => .yes
  | .no, .no => .no
  | _, _ => .unknown

def ltVerdict (I J : RInterval) : Verdict :=
  if I.hi < J.lo then .yes else if J.hi ≤ I.lo then .no else .unknown

def leVerdict (I J : RInterval) : Verdict :=
  if I.hi ≤ J.lo then .yes else if J.hi < I.lo then .no else .unknown

private def arithVerdict (f : RInterval → RInterval → Verdict) :
    Option RInterval → Option RInterval → Verdict
  | some a, some b => f a b
  | _, _ => .unknown

def verdict {n : ℕ} : Formula n → RBox n → Verdict
  | .top, _ => .yes
  | .bottom, _ => .no
  | .lt a b, B => arithVerdict ltVerdict (Expr.eval a B) (Expr.eval b B)
  | .le a b, B => arithVerdict leVerdict (Expr.eval a B) (Expr.eval b B)
  | .neg a, B => negVerdict (verdict a B)
  | .conj a b, B => conjVerdict (verdict a B) (verdict b B)
  | .disj a b, B => disjVerdict (verdict a B) (verdict b B)
  | .imp a b, B => disjVerdict (negVerdict (verdict a B)) (verdict b B)

private def Sound (v : Verdict) (p : Prop) : Prop :=
  (v = .yes → p) ∧ (v = .no → ¬ p)

private lemma ltVerdict_sound {I J : RInterval} {x y : ℝ}
    (hx : I.Mem x) (hy : J.Mem y) : Sound (ltVerdict I J) (x < y) := by
  unfold ltVerdict Sound
  split_ifs with h h'
  · constructor
    · intro _
      have hh : (I.hi : ℝ) < J.lo := by exact_mod_cast h
      linarith [hx.2,hy.1]
    · intro hf; cases hf
  · constructor
    · intro hf; cases hf
    · intro _ hf
      have hh : (J.hi : ℝ) ≤ I.lo := by exact_mod_cast h'
      linarith [hx.1,hy.2]
  · constructor <;> intro hf <;> cases hf

private lemma leVerdict_sound {I J : RInterval} {x y : ℝ}
    (hx : I.Mem x) (hy : J.Mem y) : Sound (leVerdict I J) (x ≤ y) := by
  unfold leVerdict Sound
  split_ifs with h h'
  · constructor
    · intro _
      have hh : (I.hi : ℝ) ≤ J.lo := by exact_mod_cast h
      linarith [hx.2,hy.1]
    · intro hf; cases hf
  · constructor
    · intro hf; cases hf
    · intro _ hf
      have hh : (J.hi : ℝ) < I.lo := by exact_mod_cast h'
      linarith [hx.1,hy.2]
  · constructor <;> intro hf <;> cases hf

private lemma negVerdict_sound {v : Verdict} {p : Prop} (h : Sound v p) :
    Sound (negVerdict v) (¬p) := by
  classical
  cases v <;> simp_all [Sound,negVerdict]

private lemma conjVerdict_sound {v w : Verdict} {p q : Prop}
    (hp : Sound v p) (hq : Sound w q) : Sound (conjVerdict v w) (p ∧ q) := by
  cases v <;> cases w <;> simp_all [Sound,conjVerdict]

private lemma disjVerdict_sound {v w : Verdict} {p q : Prop}
    (hp : Sound v p) (hq : Sound w q) : Sound (disjVerdict v w) (p ∨ q) := by
  cases v <;> cases w <;> simp_all [Sound,disjVerdict]

/-- A successful verdict proves the real formula throughout the box; a negative
verdict proves its negation. Unknown makes no assertion in either direction. -/
theorem verdict_sound {n : ℕ} (f : Formula n) {B : RBox n} {x : Fin n → ℝ}
    (hx : B.Mem x) :
    (verdict f B = .yes → Holds f x) ∧ (verdict f B = .no → ¬ Holds f x) := by
  classical
  change Sound (verdict f B) (Holds f x)
  induction f with
  | top => simp [Sound,verdict,Holds]
  | bottom => simp [Sound,verdict,Holds]
  | lt a b =>
    cases ha : Expr.eval a B with
    | none => simp [Sound,verdict,arithVerdict,ha]
    | some A =>
      cases hb : Expr.eval b B with
      | none => simp [Sound,verdict,arithVerdict,ha,hb]
      | some B' =>
        simpa only [verdict,arithVerdict,ha,hb,Holds] using
          ltVerdict_sound (Expr.eval_sound a hx ha) (Expr.eval_sound b hx hb)
  | le a b =>
    cases ha : Expr.eval a B with
    | none => simp [Sound,verdict,arithVerdict,ha]
    | some A =>
      cases hb : Expr.eval b B with
      | none => simp [Sound,verdict,arithVerdict,ha,hb]
      | some B' =>
        simpa only [verdict,arithVerdict,ha,hb,Holds] using
          leVerdict_sound (Expr.eval_sound a hx ha) (Expr.eval_sound b hx hb)
  | neg a ha => exact negVerdict_sound ha
  | conj a b ha hb => exact conjVerdict_sound ha hb
  | disj a b ha hb => exact disjVerdict_sound ha hb
  | imp a b ha hb =>
    have hh := disjVerdict_sound (negVerdict_sound ha) hb
    constructor
    · intro hv hp
      rcases hh.1 hv with hn | hq
      · exact False.elim (hn hp)
      · exact hq
    · intro hv himp
      apply hh.2 hv
      by_cases hp : Holds a x
      · exact Or.inr (himp hp)
      · exact Or.inl hp

end Formula

namespace RBox

def lower {n : ℕ} (B : RBox n) (i : Fin n) : RBox n :=
  Function.update B i ⟨(B i).lo,RInterval.midpoint (B i)⟩

def upper {n : ℕ} (B : RBox n) (i : Fin n) : RBox n :=
  Function.update B i ⟨RInterval.midpoint (B i),(B i).hi⟩

lemma mem_lower {n : ℕ} {B : RBox n} {x : Fin n → ℝ} (hx : B.Mem x) {i : Fin n}
    (hi : x i ≤ (RInterval.midpoint (B i) : ℝ)) : (lower B i).Mem x := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [lower,RInterval.Mem] using And.intro (hx i).1 hi
  · simpa [lower,hji] using hx j

lemma mem_upper {n : ℕ} {B : RBox n} {x : Fin n → ℝ} (hx : B.Mem x) {i : Fin n}
    (hi : (RInterval.midpoint (B i) : ℝ) ≤ x i) : (upper B i).Mem x := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [upper,RInterval.Mem] using And.intro hi (hx i).2
  · simpa [upper,hji] using hx j

/-- Search-order heuristic only: its choice cannot affect the soundness theorem. -/
def widest {n : ℕ} (B : RBox n) (weights : Fin n → ℚ) (start : Fin n) : Fin n :=
  (List.finRange n).foldl (fun best i =>
    if ((B best).hi-(B best).lo)*weights best < ((B i).hi-(B i).lo)*weights i
    then i else best) start

end RBox

/-- Finite proof search. Exhausted fuel returns false, never success. -/
def certify {n : ℕ} (f : Formula n) (weights : Fin n → ℚ) (start : Fin n) :
    ℕ → RBox n → Bool
  | 0, B => decide (Formula.verdict f B = .yes)
  | fuel+1, B =>
      if Formula.verdict f B = .yes then true else
        let i := RBox.widest B weights start
        certify f weights start fuel (RBox.lower B i) &&
          certify f weights start fuel (RBox.upper B i)

/-- The checker is a proof-producing finite-cover calculation, not an oracle. -/
theorem certify_sound {n : ℕ} (f : Formula n) (weights : Fin n → ℚ) (start : Fin n)
    (fuel : ℕ) {B : RBox n} (h : certify f weights start fuel B = true)
    {x : Fin n → ℝ} (hx : B.Mem x) : Formula.Holds f x := by
  induction fuel generalizing B with
  | zero =>
    have hv : Formula.verdict f B = .yes := of_decide_eq_true h
    exact (Formula.verdict_sound f hx).1 hv
  | succ fuel ih =>
    simp only [certify] at h
    split_ifs at h with hv
    · exact (Formula.verdict_sound f hx).1 hv
    · have hh := Bool.and_eq_true.mp h
      by_cases hl : x (RBox.widest B weights start) ≤
          (RInterval.midpoint (B (RBox.widest B weights start)) : ℝ)
      · exact ih hh.1 (RBox.mem_lower hx hl)
      · exact ih hh.2 (RBox.mem_upper hx (le_of_not_ge hl))

end SquaresInCircles.Six.ProofTools
