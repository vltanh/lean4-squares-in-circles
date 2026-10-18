module

public import SquaresInCircles.Eight.Arithmetic.ScalarExpr

/-!
# Closed interval and box coverage

Coverage is a separate proposition from row validity.  All comparisons use
weak interval membership, and both branches retain their common cut.  Empty
coverage is allowed only for a strictly empty domain; a singleton requires a
leaf or an interval containing that point.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

def ClosedChain (lo hi : ℚ) : List QInterval → Prop
  | [] => hi < lo
  | I::rest => I.lo ≤ lo ∧ (hi ≤ I.hi ∨ (lo ≤ I.hi ∧ ClosedChain I.hi hi rest))

instance closedChainDecidable (lo hi : ℚ) (xs : List QInterval) :
    Decidable (ClosedChain lo hi xs) := by
  induction xs generalizing lo <;> simp only [ClosedChain] <;> infer_instance

theorem ClosedChain.covers {lo hi : ℚ} {xs : List QInterval}
    (hc : ClosedChain lo hi xs) {x : ℝ} (hx : QInterval.Mem ⟨lo,hi⟩ x) :
    ∃ I ∈ xs, I.Mem x := by
  induction xs generalizing lo with
  | nil =>
      have he : (hi : ℝ) < lo := by exact_mod_cast hc
      exact False.elim (by linarith [hx.1,hx.2])
  | cons I rest ih =>
      have hl : (I.lo : ℝ) ≤ lo := by exact_mod_cast hc.1
      by_cases hxi : x ≤ (I.hi : ℝ)
      · exact ⟨I,List.mem_cons_self,hl.trans hx.1,hxi⟩
      · have hxi' : (I.hi : ℝ) ≤ x := (lt_of_not_ge hxi).le
        rcases hc.2 with hlast | hnext
        · have hu : (hi : ℝ) ≤ I.hi := by exact_mod_cast hlast
          exact False.elim (hxi (hx.2.trans hu))
        · obtain ⟨J,hJ,hJx⟩ := ih hnext.2 ⟨hxi',hx.2⟩
          exact ⟨J,List.mem_cons_of_mem I hJ,hJx⟩

theorem ClosedChain.sound {lo hi : ℚ} {xs : List QInterval}
    (hc : ClosedChain lo hi xs) {P : ℝ → Prop}
    (hrow : ∀ I ∈ xs, ∀ x, I.Mem x → P x)
    {x : ℝ} (hx : QInterval.Mem ⟨lo,hi⟩ x) : P x := by
  obtain ⟨I,hI,hIx⟩ := hc.covers hx
  exact hrow I hI x hIx

abbrev QBox (n : ℕ) := Fin n → QInterval

def QBox.Mem {n : ℕ} (b : QBox n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (b i).Mem (x i)

def QBox.left {n : ℕ} (b : QBox n) (i : Fin n) (c : ℚ) : QBox n :=
  Function.update b i ⟨(b i).lo,c⟩

def QBox.right {n : ℕ} (b : QBox n) (i : Fin n) (c : ℚ) : QBox n :=
  Function.update b i ⟨c,(b i).hi⟩

theorem QBox.mem_left {n : ℕ} {b : QBox n} {i : Fin n} {c : ℚ}
    {x : Fin n → ℝ} (hx : b.Mem x) (hi : x i ≤ (c : ℝ)) :
    (b.left i c).Mem x := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [left,QInterval.Mem] using And.intro (hx i).1 hi
  · simpa [left,Function.update_of_ne hji] using hx j

theorem QBox.mem_right {n : ℕ} {b : QBox n} {i : Fin n} {c : ℚ}
    {x : Fin n → ℝ} (hx : b.Mem x) (hi : (c : ℝ) ≤ x i) :
    (b.right i c).Mem x := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [right,QInterval.Mem] using And.intro hi (hx i).2
  · simpa [right,Function.update_of_ne hji] using hx j

inductive SplitCover (n : ℕ)
  | leaf
  | split (coordinate : Fin n) (cut : ℚ) (left right : SplitCover n)
  deriving DecidableEq, Repr

namespace SplitCover

/-- Leaf conclusions and all closed split coordinates are explicitly checked.
This is an ordinary finite predicate, with no statement about an external
program's return value. -/
def ValidFor {n : ℕ} (Good : QBox n → Prop) (b : QBox n) : SplitCover n → Prop
  | .leaf => Good b
  | .split i c l r => (b i).lo ≤ c ∧ c ≤ (b i).hi ∧
      ValidFor Good (b.left i c) l ∧ ValidFor Good (b.right i c) r

theorem sound {n : ℕ} {Good : QBox n → Prop} {P : (Fin n → ℝ) → Prop}
    (hGood : ∀ b, Good b → ∀ x, b.Mem x → P x)
    (tree : SplitCover n) (b : QBox n) (hv : tree.ValidFor Good b)
    (x : Fin n → ℝ) (hx : b.Mem x) : P x := by
  induction tree generalizing b with
  | leaf => exact hGood b hv x hx
  | split i c l r hl hr =>
      by_cases hxc : x i ≤ (c : ℝ)
      · exact hl (b.left i c) hv.2.2.1 (QBox.mem_left hx hxc)
      · exact hr (b.right i c) hv.2.2.2 (QBox.mem_right hx (lt_of_not_ge hxc).le)

end SplitCover
end SquaresInCircles.Eight.Arithmetic
