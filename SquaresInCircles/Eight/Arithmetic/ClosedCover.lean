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

end SquaresInCircles.Eight.Arithmetic
