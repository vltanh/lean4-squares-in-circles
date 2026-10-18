module

public import SquaresInCircles.Eight.ExactFamily.Expression

/-!
# Closed-cover rule for simultaneous stationary equations

Each exclusion retains the entire expression.  Closed cuts keep the shared
endpoint in both children.  This rule is used by generated root-isolation
proof terms; it proves localization, never root existence.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily
open Arithmetic

def SimultaneousZeros {n m : ℕ} (targets : Fin m → Formula n)
    (env : Fin n → ℝ) : Prop := ∀ i, (targets i).eval env = 0

theorem interval_excludes_zero {n : ℕ} {box : QBox n} {target : Formula n}
    (c : FormulaCertificate n) (hc : c.Valid box target)
    (hs : (c.expression.range box).hi < 0 ∨ 0 < (c.expression.range box).lo)
    {env : Fin n → ℝ} (he : box.Mem env) : target.eval env ≠ 0 := by
  have hbound := c.sound hc he
  intro hzero
  rw [hzero] at hbound
  rcases hs with hs | hs
  · have hs' : ((c.expression.range box).hi : ℝ) < 0 := by exact_mod_cast hs
    linarith [hbound.2]
  · have hs' : (0:ℝ) < (c.expression.range box).lo := by exact_mod_cast hs
    linarith [hbound.1]

theorem box_mem_of_subset {n : ℕ} {box inner : QBox n}
    (h : ∀ i, (inner i).lo ≤ (box i).lo ∧ (box i).hi ≤ (inner i).hi)
    {env : Fin n → ℝ} (he : box.Mem env) : inner.Mem env := by
  intro i
  exact QInterval.mem_mono (he i) (h i).1 (h i).2

theorem closed_box_split {n : ℕ} (box : QBox n) (i : Fin n) (cut : ℚ)
    {P : (Fin n → ℝ) → Prop}
    (hl : ∀ env, (box.left i cut).Mem env → P env)
    (hr : ∀ env, (box.right i cut).Mem env → P env)
    (env : Fin n → ℝ) (he : box.Mem env) : P env := by
  by_cases h : env i ≤ (cut : ℝ)
  · exact hl env (QBox.mem_left he h)
  · exact hr env (QBox.mem_right he (lt_of_not_ge h).le)

end SquaresInCircles.Eight.ExactFamily
