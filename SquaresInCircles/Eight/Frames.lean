module

public import SquaresInCircles.Eight.Model
public import SquaresInCircles.Common.Trigonometry
public import SquaresInCircles.Common.Analysis

/-!
# Four-type budgets and the real-frame range

Source: `HAND_EXTERIOR_FRAME_CONCENTRATION.md`. The matrix here is the
completed **hand** matrix, scaled by 10,000. It is deliberately distinct
from the historical dyadic certificate matrix.

The finite walk theorem quantifies over all 4^7 words. The continuous pair
premises remain explicit in the summation theorem: the finite walk fact is
not used as a substitute for a continuous pair proof.

Uncompiled draft. All finite arithmetic uses ordinary kernel reduction.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight

lemma next_prev (i : Vertex) : next (prev i) = i := by
  simp [next, prev]

lemma prev_next (i : Vertex) : prev (next i) = i := by
  simp [next, prev]

def nextPerm : Equiv.Perm Vertex where
  toFun := next
  invFun := prev
  left_inv := prev_next
  right_inv := next_prev

lemma sum_next {α : Type*} [AddCommMonoid α] (f : Vertex → α) :
    ∑ i, f (next i) = ∑ i, f i := by
  exact Equiv.sum_comp nextPerm f

lemma sum_prev {α : Type*} [AddCommMonoid α] (f : Vertex → α) :
    ∑ i, f (prev i) = ∑ i, f i := by
  exact Equiv.sum_comp nextPerm.symm f

lemma cyclic_difference_sum (f : Vertex → ℝ) : ∑ i, (f (next i) - f i) = 0 := by
  rw [Finset.sum_sub_distrib, sum_next, sub_self]

lemma angleGap_sum (β : Vertex → ℝ) : ∑ i, angleGap β i = 2 * Real.pi := by
  simp [angleGap, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_next]

lemma cyclic_markers_cancel (δ w ψ : Vertex → ℝ) (b : ℝ) :
    ∑ i, (δ i - b * w i + ψ (next i) - ψ i) =
      (∑ i, δ i) - b * ∑ i, w i := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_next]
  ring

lemma cyclic_summation_by_parts (ν θ : Vertex → ℝ) :
    ∑ i, ν i * (θ (next i) - θ i) =
      ∑ i, (ν (prev i) - ν i) * θ i := by
  have hshift : ∑ i, ν i * θ (next i) = ∑ i, ν (prev i) * θ i := by
    have hh := sum_next (fun i => ν (prev i) * θ i)
    simpa only [prev_next] using hh
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [hshift]

/-- Cyclic frame charges depend on total variation of their multipliers.
The common frame midpoint is subtracted before absolute values are taken. -/
lemma cyclic_charge_bound (ν θ : Vertex → ℝ) {J D : ℝ}
    (hθ : ∀ i, J ≤ θ i ∧ θ i ≤ J + D) :
    |∑ i, ν i * (θ (next i) - θ i)| ≤
      D / 2 * ∑ i, |ν (prev i) - ν i| := by
  have hD : 0 ≤ D := by linarith [(hθ 0).1, (hθ 0).2]
  have hmid (i : Vertex) : |θ i - (J + D / 2)| ≤ D / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [(hθ i).1, (hθ i).2]
  have hcoeff : ∑ i, (ν (prev i) - ν i) = 0 := by
    rw [Finset.sum_sub_distrib, sum_prev, sub_self]
  rw [cyclic_summation_by_parts]
  have hid : ∑ i, (ν (prev i) - ν i) * θ i =
      ∑ i, (ν (prev i) - ν i) * (θ i - (J + D / 2)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hcoeff, zero_mul, sub_zero]
  rw [hid]
  calc
    |∑ i, (ν (prev i) - ν i) * (θ i - (J + D / 2))| ≤
        ∑ i, |(ν (prev i) - ν i) * (θ i - (J + D / 2))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |ν (prev i) - ν i| * (D / 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hmid i) (abs_nonneg _)
    _ = D / 2 * ∑ i, |ν (prev i) - ν i| := by
      rw [← Finset.sum_mul]
      ring

/-- C, L, M, H, in precisely that order. -/
def handGammaNumerator : Fin 4 → Fin 4 → ℕ :=
  ![![9200, 9100, 9005, 8833],
    ![9100, 9100, 9005, 8833],
    ![9005, 9005, 8912, 8926],
    ![8833, 8833, 8926, 9099]]

def handGamma (i j : Fin 4) : ℝ := handGammaNumerator i j / 10000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- Complete finite seven-walk enumeration; no native evaluator enters the
trust boundary. It includes constant walks, repeated vertices, and every loop. -/
theorem four_type_seven_walk_numerator :
    ∀ τ : Vertex → Fin 4, 62096 ≤ ∑ i, handGammaNumerator (τ i) (τ (next i)) := by
  decide

theorem four_type_seven_walk (τ : Vertex → Fin 4) :
    3881 / 625 ≤ ∑ i, handGamma (τ i) (τ (next i)) := by
  have hn := four_type_seven_walk_numerator τ
  have hr : (62096 : ℝ) ≤ ∑ i, (handGammaNumerator (τ i) (τ (next i)) : ℝ) := by
    exact_mod_cast hn
  simp only [handGamma, ← Finset.sum_div]
  nlinarith

/-- The continuous edge hypotheses are charged before their markers telescope.
One fixed marker is used at a vertex on both incident edges. -/
theorem four_type_cycle_budget (τ : Vertex → Fin 4) (δ h ψ : Vertex → ℝ)
    (hpair : ∀ i,
      handGamma (τ i) (τ (next i)) <
        δ i - (9 / 50 : ℝ) * h i + ψ (next i) - ψ i) :
    3881 / 625 < (∑ i, δ i) - (9 / 50 : ℝ) * ∑ i, h i := by
  have hsum := Finset.sum_lt_sum (s := Finset.univ)
    (fun i _ => (hpair i).le) ⟨0, Finset.mem_univ _, hpair 0⟩
  rw [cyclic_markers_cancel] at hsum
  exact (four_type_seven_walk τ).trans_lt hsum

theorem physical_cycle_width_bound (τ : Vertex → Fin 4) (β h ψ : Vertex → ℝ)
    (hpair : ∀ i,
      handGamma (τ i) (τ (next i)) <
        angleGap β i - (9 / 50 : ℝ) * h i + ψ (next i) - ψ i)
    (hpi : Real.pi < 355 / 113) :
    ∑ i, h i < 10394 / 25425 := by
  have hh := four_type_cycle_budget τ (angleGap β) h ψ hpair
  rw [angleGap_sum] at hh
  linarith

/-- On the short orientation interval this is the angular width excess. -/
def frameCost (x : ℝ) : ℝ := (Real.cos x + Real.sin x - 1) / 2

def periodicFrameCost (x : ℝ) : ℝ :=
  (|Real.cos x| + |Real.sin x| - 1) / 2

lemma frameCost_zero : frameCost 0 = 0 := by norm_num [frameCost]

lemma periodicFrameCost_nonneg (x : ℝ) : 0 ≤ periodicFrameCost x := by
  have hh := Real.sin_sq_add_cos_sq x
  have hc := abs_nonneg (Real.cos x)
  have hs := abs_nonneg (Real.sin x)
  have hp := mul_nonneg hc hs
  have hsum : 1 ≤ |Real.cos x| + |Real.sin x| := by
    nlinarith [sq_abs (Real.cos x), sq_abs (Real.sin x)]
  dsimp [periodicFrameCost]
  linarith

lemma periodicFrameCost_pi_half (x : ℝ) :
    periodicFrameCost (x + Real.pi / 2) = periodicFrameCost x := by
  simp [periodicFrameCost, Real.cos_add, Real.sin_add, abs_neg, add_comm]

lemma periodicFrameCost_neg (x : ℝ) : periodicFrameCost (-x) = periodicFrameCost x := by
  simp [periodicFrameCost, Real.cos_neg, Real.sin_neg, abs_neg]

lemma frameCost_hasDerivAt (x : ℝ) :
    HasDerivAt frameCost ((Real.cos x - Real.sin x) / 2) x := by
  convert ((((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).sub_const 1).div_const 2)
    using 1 <;> dsimp [frameCost] <;> ring

lemma frameCost_monotone : MonotoneOn frameCost (Set.Icc 0 (Real.pi / 4)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · dsimp [frameCost]
    fun_prop
  · intro x hx
    exact (frameCost_hasDerivAt x).hasDerivWithinAt
  · intro x hx
    have hx' : 0 ≤ x ∧ x ≤ Real.pi / 4 := hx
    have hc := Real.cos_sub (Real.pi / 4) x
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / 4 - x by linarith) (by linarith [Real.pi_pos])
    rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four] at hs
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith

/-- An elementary closed-walk total-variation bound. It is stated for an
arbitrary selected pair of vertices, so extrema can be supplied afterwards. -/
lemma closed_walk_range_bound (θ : Vertex → ℝ) (i j : Vertex) :
    2 * |θ j - θ i| ≤ ∑ k, |θ (next k) - θ k| := by
  have hp (k : Vertex) := le_abs_self (θ (next k) - θ k)
  have hn (k : Vertex) := neg_le_abs (θ (next k) - θ k)
  rcases le_total 0 (θ j - θ i) with h | h
  · rw [abs_of_nonneg h]
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_succ, next] at * <;>
      linarith [hp 0, hp 1, hp 2, hp 3, hp 4, hp 5, hp 6,
        hn 0, hn 1, hn 2, hn 3, hn 4, hn 5, hn 6]
  · rw [abs_of_nonpos h]
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_succ, next] at * <;>
      linarith [hp 0, hp 1, hp 2, hp 3, hp 4, hp 5, hp 6,
        hn 0, hn 1, hn 2, hn 3, hn 4, hn 5, hn 6]

end SquaresInCircles.Eight
