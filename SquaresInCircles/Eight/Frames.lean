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

/-- The least weight of a two-step walk between two types, the min-plus square
of the matrix: the minimum over `b` of
`handGammaNumerator a b + handGammaNumerator b c`. -/
private def twoStepGammaNumerator : Fin 4 → Fin 4 → ℕ :=
  ![![17666, 17666, 17759, 17931],
    ![17666, 17666, 17759, 17931],
    ![17759, 17759, 17824, 17838],
    ![17931, 17931, 17838, 17666]]

/-- Complete finite seven-walk bound; no native evaluator enters the trust
boundary. It covers constant walks, repeated vertices, and every loop. A closed
seven-walk is three two-step walks and one step; each two-step walk weighs at
least `twoStepGammaNumerator` of its ends, and the kernel checks the remaining
closed walk through four types for all `4 ^ 4` choices. -/
theorem four_type_seven_walk_numerator :
    ∀ τ : Vertex → Fin 4, 62096 ≤ ∑ i, handGammaNumerator (τ i) (τ (next i)) := by
  have two : ∀ a b c : Fin 4,
      twoStepGammaNumerator a c ≤ handGammaNumerator a b + handGammaNumerator b c := by
    decide +kernel
  have close : ∀ a b c d : Fin 4, 62096 ≤ twoStepGammaNumerator a b +
      twoStepGammaNumerator b c + twoStepGammaNumerator c d + handGammaNumerator d a := by
    decide +kernel
  intro τ
  have h₁ := two (τ 0) (τ 1) (τ 2)
  have h₂ := two (τ 2) (τ 3) (τ 4)
  have h₃ := two (τ 4) (τ 5) (τ 6)
  have h₄ := close (τ 0) (τ 2) (τ 4) (τ 6)
  simp only [Fin.sum_univ_seven, next, Fin.isValue, Fin.reduceAdd]
  omega

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
    using 1
  · rfl
  · ring

lemma frameCost_monotone : MonotoneOn frameCost (Set.Icc 0 (Real.pi / 4)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (f' := fun x => (Real.cos x - Real.sin x) / 2)
  · unfold frameCost
    fun_prop
  · intro x hx
    exact (frameCost_hasDerivAt x).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx' : 0 ≤ x ∧ x ≤ Real.pi / 4 := ⟨hx.1.le, hx.2.le⟩
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
  have hsum : ∑ k, |θ (next k) - θ k| =
      |θ (next 0) - θ 0| + |θ (next 1) - θ 1| + |θ (next 2) - θ 2| + |θ (next 3) - θ 3| +
        |θ (next 4) - θ 4| + |θ (next 5) - θ 5| + |θ (next 6) - θ 6| :=
    Fin.sum_univ_seven _
  have e0 : next 0 = 1 := rfl
  have e1 : next 1 = 2 := rfl
  have e2 : next 2 = 3 := rfl
  have e3 : next 3 = 4 := rfl
  have e4 : next 4 = 5 := rfl
  have e5 : next 5 = 6 := rfl
  have e6 : next 6 = 0 := rfl
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hp3 := hp 3
  have hp4 := hp 4
  have hp5 := hp 5
  have hp6 := hp 6
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  have hn3 := hn 3
  have hn4 := hn 4
  have hn5 := hn 5
  have hn6 := hn 6
  rw [hsum]
  rw [e0, e1, e2, e3, e4, e5, e6] at *
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    revert i; decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by
    revert j; decide
  rcases le_total 0 (θ j - θ i) with h | h
  · rw [abs_of_nonneg h]
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      linarith
  · rw [abs_of_nonpos h]
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      linarith

/-! ## The shortest orientation tour and its real lift -/

lemma frameCost_concave : ConcaveOn ℝ (Set.Icc 0 (Real.pi / 4)) frameCost := by
  apply concave_of_deriv2 (fun x _ => frameCost_hasDerivAt x)
    (f' := fun x => (Real.cos x - Real.sin x) / 2)
    (f'' := fun x => -(Real.sin x + Real.cos x) / 2)
  · intro x hx
    convert (((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).div_const 2)
      using 1 <;> ring
  · intro x hx
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
      (by linarith [hx.2,Real.pi_pos])
    have hc := Real.cos_nonneg_of_mem_Icc
      (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
    linarith

lemma frameCost_nonneg {x : ℝ} (hx : x ∈ Set.Icc 0 (Real.pi/4)) :
    0 ≤ frameCost x := by
  simpa only [frameCost_zero] using
    frameCost_monotone ⟨le_rfl,by positivity⟩ hx hx.1

lemma frameCost_at_quarter : frameCost (Real.pi/4) = (Real.sqrt 2-1)/2 := by
  rw [frameCost,Real.cos_pi_div_four,Real.sin_pi_div_four]
  ring

lemma frameCost_at_quarter_pos : 0 < frameCost (Real.pi/4) := by
  rw [frameCost_at_quarter]
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  nlinarith

/-- The chord estimate is available on every initial subinterval. This also
provides the metric triangle inequality used below. -/
lemma frameCost_chord {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 0 < b) (hbH : b ≤ Real.pi/4) :
    a / b * frameCost b ≤ frameCost a := by
  have ht : 0 ≤ a/b := div_nonneg ha hb.le
  have ht1 : a/b ≤ 1 := (div_le_one₀ hb).2 hab
  have h := frameCost_concave.2
    (show (0:ℝ) ∈ Set.Icc 0 (Real.pi/4) by constructor <;> positivity)
    (show b ∈ Set.Icc 0 (Real.pi/4) from ⟨hb.le,hbH⟩)
    (sub_nonneg.2 ht1) ht (by ring : (1-a/b)+a/b=1)
  have hid : (a/b)*b=a := div_mul_cancel₀ a hb.ne'
  simpa only [smul_eq_mul,hid,frameCost_zero,mul_zero,zero_add] using h

lemma frameCost_triangle {a b c : ℝ}
    (ha : a ∈ Set.Icc 0 (Real.pi/4))
    (hb : b ∈ Set.Icc 0 (Real.pi/4))
    (hc : c ∈ Set.Icc 0 (Real.pi/4)) (htri : c ≤ a+b) :
    frameCost c ≤ frameCost a+frameCost b := by
  by_cases hs : a+b=0
  · have ha0 : a=0 := by linarith [ha.1,hb.1]
    have hb0 : b=0 := by linarith [ha.1,hb.1]
    have hc0 : c=0 := by linarith [hc.1,htri]
    simp [ha0,hb0,hc0,frameCost_zero]
  have hsp : 0 < a+b := lt_of_le_of_ne (add_nonneg ha.1 hb.1) (Ne.symm hs)
  by_cases hsH : a+b ≤ Real.pi/4
  · have h₁ := frameCost_chord ha.1 (by linarith [hb.1]) hsp hsH
    have h₂ := frameCost_chord hb.1 (by linarith [ha.1]) hsp hsH
    have hid : a/(a+b)*frameCost (a+b)+b/(a+b)*frameCost (a+b)=frameCost (a+b) := by
      field_simp
    have hmono := frameCost_monotone hc ⟨hsp.le,hsH⟩ htri
    linarith
  · have hH : 0 < Real.pi/4 := by positivity
    have h₁ := frameCost_chord ha.1 ha.2 hH le_rfl
    have h₂ := frameCost_chord hb.1 hb.2 hH le_rfl
    have hmono := frameCost_monotone hc ⟨hH.le,le_rfl⟩ hc.2
    have he : (a/(Real.pi/4)+b/(Real.pi/4))*frameCost (Real.pi/4) =
        a/(Real.pi/4)*frameCost (Real.pi/4)+b/(Real.pi/4)*frameCost (Real.pi/4) := by ring
    have hratio : 1 ≤ a/(Real.pi/4)+b/(Real.pi/4) := by
      rw [← add_div]
      exact (one_le_div hH).2 (le_of_not_ge hsH)
    have hh := mul_le_mul_of_nonneg_right hratio frameCost_at_quarter_pos.le
    linarith

lemma frameCost_seven_tenths :
    10394/25425 < 2*frameCost (7/10) := by
  have hc := cos_lower_six (x := (7/10:ℝ)) (by norm_num)
  have hs := sin_lower_seven (x := (7/10:ℝ)) (by norm_num)
  norm_num at hc hs
  dsimp [frameCost]
  linarith

lemma periodicFrameCost_of_short_nonneg {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi/4)) : periodicFrameCost x=frameCost x := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc
    (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
  simp [periodicFrameCost,frameCost,abs_of_nonneg hs,abs_of_nonneg hc]

lemma periodicFrameCost_of_short {x : ℝ} (hx : |x| ≤ Real.pi/4) :
    periodicFrameCost x=frameCost |x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    exact periodicFrameCost_of_short_nonneg ⟨h,by simpa [abs_of_nonneg h] using hx⟩
  · rw [abs_of_nonpos h,← periodicFrameCost_neg x]
    exact periodicFrameCost_of_short_nonneg ⟨neg_nonneg.2 h,by simpa [abs_of_nonpos h] using hx⟩

lemma periodicFrameCost_int_quarter (x : ℝ) (n : ℤ) :
    periodicFrameCost (x+(n:ℝ)*(Real.pi/2))=periodicFrameCost x := by
  have hnat (k : ℕ) : ∀ x : ℝ,
      periodicFrameCost (x+(k:ℝ)*(Real.pi/2))=periodicFrameCost x := by
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        calc
          periodicFrameCost (x+(k+1:ℕ)*(Real.pi/2)) =
              periodicFrameCost ((x+(k:ℝ)*(Real.pi/2))+Real.pi/2) := by congr 1; push_cast; ring
          _ = periodicFrameCost (x+(k:ℝ)*(Real.pi/2)) := periodicFrameCost_pi_half _
          _ = periodicFrameCost x := ih x
  cases n with
  | ofNat k => simpa using hnat k x
  | negSucc k =>
      have h := hnat (k+1) (x-((k+1:ℕ):ℝ)*(Real.pi/2))
      have hid : x-((k+1:ℕ):ℝ)*(Real.pi/2)+((k+1:ℕ):ℝ)*(Real.pi/2)=x := by ring
      rw [hid] at h
      simpa only [Int.cast_negSucc,sub_eq_add_neg,neg_mul] using h.symm

def nearestQuarter (x : ℝ) : ℤ := ⌊x/(Real.pi/2)+1/2⌋

def shortestQuarter (x : ℝ) : ℝ := x-(nearestQuarter x:ℝ)*(Real.pi/2)

lemma shortestQuarter_range (x : ℝ) : |shortestQuarter x| ≤ Real.pi/4 := by
  have hT : 0 < Real.pi/2 := by positivity
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x/(Real.pi/2)+1/2)) hT.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x/(Real.pi/2)+1/2)) hT
  have hid : (x/(Real.pi/2)+1/2)*(Real.pi/2)=x+Real.pi/4 := by field_simp; ring
  rw [hid] at hlo hhi
  apply abs_le.2
  dsimp [shortestQuarter,nearestQuarter]
  constructor <;> linarith

lemma shortestQuarter_cost (x : ℝ) :
    frameCost |shortestQuarter x|=periodicFrameCost x := by
  rw [← periodicFrameCost_of_short (shortestQuarter_range x)]
  have h := periodicFrameCost_int_quarter (shortestQuarter x) (nearestQuarter x)
  have hid : shortestQuarter x+(nearestQuarter x:ℝ)*(Real.pi/2)=x := by
    dsimp [shortestQuarter]
    ring
  rw [hid] at h
  exact h.symm

/-- Real lifts are constructed from the physical frame tour, including the
integer representatives. The winding vanishes by the strict cost budget. -/
structure PhysicalFrameLift (φ : Vertex → ℝ) where
  theta : Vertex → ℝ
  quarter : Vertex → ℤ
  left : ℝ
  diameter : ℝ
  diameter_nonneg : 0 ≤ diameter
  small : diameter < 7/10
  theta_range : ∀ i, left ≤ theta i ∧ theta i ≤ left+diameter
  represents : ∀ i, φ i=theta i+(quarter i:ℝ)*(Real.pi/2)

def quarterPrefix (m : Vertex → ℤ) (i : Vertex) : ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j : Vertex => j.val< i.val),m j

lemma quarterPrefix_difference (m : Vertex → ℤ) (hm : ∑ i,m i=0) (i : Vertex) :
    quarterPrefix m (next i)-quarterPrefix m i=m i := by
  rw [Fin.sum_univ_seven] at hm
  simp only [quarterPrefix,Finset.sum_filter,Fin.sum_univ_seven]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    revert i; decide
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [next] <;> omega

lemma frameCost_closed_range (θ : Vertex → ℝ) {l u : Vertex}
    (hl : ∀ i,θ l ≤ θ i) (hu : ∀ i,θ i ≤ θ u)
    (hD : θ u-θ l ≤ Real.pi/4) :
    2*frameCost (θ u-θ l) ≤ ∑ i,frameCost |θ (next i)-θ i| := by
  have hrange (i j : Vertex) : |θ j-θ i| ∈ Set.Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,(abs_le.2 ⟨?_,?_⟩).trans hD⟩ <;>
      linarith [hl i,hl j,hu i,hu j]
  let r : Vertex → ℝ := fun i => frameCost |θ i-θ l|
  have hstep (i : Vertex) : |r (next i)-r i| ≤ frameCost |θ (next i)-θ i| := by
    have h₁ := frameCost_triangle (hrange l i) (hrange i (next i)) (hrange l (next i))
      (by linarith [abs_sub_le (θ (next i)) (θ i) (θ l)])
    have h₂ := frameCost_triangle (hrange l (next i)) (hrange (next i) i) (hrange l i)
      (by linarith [abs_sub_le (θ i) (θ (next i)) (θ l)])
    rw [abs_sub_comm (θ i) (θ (next i))] at h₂
    apply abs_le.2
    dsimp [r]
    constructor <;> linarith
  have hh := closed_walk_range_bound r l u
  have hr₀ : r l=0 := by simp [r,frameCost_zero]
  have hr₁ : r u=frameCost (θ u-θ l) := by
    simp [r,abs_of_nonneg (sub_nonneg.2 (hl u))]
  rw [hr₀,hr₁,sub_zero,abs_of_nonneg (frameCost_nonneg ⟨sub_nonneg.2 (hl u),hD⟩)] at hh
  exact hh.trans (Finset.sum_le_sum (fun i _ => hstep i))

theorem physical_frame_lift_of_cost (φ : Vertex → ℝ)
    (hcost : (∑ i,periodicFrameCost (φ (next i)-φ i)) < 10394/25425) :
    Nonempty (PhysicalFrameLift φ) := by
  let m : Vertex → ℤ := fun i => nearestQuarter (φ (next i)-φ i)
  let x : Vertex → ℝ := fun i => shortestQuarter (φ (next i)-φ i)
  let U : ℝ := ∑ i,frameCost |x i|
  let V : ℝ := ∑ i,|x i|
  have hU : U < 10394/25425 := by simpa [U,x,shortestQuarter_cost] using hcost
  have hH : 0 < Real.pi/4 := by positivity
  have hseven : (7/10:ℝ) ≤ Real.pi/4 := by linarith [Real.pi_gt_three]
  have hbig : U < 2*frameCost (Real.pi/4) :=
    hU.trans (frameCost_seven_tenths.trans_le
      (mul_le_mul_of_nonneg_left (frameCost_monotone ⟨by norm_num,hseven⟩ ⟨hH.le,le_rfl⟩ hseven)
        (by norm_num)))
  have hchord (i : Vertex) : |x i| * frameCost (Real.pi/4) ≤
      (Real.pi/4)*frameCost |x i| := by
    have h := frameCost_chord (abs_nonneg (x i))
      (shortestQuarter_range (φ (next i)-φ i)) hH le_rfl
    rw [div_mul_eq_mul_div,div_le_iff₀ hH] at h
    linarith
  have hsumchord := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hchord i)
  rw [← Finset.sum_mul,← Finset.mul_sum] at hsumchord
  have hV : V < Real.pi/2 := by
    change (∑ i,|x i|)*frameCost (Real.pi/4) ≤ (Real.pi/4)*U at hsumchord
    change ∑ i,|x i| < Real.pi/2
    nlinarith [frameCost_at_quarter_pos]
  have hxs : ∑ i,x i= -(∑ i,m i:ℤ)*(Real.pi/2) := by
    have h1 : ∑ i,x i=∑ i,(φ (next i)-φ i)-∑ i,((m i:ℝ)*(Real.pi/2)) := by
      rw [← Finset.sum_sub_distrib]
      rfl
    rw [h1,cyclic_difference_sum,← Finset.sum_mul,Int.cast_sum]
    ring
  have habs : |∑ i,x i| < Real.pi/2 :=
    (Finset.abs_sum_le_sum_abs _ _).trans_lt hV
  have hm : ∑ i,m i=0 := by
    by_contra hn
    have hsplit : (1:ℤ) ≤ ∑ i,m i ∨ ∑ i,m i ≤ -1 := by omega
    rw [hxs] at habs
    rcases hsplit with hp | hn
    · have hp' : (1:ℝ) ≤ (∑ i,m i:ℤ) := by exact_mod_cast hp
      have hnegative := neg_le_abs (-(∑ i,m i:ℤ)*(Real.pi/2))
      nlinarith [Real.pi_pos]
    · have hn' : (∑ i,m i:ℤ) ≤ (-1:ℝ) := by exact_mod_cast hn
      have hpositive := le_abs_self (-(∑ i,m i:ℤ)*(Real.pi/2))
      nlinarith [Real.pi_pos]
  let M : Vertex → ℤ := quarterPrefix m
  let θ : Vertex → ℝ := fun i => φ i-(M i:ℝ)*(Real.pi/2)
  have hθstep (i : Vertex) : θ (next i)-θ i=x i := by
    have hi : M (next i)-M i=m i := quarterPrefix_difference m hm i
    have hicast : (M (next i):ℝ)-(M i:ℝ)=(m i:ℝ) := by exact_mod_cast hi
    change (φ (next i)-(M (next i):ℝ)*(Real.pi/2))-(φ i-(M i:ℝ)*(Real.pi/2)) =
      φ (next i)-φ i-(m i:ℝ)*(Real.pi/2)
    linear_combination (-(Real.pi/2))*hicast
  obtain ⟨l,hlmem,hl⟩ := Finset.exists_min_image Finset.univ θ Finset.univ_nonempty
  obtain ⟨u,humem,hu⟩ := Finset.exists_max_image Finset.univ θ Finset.univ_nonempty
  have hl' (i : Vertex) : θ l ≤ θ i := hl i (Finset.mem_univ _)
  have hu' (i : Vertex) : θ i ≤ θ u := hu i (Finset.mem_univ _)
  have hd0 : 0 ≤ θ u-θ l := sub_nonneg.2 (hl' u)
  have hdH : θ u-θ l < Real.pi/4 := by
    have hh := closed_walk_range_bound θ l u
    simp only [hθstep,abs_of_nonneg hd0] at hh
    change ∑ i,|x i| < Real.pi/2 at hV
    linarith
  have hmetric := frameCost_closed_range θ hl' hu' hdH.le
  simp only [hθstep] at hmetric
  have hdsmall : θ u-θ l < 7/10 := by
    by_contra! hbad
    have hmono := frameCost_monotone ⟨by norm_num,hseven⟩ ⟨hd0,hdH.le⟩ hbad
    change ∑ i,frameCost |x i| < 10394/25425 at hU
    linarith [frameCost_seven_tenths]
  refine ⟨⟨θ,M,θ l,θ u-θ l,hd0,hdsmall,?_,?_⟩⟩
  · intro i
    exact ⟨hl' i,by linarith [hu' i]⟩
  · intro i
    change φ i=(φ i-(M i:ℝ)*(Real.pi/2))+(M i:ℝ)*(Real.pi/2)
    ring

end SquaresInCircles.Eight
