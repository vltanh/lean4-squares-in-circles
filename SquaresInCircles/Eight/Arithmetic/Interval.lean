module

public import SquaresInCircles.Common.Trigonometry
public import Mathlib

/-!
# Exact rational intervals

Uncompiled formalization draft.  Every comparison below is an ordinary
ordered-field proposition.  No external evaluation result is a premise.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

structure QInterval where
  lo : ℚ
  hi : ℚ

namespace QInterval

def Mem (I : QInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)
def point (q : ℚ) : QInterval := ⟨q,q⟩
def add (I J : QInterval) : QInterval := ⟨I.lo+J.lo,I.hi+J.hi⟩
def neg (I : QInterval) : QInterval := ⟨-I.hi,-I.lo⟩
def sub (I J : QInterval) : QInterval := add I (neg J)
def mul (I J : QInterval) : QInterval :=
  ⟨min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)),
   max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))⟩
def inv (I : QInterval) : QInterval := ⟨I.hi⁻¹,I.lo⁻¹⟩
def pow (I : QInterval) : ℕ → QInterval
  | 0 => point 1
  | n+1 => mul (pow I n) I

@[simp] theorem mem_point (q : ℚ) : (point q).Mem (q : ℝ) := ⟨le_rfl,le_rfl⟩

theorem mem_add {I J : QInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.add J).Mem (x+y) := by
  dsimp [Mem,add] at *
  push_cast
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem mem_neg {I : QInterval} {x : ℝ} (hx : I.Mem x) : I.neg.Mem (-x) := by
  dsimp [Mem,neg] at *
  push_cast
  constructor <;> linarith [hx.1,hx.2]

theorem mem_sub {I J : QInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.sub J).Mem (x-y) := by
  simpa [sub_eq_add_neg,sub] using mem_add hx (mem_neg hy)

/-- A bilinear function on a rectangle lies between its four corner values.
This elementary proof also covers degenerate intervals. -/
theorem product_between_corners {l u L U x y m M : ℝ}
    (hx : l ≤ x ∧ x ≤ u) (hy : L ≤ y ∧ y ≤ U)
    (hlo : m ≤ l*L ∧ m ≤ l*U ∧ m ≤ u*L ∧ m ≤ u*U)
    (hhi : l*L ≤ M ∧ l*U ≤ M ∧ u*L ≤ M ∧ u*U ≤ M) :
    m ≤ x*y ∧ x*y ≤ M := by
  constructor
  · by_cases hx0 : 0 ≤ x
    · have hxy := mul_le_mul_of_nonneg_left hy.1 hx0
      by_cases hL : 0 ≤ L
      · exact hlo.1.trans ((mul_le_mul_of_nonneg_right hx.1 hL).trans hxy)
      · exact hlo.2.2.1.trans
          ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hL)).trans hxy)
    · have hxy := mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hx0)
      by_cases hU : 0 ≤ U
      · exact hlo.2.1.trans ((mul_le_mul_of_nonneg_right hx.1 hU).trans hxy)
      · exact hlo.2.2.2.trans
          ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hU)).trans hxy)
  · by_cases hx0 : 0 ≤ x
    · have hxy := mul_le_mul_of_nonneg_left hy.2 hx0
      by_cases hU : 0 ≤ U
      · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hU).trans hhi.2.2.2)
      · exact hxy.trans
          ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hU)).trans hhi.2.1)
    · have hxy := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hx0)
      by_cases hL : 0 ≤ L
      · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hL).trans hhi.2.2.1)
      · exact hxy.trans
          ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hL)).trans hhi.1)

theorem mem_mul {I J : QInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.mul J).Mem (x*y) := by
  have hll : (I.mul J).lo ≤ I.lo*J.lo :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hlu : (I.mul J).lo ≤ I.lo*J.hi :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hul : (I.mul J).lo ≤ I.hi*J.lo :=
    (min_le_right _ _).trans (min_le_left _ _)
  have huu : (I.mul J).lo ≤ I.hi*J.hi :=
    (min_le_right _ _).trans (min_le_right _ _)
  have Hll : I.lo*J.lo ≤ (I.mul J).hi :=
    (le_max_left _ _).trans (le_max_left _ _)
  have Hlu : I.lo*J.hi ≤ (I.mul J).hi :=
    (le_max_right _ _).trans (le_max_left _ _)
  have Hul : I.hi*J.lo ≤ (I.mul J).hi :=
    (le_max_left _ _).trans (le_max_right _ _)
  have Huu : I.hi*J.hi ≤ (I.mul J).hi :=
    (le_max_right _ _).trans (le_max_right _ _)
  apply product_between_corners hx hy
  · constructor
    · exact_mod_cast hll
    · constructor
      · exact_mod_cast hlu
      · exact ⟨by exact_mod_cast hul,by exact_mod_cast huu⟩
  · constructor
    · exact_mod_cast Hll
    · constructor
      · exact_mod_cast Hlu
      · exact ⟨by exact_mod_cast Hul,by exact_mod_cast Huu⟩

theorem mem_pow {I : QInterval} {x : ℝ} (hx : I.Mem x) (n : ℕ) :
    (I.pow n).Mem (x^n) := by
  induction n with
  | zero => simpa [pow] using mem_point 1
  | succ n ih => simpa [pow,pow_succ] using mem_mul ih hx

theorem mem_inv_pos {I : QInterval} {x : ℝ} (hI : 0 < I.lo) (hx : I.Mem x) :
    I.inv.Mem x⁻¹ := by
  have hIl : (0 : ℝ) < I.lo := by exact_mod_cast hI
  have hx0 : 0 < x := hIl.trans_le hx.1
  dsimp [Mem,inv]
  push_cast
  exact ⟨inv_anti₀ hx0 hx.2,inv_anti₀ hIl hx.1⟩

/-- Square-root enclosures are justified by their squared rational endpoints. -/
theorem mem_sqrt {I J : QInterval} {x : ℝ}
    (hx : I.Mem x) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo)
    (hl : J.lo^2 ≤ I.lo) (hu : I.hi ≤ J.hi^2) (hJu : 0 ≤ J.hi) :
    J.Mem (Real.sqrt x) := by
  have h0 : (0 : ℝ) ≤ I.lo := by exact_mod_cast hI
  have hl0 : (0 : ℝ) ≤ J.lo := by exact_mod_cast hJ
  have hu0 : (0 : ℝ) ≤ J.hi := by exact_mod_cast hJu
  have hlow : (J.lo : ℝ)^2 ≤ I.lo := by exact_mod_cast hl
  have hupp : (I.hi : ℝ) ≤ (J.hi : ℝ)^2 := by exact_mod_cast hu
  have hs := Real.sq_sqrt (h0.trans hx.1)
  have hn := Real.sqrt_nonneg x
  constructor <;> nlinarith [hx.1,hx.2]

theorem mem_mono {I J : QInterval} {x : ℝ} (hx : I.Mem x)
    (hl : J.lo ≤ I.lo) (hu : I.hi ≤ J.hi) : J.Mem x := by
  have h₁ : (J.lo : ℝ) ≤ I.lo := by exact_mod_cast hl
  have h₂ : (I.hi : ℝ) ≤ J.hi := by exact_mod_cast hu
  exact ⟨h₁.trans hx.1,hx.2.trans h₂⟩

end QInterval
end SquaresInCircles.Eight.Arithmetic
