module

public import SquaresInCircles.Eight.Arithmetic.Bernstein7
public import SquaresInCircles.Eight.Arithmetic.Taylor

/-!
# Positivity of `c₀ + c₁ u + c₂ sin u + c₃ cos u` on a short interval

Every finite inequality of the affine tables has this form in the angle `u`,
with coefficients known only as intervals. For `u ≥ 0`,
`sin u = sin₇ u + e_s u⁹` with `0 ≤ e_s ≤ 1/9!` and
`cos u = cos₈ u + e_c u¹⁰` with `-1/10! ≤ e_c ≤ 0`, so the expression is at least
the polynomial whose coefficients are the lower ends of the coefficient
intervals. That polynomial has integer coefficients over `unit`, and the
Bernstein test of `Bernstein11` decides its sign on the interval.

For `u ≤ 4/5` the Taylor tails also fit into the coefficient of `u⁶`, which gives a lower
polynomial of degree six and the cheaper test of `Bernstein7`; it is tried first.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic.Fixed

/-- `⌊a / k⌋` for a positive natural `k`. -/
def floorDiv (a : Int) (k : Nat) : Int := a / (k : Int)

theorem floorDiv_le (a : Int) {k : Nat} (hk : 0 < k) :
    ((floorDiv a k : Int) : ℝ) ≤ (a : ℝ) / k := by
  have hkI : (0 : Int) < k := by exact_mod_cast hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hkR]
  have h := Int.ediv_mul_le a (ne_of_gt hkI)
  have h' : ((a / (k : Int) * (k : Int) : Int) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

/-- The lower coefficients of `c₀ + c₁ u + c₂ sin u + c₃ cos u`, scaled by `unit`. -/
def trigLower (c0 c1 c2 c3 : FI) : List Int :=
  [c0.lo + c3.lo, c1.lo + c2.lo, floorDiv (-c3.hi) 2, floorDiv (-c2.hi) 6, floorDiv c3.lo 24,
   floorDiv c2.lo 120, floorDiv (-c3.hi) 720, floorDiv (-c2.hi) 5040, floorDiv c3.lo 40320,
   floorDiv (min 0 c2.lo) 362880, floorDiv (min 0 (-c3.hi)) 3628800]

/-- Split integer coefficients into their positive and negative parts. -/
def splitPos : List Int → N11
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] =>
      ⟨a0.toNat, a1.toNat, a2.toNat, a3.toNat, a4.toNat, a5.toNat, a6.toNat, a7.toNat, a8.toNat,
        a9.toNat, a10.toNat⟩
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def splitNeg : List Int → N11
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] =>
      ⟨(-a0).toNat, (-a1).toNat, (-a2).toNat, (-a3).toNat, (-a4).toNat, (-a5).toNat, (-a6).toNat,
        (-a7).toNat, (-a8).toNat, (-a9).toNat, (-a10).toNat⟩
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The positive and the negative parts of the lower coefficients, computed directly with the
integer operations of `Fixed`. -/
def lowerPN (c0 c1 c2 c3 : FI) : N11 × N11 :=
  let a0 := iadd c0.lo c3.lo
  let a1 := iadd c1.lo c2.lo
  let n3 := ineg c3.hi
  let n2 := ineg c2.hi
  let a2 := ifloor n3 2
  let a3 := ifloor n2 6
  let a4 := ifloor c3.lo 24
  let a5 := ifloor c2.lo 120
  let a6 := ifloor n3 720
  let a7 := ifloor n2 5040
  let a8 := ifloor c3.lo 40320
  let a9 := ifloor (imin (Int.ofNat 0) c2.lo) 362880
  let a10 := ifloor (imin (Int.ofNat 0) n3) 3628800
  (⟨ipos a0, ipos a1, ipos a2, ipos a3, ipos a4, ipos a5, ipos a6, ipos a7, ipos a8, ipos a9,
      ipos a10⟩,
    ⟨ineg' a0, ineg' a1, ineg' a2, ineg' a3, ineg' a4, ineg' a5, ineg' a6, ineg' a7, ineg' a8,
      ineg' a9, ineg' a10⟩)

theorem lowerPN_eq (c0 c1 c2 c3 : FI) :
    lowerPN c0 c1 c2 c3 = (splitPos (trigLower c0 c1 c2 c3), splitNeg (trigLower c0 c1 c2 c3)) := by
  simp (disch := norm_num) only [lowerPN, trigLower, splitPos, splitNeg, ipos_eq, ineg'_eq,
    iadd_eq, ineg_eq, imin_eq, ifloor_eq, floorDiv, Int.ofNat_eq_natCast, Nat.cast_zero]

/-- The positive and negative parts of the coefficients of a lower polynomial of degree six,
for `0 ≤ u ≤ 4/5`: the tails of `sin` and `cos` are bounded by multiples of `u⁶`. The integer
operations are those of `Fixed` that the kernel evaluates on natural numbers. -/
def lowerPN6 (c0 c1 c2 c3 : FI) : N7 × N7 :=
  let n3 := ineg c3.hi
  let p0 := intPN (iadd c0.lo c3.lo)
  let p1 := intPN (iadd c1.lo c2.lo)
  let p2 := floorPN n3 2
  let p3 := floorPN (ineg c2.hi) 6
  let p4 := floorPN c3.lo 24
  let p5 := floorPN c2.lo 120
  let p6 := intPN (iadd (iadd (ifloor n3 720) (ifloor (ineg (imax (Int.ofNat 0) c2.hi)) 6300))
    (ifloor (imin (Int.ofNat 0) c3.lo) 63000))
  (⟨p0.1, p1.1, p2.1, p3.1, p4.1, p5.1, p6.1⟩, ⟨p0.2, p1.2, p2.2, p3.2, p4.2, p5.2, p6.2⟩)

theorem lowerPN6_eq (c0 c1 c2 c3 : FI) : lowerPN6 c0 c1 c2 c3 =
    (⟨(c0.lo + c3.lo).toNat, (c1.lo + c2.lo).toNat, (floorDiv (-c3.hi) 2).toNat,
        (floorDiv (-c2.hi) 6).toNat, (floorDiv c3.lo 24).toNat, (floorDiv c2.lo 120).toNat,
        (floorDiv (-c3.hi) 720 + floorDiv (-(max 0 c2.hi)) 6300 +
          floorDiv (min 0 c3.lo) 63000).toNat⟩,
      ⟨(-(c0.lo + c3.lo)).toNat, (-(c1.lo + c2.lo)).toNat, (-floorDiv (-c3.hi) 2).toNat,
        (-floorDiv (-c2.hi) 6).toNat, (-floorDiv c3.lo 24).toNat, (-floorDiv c2.lo 120).toNat,
        (-(floorDiv (-c3.hi) 720 + floorDiv (-(max 0 c2.hi)) 6300 +
          floorDiv (min 0 c3.lo) 63000)).toNat⟩) := by
  simp (disch := norm_num) only [lowerPN6, intPN_eq, floorPN_eq, iadd_eq, ineg_eq, imax_eq,
    imin_eq, ifloor_eq, floorDiv, Int.ofNat_eq_natCast, Nat.cast_zero]

/-- Degree ten. -/
def trigPositive10 (den l h : Nat) (c0 c1 c2 c3 : FI) : Bool :=
  let p := lowerPN c0 c1 c2 c3
  positiveOnN den l h p.1 p.2

def trigNonneg10 (den l h : Nat) (c0 c1 c2 c3 : FI) : Bool :=
  let p := lowerPN c0 c1 c2 c3
  nonnegOnN den l h p.1 p.2

/-- Degree six, on intervals inside `[0, 4/5]`. -/
def trigPositive6 (den l h : Nat) (c0 c1 c2 c3 : FI) : Bool :=
  Nat.ble (Nat.mul 5 h) (Nat.mul 4 den) &&
    (let p := lowerPN6 c0 c1 c2 c3; positiveOnN7 den l h p.1 p.2)

def trigNonneg6 (den l h : Nat) (c0 c1 c2 c3 : FI) : Bool :=
  Nat.ble (Nat.mul 5 h) (Nat.mul 4 den) &&
    (let p := lowerPN6 c0 c1 c2 c3; nonnegOnN7 den l h p.1 p.2)

/-- For `u ∈ [0, 1]`, `c₂ sin u ≥ c₂ u - c₂⁺ u³ / 6` and `c₃ cos u ≥ c₃ - c₃⁺ u² / 2`, so the
polynomial `(c₀ + c₃) + (c₁ + c₂) u - n₂ u² - n₃ u³` with `n₂ = ⌈c₃⁺ / 2⌉`, `n₃ = ⌈c₂⁺ / 6⌉` (lower
ends, over `unit`) is below the expression. This is its positive part at `l`, scaled by `den ³`. -/
def cubicPos (den l : Nat) (c0 c1 c2 c3 : FI) : Nat :=
  Nat.add (Nat.mul (ipos (iadd c0.lo c3.lo)) (Nat.mul (Nat.mul den den) den))
    (Nat.mul (Nat.mul (ipos (iadd c1.lo c2.lo)) l) (Nat.mul den den))

/-- Its negative part at `h`, scaled by `den ³`. -/
def cubicNeg (den h : Nat) (c0 c1 c2 c3 : FI) : Nat :=
  Nat.add
    (Nat.add (Nat.mul (ineg' (iadd c0.lo c3.lo)) (Nat.mul (Nat.mul den den) den))
      (Nat.mul (Nat.mul (ineg' (iadd c1.lo c2.lo)) h) (Nat.mul den den)))
    (Nat.add (Nat.mul (Nat.mul (Nat.div (Nat.add (ipos c3.lo) 1) 2) (Nat.mul h h)) den)
      (Nat.mul (Nat.div (Nat.add (ipos c2.lo) 5) 6) (Nat.mul (Nat.mul h h) h)))

/-- Degree three, on intervals inside `[0, 1]`: the positive part increases and the negative part
decreases in `u`, so the polynomial is positive (nonnegative) on `[l, h]` when the negative part at
`h` is below (at most) the positive part at `l`. -/
def mono3 (den l h : Nat) (c0 c1 c2 c3 : FI) (strict : Bool) : Bool :=
  Nat.blt 0 den && Nat.ble h den &&
    bif strict then Nat.blt (cubicNeg den h c0 c1 c2 c3) (cubicPos den l c0 c1 c2 c3)
    else Nat.ble (cubicNeg den h c0 c1 c2 c3) (cubicPos den l c0 c1 c2 c3)

/-- `c₀ + c₁ u + c₂ sin u + c₃ cos u > 0` for `u ∈ [l / den, h / den]`: degree three first, then
six, then ten. -/
def trigPositive (den l h : Nat) (c0 c1 c2 c3 : FI) : Bool :=
  mono3 den l h c0 c1 c2 c3 true || trigPositive6 den l h c0 c1 c2 c3 ||
    trigPositive10 den l h c0 c1 c2 c3

/-- `c₀ + c₁ u + c₂ sin u + c₃ cos u ≥ 0` for `u ∈ [l / den, h / den]`. -/
def trigNonneg (den l h : Nat) (c0 c1 c2 c3 : FI) : Bool :=
  mono3 den l h c0 c1 c2 c3 false || trigNonneg6 den l h c0 c1 c2 c3 ||
    trigNonneg10 den l h c0 c1 c2 c3

end SquaresInCircles.Eight.Arithmetic.Fixed

namespace SquaresInCircles.Eight.Arithmetic.Fixed

theorem split_eval (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Int) (u : ℝ) :
    (splitPos [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]).eval u -
      (splitNeg [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]).eval u =
    (a0 : ℝ) + a1 * u + a2 * u ^ 2 + a3 * u ^ 3 + a4 * u ^ 4 + a5 * u ^ 5 + a6 * u ^ 6 +
      a7 * u ^ 7 + a8 * u ^ 8 + a9 * u ^ 9 + a10 * u ^ 10 := by
  have key (a : Int) : ((a.toNat : ℕ) : ℝ) - (((-a).toNat : ℕ) : ℝ) = a := by
    have h := Int.toNat_sub_toNat_neg a
    exact_mod_cast h
  simp only [splitPos, splitNeg, N11.eval]
  linear_combination (key a0) * u ^ 0 + u * (key a1) + u ^ 2 * (key a2) + u ^ 3 * (key a3) +
    u ^ 4 * (key a4) + u ^ 5 * (key a5) + u ^ 6 * (key a6) + u ^ 7 * (key a7) +
    u ^ 8 * (key a8) + u ^ 9 * (key a9) + u ^ 10 * (key a10)

/-- The lower polynomial of `trigLower` is below the real expression. -/
theorem trigLower_le {c0 c1 c2 c3 : FI} {x0 x1 x2 x3 u : ℝ} (h0 : c0.Mem x0) (h1 : c1.Mem x1)
    (h2 : c2.Mem x2) (h3 : c3.Mem x3) (hu : 0 ≤ u) :
    ((splitPos (trigLower c0 c1 c2 c3)).eval u - (splitNeg (trigLower c0 c1 c2 c3)).eval u) / unit ≤
      x0 + x1 * u + x2 * Real.sin u + x3 * Real.cos u := by
  have hU := unit_pos_real
  obtain ⟨es, hes0, hes1, hs⟩ := sin_remainder_coefficient hu
  obtain ⟨ec, hec0, hec1, hc⟩ := cos_remainder_coefficient hu
  rw [trigLower, split_eval, hs, hc]
  simp only [sin7, cos8]
  have l0 : ((c0.lo + c3.lo : Int) : ℝ) / unit ≤ x0 + x3 := by
    push_cast; rw [add_div]; linarith [h0.1, h3.1]
  have l1 : ((c1.lo + c2.lo : Int) : ℝ) / unit ≤ x1 + x2 := by
    push_cast; rw [add_div]; linarith [h1.1, h2.1]
  have lk (a : Int) (k : Nat) (hk : 0 < k) (y : ℝ) (hy : (a : ℝ) / unit ≤ y) :
      ((floorDiv a k : Int) : ℝ) / unit ≤ y / k := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hf := floorDiv_le a hk
    calc ((floorDiv a k : Int) : ℝ) / unit ≤ (a : ℝ) / k / unit := by gcongr
      _ = (a : ℝ) / unit / k := by ring
      _ ≤ y / k := by gcongr
  have hn3 : ((-c3.hi : Int) : ℝ) / unit ≤ -x3 := by push_cast; rw [neg_div]; linarith [h3.2]
  have hn2 : ((-c2.hi : Int) : ℝ) / unit ≤ -x2 := by push_cast; rw [neg_div]; linarith [h2.2]
  have hm2 : ((min 0 c2.lo : Int) : ℝ) / unit ≤ min 0 x2 := by
    apply le_min
    · apply div_nonpos_of_nonpos_of_nonneg _ hU.le
      exact_mod_cast (min_le_left 0 c2.lo)
    · calc ((min 0 c2.lo : Int) : ℝ) / unit ≤ (c2.lo : ℝ) / unit := by
            gcongr; exact_mod_cast (min_le_right 0 c2.lo)
        _ ≤ x2 := h2.1
  have hm3 : ((min 0 (-c3.hi) : Int) : ℝ) / unit ≤ min 0 (-x3) := by
    apply le_min
    · apply div_nonpos_of_nonpos_of_nonneg _ hU.le
      exact_mod_cast (min_le_left 0 (-c3.hi))
    · calc ((min 0 (-c3.hi) : Int) : ℝ) / unit ≤ ((-c3.hi : Int) : ℝ) / unit := by
            gcongr; exact_mod_cast (min_le_right 0 (-c3.hi))
        _ ≤ -x3 := hn3
  have l9 : ((floorDiv (min 0 c2.lo) 362880 : Int) : ℝ) / unit ≤ x2 * es := by
    have h := lk _ 362880 (by norm_num) _ hm2
    have h' : min 0 x2 / ((362880 : ℕ) : ℝ) ≤ x2 * es := by
      push_cast
      rcases le_total 0 x2 with hx | hx
      · rw [min_eq_left hx]; simp; positivity
      · rw [min_eq_right hx]
        have : x2 * (1 / 362880) ≤ x2 * es := mul_le_mul_of_nonpos_left hes1 hx
        linarith
    linarith
  have l10 : ((floorDiv (min 0 (-c3.hi)) 3628800 : Int) : ℝ) / unit ≤ x3 * ec := by
    have h := lk _ 3628800 (by norm_num) _ hm3
    have h' : min 0 (-x3) / ((3628800 : ℕ) : ℝ) ≤ x3 * ec := by
      push_cast
      rcases le_total 0 x3 with hx | hx
      · rw [min_eq_right (by linarith)]
        have : x3 * (-(1 / 3628800)) ≤ x3 * ec := mul_le_mul_of_nonneg_left hec0 hx
        linarith
      · rw [min_eq_left (by linarith)]
        simp
        exact mul_nonneg_of_nonpos_of_nonpos hx hec1
    linarith
  have p1 := mul_le_mul_of_nonneg_right l1 hu
  have p2 := mul_le_mul_of_nonneg_right (lk _ 2 (by norm_num) _ hn3) (pow_nonneg hu 2)
  have p3 := mul_le_mul_of_nonneg_right (lk _ 6 (by norm_num) _ hn2) (pow_nonneg hu 3)
  have p4 := mul_le_mul_of_nonneg_right (lk _ 24 (by norm_num) _ h3.1) (pow_nonneg hu 4)
  have p5 := mul_le_mul_of_nonneg_right (lk _ 120 (by norm_num) _ h2.1) (pow_nonneg hu 5)
  have p6 := mul_le_mul_of_nonneg_right (lk _ 720 (by norm_num) _ hn3) (pow_nonneg hu 6)
  have p7 := mul_le_mul_of_nonneg_right (lk _ 5040 (by norm_num) _ hn2) (pow_nonneg hu 7)
  have p8 := mul_le_mul_of_nonneg_right (lk _ 40320 (by norm_num) _ h3.1) (pow_nonneg hu 8)
  have p9 := mul_le_mul_of_nonneg_right l9 (pow_nonneg hu 9)
  have p10 := mul_le_mul_of_nonneg_right l10 (pow_nonneg hu 10)
  push_cast at p2 p3 p4 p5 p6 p7 p8
  linear_combination l0 + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9 + p10

/-! ### Degree six -/

theorem sin_lower6 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 4 / 5) :
    u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 6 / 6300 ≤ Real.sin u := by
  have h := (trig_taylor_bounds h0).1
  simp only [sin7] at h
  have hm : u ^ 6 * u ≤ u ^ 6 * (4 / 5) := mul_le_mul_of_nonneg_left h1 (pow_nonneg h0 6)
  nlinarith

theorem sin_upper5 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 4 / 5) :
    Real.sin u ≤ u - u ^ 3 / 6 + u ^ 5 / 120 := by
  have h := (trig_taylor_bounds h0).2.1
  simp only [sin9, sin7] at h
  have hu2 : u ^ 2 ≤ 72 := by nlinarith
  have hm : u ^ 7 * u ^ 2 ≤ u ^ 7 * 72 := mul_le_mul_of_nonneg_left hu2 (pow_nonneg h0 7)
  nlinarith

theorem cos_lower6 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 4 / 5) :
    1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 ≤ Real.cos u := by
  have h := (trig_taylor_bounds h0).2.2.1
  simp only [cos10, cos8] at h
  have hu2 : u ^ 2 ≤ 90 := by nlinarith
  have hm : u ^ 8 * u ^ 2 ≤ u ^ 8 * 90 := mul_le_mul_of_nonneg_left hu2 (pow_nonneg h0 8)
  nlinarith

theorem cos_upper6 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 4 / 5) :
    Real.cos u ≤ 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 6 / 63000 := by
  have h := (trig_taylor_bounds h0).2.2.2
  simp only [cos8] at h
  have hu2 : u ^ 2 ≤ 16 / 25 := by nlinarith
  have hm : u ^ 6 * u ^ 2 ≤ u ^ 6 * (16 / 25) := mul_le_mul_of_nonneg_left hu2 (pow_nonneg h0 6)
  nlinarith

theorem lowerPN6_eval (c0 c1 c2 c3 : FI) (u : ℝ) :
    (lowerPN6 c0 c1 c2 c3).1.eval u - (lowerPN6 c0 c1 c2 c3).2.eval u =
      ((c0.lo + c3.lo : Int) : ℝ) + ((c1.lo + c2.lo : Int) : ℝ) * u +
        ((floorDiv (-c3.hi) 2 : Int) : ℝ) * u ^ 2 + ((floorDiv (-c2.hi) 6 : Int) : ℝ) * u ^ 3 +
        ((floorDiv c3.lo 24 : Int) : ℝ) * u ^ 4 + ((floorDiv c2.lo 120 : Int) : ℝ) * u ^ 5 +
        ((floorDiv (-c3.hi) 720 + floorDiv (-(max 0 c2.hi)) 6300 + floorDiv (min 0 c3.lo) 63000 :
          Int) : ℝ) * u ^ 6 := by
  have key (a : Int) : ((a.toNat : ℕ) : ℝ) - (((-a).toNat : ℕ) : ℝ) = a := by
    have h := Int.toNat_sub_toNat_neg a
    exact_mod_cast h
  rw [lowerPN6_eq]
  simp only [N7.eval]
  linear_combination (key (c0.lo + c3.lo)) * u ^ 0 + u * (key (c1.lo + c2.lo)) +
    u ^ 2 * (key (floorDiv (-c3.hi) 2)) + u ^ 3 * (key (floorDiv (-c2.hi) 6)) +
    u ^ 4 * (key (floorDiv c3.lo 24)) + u ^ 5 * (key (floorDiv c2.lo 120)) +
    u ^ 6 * (key (floorDiv (-c3.hi) 720 + floorDiv (-(max 0 c2.hi)) 6300 +
      floorDiv (min 0 c3.lo) 63000))

/-- The degree-six lower polynomial is below the real expression on `[0, 4/5]`. -/
theorem lower6_le {c0 c1 c2 c3 : FI} {x0 x1 x2 x3 u : ℝ} (h0 : c0.Mem x0) (h1 : c1.Mem x1)
    (h2 : c2.Mem x2) (h3 : c3.Mem x3) (hu : 0 ≤ u) (hu1 : u ≤ 4 / 5) :
    ((lowerPN6 c0 c1 c2 c3).1.eval u - (lowerPN6 c0 c1 c2 c3).2.eval u) / unit ≤
      x0 + x1 * u + x2 * Real.sin u + x3 * Real.cos u := by
  have hU := unit_pos_real
  rw [lowerPN6_eval]
  have l0 : ((c0.lo + c3.lo : Int) : ℝ) / unit ≤ x0 + x3 := by
    push_cast; rw [add_div]; linarith [h0.1, h3.1]
  have l1 : ((c1.lo + c2.lo : Int) : ℝ) / unit ≤ x1 + x2 := by
    push_cast; rw [add_div]; linarith [h1.1, h2.1]
  have lk (a : Int) (k : Nat) (hk : 0 < k) (y : ℝ) (hy : (a : ℝ) / unit ≤ y) :
      ((floorDiv a k : Int) : ℝ) / unit ≤ y / k := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hf := floorDiv_le a hk
    calc ((floorDiv a k : Int) : ℝ) / unit ≤ (a : ℝ) / k / unit := by gcongr
      _ = (a : ℝ) / unit / k := by ring
      _ ≤ y / k := by gcongr
  have hn3 : ((-c3.hi : Int) : ℝ) / unit ≤ -x3 := by push_cast; rw [neg_div]; linarith [h3.2]
  have hn2 : ((-c2.hi : Int) : ℝ) / unit ≤ -x2 := by push_cast; rw [neg_div]; linarith [h2.2]
  have hmx2 : ((-(max 0 c2.hi) : Int) : ℝ) / unit ≤ -(max 0 x2) := by
    have : max 0 x2 ≤ ((max 0 c2.hi : Int) : ℝ) / unit := by
      apply max_le
      · apply div_nonneg _ hU.le
        exact_mod_cast (le_max_left 0 c2.hi)
      · calc x2 ≤ (c2.hi : ℝ) / unit := h2.2
          _ ≤ ((max 0 c2.hi : Int) : ℝ) / unit := by
            gcongr; exact_mod_cast (le_max_right 0 c2.hi)
    push_cast at this ⊢
    rw [neg_div]
    linarith
  have hm3 : ((min 0 c3.lo : Int) : ℝ) / unit ≤ min 0 x3 := by
    apply le_min
    · apply div_nonpos_of_nonpos_of_nonneg _ hU.le
      exact_mod_cast (min_le_left 0 c3.lo)
    · calc ((min 0 c3.lo : Int) : ℝ) / unit ≤ (c3.lo : ℝ) / unit := by
            gcongr; exact_mod_cast (min_le_right 0 c3.lo)
        _ ≤ x3 := h3.1
  have l6 : ((floorDiv (-c3.hi) 720 + floorDiv (-(max 0 c2.hi)) 6300 +
      floorDiv (min 0 c3.lo) 63000 : Int) : ℝ) / unit ≤
      -x3 / 720 + -(max 0 x2) / 6300 + min 0 x3 / 63000 := by
    have a := lk _ 720 (by norm_num) _ hn3
    have b := lk _ 6300 (by norm_num) _ hmx2
    have c := lk _ 63000 (by norm_num) _ hm3
    push_cast at a b c ⊢
    rw [add_div, add_div]
    linarith
  have hS : x2 * (u - u ^ 3 / 6 + u ^ 5 / 120) - max 0 x2 * (u ^ 6 / 6300) ≤ x2 * Real.sin u := by
    rcases le_total 0 x2 with hx | hx
    · rw [max_eq_right hx]
      have := mul_le_mul_of_nonneg_left (sin_lower6 hu hu1) hx
      linarith
    · rw [max_eq_left hx]
      have := mul_le_mul_of_nonpos_left (sin_upper5 hu hu1) hx
      linarith
  have hC : x3 * (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720) + min 0 x3 * (u ^ 6 / 63000) ≤
      x3 * Real.cos u := by
    rcases le_total 0 x3 with hx | hx
    · rw [min_eq_left hx]
      have := mul_le_mul_of_nonneg_left (cos_lower6 hu hu1) hx
      linarith
    · rw [min_eq_right hx]
      have := mul_le_mul_of_nonpos_left (cos_upper6 hu hu1) hx
      linarith
  have p1 := mul_le_mul_of_nonneg_right l1 hu
  have p2 := mul_le_mul_of_nonneg_right (lk _ 2 (by norm_num) _ hn3) (pow_nonneg hu 2)
  have p3 := mul_le_mul_of_nonneg_right (lk _ 6 (by norm_num) _ hn2) (pow_nonneg hu 3)
  have p4 := mul_le_mul_of_nonneg_right (lk _ 24 (by norm_num) _ h3.1) (pow_nonneg hu 4)
  have p5 := mul_le_mul_of_nonneg_right (lk _ 120 (by norm_num) _ h2.1) (pow_nonneg hu 5)
  have p6 := mul_le_mul_of_nonneg_right l6 (pow_nonneg hu 6)
  push_cast at p2 p3 p4 p5
  linear_combination l0 + p1 + p2 + p3 + p4 + p5 + p6 + hS + hC

theorem trigPositive6_sound {den l h : Nat} {c0 c1 c2 c3 : FI}
    (hp : trigPositive6 den l h c0 c1 c2 c3 = true) {x0 x1 x2 x3 u : ℝ}
    (h0 : c0.Mem x0) (h1 : c1.Mem x1) (h2 : c2.Mem x2) (h3 : c3.Mem x3)
    (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    0 < x0 + x1 * u + x2 * Real.sin u + x3 * Real.cos u := by
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  simp only [trigPositive6, Bool.and_eq_true, Nat.ble_eq, nat_mul_eq] at hp
  obtain ⟨h45, hp⟩ := hp
  have hden : 0 < den := by
    simp only [positiveOnN7, Bool.and_eq_true, Nat.blt_eq] at hp
    exact hp.1.1
  have hu1 : u ≤ 4 / 5 := by
    have hdR : (0 : ℝ) < den := by exact_mod_cast hden
    refine hu.2.trans ?_
    rw [div_le_iff₀ hdR]
    have : ((5 * h : ℕ) : ℝ) ≤ ((4 * den : ℕ) : ℝ) := by exact_mod_cast h45
    push_cast at this
    linarith
  have hpos := positiveOnN7_sound hp hu
  have hle := lower6_le h0 h1 h2 h3 hu0 hu1
  have hU := unit_pos_real
  have : 0 < ((lowerPN6 c0 c1 c2 c3).1.eval u - (lowerPN6 c0 c1 c2 c3).2.eval u) / unit :=
    div_pos (by linarith) hU
  linarith

theorem trigNonneg6_sound {den l h : Nat} {c0 c1 c2 c3 : FI}
    (hp : trigNonneg6 den l h c0 c1 c2 c3 = true) {x0 x1 x2 x3 u : ℝ}
    (h0 : c0.Mem x0) (h1 : c1.Mem x1) (h2 : c2.Mem x2) (h3 : c3.Mem x3)
    (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    0 ≤ x0 + x1 * u + x2 * Real.sin u + x3 * Real.cos u := by
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  simp only [trigNonneg6, Bool.and_eq_true, Nat.ble_eq, nat_mul_eq] at hp
  obtain ⟨h45, hp⟩ := hp
  have hden : 0 < den := by
    simp only [nonnegOnN7, Bool.and_eq_true, Nat.blt_eq] at hp
    exact hp.1.1
  have hu1 : u ≤ 4 / 5 := by
    have hdR : (0 : ℝ) < den := by exact_mod_cast hden
    refine hu.2.trans ?_
    rw [div_le_iff₀ hdR]
    have : ((5 * h : ℕ) : ℝ) ≤ ((4 * den : ℕ) : ℝ) := by exact_mod_cast h45
    push_cast at this
    linarith
  have hnn := nonnegOnN7_sound hp hu
  have hle := lower6_le h0 h1 h2 h3 hu0 hu1
  have hU := unit_pos_real
  have : 0 ≤ ((lowerPN6 c0 c1 c2 c3).1.eval u - (lowerPN6 c0 c1 c2 c3).2.eval u) / unit :=
    div_nonneg (by linarith) hU.le
  linarith

/-! ### Degree ten -/

theorem trigPositive10_sound {den l h : Nat} {c0 c1 c2 c3 : FI}
    (hp : trigPositive10 den l h c0 c1 c2 c3 = true) {x0 x1 x2 x3 u : ℝ}
    (h0 : c0.Mem x0) (h1 : c1.Mem x1) (h2 : c2.Mem x2) (h3 : c3.Mem x3)
    (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    0 < x0 + x1 * u + x2 * Real.sin u + x3 * Real.cos u := by
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  simp only [trigPositive10, lowerPN_eq] at hp
  have hpos := positiveOnN_sound hp hu
  have hle := trigLower_le h0 h1 h2 h3 hu0
  have hU := unit_pos_real
  have : 0 < ((splitPos (trigLower c0 c1 c2 c3)).eval u -
      (splitNeg (trigLower c0 c1 c2 c3)).eval u) / unit := div_pos (by linarith) hU
  linarith

theorem trigNonneg10_sound {den l h : Nat} {c0 c1 c2 c3 : FI}
    (hp : trigNonneg10 den l h c0 c1 c2 c3 = true) {x0 x1 x2 x3 u : ℝ}
    (h0 : c0.Mem x0) (h1 : c1.Mem x1) (h2 : c2.Mem x2) (h3 : c3.Mem x3)
    (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    0 ≤ x0 + x1 * u + x2 * Real.sin u + x3 * Real.cos u := by
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  simp only [trigNonneg10, lowerPN_eq] at hp
  have hnn := nonnegOnN_sound hp hu
  have hle := trigLower_le h0 h1 h2 h3 hu0
  have hU := unit_pos_real
  have : 0 ≤ ((splitPos (trigLower c0 c1 c2 c3)).eval u -
      (splitNeg (trigLower c0 c1 c2 c3)).eval u) / unit := div_nonneg (by linarith) hU.le
  linarith

/-! ### Degree three -/

theorem cubicPos_eq (den l : Nat) (c0 c1 c2 c3 : FI) :
    cubicPos den l c0 c1 c2 c3 =
      (c0.lo + c3.lo).toNat * den ^ 3 + (c1.lo + c2.lo).toNat * l * den ^ 2 := by
  simp only [cubicPos, ipos_eq, iadd_eq, nat_add_eq, nat_mul_eq]
  ring

theorem cubicNeg_eq (den h : Nat) (c0 c1 c2 c3 : FI) :
    cubicNeg den h c0 c1 c2 c3 =
      (-(c0.lo + c3.lo)).toNat * den ^ 3 + (-(c1.lo + c2.lo)).toNat * h * den ^ 2 +
        (c3.lo.toNat + 1) / 2 * h ^ 2 * den + (c2.lo.toNat + 5) / 6 * h ^ 3 := by
  simp only [cubicNeg, ipos_eq, ineg'_eq, iadd_eq, nat_add_eq, nat_mul_eq, nat_div_eq]
  ring

/-- The degree-three polynomial is below the expression on `[0, 1]`. -/
theorem cubic_le {c0 c1 c2 c3 : FI} {x0 x1 x2 x3 u : ℝ} {n2 n3 : Nat}
    (h0 : c0.Mem x0) (h1 : c1.Mem x1) (h2 : c2.Mem x2) (h3 : c3.Mem x3)
    (hn2 : c3.lo ≤ 2 * (n2 : Int)) (hn3 : c2.lo ≤ 6 * (n3 : Int)) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (((c0.lo + c3.lo : Int) : ℝ) + ((c1.lo + c2.lo : Int) : ℝ) * u - n2 * u ^ 2 - n3 * u ^ 3) /
        unit ≤ x0 + x1 * u + x2 * Real.sin u + x3 * Real.cos u := by
  have hU := unit_pos_real
  have hsin0 : 0 ≤ Real.sin u :=
    Real.sin_nonneg_of_nonneg_of_le_pi hu0 (hu1.trans (by linarith [Real.pi_gt_three]))
  have hcos0 : 0 ≤ Real.cos u :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have hu2 : 0 ≤ u ^ 2 := pow_nonneg hu0 2
  have hu3 : 0 ≤ u ^ 3 := pow_nonneg hu0 3
  have e0 : (c0.lo : ℝ) ≤ x0 * unit := (div_le_iff₀ hU).mp h0.1
  have e1 : (c1.lo : ℝ) * u ≤ x1 * unit * u :=
    mul_le_mul_of_nonneg_right ((div_le_iff₀ hU).mp h1.1) hu0
  have e2 : (c2.lo : ℝ) * u - n3 * u ^ 3 ≤ x2 * unit * Real.sin u := by
    have hx : (c2.lo : ℝ) * Real.sin u ≤ x2 * unit * Real.sin u :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ hU).mp h2.1) hsin0
    have hn : (c2.lo : ℝ) ≤ 6 * n3 := by exact_mod_cast hn3
    rcases le_total 0 (c2.lo : ℝ) with hc | hc
    · have A := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hu0) hc
      have B := mul_le_mul_of_nonneg_right hn hu3
      linarith
    · have A := mul_le_mul_of_nonpos_left (Real.sin_le hu0) hc
      have : (0 : ℝ) ≤ n3 * u ^ 3 := by positivity
      linarith
  have e3 : (c3.lo : ℝ) - n2 * u ^ 2 ≤ x3 * unit * Real.cos u := by
    have hx : (c3.lo : ℝ) * Real.cos u ≤ x3 * unit * Real.cos u :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ hU).mp h3.1) hcos0
    have hn : (c3.lo : ℝ) ≤ 2 * n2 := by exact_mod_cast hn2
    rcases le_total 0 (c3.lo : ℝ) with hc | hc
    · have A := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := u)) hc
      have B := mul_le_mul_of_nonneg_right hn hu2
      linarith
    · have A := mul_le_mul_of_nonpos_left (Real.cos_le_one u) hc
      have : (0 : ℝ) ≤ n2 * u ^ 2 := by positivity
      linarith
  rw [div_le_iff₀ hU]
  push_cast
  linarith

/-- Scaled by `den ³`, the comparison of the two parts bounds the polynomial below on
`[l / den, h / den]`. -/
theorem cubic_gap {den l h p0 p1 q0 q1 n2 n3 : Nat} (hden : 0 < den) {u : ℝ}
    (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    (((p0 * den ^ 3 + p1 * l * den ^ 2 : Nat) : ℝ) -
        ((q0 * den ^ 3 + q1 * h * den ^ 2 + n2 * h ^ 2 * den + n3 * h ^ 3 : Nat) : ℝ)) / den ^ 3 ≤
      (p0 : ℝ) - q0 + ((p1 : ℝ) - q1) * u - n2 * u ^ 2 - n3 * u ^ 3 := by
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  have hd3 : (0 : ℝ) < (den : ℝ) ^ 3 := by positivity
  have hv : (l : ℝ) ≤ u * den := (div_le_iff₀ hdR).mp hu.1
  have hv' : u * den ≤ (h : ℝ) := (le_div_iff₀ hdR).mp hu.2
  have hv0 : 0 ≤ u * den := le_trans (Nat.cast_nonneg l) hv
  have e1 : (p1 : ℝ) * l * den ^ 2 ≤ p1 * (u * den) * den ^ 2 := by gcongr
  have e2 : (q1 : ℝ) * (u * den) * den ^ 2 ≤ q1 * h * den ^ 2 := by gcongr
  have e3 : (n2 : ℝ) * (u * den) ^ 2 * den ≤ n2 * h ^ 2 * den := by gcongr
  have e4 : (n3 : ℝ) * (u * den) ^ 3 ≤ n3 * h ^ 3 := by gcongr
  rw [div_le_iff₀ hd3]
  push_cast
  linarith

/-- A degree-three comparison bounds the expression below by the scaled difference of the parts. -/
theorem mono3_lower {den l h : Nat} {c0 c1 c2 c3 : FI} (hden : 0 < den) (hhd : h ≤ den)
    {x0 x1 x2 x3 u : ℝ} (h0 : c0.Mem x0) (h1 : c1.Mem x1) (h2 : c2.Mem x2) (h3 : c3.Mem x3)
    (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    (((cubicPos den l c0 c1 c2 c3 : Nat) : ℝ) - (cubicNeg den h c0 c1 c2 c3 : Nat)) / den ^ 3 /
        unit ≤ x0 + x1 * u + x2 * Real.sin u + x3 * Real.cos u := by
  have hU := unit_pos_real
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  have hu1 : u ≤ 1 := hu.2.trans (by rw [div_le_one hdR]; exact_mod_cast hhd)
  have hn2 : c3.lo ≤ 2 * (((c3.lo.toNat + 1) / 2 : Nat) : Int) := by omega
  have hn3 : c2.lo ≤ 6 * (((c2.lo.toNat + 5) / 6 : Nat) : Int) := by omega
  have ha0 : ((c0.lo + c3.lo : Int) : ℝ) =
      ((c0.lo + c3.lo).toNat : ℝ) - ((-(c0.lo + c3.lo)).toNat : ℝ) := by
    exact_mod_cast (Int.toNat_sub_toNat_neg (c0.lo + c3.lo)).symm
  have ha1 : ((c1.lo + c2.lo : Int) : ℝ) =
      ((c1.lo + c2.lo).toNat : ℝ) - ((-(c1.lo + c2.lo)).toNat : ℝ) := by
    exact_mod_cast (Int.toNat_sub_toNat_neg (c1.lo + c2.lo)).symm
  refine le_trans ?_ (cubic_le h0 h1 h2 h3 hn2 hn3 hu0 hu1)
  apply div_le_div_of_nonneg_right _ hU.le
  rw [cubicPos_eq, cubicNeg_eq, ha0, ha1]
  exact cubic_gap hden hu

/-! ### Both degrees -/

/-- A successful test proves the strict inequality on the whole interval. -/
theorem trigPositive_sound {den l h : Nat} {c0 c1 c2 c3 : FI}
    (hp : trigPositive den l h c0 c1 c2 c3 = true) {x0 x1 x2 x3 u : ℝ}
    (h0 : c0.Mem x0) (h1 : c1.Mem x1) (h2 : c2.Mem x2) (h3 : c3.Mem x3)
    (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    0 < x0 + x1 * u + x2 * Real.sin u + x3 * Real.cos u := by
  simp only [trigPositive, Bool.or_eq_true] at hp
  rcases hp with (hp | hp) | hp
  · simp only [mono3, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Bool.cond_true] at hp
    have hl := mono3_lower hp.1.1 hp.1.2 h0 h1 h2 h3 hu
    have hc : (0 : ℝ) <
        ((cubicPos den l c0 c1 c2 c3 : Nat) : ℝ) - (cubicNeg den h c0 c1 c2 c3 : Nat) :=
      sub_pos.mpr (by exact_mod_cast hp.2)
    have : (0 : ℝ) <
        ((cubicPos den l c0 c1 c2 c3 : Nat) - (cubicNeg den h c0 c1 c2 c3 : Nat) : ℝ) / den ^ 3 /
          unit := by
      have : (0 : ℝ) < den := by exact_mod_cast hp.1.1
      have := unit_pos_real
      positivity
    linarith
  · exact trigPositive6_sound hp h0 h1 h2 h3 hu
  · exact trigPositive10_sound hp h0 h1 h2 h3 hu

/-- A successful weak test proves the weak inequality on the whole interval. -/
theorem trigNonneg_sound {den l h : Nat} {c0 c1 c2 c3 : FI}
    (hp : trigNonneg den l h c0 c1 c2 c3 = true) {x0 x1 x2 x3 u : ℝ}
    (h0 : c0.Mem x0) (h1 : c1.Mem x1) (h2 : c2.Mem x2) (h3 : c3.Mem x3)
    (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    0 ≤ x0 + x1 * u + x2 * Real.sin u + x3 * Real.cos u := by
  simp only [trigNonneg, Bool.or_eq_true] at hp
  rcases hp with (hp | hp) | hp
  · simp only [mono3, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Bool.cond_false] at hp
    have hl := mono3_lower hp.1.1 hp.1.2 h0 h1 h2 h3 hu
    have hc : (0 : ℝ) ≤
        ((cubicPos den l c0 c1 c2 c3 : Nat) : ℝ) - (cubicNeg den h c0 c1 c2 c3 : Nat) :=
      sub_nonneg.mpr (by exact_mod_cast hp.2)
    have : (0 : ℝ) ≤
        ((cubicPos den l c0 c1 c2 c3 : Nat) - (cubicNeg den h c0 c1 c2 c3 : Nat) : ℝ) / den ^ 3 /
          unit := by
      have := unit_pos_real
      positivity
    linarith
  · exact trigNonneg6_sound hp h0 h1 h2 h3 hu
  · exact trigNonneg10_sound hp h0 h1 h2 h3 hu

end SquaresInCircles.Eight.Arithmetic.Fixed
