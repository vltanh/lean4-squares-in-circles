module

public import SquaresInCircles.Eight.Arithmetic.Fixed

/-!
# Degree-ten Bernstein tests on eleven natural numbers

A polynomial with integer coefficients is split as `P - N` with `P` and `N`
nonnegative. Moving it to `[0, 1]` and expanding it in the Bernstein basis are
linear maps with nonnegative coefficients, so they act on `P` and `N`
separately, in natural numbers, which the kernel evaluates fastest.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic.Fixed

/-- Eleven coefficients, lowest degree first. -/
structure N11 where

  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
  c6 : Nat
  c7 : Nat
  c8 : Nat
  c9 : Nat
  c10 : Nat
  deriving DecidableEq, Repr

namespace N11

/-- `Σ c_j x^j`. -/
noncomputable def eval (q : N11) (x : ℝ) : ℝ :=
  (q.c0 : ℝ) * x ^ 0 + (q.c1 : ℝ) * x ^ 1 + (q.c2 : ℝ) * x ^ 2 + (q.c3 : ℝ) * x ^ 3 +
    (q.c4 : ℝ) * x ^ 4 + (q.c5 : ℝ) * x ^ 5 + (q.c6 : ℝ) * x ^ 6 + (q.c7 : ℝ) * x ^ 7 +
    (q.c8 : ℝ) * x ^ 8 + (q.c9 : ℝ) * x ^ 9 + (q.c10 : ℝ) * x ^ 10

/-- The coefficients of `den ^ 10 q((l + d t) / den)`, a polynomial in `t`: the Taylor shift by
`l` by synthetic division (Horner), then the scaling by `d`. -/
def shift (den l d : Nat) (p : N11) : N11 :=
  let e2 := Nat.mul den den
  let e3 := Nat.mul e2 den
  let e4 := Nat.mul e3 den
  let e5 := Nat.mul e4 den
  let e6 := Nat.mul e5 den
  let e7 := Nat.mul e6 den
  let e8 := Nat.mul e7 den
  let e9 := Nat.mul e8 den
  let e10 := Nat.mul e9 den
  let b0 := Nat.mul p.c0 e10
  let b1 := Nat.mul p.c1 e9
  let b2 := Nat.mul p.c2 e8
  let b3 := Nat.mul p.c3 e7
  let b4 := Nat.mul p.c4 e6
  let b5 := Nat.mul p.c5 e5
  let b6 := Nat.mul p.c6 e4
  let b7 := Nat.mul p.c7 e3
  let b8 := Nat.mul p.c8 e2
  let b9 := Nat.mul p.c9 den
  let b10 := p.c10
  let h0_9 := Nat.add b9 (Nat.mul l b10)
  let h0_8 := Nat.add b8 (Nat.mul l h0_9)
  let h0_7 := Nat.add b7 (Nat.mul l h0_8)
  let h0_6 := Nat.add b6 (Nat.mul l h0_7)
  let h0_5 := Nat.add b5 (Nat.mul l h0_6)
  let h0_4 := Nat.add b4 (Nat.mul l h0_5)
  let h0_3 := Nat.add b3 (Nat.mul l h0_4)
  let h0_2 := Nat.add b2 (Nat.mul l h0_3)
  let h0_1 := Nat.add b1 (Nat.mul l h0_2)
  let h0_0 := Nat.add b0 (Nat.mul l h0_1)
  let h1_9 := Nat.add h0_9 (Nat.mul l b10)
  let h1_8 := Nat.add h0_8 (Nat.mul l h1_9)
  let h1_7 := Nat.add h0_7 (Nat.mul l h1_8)
  let h1_6 := Nat.add h0_6 (Nat.mul l h1_7)
  let h1_5 := Nat.add h0_5 (Nat.mul l h1_6)
  let h1_4 := Nat.add h0_4 (Nat.mul l h1_5)
  let h1_3 := Nat.add h0_3 (Nat.mul l h1_4)
  let h1_2 := Nat.add h0_2 (Nat.mul l h1_3)
  let h1_1 := Nat.add h0_1 (Nat.mul l h1_2)
  let h2_9 := Nat.add h1_9 (Nat.mul l b10)
  let h2_8 := Nat.add h1_8 (Nat.mul l h2_9)
  let h2_7 := Nat.add h1_7 (Nat.mul l h2_8)
  let h2_6 := Nat.add h1_6 (Nat.mul l h2_7)
  let h2_5 := Nat.add h1_5 (Nat.mul l h2_6)
  let h2_4 := Nat.add h1_4 (Nat.mul l h2_5)
  let h2_3 := Nat.add h1_3 (Nat.mul l h2_4)
  let h2_2 := Nat.add h1_2 (Nat.mul l h2_3)
  let h3_9 := Nat.add h2_9 (Nat.mul l b10)
  let h3_8 := Nat.add h2_8 (Nat.mul l h3_9)
  let h3_7 := Nat.add h2_7 (Nat.mul l h3_8)
  let h3_6 := Nat.add h2_6 (Nat.mul l h3_7)
  let h3_5 := Nat.add h2_5 (Nat.mul l h3_6)
  let h3_4 := Nat.add h2_4 (Nat.mul l h3_5)
  let h3_3 := Nat.add h2_3 (Nat.mul l h3_4)
  let h4_9 := Nat.add h3_9 (Nat.mul l b10)
  let h4_8 := Nat.add h3_8 (Nat.mul l h4_9)
  let h4_7 := Nat.add h3_7 (Nat.mul l h4_8)
  let h4_6 := Nat.add h3_6 (Nat.mul l h4_7)
  let h4_5 := Nat.add h3_5 (Nat.mul l h4_6)
  let h4_4 := Nat.add h3_4 (Nat.mul l h4_5)
  let h5_9 := Nat.add h4_9 (Nat.mul l b10)
  let h5_8 := Nat.add h4_8 (Nat.mul l h5_9)
  let h5_7 := Nat.add h4_7 (Nat.mul l h5_8)
  let h5_6 := Nat.add h4_6 (Nat.mul l h5_7)
  let h5_5 := Nat.add h4_5 (Nat.mul l h5_6)
  let h6_9 := Nat.add h5_9 (Nat.mul l b10)
  let h6_8 := Nat.add h5_8 (Nat.mul l h6_9)
  let h6_7 := Nat.add h5_7 (Nat.mul l h6_8)
  let h6_6 := Nat.add h5_6 (Nat.mul l h6_7)
  let h7_9 := Nat.add h6_9 (Nat.mul l b10)
  let h7_8 := Nat.add h6_8 (Nat.mul l h7_9)
  let h7_7 := Nat.add h6_7 (Nat.mul l h7_8)
  let h8_9 := Nat.add h7_9 (Nat.mul l b10)
  let h8_8 := Nat.add h7_8 (Nat.mul l h8_9)
  let h9_9 := Nat.add h8_9 (Nat.mul l b10)
  let d2 := Nat.mul d d
  let d3 := Nat.mul d2 d
  let d4 := Nat.mul d3 d
  let d5 := Nat.mul d4 d
  let d6 := Nat.mul d5 d
  let d7 := Nat.mul d6 d
  let d8 := Nat.mul d7 d
  let d9 := Nat.mul d8 d
  let d10 := Nat.mul d9 d
  ⟨h0_0,
   Nat.mul d h1_1,
   Nat.mul d2 h2_2,
   Nat.mul d3 h3_3,
   Nat.mul d4 h4_4,
   Nat.mul d5 h5_5,
   Nat.mul d6 h6_6,
   Nat.mul d7 h7_7,
   Nat.mul d8 h8_8,
   Nat.mul d9 h9_9,
   Nat.mul d10 b10⟩

/-- The Bernstein numerators `10! b_k = Σ_{j ≤ k} C(k, j) j! (10 - j)! c_j`, by Pascal's rule. -/
def bern (q : N11) : N11 :=
  let a0 := Nat.mul 3628800 q.c0
  let a1 := Nat.mul 362880 q.c1
  let a2 := Nat.mul 80640 q.c2
  let a3 := Nat.mul 30240 q.c3
  let a4 := Nat.mul 17280 q.c4
  let a5 := Nat.mul 14400 q.c5
  let a6 := Nat.mul 17280 q.c6
  let a7 := Nat.mul 30240 q.c7
  let a8 := Nat.mul 80640 q.c8
  let a9 := Nat.mul 362880 q.c9
  let a10 := Nat.mul 3628800 q.c10
  let s1_10 := Nat.add a10 a9
  let s1_9 := Nat.add a9 a8
  let s1_8 := Nat.add a8 a7
  let s1_7 := Nat.add a7 a6
  let s1_6 := Nat.add a6 a5
  let s1_5 := Nat.add a5 a4
  let s1_4 := Nat.add a4 a3
  let s1_3 := Nat.add a3 a2
  let s1_2 := Nat.add a2 a1
  let s1_1 := Nat.add a1 a0
  let s2_10 := Nat.add s1_10 s1_9
  let s2_9 := Nat.add s1_9 s1_8
  let s2_8 := Nat.add s1_8 s1_7
  let s2_7 := Nat.add s1_7 s1_6
  let s2_6 := Nat.add s1_6 s1_5
  let s2_5 := Nat.add s1_5 s1_4
  let s2_4 := Nat.add s1_4 s1_3
  let s2_3 := Nat.add s1_3 s1_2
  let s2_2 := Nat.add s1_2 s1_1
  let s3_10 := Nat.add s2_10 s2_9
  let s3_9 := Nat.add s2_9 s2_8
  let s3_8 := Nat.add s2_8 s2_7
  let s3_7 := Nat.add s2_7 s2_6
  let s3_6 := Nat.add s2_6 s2_5
  let s3_5 := Nat.add s2_5 s2_4
  let s3_4 := Nat.add s2_4 s2_3
  let s3_3 := Nat.add s2_3 s2_2
  let s4_10 := Nat.add s3_10 s3_9
  let s4_9 := Nat.add s3_9 s3_8
  let s4_8 := Nat.add s3_8 s3_7
  let s4_7 := Nat.add s3_7 s3_6
  let s4_6 := Nat.add s3_6 s3_5
  let s4_5 := Nat.add s3_5 s3_4
  let s4_4 := Nat.add s3_4 s3_3
  let s5_10 := Nat.add s4_10 s4_9
  let s5_9 := Nat.add s4_9 s4_8
  let s5_8 := Nat.add s4_8 s4_7
  let s5_7 := Nat.add s4_7 s4_6
  let s5_6 := Nat.add s4_6 s4_5
  let s5_5 := Nat.add s4_5 s4_4
  let s6_10 := Nat.add s5_10 s5_9
  let s6_9 := Nat.add s5_9 s5_8
  let s6_8 := Nat.add s5_8 s5_7
  let s6_7 := Nat.add s5_7 s5_6
  let s6_6 := Nat.add s5_6 s5_5
  let s7_10 := Nat.add s6_10 s6_9
  let s7_9 := Nat.add s6_9 s6_8
  let s7_8 := Nat.add s6_8 s6_7
  let s7_7 := Nat.add s6_7 s6_6
  let s8_10 := Nat.add s7_10 s7_9
  let s8_9 := Nat.add s7_9 s7_8
  let s8_8 := Nat.add s7_8 s7_7
  let s9_10 := Nat.add s8_10 s8_9
  let s9_9 := Nat.add s8_9 s8_8
  let s10_10 := Nat.add s9_10 s9_9
  ⟨a0, s1_1, s2_2, s3_3, s4_4, s5_5, s6_6, s7_7, s8_8, s9_9, s10_10⟩

/-- Componentwise strict comparison `N < P`. -/
def lt (N P : N11) : Bool :=
  Nat.blt N.c0 P.c0 &&
    Nat.blt N.c1 P.c1 &&
    Nat.blt N.c2 P.c2 &&
    Nat.blt N.c3 P.c3 &&
    Nat.blt N.c4 P.c4 &&
    Nat.blt N.c5 P.c5 &&
    Nat.blt N.c6 P.c6 &&
    Nat.blt N.c7 P.c7 &&
    Nat.blt N.c8 P.c8 &&
    Nat.blt N.c9 P.c9 &&
    Nat.blt N.c10 P.c10

/-- Componentwise comparison `N ≤ P`. -/
def le (N P : N11) : Bool :=
  Nat.ble N.c0 P.c0 &&
    Nat.ble N.c1 P.c1 &&
    Nat.ble N.c2 P.c2 &&
    Nat.ble N.c3 P.c3 &&
    Nat.ble N.c4 P.c4 &&
    Nat.ble N.c5 P.c5 &&
    Nat.ble N.c6 P.c6 &&
    Nat.ble N.c7 P.c7 &&
    Nat.ble N.c8 P.c8 &&
    Nat.ble N.c9 P.c9 &&
    Nat.ble N.c10 P.c10

/-- `den ^ 10 q (x / den) = Σ q_j x ^ j den ^ (10 - j)`, by Horner's rule. -/
def evalAt (den x : Nat) (q : N11) : Nat :=
  let e2 := Nat.mul den den
  let e3 := Nat.mul e2 den
  let e4 := Nat.mul e3 den
  let e5 := Nat.mul e4 den
  let e6 := Nat.mul e5 den
  let e7 := Nat.mul e6 den
  let e8 := Nat.mul e7 den
  let e9 := Nat.mul e8 den
  let e10 := Nat.mul e9 den
  let v1 := Nat.add (Nat.mul q.c10 x) (Nat.mul q.c9 den)
  let v2 := Nat.add (Nat.mul v1 x) (Nat.mul q.c8 e2)
  let v3 := Nat.add (Nat.mul v2 x) (Nat.mul q.c7 e3)
  let v4 := Nat.add (Nat.mul v3 x) (Nat.mul q.c6 e4)
  let v5 := Nat.add (Nat.mul v4 x) (Nat.mul q.c5 e5)
  let v6 := Nat.add (Nat.mul v5 x) (Nat.mul q.c4 e6)
  let v7 := Nat.add (Nat.mul v6 x) (Nat.mul q.c3 e7)
  let v8 := Nat.add (Nat.mul v7 x) (Nat.mul q.c2 e8)
  let v9 := Nat.add (Nat.mul v8 x) (Nat.mul q.c1 e9)
  Nat.add (Nat.mul v9 x) (Nat.mul q.c0 e10)

end N11

/-- `P - N > 0` on `[l / den, h / den]`: either `N(h) < P(l)`, enough since both have
nonnegative coefficients and so increase, or the Bernstein test. -/
def positiveOnN (den l h : Nat) (P N : N11) : Bool :=
  Nat.blt 0 den && Nat.ble l h &&
    (Nat.blt (N.evalAt den h) (P.evalAt den l) ||
      N11.lt (N.shift den l (Nat.sub h l)).bern (P.shift den l (Nat.sub h l)).bern)

/-- `P - N ≥ 0` on `[l / den, h / den]`, in the same two ways. -/
def nonnegOnN (den l h : Nat) (P N : N11) : Bool :=
  Nat.blt 0 den && Nat.ble l h &&
    (Nat.ble (N.evalAt den h) (P.evalAt den l) ||
      N11.le (N.shift den l (Nat.sub h l)).bern (P.shift den l (Nat.sub h l)).bern)

end SquaresInCircles.Eight.Arithmetic.Fixed

namespace SquaresInCircles.Eight.Arithmetic.Fixed

/-- The Bernstein basis values of degree ten are nonnegative on `[0, 1]` and sum to one. -/
theorem bernstein10_basis {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    (0 ≤ (1 - t) ^ 10 ∧ 0 ≤ 10 * t * (1 - t) ^ 9 ∧ 0 ≤ 45 * t ^ 2 * (1 - t) ^ 8 ∧
      0 ≤ 120 * t ^ 3 * (1 - t) ^ 7 ∧ 0 ≤ 210 * t ^ 4 * (1 - t) ^ 6 ∧
      0 ≤ 252 * t ^ 5 * (1 - t) ^ 5 ∧ 0 ≤ 210 * t ^ 6 * (1 - t) ^ 4 ∧
      0 ≤ 120 * t ^ 7 * (1 - t) ^ 3 ∧ 0 ≤ 45 * t ^ 8 * (1 - t) ^ 2 ∧
      0 ≤ 10 * t ^ 9 * (1 - t) ∧ 0 ≤ t ^ 10) ∧
    (1 - t) ^ 10 + 10 * t * (1 - t) ^ 9 + 45 * t ^ 2 * (1 - t) ^ 8 + 120 * t ^ 3 * (1 - t) ^ 7 +
      210 * t ^ 4 * (1 - t) ^ 6 + 252 * t ^ 5 * (1 - t) ^ 5 + 210 * t ^ 6 * (1 - t) ^ 4 +
      120 * t ^ 7 * (1 - t) ^ 3 + 45 * t ^ 8 * (1 - t) ^ 2 + 10 * t ^ 9 * (1 - t) + t ^ 10 = 1 := by
  have h0 : 0 ≤ t := ht.1
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  refine ⟨⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity, by positivity, by positivity⟩, ?_⟩
  have := add_pow t (1 - t) 10
  simp only [add_sub_cancel, one_pow, Finset.sum_range_succ, Finset.sum_range_zero] at this
  norm_num [Nat.choose] at this
  linarith

/-- The point of `[0, 1]` that `x ↦ (l + (h - l) x) / den` sends to `u`. -/
theorem shift_point {den l h : Int} (hden : 0 < den) (hlh : l ≤ h) {u : ℝ}
    (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧ ((l : ℝ) + ((h - l : Int) : ℝ) * t) / den = u := by
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  rcases eq_or_lt_of_le hlh with he | hlt
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    subst he
    push_cast
    simp only [sub_self, zero_mul, add_zero]
    exact le_antisymm hu.1 hu.2 |>.symm ▸ rfl
  · have hl : (l : ℝ) < h := by exact_mod_cast hlt
    refine ⟨(u * den - l) / (h - l), ⟨?_, ?_⟩, ?_⟩
    · apply div_nonneg _ (by linarith)
      have := (div_le_iff₀ hd).mp hu.1
      linarith
    · apply (div_le_one (by linarith)).mpr
      have := (le_div_iff₀ hd).mp hu.2
      linarith
    · have hne : (h : ℝ) - l ≠ 0 := by linarith
      push_cast
      field_simp
      ring

end SquaresInCircles.Eight.Arithmetic.Fixed

namespace SquaresInCircles.Eight.Arithmetic.Fixed
namespace N11

theorem shift_eval (den l d : Nat) (hden : 0 < den) (p : N11) (t : ℝ) :
    (p.shift den l d).eval t = (den : ℝ) ^ 10 * p.eval (((l : ℝ) + d * t) / den) := by
  have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  have h : (p.shift den l d).eval t =
      (p.c0 : ℝ) * den ^ 10 + p.c1 * den ^ 9 * (l + d * t) ^ 1 + p.c2 * den ^ 8 * (l +
        d * t) ^ 2 + p.c3 * den ^ 7 * (l + d * t) ^ 3 + p.c4 * den ^ 6 * (l + d * t) ^ 4 +
        p.c5 * den ^ 5 * (l + d * t) ^ 5 + p.c6 * den ^ 4 * (l + d * t) ^ 6 +
        p.c7 * den ^ 3 * (l + d * t) ^ 7 + p.c8 * den ^ 2 * (l + d * t) ^ 8 +
        p.c9 * den ^ 1 * (l + d * t) ^ 9 + p.c10 * (l + d * t) ^ 10 := by
    delta shift
    dsimp only
    simp only [eval, nat_add_eq, nat_mul_eq]
    push_cast
    ring
  rw [h]
  simp only [eval]
  field_simp

theorem bern_identity (q : N11) (t : ℝ) :
    3628800 * q.eval t =
      (q.bern.c0 : ℝ) * ((1 - t) ^ 10) +
      (q.bern.c1 : ℝ) * (10 * t * (1 - t) ^ 9) +
      (q.bern.c2 : ℝ) * (45 * t ^ 2 * (1 - t) ^ 8) +
      (q.bern.c3 : ℝ) * (120 * t ^ 3 * (1 - t) ^ 7) +
      (q.bern.c4 : ℝ) * (210 * t ^ 4 * (1 - t) ^ 6) +
      (q.bern.c5 : ℝ) * (252 * t ^ 5 * (1 - t) ^ 5) +
      (q.bern.c6 : ℝ) * (210 * t ^ 6 * (1 - t) ^ 4) +
      (q.bern.c7 : ℝ) * (120 * t ^ 7 * (1 - t) ^ 3) +
      (q.bern.c8 : ℝ) * (45 * t ^ 8 * (1 - t) ^ 2) +
      (q.bern.c9 : ℝ) * (10 * t ^ 9 * (1 - t)) +
      (q.bern.c10 : ℝ) * (t ^ 10) := by
  simp only [bern, eval, nat_add_eq, nat_mul_eq]
  push_cast
  ring

theorem lt_sound {N P : N11} (h : lt N P = true) :
    (1 : ℝ) ≤ (P.c0 : ℝ) - N.c0 ∧
    (1 : ℝ) ≤ (P.c1 : ℝ) - N.c1 ∧
    (1 : ℝ) ≤ (P.c2 : ℝ) - N.c2 ∧
    (1 : ℝ) ≤ (P.c3 : ℝ) - N.c3 ∧
    (1 : ℝ) ≤ (P.c4 : ℝ) - N.c4 ∧
    (1 : ℝ) ≤ (P.c5 : ℝ) - N.c5 ∧
    (1 : ℝ) ≤ (P.c6 : ℝ) - N.c6 ∧
    (1 : ℝ) ≤ (P.c7 : ℝ) - N.c7 ∧
    (1 : ℝ) ≤ (P.c8 : ℝ) - N.c8 ∧
    (1 : ℝ) ≤ (P.c9 : ℝ) - N.c9 ∧
    (1 : ℝ) ≤ (P.c10 : ℝ) - N.c10 := by
  simp only [lt, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have key (a b : Nat) (hab : a < b) : (1 : ℝ) ≤ (b : ℝ) - a := by
    have : ((a + 1 : Nat) : ℝ) ≤ b := by exact_mod_cast hab
    push_cast at this; linarith
  exact ⟨key _ _ h0, key _ _ h1, key _ _ h2, key _ _ h3, key _ _ h4, key _ _ h5, key _ _ h6,
    key _ _ h7, key _ _ h8, key _ _ h9, key _ _ h10⟩

theorem le_sound {N P : N11} (h : le N P = true) :
    (0 : ℝ) ≤ (P.c0 : ℝ) - N.c0 ∧
    (0 : ℝ) ≤ (P.c1 : ℝ) - N.c1 ∧
    (0 : ℝ) ≤ (P.c2 : ℝ) - N.c2 ∧
    (0 : ℝ) ≤ (P.c3 : ℝ) - N.c3 ∧
    (0 : ℝ) ≤ (P.c4 : ℝ) - N.c4 ∧
    (0 : ℝ) ≤ (P.c5 : ℝ) - N.c5 ∧
    (0 : ℝ) ≤ (P.c6 : ℝ) - N.c6 ∧
    (0 : ℝ) ≤ (P.c7 : ℝ) - N.c7 ∧
    (0 : ℝ) ≤ (P.c8 : ℝ) - N.c8 ∧
    (0 : ℝ) ≤ (P.c9 : ℝ) - N.c9 ∧
    (0 : ℝ) ≤ (P.c10 : ℝ) - N.c10 := by
  simp only [le, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have key (a b : Nat) (hab : a ≤ b) : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  exact ⟨key _ _ h0, key _ _ h1, key _ _ h2, key _ _ h3, key _ _ h4, key _ _ h5, key _ _ h6,
    key _ _ h7, key _ _ h8, key _ _ h9, key _ _ h10⟩

end N11
end SquaresInCircles.Eight.Arithmetic.Fixed

namespace SquaresInCircles.Eight.Arithmetic.Fixed

theorem shift_point_nat {den l h : Nat} (hden : 0 < den) (hlh : l ≤ h) {u : ℝ}
    (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧ ((l : ℝ) + ((h - l : Nat) : ℝ) * t) / den = u := by
  have hu' : (((l : Int) : ℝ) / ((den : Int) : ℝ) ≤ u ∧ u ≤ ((h : Int) : ℝ) / ((den : Int) : ℝ)) := by
    push_cast; exact hu
  obtain ⟨t, ht, htu⟩ := shift_point (den := den) (l := l) (h := h) (by exact_mod_cast hden)
    (by exact_mod_cast hlh) hu'
  refine ⟨t, ht, ?_⟩
  rw [← htu]
  push_cast [Nat.cast_sub hlh]
  ring

/-- The gap between the two sides of a Bernstein comparison, at one point of `[0, 1]`. -/
theorem bern_gap_pos (PS NS : N11) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) (hlt : N11.lt NS.bern PS.bern = true) :
    NS.eval t < PS.eval t := by
  obtain ⟨⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩, hsum⟩ := bernstein10_basis ht
  have hP := N11.bern_identity PS t
  have hN := N11.bern_identity NS t
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := N11.lt_sound hlt
  linarith [mul_le_mul_of_nonneg_right r0 b0, mul_le_mul_of_nonneg_right r1 b1,
    mul_le_mul_of_nonneg_right r2 b2, mul_le_mul_of_nonneg_right r3 b3,
    mul_le_mul_of_nonneg_right r4 b4, mul_le_mul_of_nonneg_right r5 b5,
    mul_le_mul_of_nonneg_right r6 b6, mul_le_mul_of_nonneg_right r7 b7,
    mul_le_mul_of_nonneg_right r8 b8, mul_le_mul_of_nonneg_right r9 b9,
    mul_le_mul_of_nonneg_right r10 b10]

theorem bern_gap_nonneg (PS NS : N11) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) (hle : N11.le NS.bern PS.bern = true) :
    NS.eval t ≤ PS.eval t := by
  obtain ⟨⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩, -⟩ := bernstein10_basis ht
  have hP := N11.bern_identity PS t
  have hN := N11.bern_identity NS t
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := N11.le_sound hle
  linarith [mul_nonneg r0 b0, mul_nonneg r1 b1, mul_nonneg r2 b2, mul_nonneg r3 b3,
    mul_nonneg r4 b4, mul_nonneg r5 b5, mul_nonneg r6 b6, mul_nonneg r7 b7,
    mul_nonneg r8 b8, mul_nonneg r9 b9, mul_nonneg r10 b10]

namespace N11

/-- A polynomial with natural coefficients increases on `[0, ∞)`. -/
theorem eval_mono (q : N11) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : q.eval s ≤ q.eval t := by
  simp only [eval]
  gcongr

theorem evalAt_eq (den x : Nat) (hden : 0 < den) (q : N11) :
    (q.evalAt den x : ℝ) = (den : ℝ) ^ 10 * q.eval ((x : ℝ) / den) := by
  have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  simp only [evalAt, eval, nat_add_eq, nat_mul_eq]
  push_cast
  field_simp
  ring

/-- `N(h) < P(l)` gives `N < P` on `[l / den, h / den]`. -/
theorem mono_gap {den l h : Nat} (hden : 0 < den) {P N : N11}
    {u : ℝ} (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    N.eval u ≤ (N.evalAt den h : ℝ) / (den : ℝ) ^ 10 ∧
      (P.evalAt den l : ℝ) / (den : ℝ) ^ 10 ≤ P.eval u := by
  have hd : (0 : ℝ) < (den : ℝ) ^ 10 := by positivity
  have hl : (0 : ℝ) ≤ (l : ℝ) / den := by positivity
  rw [evalAt_eq den h hden, evalAt_eq den l hden, mul_div_cancel_left₀ _ hd.ne',
    mul_div_cancel_left₀ _ hd.ne']
  exact ⟨N.eval_mono (hl.trans hu.1) hu.2, P.eval_mono hl hu.1⟩

end N11

/-- A successful strict test proves `N < P` on the whole interval. -/
theorem positiveOnN_sound {den l h : Nat} {P N : N11} (hp : positiveOnN den l h P N = true)
    {u : ℝ} (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) : N.eval u < P.eval u := by
  simp only [positiveOnN, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at hp
  obtain ⟨⟨hden, hlh⟩, hmono | hlt⟩ := hp
  · obtain ⟨h1, h2⟩ := N11.mono_gap (P := P) (N := N) hden hu
    have hd : (0 : ℝ) < (den : ℝ) ^ 10 := by positivity
    have : (N.evalAt den h : ℝ) < P.evalAt den l := by exact_mod_cast hmono
    have := div_lt_div_of_pos_right this hd
    linarith
  obtain ⟨t, ht, htu⟩ := shift_point_nat hden hlh hu
  have hgap := bern_gap_pos _ _ ht hlt
  rw [nat_sub_eq, N11.shift_eval den l (h - l) hden P t, N11.shift_eval den l (h - l) hden N t,
    htu] at hgap
  have hd : (0 : ℝ) < (den : ℝ) ^ 10 := by positivity
  exact lt_of_mul_lt_mul_left hgap hd.le

/-- A successful weak test proves `N ≤ P` on the whole interval. -/
theorem nonnegOnN_sound {den l h : Nat} {P N : N11} (hp : nonnegOnN den l h P N = true)
    {u : ℝ} (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) : N.eval u ≤ P.eval u := by
  simp only [nonnegOnN, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at hp
  obtain ⟨⟨hden, hlh⟩, hmono | hle⟩ := hp
  · obtain ⟨h1, h2⟩ := N11.mono_gap (P := P) (N := N) hden hu
    have hd : (0 : ℝ) < (den : ℝ) ^ 10 := by positivity
    have : (N.evalAt den h : ℝ) ≤ P.evalAt den l := by exact_mod_cast hmono
    have := div_le_div_of_nonneg_right this hd.le
    linarith
  obtain ⟨t, ht, htu⟩ := shift_point_nat hden hlh hu
  have hgap := bern_gap_nonneg _ _ ht hle
  rw [nat_sub_eq, N11.shift_eval den l (h - l) hden P t, N11.shift_eval den l (h - l) hden N t,
    htu] at hgap
  have hd : (0 : ℝ) < (den : ℝ) ^ 10 := by positivity
  exact le_of_mul_le_mul_left hgap hd

end SquaresInCircles.Eight.Arithmetic.Fixed
