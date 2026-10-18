module

public import SquaresInCircles.Eight.Arithmetic.Bernstein11

/-!
# Degree-six Bernstein tests on seven natural numbers

The degree-six analogue of `Bernstein11`. It is about half as costly in the kernel, and enough
for most inequalities of the tables; the degree-ten test is the fallback.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic.Fixed

/-- Seven coefficients, lowest degree first. -/
structure N7 where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
  c6 : Nat
  deriving DecidableEq, Repr

namespace N7

/-- `Σ c_j x^j`. -/
noncomputable def eval (q : N7) (x : ℝ) : ℝ :=
  (q.c0 : ℝ) * x ^ 0 + (q.c1 : ℝ) * x ^ 1 + (q.c2 : ℝ) * x ^ 2 + (q.c3 : ℝ) * x ^ 3 +
    (q.c4 : ℝ) * x ^ 4 + (q.c5 : ℝ) * x ^ 5 + (q.c6 : ℝ) * x ^ 6

/-- The coefficients of `den ^ 6 q((l + d t) / den)`, a polynomial in `t`: the Taylor shift by
`l` by synthetic division (Horner), then the scaling by `d`. The operations of `Nat` are called
directly, which the kernel evaluates without unfolding the arithmetic type classes. -/
def shift (den l d : Nat) (p : N7) : N7 :=
  let e2 := Nat.mul den den
  let e3 := Nat.mul e2 den
  let e4 := Nat.mul e3 den
  let e5 := Nat.mul e4 den
  let e6 := Nat.mul e5 den
  let b0 := Nat.mul p.c0 e6
  let b1 := Nat.mul p.c1 e5
  let b2 := Nat.mul p.c2 e4
  let b3 := Nat.mul p.c3 e3
  let b4 := Nat.mul p.c4 e2
  let b5 := Nat.mul p.c5 den
  let b6 := p.c6
  let h0_5 := Nat.add b5 (Nat.mul l b6)
  let h0_4 := Nat.add b4 (Nat.mul l h0_5)
  let h0_3 := Nat.add b3 (Nat.mul l h0_4)
  let h0_2 := Nat.add b2 (Nat.mul l h0_3)
  let h0_1 := Nat.add b1 (Nat.mul l h0_2)
  let h0_0 := Nat.add b0 (Nat.mul l h0_1)
  let h1_5 := Nat.add h0_5 (Nat.mul l b6)
  let h1_4 := Nat.add h0_4 (Nat.mul l h1_5)
  let h1_3 := Nat.add h0_3 (Nat.mul l h1_4)
  let h1_2 := Nat.add h0_2 (Nat.mul l h1_3)
  let h1_1 := Nat.add h0_1 (Nat.mul l h1_2)
  let h2_5 := Nat.add h1_5 (Nat.mul l b6)
  let h2_4 := Nat.add h1_4 (Nat.mul l h2_5)
  let h2_3 := Nat.add h1_3 (Nat.mul l h2_4)
  let h2_2 := Nat.add h1_2 (Nat.mul l h2_3)
  let h3_5 := Nat.add h2_5 (Nat.mul l b6)
  let h3_4 := Nat.add h2_4 (Nat.mul l h3_5)
  let h3_3 := Nat.add h2_3 (Nat.mul l h3_4)
  let h4_5 := Nat.add h3_5 (Nat.mul l b6)
  let h4_4 := Nat.add h3_4 (Nat.mul l h4_5)
  let h5_5 := Nat.add h4_5 (Nat.mul l b6)
  let d2 := Nat.mul d d
  let d3 := Nat.mul d2 d
  let d4 := Nat.mul d3 d
  let d5 := Nat.mul d4 d
  let d6 := Nat.mul d5 d
  ⟨h0_0,
   Nat.mul d h1_1,
   Nat.mul d2 h2_2,
   Nat.mul d3 h3_3,
   Nat.mul d4 h4_4,
   Nat.mul d5 h5_5,
   Nat.mul d6 b6⟩

/-- The Bernstein numerators `6! b_k = Σ_{j ≤ k} C(k, j) j! (6 - j)! c_j`, by Pascal's rule. -/
def bern (q : N7) : N7 :=
  let a0 := Nat.mul 720 q.c0
  let a1 := Nat.mul 120 q.c1
  let a2 := Nat.mul 48 q.c2
  let a3 := Nat.mul 36 q.c3
  let a4 := Nat.mul 48 q.c4
  let a5 := Nat.mul 120 q.c5
  let a6 := Nat.mul 720 q.c6
  let s1_6 := Nat.add a6 a5
  let s1_5 := Nat.add a5 a4
  let s1_4 := Nat.add a4 a3
  let s1_3 := Nat.add a3 a2
  let s1_2 := Nat.add a2 a1
  let s1_1 := Nat.add a1 a0
  let s2_6 := Nat.add s1_6 s1_5
  let s2_5 := Nat.add s1_5 s1_4
  let s2_4 := Nat.add s1_4 s1_3
  let s2_3 := Nat.add s1_3 s1_2
  let s2_2 := Nat.add s1_2 s1_1
  let s3_6 := Nat.add s2_6 s2_5
  let s3_5 := Nat.add s2_5 s2_4
  let s3_4 := Nat.add s2_4 s2_3
  let s3_3 := Nat.add s2_3 s2_2
  let s4_6 := Nat.add s3_6 s3_5
  let s4_5 := Nat.add s3_5 s3_4
  let s4_4 := Nat.add s3_4 s3_3
  let s5_6 := Nat.add s4_6 s4_5
  let s5_5 := Nat.add s4_5 s4_4
  let s6_6 := Nat.add s5_6 s5_5
  ⟨a0, s1_1, s2_2, s3_3, s4_4, s5_5, s6_6⟩

/-- Componentwise strict comparison `N < P`. -/
def lt (N P : N7) : Bool :=
  Nat.blt N.c0 P.c0 &&
    Nat.blt N.c1 P.c1 &&
    Nat.blt N.c2 P.c2 &&
    Nat.blt N.c3 P.c3 &&
    Nat.blt N.c4 P.c4 &&
    Nat.blt N.c5 P.c5 &&
    Nat.blt N.c6 P.c6

/-- Componentwise comparison `N ≤ P`. -/
def le (N P : N7) : Bool :=
  Nat.ble N.c0 P.c0 &&
    Nat.ble N.c1 P.c1 &&
    Nat.ble N.c2 P.c2 &&
    Nat.ble N.c3 P.c3 &&
    Nat.ble N.c4 P.c4 &&
    Nat.ble N.c5 P.c5 &&
    Nat.ble N.c6 P.c6

/-- `den ^ 6 q (x / den) = Σ q_j x ^ j den ^ (6 - j)`, by Horner's rule. -/
def evalAt (den x : Nat) (q : N7) : Nat :=
  let e2 := Nat.mul den den
  let e3 := Nat.mul e2 den
  let e4 := Nat.mul e3 den
  let e5 := Nat.mul e4 den
  let e6 := Nat.mul e5 den
  let v1 := Nat.add (Nat.mul q.c6 x) (Nat.mul q.c5 den)
  let v2 := Nat.add (Nat.mul v1 x) (Nat.mul q.c4 e2)
  let v3 := Nat.add (Nat.mul v2 x) (Nat.mul q.c3 e3)
  let v4 := Nat.add (Nat.mul v3 x) (Nat.mul q.c2 e4)
  let v5 := Nat.add (Nat.mul v4 x) (Nat.mul q.c1 e5)
  Nat.add (Nat.mul v5 x) (Nat.mul q.c0 e6)

end N7

/-- `P - N > 0` on `[l / den, h / den]`: either `N(h) < P(l)`, enough since both have
nonnegative coefficients and so increase, or the Bernstein test. -/
def positiveOnN7 (den l h : Nat) (P N : N7) : Bool :=
  Nat.blt 0 den && Nat.ble l h &&
    (Nat.blt (N.evalAt den h) (P.evalAt den l) ||
      N7.lt (N.shift den l (Nat.sub h l)).bern (P.shift den l (Nat.sub h l)).bern)

/-- `P - N ≥ 0` on `[l / den, h / den]`, in the same two ways. -/
def nonnegOnN7 (den l h : Nat) (P N : N7) : Bool :=
  Nat.blt 0 den && Nat.ble l h &&
    (Nat.ble (N.evalAt den h) (P.evalAt den l) ||
      N7.le (N.shift den l (Nat.sub h l)).bern (P.shift den l (Nat.sub h l)).bern)

/-- The Bernstein basis values of degree six are nonnegative on `[0, 1]` and sum to one. -/
theorem bernstein6_basis {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    (0 ≤ (1 - t) ^ 6 ∧ 0 ≤ 6 * t * (1 - t) ^ 5 ∧ 0 ≤ 15 * t ^ 2 * (1 - t) ^ 4 ∧
      0 ≤ 20 * t ^ 3 * (1 - t) ^ 3 ∧ 0 ≤ 15 * t ^ 4 * (1 - t) ^ 2 ∧ 0 ≤ 6 * t ^ 5 * (1 - t) ∧
      0 ≤ t ^ 6) ∧
    (1 - t) ^ 6 + 6 * t * (1 - t) ^ 5 + 15 * t ^ 2 * (1 - t) ^ 4 + 20 * t ^ 3 * (1 - t) ^ 3 +
      15 * t ^ 4 * (1 - t) ^ 2 + 6 * t ^ 5 * (1 - t) + t ^ 6 = 1 := by
  have h0 : 0 ≤ t := ht.1
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  refine ⟨⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity,
    by positivity⟩, ?_⟩
  ring_nf

namespace N7

theorem shift_eval (den l d : Nat) (hden : 0 < den) (p : N7) (t : ℝ) :
    (p.shift den l d).eval t = (den : ℝ) ^ 6 * p.eval (((l : ℝ) + d * t) / den) := by
  have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  have h : (p.shift den l d).eval t =
      (p.c0 : ℝ) * den ^ 6 + p.c1 * den ^ 5 * (l + d * t) ^ 1 + p.c2 * den ^ 4 * (l + d * t) ^ 2 +
        p.c3 * den ^ 3 * (l + d * t) ^ 3 + p.c4 * den ^ 2 * (l + d * t) ^ 4 +
        p.c5 * den ^ 1 * (l + d * t) ^ 5 + p.c6 * (l + d * t) ^ 6 := by
    delta shift
    dsimp only
    simp only [eval, nat_add_eq, nat_mul_eq]
    push_cast
    ring
  rw [h]
  simp only [eval]
  field_simp

theorem bern_identity (q : N7) (t : ℝ) :
    720 * q.eval t =
      (q.bern.c0 : ℝ) * ((1 - t) ^ 6) +
      (q.bern.c1 : ℝ) * (6 * t * (1 - t) ^ 5) +
      (q.bern.c2 : ℝ) * (15 * t ^ 2 * (1 - t) ^ 4) +
      (q.bern.c3 : ℝ) * (20 * t ^ 3 * (1 - t) ^ 3) +
      (q.bern.c4 : ℝ) * (15 * t ^ 4 * (1 - t) ^ 2) +
      (q.bern.c5 : ℝ) * (6 * t ^ 5 * (1 - t)) +
      (q.bern.c6 : ℝ) * (t ^ 6) := by
  delta bern
  dsimp only
  simp only [eval, nat_add_eq, nat_mul_eq]
  push_cast
  ring

theorem lt_sound {N P : N7} (h : lt N P = true) :
    (1 : ℝ) ≤ (P.c0 : ℝ) - N.c0 ∧
    (1 : ℝ) ≤ (P.c1 : ℝ) - N.c1 ∧
    (1 : ℝ) ≤ (P.c2 : ℝ) - N.c2 ∧
    (1 : ℝ) ≤ (P.c3 : ℝ) - N.c3 ∧
    (1 : ℝ) ≤ (P.c4 : ℝ) - N.c4 ∧
    (1 : ℝ) ≤ (P.c5 : ℝ) - N.c5 ∧
    (1 : ℝ) ≤ (P.c6 : ℝ) - N.c6 := by
  simp only [lt, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have key (a b : Nat) (hab : a < b) : (1 : ℝ) ≤ (b : ℝ) - a := by
    have : ((a + 1 : Nat) : ℝ) ≤ b := by exact_mod_cast hab
    push_cast at this; linarith
  exact ⟨key _ _ h0, key _ _ h1, key _ _ h2, key _ _ h3, key _ _ h4, key _ _ h5, key _ _ h6⟩

theorem le_sound {N P : N7} (h : le N P = true) :
    (0 : ℝ) ≤ (P.c0 : ℝ) - N.c0 ∧
    (0 : ℝ) ≤ (P.c1 : ℝ) - N.c1 ∧
    (0 : ℝ) ≤ (P.c2 : ℝ) - N.c2 ∧
    (0 : ℝ) ≤ (P.c3 : ℝ) - N.c3 ∧
    (0 : ℝ) ≤ (P.c4 : ℝ) - N.c4 ∧
    (0 : ℝ) ≤ (P.c5 : ℝ) - N.c5 ∧
    (0 : ℝ) ≤ (P.c6 : ℝ) - N.c6 := by
  simp only [le, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have key (a b : Nat) (hab : a ≤ b) : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  exact ⟨key _ _ h0, key _ _ h1, key _ _ h2, key _ _ h3, key _ _ h4, key _ _ h5, key _ _ h6⟩

end N7

theorem bern7_gap_pos (PS NS : N7) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1)
    (hlt : N7.lt NS.bern PS.bern = true) : NS.eval t < PS.eval t := by
  obtain ⟨⟨b0, b1, b2, b3, b4, b5, b6⟩, hsum⟩ := bernstein6_basis ht
  have hP := N7.bern_identity PS t
  have hN := N7.bern_identity NS t
  obtain ⟨r0, r1, r2, r3, r4, r5, r6⟩ := N7.lt_sound hlt
  linarith [mul_le_mul_of_nonneg_right r0 b0, mul_le_mul_of_nonneg_right r1 b1,
    mul_le_mul_of_nonneg_right r2 b2, mul_le_mul_of_nonneg_right r3 b3,
    mul_le_mul_of_nonneg_right r4 b4, mul_le_mul_of_nonneg_right r5 b5,
    mul_le_mul_of_nonneg_right r6 b6]

theorem bern7_gap_nonneg (PS NS : N7) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1)
    (hle : N7.le NS.bern PS.bern = true) : NS.eval t ≤ PS.eval t := by
  obtain ⟨⟨b0, b1, b2, b3, b4, b5, b6⟩, -⟩ := bernstein6_basis ht
  have hP := N7.bern_identity PS t
  have hN := N7.bern_identity NS t
  obtain ⟨r0, r1, r2, r3, r4, r5, r6⟩ := N7.le_sound hle
  linarith [mul_nonneg r0 b0, mul_nonneg r1 b1, mul_nonneg r2 b2, mul_nonneg r3 b3,
    mul_nonneg r4 b4, mul_nonneg r5 b5, mul_nonneg r6 b6]

namespace N7

/-- A polynomial with natural coefficients increases on `[0, ∞)`. -/
theorem eval_mono (q : N7) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : q.eval s ≤ q.eval t := by
  simp only [eval]
  gcongr

theorem evalAt_eq (den x : Nat) (hden : 0 < den) (q : N7) :
    (q.evalAt den x : ℝ) = (den : ℝ) ^ 6 * q.eval ((x : ℝ) / den) := by
  have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  simp only [evalAt, eval, nat_add_eq, nat_mul_eq]
  push_cast
  field_simp
  ring

/-- `N(h) < P(l)` gives `N < P` on `[l / den, h / den]`. -/
theorem mono_gap {den l h : Nat} (hden : 0 < den) {P N : N7}
    {u : ℝ} (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) :
    N.eval u ≤ (N.evalAt den h : ℝ) / (den : ℝ) ^ 6 ∧
      (P.evalAt den l : ℝ) / (den : ℝ) ^ 6 ≤ P.eval u := by
  have hd : (0 : ℝ) < (den : ℝ) ^ 6 := by positivity
  have hl : (0 : ℝ) ≤ (l : ℝ) / den := by positivity
  rw [evalAt_eq den h hden, evalAt_eq den l hden, mul_div_cancel_left₀ _ hd.ne',
    mul_div_cancel_left₀ _ hd.ne']
  exact ⟨N.eval_mono (hl.trans hu.1) hu.2, P.eval_mono hl hu.1⟩

end N7

/-- A successful strict test proves `N < P` on the whole interval. -/
theorem positiveOnN7_sound {den l h : Nat} {P N : N7} (hp : positiveOnN7 den l h P N = true)
    {u : ℝ} (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) : N.eval u < P.eval u := by
  simp only [positiveOnN7, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at hp
  obtain ⟨⟨hden, hlh⟩, hmono | hlt⟩ := hp
  · obtain ⟨h1, h2⟩ := N7.mono_gap (P := P) (N := N) hden hu
    have hd : (0 : ℝ) < (den : ℝ) ^ 6 := by positivity
    have : (N.evalAt den h : ℝ) < P.evalAt den l := by exact_mod_cast hmono
    have := div_lt_div_of_pos_right this hd
    linarith
  obtain ⟨t, ht, htu⟩ := shift_point_nat hden hlh hu
  have hgap := bern7_gap_pos _ _ ht hlt
  rw [nat_sub_eq, N7.shift_eval den l (h - l) hden P t, N7.shift_eval den l (h - l) hden N t,
    htu] at hgap
  have hd : (0 : ℝ) < (den : ℝ) ^ 6 := by positivity
  exact lt_of_mul_lt_mul_left hgap hd.le

/-- A successful weak test proves `N ≤ P` on the whole interval. -/
theorem nonnegOnN7_sound {den l h : Nat} {P N : N7} (hp : nonnegOnN7 den l h P N = true)
    {u : ℝ} (hu : (l : ℝ) / den ≤ u ∧ u ≤ (h : ℝ) / den) : N.eval u ≤ P.eval u := by
  simp only [nonnegOnN7, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at hp
  obtain ⟨⟨hden, hlh⟩, hmono | hle⟩ := hp
  · obtain ⟨h1, h2⟩ := N7.mono_gap (P := P) (N := N) hden hu
    have hd : (0 : ℝ) < (den : ℝ) ^ 6 := by positivity
    have : (N.evalAt den h : ℝ) ≤ P.evalAt den l := by exact_mod_cast hmono
    have := div_le_div_of_nonneg_right this hd.le
    linarith
  obtain ⟨t, ht, htu⟩ := shift_point_nat hden hlh hu
  have hgap := bern7_gap_nonneg _ _ ht hle
  rw [nat_sub_eq, N7.shift_eval den l (h - l) hden P t, N7.shift_eval den l (h - l) hden N t,
    htu] at hgap
  have hd : (0 : ℝ) < (den : ℝ) ^ 6 := by positivity
  exact le_of_mul_le_mul_left hgap hd

end SquaresInCircles.Eight.Arithmetic.Fixed
