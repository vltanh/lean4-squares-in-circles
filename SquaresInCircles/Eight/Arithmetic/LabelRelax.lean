module

public import SquaresInCircles.Eight.Arithmetic.RowCheck

/-!
# Affine bounds of quadratic labels on an arc

A label of the pair tables is `c + p a + q b + r b² + s a b`, where the constant `c` is known
only to lie in a rational interval `[c⁻, c⁺]` (it contains `π` or a square root). An arc of a
table carries an affine label `ℓ`: below the label for a source arc, above it for a target arc.

On a circle chart `a² + b² = κ₀ + κ₁ (a + b)`, and each of `a`, `b`, `a + b`, `a - b` lies
between bounds `x⁻ ≤ x ≤ x⁺` on the arc, so `(x - x⁻)(x⁺ - x) ≥ 0`. With multipliers `μ ≥ 0`
fixed by the signs of `r` and `s`, the difference of the label and `ℓ`, minus these products
and a multiple of the circle identity, is an affine function `e₀ + e₁ a + e₂ b`; the check is
that its minimum over the box `[a⁻, a⁺] × [b⁻, b⁺]` is nonnegative. On the core side
`a = 7/12`, and `b²` is bounded above by its secant or below by its midpoint tangent.

The bounds `x⁻` and `x⁺` are `sourceLower` of `±x` on the arc box of the table.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic
open Fixed

/-- A label `c + p a + q b + r b² + s a b` whose constant `c` lies in `[cLo, cHi]`. -/
structure QuadLabel where
  cLo : ℚ
  cHi : ℚ
  p : ℚ
  q : ℚ
  r : ℚ
  s : ℚ

instance : Inhabited QuadLabel := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

namespace QuadLabel

/-- The label with the constant `c`. -/
def eval (L : QuadLabel) (c a b : ℝ) : ℝ := c + L.p * a + L.q * b + L.r * b ^ 2 + L.s * a * b

/-- The opposite label. -/
def neg (L : QuadLabel) : QuadLabel := ⟨-L.cHi, -L.cLo, -L.p, -L.q, -L.r, -L.s⟩

theorem eval_neg (L : QuadLabel) (c a b : ℝ) : L.neg.eval (-c) a b = -L.eval c a b := by
  simp only [eval, neg, Rat.cast_neg]
  ring

/-- The label with the sign `σ`: itself or its opposite. -/
def signed (L : QuadLabel) (σ : Bool) : QuadLabel := if σ then L else L.neg

theorem signed_eval (L : QuadLabel) (σ : Bool) (c a b : ℝ) :
    (L.signed σ).eval (sgnR σ * c) a b = sgnR σ * L.eval c a b := by
  cases σ
  · simp only [signed, sgnR, Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    exact L.eval_neg c a b
  · simp [signed, sgnR]

theorem signed_bounds {L : QuadLabel} {c : ℝ} (h : (L.cLo : ℝ) ≤ c ∧ c ≤ L.cHi) (σ : Bool) :
    ((L.signed σ).cLo : ℝ) ≤ sgnR σ * c ∧ sgnR σ * c ≤ (L.signed σ).cHi := by
  cases σ
  · simp only [signed, sgnR, neg, Bool.false_eq_true, ↓reduceIte, Rat.cast_neg]
    constructor <;> linarith [h.1, h.2]
  · simpa [signed, sgnR] using h

end QuadLabel

/-- The affine label of the arc is below (`lower`) or above the quadratic label at every point of
the arc, for every admissible constant. -/
def ArcData.Bounds (arc : ArcData) (Q : ℝ) (L : QuadLabel) (lower : Bool) : Prop :=
  if lower then
    ∀ c : ℝ, (L.cLo : ℝ) ≤ c → ∀ a b : ℝ, arc.Contains Q a b → arc.label.eval a b ≤ L.eval c a b
  else
    ∀ c : ℝ, c ≤ (L.cHi : ℝ) → ∀ a b : ℝ, arc.Contains Q a b → L.eval c a b ≤ arc.label.eval a b

/-! ### Bounds of the coordinates on an arc -/

/-- The lower bound of `x a + y b` on the arc of a box, for integers `x` and `y`. -/
def boxLower (B : ArcBox) (x y : Int) : ℚ :=
  (sourceLower B (FI.point (x * unit)) (FI.point (y * unit)) : ℚ) / unit

theorem mem_point_int (x : Int) : (FI.point (x * unit)).Mem (x : ℝ) := by
  have h := FI.mem_point_div (x * unit)
  have hU : (unit : ℝ) ≠ 0 := ne_of_gt unit_pos_real
  rwa [Int.cast_mul, mul_div_assoc, div_self hU, mul_one] at h

theorem boxLower_le {B : ArcBox} {P : PreparedArc} (hB : B.Encloses P) (x y : Int) {a b : ℝ}
    (hab : P.data.Contains P.radius a b) : (boxLower B x y : ℝ) ≤ x * a + y * b := by
  have h := sourceLower_sound hB (mem_point_int x) (mem_point_int y) hab
  simpa [boxLower] using h

/-- Bounds of `a`, `b`, `a + b` and `a - b` on an arc. -/
structure Ranges where
  aL : ℚ
  aH : ℚ
  bL : ℚ
  bH : ℚ
  sL : ℚ
  sH : ℚ
  dL : ℚ
  dH : ℚ

def Ranges.ofBox (B : ArcBox) : Ranges :=
  ⟨boxLower B 1 0, -boxLower B (-1) 0, boxLower B 0 1, -boxLower B 0 (-1),
    boxLower B 1 1, -boxLower B (-1) (-1), boxLower B 1 (-1), -boxLower B (-1) 1⟩

/-- The point `(a, b)` lies in the ranges. -/
structure Ranges.Holds (R : Ranges) (a b : ℝ) : Prop where
  aL : (R.aL : ℝ) ≤ a
  aH : a ≤ R.aH
  bL : (R.bL : ℝ) ≤ b
  bH : b ≤ R.bH
  sL : (R.sL : ℝ) ≤ a + b
  sH : a + b ≤ R.sH
  dL : (R.dL : ℝ) ≤ a - b
  dH : a - b ≤ R.dH

theorem Ranges.ofBox_holds {B : ArcBox} {P : PreparedArc} (hB : B.Encloses P) {a b : ℝ}
    (hab : P.data.Contains P.radius a b) : (Ranges.ofBox B).Holds a b := by
  have h1 := boxLower_le hB 1 0 hab
  have h2 := boxLower_le hB (-1) 0 hab
  have h3 := boxLower_le hB 0 1 hab
  have h4 := boxLower_le hB 0 (-1) hab
  have h5 := boxLower_le hB 1 1 hab
  have h6 := boxLower_le hB (-1) (-1) hab
  have h7 := boxLower_le hB 1 (-1) hab
  have h8 := boxLower_le hB (-1) 1 hab
  push_cast at h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Ranges.ofBox, Rat.cast_neg] <;> linarith

/-! ### The affine remainder -/

/-- The coefficients `(e₀, e₁)` of the remainder `e₀ + e₁ b` on the core side `a = 7/12`, for
the difference `d₀ + d₁ a + d₂ b + r b² + s a b`: `b²` is replaced by its secant on `[b⁻, b⁺]`
when `r ≤ 0` and by its tangent at the midpoint `m` when `r > 0`. -/
def sideRemainder (R : Ranges) (d0 d1 d2 r s : ℚ) : ℚ × ℚ :=
  if r ≤ 0 then (d0 + 7 / 12 * d1 - r * (R.bL * R.bH), d2 + 7 / 12 * s + r * (R.bL + R.bH))
  else (d0 + 7 / 12 * d1 - r * ((R.bL + R.bH) / 2) ^ 2, d2 + 7 / 12 * s + r * (R.bL + R.bH))

/-- The multipliers of `(a - a⁻)(a⁺ - a)`, `(b - b⁻)(b⁺ - b)`, `(a - b - d⁻)(d⁺ - a + b)` and
`(a + b - s⁻)(s⁺ - a - b)`: they cancel `r b² + s a b` together with the circle identity. -/
def muA (r : ℚ) : ℚ := max r 0
def muB (r : ℚ) : ℚ := max (-r) 0
def muD (s : ℚ) : ℚ := max s 0 / 2
def muS (s : ℚ) : ℚ := max (-s) 0 / 2

/-- The coefficients `(e₀, e₁, e₂)` of the remainder on a circle chart
`a² + b² = κ₀ + κ₁ (a + b)`, after subtracting `μ_a (a - a⁻)(a⁺ - a)`, `μ_b (b - b⁻)(b⁺ - b)`,
`μ_s (a + b - s⁻)(s⁺ - a - b)`, `μ_d (a - b - d⁻)(d⁺ - a + b)` and `ν (a² + b² - κ₀ - κ₁ (a + b))`
from `d₀ + d₁ a + d₂ b + r b² + s a b`, with `ν = μ_a + μ_d + μ_s`. -/
def circleRemainder (R : Ranges) (κ0 κ1 d0 d1 d2 r s : ℚ) : ℚ × ℚ × ℚ :=
  (d0 + muA r * (R.aL * R.aH) + muB r * (R.bL * R.bH) + muS s * (R.sL * R.sH) +
      muD s * (R.dL * R.dH) + (muA r + muD s + muS s) * κ0,
    d1 - muA r * (R.aL + R.aH) - muS s * (R.sL + R.sH) - muD s * (R.dL + R.dH) +
      (muA r + muD s + muS s) * κ1,
    d2 - muB r * (R.bL + R.bH) - muS s * (R.sL + R.sH) + muD s * (R.dL + R.dH) +
      (muA r + muD s + muS s) * κ1)

theorem min_mul_le {e l h x : ℝ} (hl : l ≤ x) (hh : x ≤ h) : min (e * l) (e * h) ≤ e * x := by
  rcases le_total 0 e with he | he
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hl he)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hh he)

theorem sideRemainder_le {R : Ranges} {d0 d1 d2 r s : ℚ} {b : ℝ} (hb : (R.bL : ℝ) ≤ b ∧ b ≤ R.bH) :
    ((sideRemainder R d0 d1 d2 r s).1 : ℝ) + (sideRemainder R d0 d1 d2 r s).2 * b ≤
      d0 + d1 * (7 / 12) + d2 * b + r * b ^ 2 + s * (7 / 12) * b := by
  unfold sideRemainder
  split_ifs with hr
  · have hr' : (r : ℝ) ≤ 0 := by exact_mod_cast hr
    have hp : 0 ≤ (b - R.bL) * (R.bH - b) := mul_nonneg (by linarith) (by linarith)
    push_cast
    nlinarith
  · have hr' : (0 : ℝ) ≤ r := by exact_mod_cast (le_of_lt (lt_of_not_ge hr))
    push_cast
    nlinarith [mul_nonneg hr' (sq_nonneg (b - (R.bL + R.bH) / 2))]

theorem circleRemainder_le {R : Ranges} {κ0 κ1 d0 d1 d2 r s : ℚ} {a b : ℝ} (hR : R.Holds a b)
    (hc : a ^ 2 + b ^ 2 = κ0 + κ1 * (a + b)) :
    ((circleRemainder R κ0 κ1 d0 d1 d2 r s).1 : ℝ) +
        (circleRemainder R κ0 κ1 d0 d1 d2 r s).2.1 * a +
        (circleRemainder R κ0 κ1 d0 d1 d2 r s).2.2 * b ≤
      d0 + d1 * a + d2 * b + r * b ^ 2 + s * a * b := by
  have hr : (r : ℝ) = muA r - muB r := by
    rcases le_total 0 r with h | h
    · simp [muA, muB, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    · simp [muA, muB, max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
  have hs : (s : ℝ) = 2 * muD s - 2 * muS s := by
    rcases le_total 0 s with h | h
    · rw [muD, muS, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      push_cast
      ring
    · rw [muD, muS, max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      push_cast
      ring
  have ha : (0 : ℝ) ≤ muA r := by exact_mod_cast le_max_right r 0
  have hb : (0 : ℝ) ≤ muB r := by exact_mod_cast le_max_right (-r) 0
  have hd : (0 : ℝ) ≤ muD s := by
    have : (0 : ℚ) ≤ muD s := div_nonneg (le_max_right s 0) (by norm_num)
    exact_mod_cast this
  have hs' : (0 : ℝ) ≤ muS s := by
    have : (0 : ℚ) ≤ muS s := div_nonneg (le_max_right (-s) 0) (by norm_num)
    exact_mod_cast this
  have pa : 0 ≤ (a - R.aL) * (R.aH - a) := mul_nonneg (by linarith [hR.aL]) (by linarith [hR.aH])
  have pb : 0 ≤ (b - R.bL) * (R.bH - b) := mul_nonneg (by linarith [hR.bL]) (by linarith [hR.bH])
  have ps : 0 ≤ (a + b - R.sL) * (R.sH - (a + b)) :=
    mul_nonneg (by linarith [hR.sL]) (by linarith [hR.sH])
  have pd : 0 ≤ (a - b - R.dL) * (R.dH - (a - b)) :=
    mul_nonneg (by linarith [hR.dL]) (by linarith [hR.dH])
  have key : (d0 : ℝ) + d1 * a + d2 * b + r * b ^ 2 + s * a * b -
      (((circleRemainder R κ0 κ1 d0 d1 d2 r s).1 : ℝ) +
        (circleRemainder R κ0 κ1 d0 d1 d2 r s).2.1 * a +
        (circleRemainder R κ0 κ1 d0 d1 d2 r s).2.2 * b) =
      muA r * ((a - R.aL) * (R.aH - a)) + muB r * ((b - R.bL) * (R.bH - b)) +
        muS s * ((a + b - R.sL) * (R.sH - (a + b))) +
        muD s * ((a - b - R.dL) * (R.dH - (a - b))) +
        (muA r + muD s + muS s) * (a ^ 2 + b ^ 2 - (κ0 + κ1 * (a + b))) := by
    simp only [circleRemainder]
    rw [hr, hs]
    push_cast
    ring
  have hzero : a ^ 2 + b ^ 2 - ((κ0 : ℝ) + κ1 * (a + b)) = 0 := by linarith
  rw [hzero, mul_zero, add_zero] at key
  have := add_nonneg (add_nonneg (add_nonneg (mul_nonneg ha pa) (mul_nonneg hb pb))
    (mul_nonneg hs' ps)) (mul_nonneg hd pd)
  linarith

/-! ### The check of one arc -/

/-- The remainder `e₀ + e₁ b` is nonnegative on `[b⁻, b⁺]`. -/
def sideOK (R : Ranges) (e : ℚ × ℚ) : Bool := decide (0 ≤ e.1 + min (e.2 * R.bL) (e.2 * R.bH))

/-- The remainder `e₀ + e₁ a + e₂ b` is nonnegative on `[a⁻, a⁺] × [b⁻, b⁺]`. -/
def circleOK (R : Ranges) (e : ℚ × ℚ × ℚ) : Bool :=
  decide (0 ≤ e.1 + min (e.2.1 * R.aL) (e.2.1 * R.aH) + min (e.2.2 * R.bL) (e.2.2 * R.bH))

theorem sideOK_sound {R : Ranges} {e : ℚ × ℚ} (h : sideOK R e = true) {b : ℝ}
    (hb : (R.bL : ℝ) ≤ b ∧ b ≤ R.bH) : 0 ≤ (e.1 : ℝ) + e.2 * b := by
  simp only [sideOK, decide_eq_true_eq] at h
  have h' : (0 : ℝ) ≤ ((e.1 + min (e.2 * R.bL) (e.2 * R.bH) : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  have := min_mul_le (e := (e.2 : ℝ)) hb.1 hb.2
  linarith

theorem circleOK_sound {R : Ranges} {e : ℚ × ℚ × ℚ} (h : circleOK R e = true) {a b : ℝ}
    (hR : R.Holds a b) : 0 ≤ (e.1 : ℝ) + e.2.1 * a + e.2.2 * b := by
  simp only [circleOK, decide_eq_true_eq] at h
  have h' : (0 : ℝ) ≤ ((e.1 + min (e.2.1 * R.aL) (e.2.1 * R.aH) +
      min (e.2.2 * R.bL) (e.2.2 * R.bH) : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  have h1 := min_mul_le (e := (e.2.1 : ℝ)) hR.aL hR.aH
  have h2 := min_mul_le (e := (e.2.2 : ℝ)) hR.bL hR.bH
  linarith

/-- `a² + b² = κ₀ + κ₁ (a + b)` on the outer circle and on the core corner. -/
def kappa0 (Q : ℚ) (outer : Bool) : ℚ := if outer then Q - 1 / 2 else -71 / 144
def kappa1 (outer : Bool) : ℚ := if outer then -1 else 1

/-- `ℓ ≤ L` on the arc whose box is `B`: the remainder of `L - ℓ` is nonnegative on the box of
`a` and `b`. The chart is the core side, the outer circle or the core corner. -/
def lowerCheck (Q : ℚ) (B : ArcBox) (side outer : Bool) (L : QuadLabel) (ℓ : AffineLabel) :
    Bool :=
  if side then
    sideOK (Ranges.ofBox B)
      (sideRemainder (Ranges.ofBox B) (L.cLo - ℓ.c) (L.p - ℓ.p) (L.q - ℓ.q) L.r L.s)
  else
    circleOK (Ranges.ofBox B)
      (circleRemainder (Ranges.ofBox B) (kappa0 Q outer) (kappa1 outer) (L.cLo - ℓ.c)
        (L.p - ℓ.p) (L.q - ℓ.q) L.r L.s)

theorem lowerCheck_sound {Q : ℚ} {B : ArcBox} {arc : ArcData}
    (hB : B.Encloses (PreparedArc.ofArc Q arc)) {L : QuadLabel} {ℓ : AffineLabel}
    (h : lowerCheck Q B arc.side arc.outer L ℓ = true) {c a b : ℝ} (hc : (L.cLo : ℝ) ≤ c)
    (hab : arc.Contains Q a b) : ℓ.eval a b ≤ L.eval c a b := by
  have hP : (PreparedArc.ofArc Q arc).data.Contains
      (PreparedArc.ofArc Q arc).radius a b := by
    rw [PreparedArc.ofArc_data, PreparedArc.ofArc_radius]
    exact hab
  have hR := Ranges.ofBox_holds hB hP
  have hon := hab.2.2.2.2
  simp only [AffineLabel.eval, QuadLabel.eval]
  cases hs : arc.side
  · -- a circle chart
    simp only [lowerCheck, hs, Bool.false_eq_true, ↓reduceIte] at h
    have hcirc : a ^ 2 + b ^ 2 = kappa0 Q arc.outer + kappa1 arc.outer * (a + b) := by
      cases ho : arc.outer
      · have hhi : ¬ arc.tangent.hi ≤ 6 / 7 := by simpa [ArcData.side, ho] using hs
        simp only [ArcData.OnCurve, ho, hhi, Bool.false_eq_true, ↓reduceIte] at hon
        simp only [kappa0, kappa1, Bool.false_eq_true, ↓reduceIte]
        push_cast
        nlinarith [hon.2]
      · simp only [ArcData.OnCurve, ho, ↓reduceIte] at hon
        simp only [kappa0, kappa1, ↓reduceIte]
        push_cast
        nlinarith [hon]
    have hrem := circleRemainder_le (d0 := L.cLo - ℓ.c) (d1 := L.p - ℓ.p) (d2 := L.q - ℓ.q)
      (r := L.r) (s := L.s) hR hcirc
    have hok := circleOK_sound h hR
    push_cast at hrem
    linarith
  · -- the core side
    simp only [lowerCheck, hs, ↓reduceIte] at h
    have ho : arc.outer = false := by
      cases ho : arc.outer <;> simp_all [ArcData.side]
    have hhi : arc.tangent.hi ≤ 6 / 7 := by simpa [ArcData.side, ho] using hs
    simp only [ArcData.OnCurve, ho, hhi, Bool.false_eq_true, ↓reduceIte] at hon
    obtain ⟨ha, -⟩ := hon
    subst ha
    have hrem := sideRemainder_le (R := Ranges.ofBox B) (d0 := L.cLo - ℓ.c) (d1 := L.p - ℓ.p)
      (d2 := L.q - ℓ.q) (r := L.r) (s := L.s) ⟨hR.bL, hR.bH⟩
    have hok := sideOK_sound h ⟨hR.bL, hR.bH⟩
    push_cast at hrem
    linarith

/-- The check of one arc against its quadratic label: below it (`lower`) or above it. -/
def labelCheck (Q : ℚ) (B : ArcBox) (arc : ArcData) (L : QuadLabel) (lower : Bool) : Bool :=
  if lower then lowerCheck Q B arc.side arc.outer L arc.label
  else lowerCheck Q B arc.side arc.outer L.neg arc.label.neg

theorem labelCheck_sound {Q : ℚ} {B : ArcBox} {arc : ArcData}
    (hB : B.Encloses (PreparedArc.ofArc Q arc)) {L : QuadLabel} {lower : Bool}
    (h : labelCheck Q B arc L lower = true) : arc.Bounds Q L lower := by
  unfold labelCheck at h
  unfold ArcData.Bounds
  cases lower
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    intro c hc a b hab
    have hc' : ((L.neg.cLo : ℚ) : ℝ) ≤ -c := by simp [QuadLabel.neg]; linarith
    have h1 := lowerCheck_sound hB h hc' hab
    rw [QuadLabel.eval_neg] at h1
    simp only [AffineLabel.eval, AffineLabel.neg, Rat.cast_neg] at h1 ⊢
    linarith
  · simp only [↓reduceIte] at h ⊢
    intro c hc a b hab
    exact lowerCheck_sound hB h hc hab

/-! ### All arcs of a table -/

/-- Each arc of a table bounds its quadratic label, below or above as its entry says. -/
def SpecsHold (M : AffineTableMeta) (C : TableCtx) (specs : List (QuadLabel × Bool)) : Prop :=
  ∀ i < C.n, (nth default M.arcs i).Bounds M.radius (nth default specs i).1
    (nth default specs i).2

/-- The label checks of the arcs of `as`, the first with index `i`, against the entries of `Ls`,
with the boxes `B` of the table (in groups, see `boxAt`). -/
def labelsCheck (Q : ℚ) (B : List (List ArcBox)) :
    Nat → List ArcData → List (QuadLabel × Bool) → Bool
  | i, a :: as, L :: Ls => labelCheck Q (boxAt B i) a L.1 L.2 && labelsCheck Q B (i + 1) as Ls
  | _, [], _ => true
  | _, _ :: _, [] => false

theorem labelsCheck_nth {Q : ℚ} {B : List (List ArcBox)} :
    ∀ {i : Nat} {as : List ArcData} {Ls : List (QuadLabel × Bool)},
      labelsCheck Q B i as Ls = true → ∀ j < as.length,
        labelCheck Q (boxAt B (i + j)) (nth default as j) (nth default Ls j).1
          (nth default Ls j).2 = true
  | _, [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | _, _ :: _, [], h, _, _ => by simp [labelsCheck] at h
  | i, a :: as, L :: Ls, h, j, hj => by
      simp only [labelsCheck, Bool.and_eq_true] at h
      cases j with
      | zero => exact h.1
      | succ j =>
          have := labelsCheck_nth h.2 j (by simpa using hj)
          rwa [Nat.add_assoc, Nat.add_comm 1 j] at this

theorem labelsCheck_sound {M : AffineTableMeta} {C : TableCtx} (hC : C.Valid M)
    {specs : List (QuadLabel × Bool)} (h : labelsCheck M.radius C.boxes 0 M.arcs specs = true) :
    SpecsHold M C specs := by
  intro i hi
  have hl := labelsCheck_nth h i (hC.n_eq ▸ hi)
  rw [Nat.zero_add] at hl
  have hB := hC.boxes i hi
  rw [← nth_eq_getD] at hB
  exact labelCheck_sound hB hl

end SquaresInCircles.Eight.Arithmetic
