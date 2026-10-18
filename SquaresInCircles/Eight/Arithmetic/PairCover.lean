module

public import SquaresInCircles.Eight.Arithmetic.AtanBounds
public import SquaresInCircles.Eight.Arithmetic.LabelRelax

/-!
# Coverage trees of the pair tables

A pair problem fixes a source end and a target end (chart, sign, tangent range and quadratic
label), an original separating axis, a charge `β`, a target `γ` and halves `(k, r, u⁺)`: on the
half the relative frame angle is `φ = k π / 2 ± u` with `0 ≤ u ≤ u⁺`. Its claim
(`PairProblem.Cell`) is the charged inequality
`γ < φ + L_s(a, b) - L_t(A, B) - β h(φ)` for every source state, target state and angle that
satisfy the physical gap `19/25 ≤ φ + α_s - α_t ≤ 3π/4` and the axis margin.

A tree splits the box (source tangent) × (target tangent) × (angle): the tangent intervals and
the angle interval are bisected. At a leaf either
* the gap excludes the whole cell (`gap`): `arctan` bounds at the ends of the tangent intervals
  confine `u` to an interval disjoint from the cell, or it confines `u` to a subinterval on which
  the tree continues (`trim`); or
* the next row of the table covers the cell (`row`): its arcs contain the two tangent intervals
  with the same chart and sign, its angle interval contains the cell's, it has the axis, quarter
  and half of the problem, and its arcs' affine labels bound the quadratic labels of the problem
  (`SpecsHold`). Its claim (`AffineTableRow.Claim`) then gives the inequality on the cell.

`problemsCheck` walks the problems, their halves and their trees in order and consumes the rows
in the same order, so a leaf needs no row index.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic.PairCover

open Arithmetic Fixed

/-! ### Problems -/

/-- One end of a pair: the chart (the outer circle, or the core side or the core corner), the
sign, the tangent range and the label. -/
structure PairEnd where
  outer : Bool
  side : Bool
  positive : Bool
  range : QInterval
  label : QuadLabel
  deriving DecidableEq, Repr

/-- `(a, b)` is on the chart of `E`. -/
def PairEnd.OnCurve (E : PairEnd) (Q a b : ℝ) : Prop :=
  if E.outer then (a + 1 / 2) ^ 2 + (b + 1 / 2) ^ 2 = Q
  else if E.side then a = 7 / 12 ∧ b ≤ 1 / 2
  else 1 / 2 ≤ b ∧ (a - 1 / 2) ^ 2 + (b - 1 / 2) ^ 2 = (1 / 12 : ℝ) ^ 2

/-- `(a, b)` is a point of the chart of `E` whose tangent `b / a` lies in `S`. -/
def PairEnd.Mem (E : PairEnd) (Q : ℝ) (S : QInterval) (a b : ℝ) : Prop :=
  0 < a ∧ 0 ≤ b ∧ b ≤ a ∧ S.Mem (b / a) ∧ E.OnCurve Q a b

/-- A pair problem: its ends, original axis, charge, target and halves `(k, r, u⁺)`. -/
structure PairProblem where
  src : PairEnd
  tgt : PairEnd
  axis : ForwardAxis
  charge : ℚ
  target : ℚ
  halves : List (ℕ × Bool × ℕ)
  deriving DecidableEq, Repr

/-- The angle `k π / 2 ± u` of the half `(k, r)`. -/
def phiOf (k : ℕ) (r : Bool) (u : ℝ) : ℝ := (k : ℝ) * Real.pi / 2 + sgnR r * u

/-- The physical gap `φ + σ arctan (b / a) - τ arctan (B / A)`. -/
def PairProblem.gap (P : PairProblem) (φ a b A B : ℝ) : ℝ :=
  φ + sgnR P.src.positive * Real.arctan (b / a) - sgnR P.tgt.positive * Real.arctan (B / A)

/-- The inequality of `P` on the cell `S × T × [l / den, h / den]` of the half `(k, r)`, for
every admissible pair of label constants. -/
def PairProblem.Cell (P : PairProblem) (Q : ℝ) (den k : ℕ) (r : Bool) (S T : QInterval)
    (l h : ℕ) : Prop :=
  ∀ cs ct : ℝ, (P.src.label.cLo : ℝ) ≤ cs → ct ≤ P.tgt.label.cHi →
  ∀ a b A B u : ℝ, P.src.Mem Q S a b → P.tgt.Mem Q T A B → (l : ℝ) / den ≤ u →
    u ≤ (h : ℝ) / den → 19 / 25 ≤ P.gap (phiOf k r u) a b A B →
    P.gap (phiOf k r u) a b A B ≤ 3 * Real.pi / 4 →
    0 ≤ forwardMargin P.axis (sgnR P.src.positive) (sgnR P.tgt.positive) a b A B (phiOf k r u) →
    (P.target : ℝ) < phiOf k r u + P.src.label.eval cs a b - P.tgt.label.eval ct A B -
      P.charge * frameCharge (phiOf k r u)

/-! ### The angles allowed by the gap -/

/-- `19/25` over `angleUnit`. -/
def gapLo : Int := 76000000000000000000

/-- An upper bound of `3π/4` over `angleUnit`. -/
def gapHi : Int := 235619449019234492925

/-- Bounds of `π/2` over `angleUnit`. -/
def piHalfLo : Int := 157079632679489661900
def piHalfHi : Int := 157079632679489661950

theorem gapLo_eq : (gapLo : ℝ) / angleUnit = 19 / 25 := by norm_num [gapLo, angleUnit]

theorem gapHi_bound : 3 * Real.pi / 4 ≤ (gapHi : ℝ) / angleUnit := by
  have h := pi_hand_enclosure.2
  norm_num [gapHi, angleUnit]
  linarith

theorem piHalf_bounds :
    (piHalfLo : ℝ) / angleUnit ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ (piHalfHi : ℝ) / angleUnit := by
  have h := pi_hand_enclosure
  constructor <;> norm_num [piHalfLo, piHalfHi, angleUnit] <;> linarith [h.1, h.2]

/-- Bounds over `angleUnit` of `σ arctan t` for `t ∈ S`. -/
def alphaLo (σ : Bool) (S : QInterval) : Int := if σ then atanLo S.lo else -atanHi S.hi
def alphaHi (σ : Bool) (S : QInterval) : Int := if σ then atanHi S.hi else -atanLo S.lo

theorem alpha_bounds (σ : Bool) {S : QInterval} {t : ℝ} (ht : S.Mem t) :
    (alphaLo σ S : ℝ) / angleUnit ≤ sgnR σ * Real.arctan t ∧
      sgnR σ * Real.arctan t ≤ (alphaHi σ S : ℝ) / angleUnit := by
  have hlo := Real.arctan_mono ht.1
  have hhi := Real.arctan_mono ht.2
  have l1 := atanLo_le S.lo
  have l2 := le_atanHi S.lo
  have h1 := atanLo_le S.hi
  have h2 := le_atanHi S.hi
  cases σ
  · simp only [alphaLo, alphaHi, sgnR, Bool.false_eq_true, ↓reduceIte, Int.cast_neg, neg_div]
    constructor <;> linarith
  · simp only [alphaLo, alphaHi, sgnR, ↓reduceIte, one_mul]
    constructor <;> linarith

/-- Bounds over `angleUnit` of the angle `u` of the half `(k, r)` allowed by the gap, when the
tangents lie in `S` and `T`. -/
def uLo (k : ℕ) (r σ τ : Bool) (S T : QInterval) : Int :=
  if r then gapLo - alphaHi σ S + alphaLo τ T - k * piHalfHi
  else k * piHalfLo - (gapHi - alphaLo σ S + alphaHi τ T)

def uHi (k : ℕ) (r σ τ : Bool) (S T : QInterval) : Int :=
  if r then gapHi - alphaLo σ S + alphaHi τ T - k * piHalfLo
  else k * piHalfHi - (gapLo - alphaHi σ S + alphaLo τ T)

theorem u_bounds {k : ℕ} {r σ τ : Bool} {S T : QInterval} {u ts tt : ℝ} (hs : S.Mem ts)
    (ht : T.Mem tt)
    (h1 : 19 / 25 ≤ phiOf k r u + sgnR σ * Real.arctan ts - sgnR τ * Real.arctan tt)
    (h2 : phiOf k r u + sgnR σ * Real.arctan ts - sgnR τ * Real.arctan tt ≤ 3 * Real.pi / 4) :
    (uLo k r σ τ S T : ℝ) / angleUnit ≤ u ∧ u ≤ (uHi k r σ τ S T : ℝ) / angleUnit := by
  obtain ⟨as1, as2⟩ := alpha_bounds σ hs
  obtain ⟨at1, at2⟩ := alpha_bounds τ ht
  obtain ⟨p1, p2⟩ := piHalf_bounds
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have k1 := mul_le_mul_of_nonneg_left p1 hk
  have k2 := mul_le_mul_of_nonneg_left p2 hk
  have g1 := gapLo_eq
  have g2 := gapHi_bound
  set A : ℝ := (angleUnit : ℝ)
  have hφ : phiOf k r u = (k : ℝ) * (Real.pi / 2) + sgnR r * u := by unfold phiOf; ring
  rw [hφ] at h1 h2
  cases r
  · have hr : sgnR false = -1 := rfl
    rw [hr] at h1 h2
    have e1 : (uLo k false σ τ S T : ℝ) / A = k * ((piHalfLo : ℝ) / A) -
        ((gapHi : ℝ) / A - (alphaLo σ S : ℝ) / A + (alphaHi τ T : ℝ) / A) := by
      simp only [uLo, Bool.false_eq_true, ↓reduceIte]
      push_cast
      ring
    have e2 : (uHi k false σ τ S T : ℝ) / A = k * ((piHalfHi : ℝ) / A) -
        ((gapLo : ℝ) / A - (alphaHi σ S : ℝ) / A + (alphaLo τ T : ℝ) / A) := by
      simp only [uHi, Bool.false_eq_true, ↓reduceIte]
      push_cast
      ring
    rw [e1, e2]
    constructor <;> linarith
  · have hr : sgnR true = 1 := rfl
    rw [hr] at h1 h2
    have e1 : (uLo k true σ τ S T : ℝ) / A = (gapLo : ℝ) / A - (alphaHi σ S : ℝ) / A +
        (alphaLo τ T : ℝ) / A - k * ((piHalfHi : ℝ) / A) := by
      simp only [uLo, ↓reduceIte]
      push_cast
      ring
    have e2 : (uHi k true σ τ S T : ℝ) / A = (gapHi : ℝ) / A - (alphaLo σ S : ℝ) / A +
        (alphaHi τ T : ℝ) / A - k * ((piHalfLo : ℝ) / A) := by
      simp only [uHi, ↓reduceIte]
      push_cast
      ring
    rw [e1, e2]
    constructor <;> linarith

/-- `[l, h] / den` and `[lo, hi] / angleUnit` are disjoint. -/
def gapEmpty (den l h : ℕ) (lo hi : Int) : Bool :=
  decide (min ((h : Int) * angleUnit) (hi * den) < max ((l : Int) * angleUnit) (lo * den))

/-- `[l, h] / den ∩ [lo, hi] / angleUnit ⊆ [lo', hi'] / den`. -/
def trimOK (den l h lo' hi' : ℕ) (lo hi : Int) : Bool :=
  decide ((lo' : Int) * angleUnit ≤ max ((l : Int) * angleUnit) (lo * den)) &&
    decide (min ((h : Int) * angleUnit) (hi * den) ≤ (hi' : Int) * angleUnit)

theorem scaled_bounds {den l h : ℕ} (hden : 0 < den) {lo hi : Int} {u : ℝ}
    (hl : (l : ℝ) / den ≤ u) (hh : u ≤ (h : ℝ) / den) (hlo : (lo : ℝ) / angleUnit ≤ u)
    (hhi : u ≤ (hi : ℝ) / angleUnit) :
    ((max ((l : Int) * angleUnit) (lo * den) : Int) : ℝ) ≤ u * den * angleUnit ∧
      u * den * angleUnit ≤ ((min ((h : Int) * angleUnit) (hi * den) : Int) : ℝ) := by
  have hA := angleUnit_pos
  have hD : (0 : ℝ) < den := by exact_mod_cast hden
  rw [div_le_iff₀ hD] at hl
  rw [le_div_iff₀ hD] at hh
  rw [div_le_iff₀ hA] at hlo
  rw [le_div_iff₀ hA] at hhi
  push_cast
  constructor
  · apply max_le <;> nlinarith
  · apply le_min <;> nlinarith

theorem gapEmpty_false {den l h : ℕ} (hden : 0 < den) {lo hi : Int} {u : ℝ}
    (hl : (l : ℝ) / den ≤ u) (hh : u ≤ (h : ℝ) / den) (hlo : (lo : ℝ) / angleUnit ≤ u)
    (hhi : u ≤ (hi : ℝ) / angleUnit) : gapEmpty den l h lo hi = false := by
  obtain ⟨h1, h2⟩ := scaled_bounds hden hl hh hlo hhi
  simp only [gapEmpty, decide_eq_false_iff_not, not_lt]
  exact_mod_cast h1.trans h2

theorem trimOK_bounds {den l h lo' hi' : ℕ} (hden : 0 < den) {lo hi : Int} {u : ℝ}
    (ht : trimOK den l h lo' hi' lo hi = true)
    (hl : (l : ℝ) / den ≤ u) (hh : u ≤ (h : ℝ) / den) (hlo : (lo : ℝ) / angleUnit ≤ u)
    (hhi : u ≤ (hi : ℝ) / angleUnit) : (lo' : ℝ) / den ≤ u ∧ u ≤ (hi' : ℝ) / den := by
  have hA := angleUnit_pos
  have hD : (0 : ℝ) < den := by exact_mod_cast hden
  obtain ⟨h1, h2⟩ := scaled_bounds hden hl hh hlo hhi
  simp only [trimOK, Bool.and_eq_true, decide_eq_true_eq] at ht
  have t1 : (((lo' : Int) * angleUnit : Int) : ℝ) ≤
      ((max ((l : Int) * angleUnit) (lo * den) : Int) : ℝ) := by exact_mod_cast ht.1
  have t2 : ((min ((h : Int) * angleUnit) (hi * den) : Int) : ℝ) ≤
      (((hi' : Int) * angleUnit : Int) : ℝ) := by exact_mod_cast ht.2
  have c1 : (lo' : ℝ) * angleUnit ≤ u * den * angleUnit := by
    have := t1.trans h1
    push_cast at this
    exact this
  have c2 : u * den * angleUnit ≤ (hi' : ℝ) * angleUnit := by
    have := h2.trans t2
    push_cast at this
    exact this
  constructor
  · rw [div_le_iff₀ hD]
    exact le_of_mul_le_mul_right c1 hA
  · rw [le_div_iff₀ hD]
    exact le_of_mul_le_mul_right c2 hA

/-! ### Trees -/

/-- A coverage tree of one half of a problem. -/
inductive PairTree where
  /-- The gap excludes the cell. -/
  | gap : PairTree
  /-- The gap confines the angle to `[lo, hi]`; the subtree covers that cell. -/
  | trim (lo hi : ℕ) (t : PairTree) : PairTree
  /-- Bisect the source tangent interval. -/
  | source (left right : PairTree) : PairTree
  /-- Bisect the target tangent interval. -/
  | target (left right : PairTree) : PairTree
  /-- Bisect the angle interval. -/
  | angle (left right : PairTree) : PairTree
  /-- The next row covers the cell. -/
  | row : PairTree

/-- The lower half of an interval. -/
def lowerHalf (S : QInterval) : QInterval := ⟨S.lo, (S.lo + S.hi) / 2⟩

/-- The upper half of an interval. -/
def upperHalf (S : QInterval) : QInterval := ⟨(S.lo + S.hi) / 2, S.hi⟩

theorem mem_halves {S : QInterval} {t : ℝ} (ht : S.Mem t) :
    (lowerHalf S).Mem t ∨ (upperHalf S).Mem t := by
  rcases le_total t (((S.lo + S.hi) / 2 : ℚ) : ℝ) with h | h
  · exact Or.inl ⟨ht.1, h⟩
  · exact Or.inr ⟨h, ht.2⟩

/-- The arc `a` covers the end `E` on the tangent interval `S`. -/
def arcFits (a : ArcData) (E : PairEnd) (S : QInterval) : Bool :=
  (a.outer == E.outer) && (a.side == E.side) && (a.positive == E.positive) &&
    decide (a.tangent.lo ≤ S.lo) && decide (S.hi ≤ a.tangent.hi)

/-- The row `x` covers the cell `S × T × [l, h]` of the half `(k, r)` of `P`. -/
def leafCheck (M : AffineTableMeta) (C : TableCtx) (specs : List (QuadLabel × Bool))
    (P : PairProblem) (k : ℕ) (r : Bool) (S T : QInterval) (l h : ℕ) (x : AffineRow) : Bool :=
  decide (x.source < C.n) && decide (x.target < C.n) && (axisOf x.axis == P.axis) &&
    (x.quarter == k) && (x.positive == r) && decide (x.lo ≤ l) && decide (h ≤ x.hi) &&
    arcFits (nth default M.arcs x.source) P.src S &&
    arcFits (nth default M.arcs x.target) P.tgt T &&
    (nth default specs x.source == (P.src.label, true)) &&
    (nth default specs x.target == (P.tgt.label, false)) &&
    decide (P.target ≤ M.target (Fin.ofNat 7 x.edge)) &&
    (M.charge (Fin.ofNat 7 x.edge) == P.charge)

/-- The check of a tree on a cell. It returns the rows that follow the rows of its leaves. -/
def treeCheck (M : AffineTableMeta) (C : TableCtx) (specs : List (QuadLabel × Bool))
    (P : PairProblem) (k : ℕ) (r : Bool) (t : PairTree) :
    QInterval → QInterval → ℕ → ℕ → List AffineRow → Option (List AffineRow) :=
  PairTree.rec
    (motive := fun _ => QInterval → QInterval → ℕ → ℕ → List AffineRow → Option (List AffineRow))
    (fun S T l h rows =>
      if gapEmpty C.den l h (uLo k r P.src.positive P.tgt.positive S T)
        (uHi k r P.src.positive P.tgt.positive S T) then some rows else none)
    (fun lo hi _ ih S T l h rows =>
      if trimOK C.den l h lo hi (uLo k r P.src.positive P.tgt.positive S T)
        (uHi k r P.src.positive P.tgt.positive S T) then ih S T lo hi rows else none)
    (fun _ _ ihl ihr S T l h rows =>
      (ihl (lowerHalf S) T l h rows).bind (ihr (upperHalf S) T l h))
    (fun _ _ ihl ihr S T l h rows =>
      (ihl S (lowerHalf T) l h rows).bind (ihr S (upperHalf T) l h))
    (fun _ _ ihl ihr S T l h rows =>
      (ihl S T l ((l + h) / 2) rows).bind (ihr S T ((l + h) / 2) h))
    (fun S T l h rows =>
      match rows with
      | [] => none
      | x :: rest => if leafCheck M C specs P k r S T l h x then some rest else none)
    t

/-! ### Soundness -/

section Sound

variable {M : AffineTableMeta} {C : TableCtx} {specs : List (QuadLabel × Bool)}

theorem arcFits_contains {a : ArcData} {E : PairEnd} {S : QInterval} (h : arcFits a E S = true)
    {Q : ℝ} {x y : ℝ} (hxy : E.Mem Q S x y) : a.Contains Q x y ∧ a.sign = sgnR E.positive := by
  simp only [arcFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ho, hs⟩, hp⟩, hl⟩, hh⟩ := h
  obtain ⟨hx, hy, hyx, hS, hc⟩ := hxy
  refine ⟨⟨hx, hy, hyx, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact le_trans (by exact_mod_cast hl) hS.1
  · exact le_trans hS.2 (by exact_mod_cast hh)
  · unfold ArcData.OnCurve
    unfold PairEnd.OnCurve at hc
    rw [ho]
    cases hE : E.outer
    · simp only [hE, Bool.false_eq_true, ↓reduceIte] at hc ⊢
      have hside : a.side = E.side := hs
      simp only [ArcData.side, ho, hE, Bool.not_false, Bool.true_and] at hside
      cases hES : E.side
      · rw [hES] at hside
        have hn : ¬ a.tangent.hi ≤ 6 / 7 := by simpa using hside
        simp only [hES, Bool.false_eq_true, ↓reduceIte] at hc
        simp only [hn, ↓reduceIte]
        exact hc
      · rw [hES] at hside
        have hn : a.tangent.hi ≤ 6 / 7 := by simpa using hside
        simp only [hES, ↓reduceIte] at hc
        simp only [hn, ↓reduceIte]
        exact hc
    · simp only [hE, ↓reduceIte] at hc ⊢
      exact hc
  · simp [ArcData.sign, sgnR, hp]

theorem leafCheck_sound (hC : C.Valid M) (hspecs : SpecsHold M C specs) {P : PairProblem}
    {k : ℕ} {r : Bool} {S T : QInterval} {l h : ℕ} {x : AffineRow}
    (hx : leafCheck M C specs P k r S T l h x = true) (hclaim : (x.toTableRow M C.den).Claim M) :
    P.Cell M.radius C.den k r S T l h := by
  intro cs ct hcs hct a b A B u hsrc htgt hl hh _ _ hmargin
  simp only [leafCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, ht⟩, hax⟩, hk⟩, hr⟩, hlo⟩, hhi⟩, hfs⟩, hft⟩, hss⟩, hst⟩, hγ⟩, hβ⟩ := hx
  obtain ⟨hcs', hsσ⟩ := arcFits_contains hfs hsrc
  obtain ⟨hct', htτ⟩ := arcFits_contains hft htgt
  have hsa : (x.toTableRow M C.den).sourceArc M = nth default M.arcs x.source := by
    simp [AffineTableRow.sourceArc, AffineRow.toTableRow, nth_eq_getD]
  have hta : (x.toTableRow M C.den).targetArc M = nth default M.arcs x.target := by
    simp [AffineTableRow.targetArc, AffineRow.toTableRow, nth_eq_getD]
  have hphi : (x.toTableRow M C.den).phi u = phiOf k r u := by
    simp only [AffineTableRow.phi, AffineRow.toTableRow, AffineTableRow.sign, phiOf, sgnR, hk, hr]
  have hD : (0 : ℝ) < C.den := by exact_mod_cast hC.den_pos
  have hangle : (x.toTableRow M C.den).angle.Mem u := by
    simp only [AffineRow.toTableRow, QInterval.Mem]
    push_cast
    constructor
    · refine le_trans ?_ hl
      exact div_le_div_of_nonneg_right (by exact_mod_cast hlo) hD.le
    · refine le_trans hh ?_
      exact div_le_div_of_nonneg_right (by exact_mod_cast hhi) hD.le
  have hdom : (x.toTableRow M C.den).Domain M a b A B u :=
    ⟨by rw [hsa]; exact hcs', by rw [hta]; exact hct', hangle⟩
  have hmargin' : 0 ≤ forwardMargin (x.toTableRow M C.den).axis
      ((x.toTableRow M C.den).sourceArc M).sign ((x.toTableRow M C.den).targetArc M).sign
      a b A B ((x.toTableRow M C.den).phi u) := by
    have hax' : (x.toTableRow M C.den).axis = P.axis := hax
    rw [hax', hsa, hta, hsσ, htτ, hphi]
    exact hmargin
  have hc := hclaim a b A B u hdom hmargin'
  have hbs := hspecs x.source hs
  have hbt := hspecs x.target ht
  rw [hss] at hbs
  rw [hst] at hbt
  simp only [ArcData.Bounds, ↓reduceIte, Bool.false_eq_true] at hbs hbt
  have ls := hbs cs hcs a b hcs'
  have lt := hbt ct hct A B hct'
  have htarget : (P.target : ℝ) ≤ (x.toTableRow M C.den).lowerTarget := by
    simp only [AffineRow.toTableRow]
    exact_mod_cast hγ
  have hcharge : (M.charge (x.toTableRow M C.den).edge : ℝ) = P.charge := by
    simp only [AffineRow.toTableRow]
    exact_mod_cast hβ
  rw [hsa, hta, hphi, hcharge] at hc
  simp only [chargedCost] at hc
  linarith

theorem treeCheck_gap (P : PairProblem) (k : ℕ) (r : Bool) (S T : QInterval) (l h : ℕ)
    (rows : List AffineRow) :
    treeCheck M C specs P k r .gap S T l h rows =
      if gapEmpty C.den l h (uLo k r P.src.positive P.tgt.positive S T)
        (uHi k r P.src.positive P.tgt.positive S T) then some rows else none := rfl

theorem treeCheck_trim (P : PairProblem) (k : ℕ) (r : Bool) (lo hi : ℕ) (t : PairTree)
    (S T : QInterval) (l h : ℕ) (rows : List AffineRow) :
    treeCheck M C specs P k r (.trim lo hi t) S T l h rows =
      if trimOK C.den l h lo hi (uLo k r P.src.positive P.tgt.positive S T)
        (uHi k r P.src.positive P.tgt.positive S T)
      then treeCheck M C specs P k r t S T lo hi rows else none := rfl

theorem treeCheck_source (P : PairProblem) (k : ℕ) (r : Bool) (tl tr : PairTree)
    (S T : QInterval) (l h : ℕ) (rows : List AffineRow) :
    treeCheck M C specs P k r (.source tl tr) S T l h rows =
      (treeCheck M C specs P k r tl (lowerHalf S) T l h rows).bind
        (treeCheck M C specs P k r tr (upperHalf S) T l h) := rfl

theorem treeCheck_target (P : PairProblem) (k : ℕ) (r : Bool) (tl tr : PairTree)
    (S T : QInterval) (l h : ℕ) (rows : List AffineRow) :
    treeCheck M C specs P k r (.target tl tr) S T l h rows =
      (treeCheck M C specs P k r tl S (lowerHalf T) l h rows).bind
        (treeCheck M C specs P k r tr S (upperHalf T) l h) := rfl

theorem treeCheck_angle (P : PairProblem) (k : ℕ) (r : Bool) (tl tr : PairTree)
    (S T : QInterval) (l h : ℕ) (rows : List AffineRow) :
    treeCheck M C specs P k r (.angle tl tr) S T l h rows =
      (treeCheck M C specs P k r tl S T l ((l + h) / 2) rows).bind
        (treeCheck M C specs P k r tr S T ((l + h) / 2) h) := rfl

theorem treeCheck_row_nil (P : PairProblem) (k : ℕ) (r : Bool) (S T : QInterval) (l h : ℕ) :
    treeCheck M C specs P k r .row S T l h [] = none := rfl

theorem treeCheck_row_cons (P : PairProblem) (k : ℕ) (r : Bool) (S T : QInterval) (l h : ℕ)
    (x : AffineRow) (rest : List AffineRow) :
    treeCheck M C specs P k r .row S T l h (x :: rest) =
      if leafCheck M C specs P k r S T l h x then some rest else none := rfl

/-- A tree that passes its check covers its cell, given the claims of the rows it consumes. -/
theorem treeCheck_sound (hC : C.Valid M) (hspecs : SpecsHold M C specs) (P : PairProblem)
    (k : ℕ) (r : Bool) :
    ∀ (t : PairTree) (S T : QInterval) (l h : ℕ) (rows rows' : List AffineRow),
      treeCheck M C specs P k r t S T l h rows = some rows' →
      (∀ x ∈ rows, (x.toTableRow M C.den).Claim M) →
      (∀ x ∈ rows', x ∈ rows) ∧ P.Cell M.radius C.den k r S T l h := by
  intro t
  induction t with
  | gap =>
      intro S T l h rows rows' hc _
      rw [treeCheck_gap] at hc
      split_ifs at hc with hg
      cases hc
      refine ⟨fun x hx => hx, ?_⟩
      intro cs ct _ _ a b A B u hsrc htgt hl hh h1 h2 _
      have hu := u_bounds hsrc.2.2.2.1 htgt.2.2.2.1 h1 h2
      have hf := gapEmpty_false hC.den_pos hl hh hu.1 hu.2
      rw [hf] at hg
      exact absurd hg Bool.false_ne_true
  | trim lo hi t ih =>
      intro S T l h rows rows' hc hrows
      rw [treeCheck_trim] at hc
      split_ifs at hc with hg
      obtain ⟨hsub, hcell⟩ := ih S T lo hi rows rows' hc hrows
      refine ⟨hsub, ?_⟩
      intro cs ct hcs hct a b A B u hsrc htgt hl hh h1 h2 hm
      have hu := u_bounds hsrc.2.2.2.1 htgt.2.2.2.1 h1 h2
      obtain ⟨hl', hh'⟩ := trimOK_bounds hC.den_pos hg hl hh hu.1 hu.2
      exact hcell cs ct hcs hct a b A B u hsrc htgt hl' hh' h1 h2 hm
  | source tl tr ihl ihr =>
      intro S T l h rows rows' hc hrows
      rw [treeCheck_source] at hc
      obtain ⟨rows1, h1, h2⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨s1, c1⟩ := ihl _ _ _ _ _ _ h1 hrows
      obtain ⟨s2, c2⟩ := ihr _ _ _ _ _ _ h2 (fun x hx => hrows x (s1 x hx))
      refine ⟨fun x hx => s1 x (s2 x hx), ?_⟩
      intro cs ct hcs hct a b A B u hsrc htgt hl hh hg1 hg2 hm
      obtain ⟨ha, hb, hba, hS, hon⟩ := hsrc
      rcases mem_halves hS with hS' | hS'
      · exact c1 cs ct hcs hct a b A B u ⟨ha, hb, hba, hS', hon⟩ htgt hl hh hg1 hg2 hm
      · exact c2 cs ct hcs hct a b A B u ⟨ha, hb, hba, hS', hon⟩ htgt hl hh hg1 hg2 hm
  | target tl tr ihl ihr =>
      intro S T l h rows rows' hc hrows
      rw [treeCheck_target] at hc
      obtain ⟨rows1, h1, h2⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨s1, c1⟩ := ihl _ _ _ _ _ _ h1 hrows
      obtain ⟨s2, c2⟩ := ihr _ _ _ _ _ _ h2 (fun x hx => hrows x (s1 x hx))
      refine ⟨fun x hx => s1 x (s2 x hx), ?_⟩
      intro cs ct hcs hct a b A B u hsrc htgt hl hh hg1 hg2 hm
      obtain ⟨ha, hb, hba, hT, hon⟩ := htgt
      rcases mem_halves hT with hT' | hT'
      · exact c1 cs ct hcs hct a b A B u hsrc ⟨ha, hb, hba, hT', hon⟩ hl hh hg1 hg2 hm
      · exact c2 cs ct hcs hct a b A B u hsrc ⟨ha, hb, hba, hT', hon⟩ hl hh hg1 hg2 hm
  | angle tl tr ihl ihr =>
      intro S T l h rows rows' hc hrows
      rw [treeCheck_angle] at hc
      obtain ⟨rows1, h1, h2⟩ := Option.bind_eq_some_iff.mp hc
      obtain ⟨s1, c1⟩ := ihl _ _ _ _ _ _ h1 hrows
      obtain ⟨s2, c2⟩ := ihr _ _ _ _ _ _ h2 (fun x hx => hrows x (s1 x hx))
      refine ⟨fun x hx => s1 x (s2 x hx), ?_⟩
      intro cs ct hcs hct a b A B u hsrc htgt hl hh hg1 hg2 hm
      rcases le_total u ((((l + h) / 2 : ℕ) : ℝ) / C.den) with hu | hu
      · exact c1 cs ct hcs hct a b A B u hsrc htgt hl hu hg1 hg2 hm
      · exact c2 cs ct hcs hct a b A B u hsrc htgt hu hh hg1 hg2 hm
  | row =>
      intro S T l h rows rows' hc hrows
      cases rows with
      | nil => rw [treeCheck_row_nil] at hc; cases hc
      | cons x rest =>
          rw [treeCheck_row_cons] at hc
          split_ifs at hc with hx
          cases hc
          exact ⟨fun y hy => List.mem_cons_of_mem x hy,
            leafCheck_sound hC hspecs hx (hrows x List.mem_cons_self)⟩

/-! ### Problems and tables -/

/-- The trees of the halves of `P`, in order, each from the full box of the half. -/
def halvesCheck (M : AffineTableMeta) (C : TableCtx) (specs : List (QuadLabel × Bool))
    (P : PairProblem) : List (ℕ × Bool × ℕ) → List PairTree → List AffineRow →
    Option (List PairTree × List AffineRow)
  | [], ts, rows => some (ts, rows)
  | _ :: _, [], _ => none
  | (k, r, umax) :: hs, t :: ts, rows =>
      match treeCheck M C specs P k r t P.src.range P.tgt.range 0 umax rows with
      | none => none
      | some rows' => halvesCheck M C specs P hs ts rows'

/-- The trees of all problems, in order; the rows of the leaves are consumed in order. -/
def problemsCheck (M : AffineTableMeta) (C : TableCtx) (specs : List (QuadLabel × Bool)) :
    List PairProblem → List PairTree → List AffineRow → Bool
  | [], _, _ => true
  | P :: Ps, ts, rows =>
      match halvesCheck M C specs P P.halves ts rows with
      | none => false
      | some (ts', rows') => problemsCheck M C specs Ps ts' rows'

/-- `P` holds on every half: the full box of each half is covered. -/
def PairProblem.Holds (P : PairProblem) (Q : ℝ) (den : ℕ) : Prop :=
  ∀ hv ∈ P.halves, P.Cell Q den hv.1 hv.2.1 P.src.range P.tgt.range 0 hv.2.2

theorem halvesCheck_sound (hC : C.Valid M) (hspecs : SpecsHold M C specs) (P : PairProblem) :
    ∀ (hs : List (ℕ × Bool × ℕ)) (ts : List PairTree) (rows : List AffineRow)
      (ts' : List PairTree) (rows' : List AffineRow),
      halvesCheck M C specs P hs ts rows = some (ts', rows') →
      (∀ x ∈ rows, (x.toTableRow M C.den).Claim M) →
      (∀ x ∈ rows', x ∈ rows) ∧
        ∀ hv ∈ hs, P.Cell M.radius C.den hv.1 hv.2.1 P.src.range P.tgt.range 0 hv.2.2
  | [], ts, rows, ts', rows', hc, _ => by
      simp only [halvesCheck, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨-, rfl⟩ := hc
      exact ⟨fun x hx => hx, fun hv hv' => absurd hv' List.not_mem_nil⟩
  | _ :: _, [], _, _, _, hc, _ => by simp [halvesCheck] at hc
  | (k, r, umax) :: hs, t :: ts, rows, ts', rows', hc, hrows => by
      simp only [halvesCheck] at hc
      split at hc
      · cases hc
      · rename_i rows1 h1
        obtain ⟨s1, c1⟩ := treeCheck_sound hC hspecs P k r t _ _ _ _ _ _ h1 hrows
        obtain ⟨s2, c2⟩ := halvesCheck_sound hC hspecs P hs ts rows1 ts' rows' hc
          (fun x hx => hrows x (s1 x hx))
        refine ⟨fun x hx => s1 x (s2 x hx), fun hv hv' => ?_⟩
        rcases List.mem_cons.mp hv' with rfl | hv'
        · exact c1
        · exact c2 hv hv'

theorem problemsCheck_sound (hC : C.Valid M) (hspecs : SpecsHold M C specs) :
    ∀ (Ps : List PairProblem) (ts : List PairTree) (rows : List AffineRow),
      problemsCheck M C specs Ps ts rows = true →
      (∀ x ∈ rows, (x.toTableRow M C.den).Claim M) → ∀ P ∈ Ps, P.Holds M.radius C.den
  | [], _, _, _, _ => fun P hP => absurd hP List.not_mem_nil
  | P :: Ps, ts, rows, hc, hrows => by
      simp only [problemsCheck] at hc
      split at hc
      · cases hc
      · rename_i ts' rows' h1
        obtain ⟨s1, c1⟩ := halvesCheck_sound hC hspecs P P.halves ts rows ts' rows' h1 hrows
        intro P' hP'
        rcases List.mem_cons.mp hP' with rfl | hP'
        · exact c1
        · exact problemsCheck_sound hC hspecs Ps ts' rows' hc (fun x hx => hrows x (s1 x hx)) P'
            hP'

end Sound

/-- The problems of a table hold, from its four finite checks: the table data, the labels of its
arcs, the claims of its rows and the trees of its problems. -/
theorem table_sound {M : AffineTableMeta} {C : TableCtx} {specs : List (QuadLabel × Bool)}
    {Ps : List PairProblem} {ts : List PairTree} {rows : List AffineRow} (hC : C.Valid M)
    (hlabels : labelsCheck M.radius C.boxes 0 M.arcs specs = true)
    (hrows : ∀ x ∈ rows, (x.toTableRow M C.den).Claim M)
    (htrees : problemsCheck M C specs Ps ts rows = true) :
    ∀ P ∈ Ps, P.Holds M.radius C.den :=
  problemsCheck_sound hC (labelsCheck_sound hC hlabels) Ps ts rows htrees hrows

end SquaresInCircles.Eight.Arithmetic.PairCover
