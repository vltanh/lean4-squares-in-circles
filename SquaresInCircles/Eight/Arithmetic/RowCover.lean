module

public import SquaresInCircles.Eight.Arithmetic.AtanBounds

/-!
# A linear check of the angle coverage of an affine table

For every pair of arcs with consecutive roles, every allowed axis and both halves, the required
angles `AffineCover.required` must lie in the angle intervals of the rows of that pair, axis
and half (`AffineCover.AngleCovers`). The rows are sorted by (source, target, axis, half). A
walk over the arc pairs of a block of sources, in the same order, takes the rows of each key
from the front of the remaining list and checks that they cover the required interval
(`coverBlock`); blocks covering all sources give the coverage (`coverBlocks_sound`). The keys
whose axis no feasible separator has (`ExcludedArcs`) are skipped. The required interval is
enclosed by integers over `unit * den`, from fixed-point enclosures of the arctangent intervals
of the arcs, which `alphasRange` checks against the integer arctangent bounds of `AtanBounds`.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic
open Fixed

/-- `F` encloses the rational interval `Q`. -/
def Fixed.FI.Covers (F : FI) (Q : QInterval) : Prop :=
  (F.lo : ℝ) / unit ≤ Q.lo ∧ (Q.hi : ℝ) ≤ (F.hi : ℝ) / unit

theorem Fixed.FI.covers_of_wider {F : FI} {Q : QInterval} (h : F.wider (FI.ofQI Q) = true) :
    F.Covers Q := by
  simp only [FI.wider, ile_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  have hU := unit_pos_real
  have hl := (FI.mem_ofQ Q.lo).1
  have hh := (FI.mem_ofQ Q.hi).2
  have h1 : (F.lo : ℝ) ≤ (FI.ofQ Q.lo).lo := by exact_mod_cast h.1
  have h2 : ((FI.ofQ Q.hi).hi : ℝ) ≤ F.hi := by exact_mod_cast h.2
  exact ⟨(div_le_div_of_nonneg_right h1 hU.le).trans hl,
    hh.trans (div_le_div_of_nonneg_right h2 hU.le)⟩

theorem QInterval.mem_of_mem_inter {I J : QInterval} {x : ℝ} (h : (I.inter J).Mem x) :
    I.Mem x ∧ J.Mem x := by
  obtain ⟨h1, h2⟩ := h
  simp only [QInterval.inter, Rat.cast_max, Rat.cast_min, max_le_iff, le_min_iff] at h1 h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

/-! ### The required interval in integers -/

/-- The phase difference `gap - α_s + α_t - base` (or its negative), in fixed point. -/
def rawAngle (gap base αs αt : FI) (r : Bool) : FI :=
  if r then ((gap.sub αs).add αt).sub base else base.sub ((gap.sub αs).add αt)

/-- The lower end over `unit * den` of the required interval. -/
def reqLo (den : Nat) (raw : FI) (dlo : Int) : Int :=
  imax (imax (imul raw.lo (Int.ofNat den)) dlo) (Int.ofNat 0)

/-- The upper end over `unit * den` of the required interval. -/
def reqHi (den : Nat) (raw : FI) (dhi : Int) : Int :=
  imin (imin (imul raw.hi (Int.ofNat den)) dhi) (ifloor (imul (Int.ofNat 7) (imul unit (Int.ofNat den))) 10)

theorem reqLo_eq (den : Nat) (raw : FI) (dlo : Int) :
    reqLo den raw dlo = max (max (raw.lo * den) dlo) 0 := by
  simp [reqLo, Int.ofNat_eq_natCast]

theorem reqHi_eq (den : Nat) (raw : FI) (dhi : Int) :
    reqHi den raw dhi = min (min (raw.hi * den) dhi) (7 * (unit * den) / 10) := by
  simp (disch := norm_num) [reqHi, ifloor_eq, Int.ofNat_eq_natCast]

/-- The fixed-point data of the angle coverage: the angle scale, the gap interval, per role the
base angle and the difference range over `unit * den`, per arc its arctangent interval. -/
structure CoverCtx where
  den : Nat
  gap : FI
  base : List FI
  dLo : List Int
  dHi : List Int
  alphas : List FI

structure CoverCtx.Valid (K : AffineCover) (M : AffineTableMeta) (C : CoverCtx) : Prop where
  den_pos : 0 < C.den
  gap : C.gap.Covers ⟨19/25, 710/113-114/25⟩
  base : ∀ i : Fin 7, (nth ⟨0, 0⟩ C.base i).Covers (AffineCover.baseBox M i)
  dLo : ∀ i : Fin 7, ((nth 0 C.dLo i : Int) : ℝ) = ((M.differenceRange i).lo : ℝ) * (unit * C.den)
  dHi : ∀ i : Fin 7, ((nth 0 C.dHi i : Int) : ℝ) = ((M.differenceRange i).hi : ℝ) * (unit * C.den)
  alpha : ∀ k < M.arcs.length, (nth ⟨0, 0⟩ C.alphas k).Covers (K.alphaBox M k)

theorem seven_tenths_eq (den : Nat) :
    ((7 * (unit * den) / 10 : Int) : ℝ) = 7 / 10 * ((unit : ℝ) * den) := by
  have h : (7 * (unit * den) : Int) = 10 * (7 * (unit / 10) * den) := by
    simp only [unit]
    ring_nf
  rw [h, Int.mul_ediv_cancel_left _ (by norm_num)]
  simp only [unit]
  push_cast
  ring

theorem rawAngle_covers {G A B Bs : QInterval} {g a b bs : FI} (hg : g.Covers G)
    (ha : a.Covers A) (hb : b.Covers B) (hbs : bs.Covers Bs) (r : Bool) :
    (rawAngle g bs a b r).Covers
      (if r then ((G.sub A).add B).sub Bs else Bs.sub ((G.sub A).add B)) := by
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hs1, hs2⟩ := hbs
  cases r <;>
    simp only [rawAngle, FI.Covers, FI.sub, FI.add, isub_eq, iadd_eq, QInterval.sub,
      QInterval.add, QInterval.neg, Bool.false_eq_true, ↓reduceIte] <;>
    push_cast <;> simp only [add_div, sub_div] <;> constructor <;> linarith

/-- The required interval of an arc pair lies in the integer interval of its enclosures. -/
theorem required_bounds {K : AffineCover} {M : AffineTableMeta} {C : CoverCtx}
    (hC : C.Valid K M) {s t : ℕ} (hs : s < M.arcs.length) (ht : t < M.arcs.length) (r : Bool)
    {u : ℝ} (hu : (K.required M s t r).Mem u) :
    let i := (arcAt M s).role
    let raw := rawAngle C.gap (nth ⟨0, 0⟩ C.base i) (nth ⟨0, 0⟩ C.alphas s)
      (nth ⟨0, 0⟩ C.alphas t) r
    let dlo := if r then nth 0 C.dLo i else -nth 0 C.dHi i
    let dhi := if r then nth 0 C.dHi i else -nth 0 C.dLo i
    (reqLo C.den raw dlo : ℝ) / ((unit : ℝ) * C.den) ≤ u ∧
      u ≤ (reqHi C.den raw dhi : ℝ) / ((unit : ℝ) * C.den) := by
  intro i raw dlo dhi
  have hU := unit_pos_real
  have hD : (0 : ℝ) < C.den := by exact_mod_cast hC.den_pos
  have hL : (0 : ℝ) < (unit : ℝ) * C.den := mul_pos hU hD
  obtain ⟨hu1, hu3⟩ := QInterval.mem_of_mem_inter hu
  obtain ⟨hraw, hdiff⟩ := QInterval.mem_of_mem_inter hu1
  have hcov := rawAngle_covers hC.gap (hC.alpha s hs) (hC.alpha t ht) (hC.base i) r
  simp only [AffineCover.phaseBox] at hraw hdiff
  have hrl : (raw.lo : ℝ) / unit ≤ u := hcov.1.trans hraw.1
  have hrh : u ≤ (raw.hi : ℝ) / unit := hraw.2.trans hcov.2
  have hdl : (dlo : ℝ) ≤ u * ((unit : ℝ) * C.den) := by
    cases r
    · simp only [dlo, Bool.false_eq_true, ↓reduceIte] at hdiff ⊢
      have h := hdiff.1
      simp only [QInterval.neg, Rat.cast_neg] at h
      push_cast
      rw [hC.dHi i]
      nlinarith
    · simp only [dlo, ↓reduceIte] at hdiff ⊢
      rw [hC.dLo i]
      nlinarith [hdiff.1]
  have hdh : u * ((unit : ℝ) * C.den) ≤ (dhi : ℝ) := by
    cases r
    · simp only [dhi, Bool.false_eq_true, ↓reduceIte] at hdiff ⊢
      have h := hdiff.2
      simp only [QInterval.neg, Rat.cast_neg] at h
      push_cast
      rw [hC.dLo i]
      nlinarith
    · simp only [dhi, ↓reduceIte] at hdiff ⊢
      rw [hC.dHi i]
      nlinarith [hdiff.2]
  obtain ⟨h31, h32⟩ := hu3
  push_cast at h31 h32
  constructor
  · rw [div_le_iff₀ hL]
    rw [reqLo_eq]
    push_cast
    refine max_le (max_le ?_ hdl) (by positivity)
    rw [div_le_iff₀ hU] at hrl
    nlinarith
  · rw [le_div_iff₀ hL]
    rw [reqHi_eq]
    push_cast
    refine le_min (le_min ?_ hdh) ?_
    · rw [le_div_iff₀ hU] at hrh
      nlinarith
    · rw [seven_tenths_eq]
      nlinarith

/-! ### The walk over the arc pairs -/

def axisNum : ForwardAxis → Nat
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4

theorem axisOf_axisNum (a : ForwardAxis) : axisOf (axisNum a) = a := by cases a <;> rfl

/-- The key of a row: source, target, axis and half. -/
def keyOf (s t a : Nat) (r : Bool) (x : AffineRow) : Bool :=
  Nat.beq x.source s && Nat.beq x.target t && Nat.beq x.axis a &&
    (bif r then x.positive else !x.positive)

theorem keyOf_eq_true {s t a : Nat} {r : Bool} {x : AffineRow} :
    keyOf s t a r x = true ↔ x.source = s ∧ x.target = t ∧ x.axis = a ∧ x.positive = r := by
  cases r <;> simp [keyOf, Nat.beq_eq, and_assoc]

/-- `ExcludedArcs aS aT (axisOf a)`, decided. -/
def excludedB (aS aT : ArcData) (a : Nat) : Bool :=
  ((Nat.beq aS.role.val 0 || Nat.beq aS.role.val 2 || Nat.beq aS.role.val 4) &&
      ((Nat.beq a 2 && !aT.outer) || (Nat.beq a 4 && !aS.outer))) ||
    (Nat.beq a 1 && !aS.positive && !aT.outer) || (Nat.beq a 3 && aT.positive && !aS.outer)

theorem excludedB_iff (aS aT : ArcData) (axis : ForwardAxis) :
    excludedB aS aT (axisNum axis) = true ↔ ExcludedArcs aS aT axis := by
  have hz : aS.role ∈ Candidate.zeroEdges ↔
      (aS.role.val = 0 ∨ aS.role.val = 2 ∨ aS.role.val = 4) := by
    rcases aS with ⟨_, ⟨r, hr⟩, _, _, _, _⟩
    simp only [Candidate.zeroEdges, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp
  cases axis <;> simp [excludedB, ExcludedArcs, axisNum, hz, Nat.beq_eq] <;> tauto

theorem div_unit_den (n : Nat) {den : Nat} (hden : 0 < den) :
    (((n : Int) * unit : Int) : ℝ) / ((unit : ℝ) * den) = (n : ℝ) / den := by
  have hU := unit_pos_real
  have hD : (0 : ℝ) < den := by exact_mod_cast hden
  push_cast
  field_simp

/-- Every angle of `[lo, hi]` (over `unit * den`) lies in a row of `R` of key `(s, t, a, r)`
on edge `i` with quarter `w`. -/
def KeyCovered (den s t i w a : Nat) (r : Bool) (lo hi : Int) (R : List AffineRow) : Prop :=
  ∀ u : ℝ, (lo : ℝ) / ((unit : ℝ) * den) ≤ u → u ≤ (hi : ℝ) / ((unit : ℝ) * den) →
    ∃ x ∈ R, keyOf s t a r x = true ∧ x.edge = i ∧ x.quarter = w ∧
      (x.lo : ℝ) / den ≤ u ∧ u ≤ (x.hi : ℝ) / den

theorem KeyCovered.mono {den s t i w a : Nat} {r : Bool} {lo hi : Int} {R R₀ : List AffineRow}
    (h : KeyCovered den s t i w a r lo hi R) (hsub : ∀ x ∈ R, x ∈ R₀) :
    KeyCovered den s t i w a r lo hi R₀ := by
  intro u h1 h2
  obtain ⟨x, hx, hrest⟩ := h u h1 h2
  exact ⟨x, hsub x hx, hrest⟩

/-- One pass over the rows of a key at the front of a list, from the point `cur` on (over
`unit * den`): each row starts at or before the point reached so far and is on edge `i` with
quarter `w`; once a row reaches `hi` (`done`), the other rows of the key are passed over. The
result is the list after the rows of the key, once `hi` is reached. -/
def walkKey (key : AffineRow → Bool) (i w : Nat) (hi : Int) (R : List AffineRow) :
    Int → Bool → Option (List AffineRow) :=
  List.rec (motive := fun _ => Int → Bool → Option (List AffineRow))
    (fun _ done => bif done then some [] else none)
    (fun x xs ih cur done =>
      bif key x then
        (bif done then ih cur true
        else bif Nat.beq x.edge i && Nat.beq x.quarter w &&
            ile (imul (Int.ofNat x.lo) unit) cur then
          ih (imax cur (imul (Int.ofNat x.hi) unit)) (ile hi (imul (Int.ofNat x.hi) unit))
        else none)
      else bif done then some (x :: xs) else none)
    R

theorem walkKey_sound {key : AffineRow → Bool} {i w den : Nat} (hden : 0 < den) {hi : Int} :
    ∀ {R : List AffineRow} {cur : Int} {done : Bool} {R' : List AffineRow},
      walkKey key i w hi R cur done = some R' →
      (∀ x ∈ R', x ∈ R) ∧ (done = false →
        ∀ u : ℝ, (cur : ℝ) / ((unit : ℝ) * den) ≤ u → u ≤ (hi : ℝ) / ((unit : ℝ) * den) →
          ∃ x ∈ R, key x = true ∧ x.edge = i ∧ x.quarter = w ∧
            (x.lo : ℝ) / den ≤ u ∧ u ≤ (x.hi : ℝ) / den)
  | [], cur, done, R', h => by
      have h' : (bif done then some [] else none) = some R' := h
      cases done
      · simp at h'
      · simp only [Bool.cond_true, Option.some.injEq] at h'
        subst h'
        exact ⟨fun x hx => absurd hx List.not_mem_nil, fun h => absurd h (by decide)⟩
  | x :: xs, cur, done, R', h => by
      have hU := unit_pos_real
      have hD : (0 : ℝ) < den := by exact_mod_cast hden
      have hL : (0 : ℝ) < (unit : ℝ) * den := mul_pos hU hD
      have h' : (bif key x then
          (bif done then walkKey key i w hi xs cur true
          else bif Nat.beq x.edge i && Nat.beq x.quarter w &&
              ile (imul (Int.ofNat x.lo) unit) cur then
            walkKey key i w hi xs (imax cur (imul (Int.ofNat x.hi) unit))
              (ile hi (imul (Int.ofNat x.hi) unit))
          else none)
        else bif done then some (x :: xs) else none) = some R' := h
      cases hk : key x
      · simp only [hk, Bool.cond_false] at h'
        cases done
        · simp at h'
        · simp only [Bool.cond_true, Option.some.injEq] at h'
          subst h'
          exact ⟨fun y hy => hy, fun h => absurd h (by decide)⟩
      · simp only [hk, Bool.cond_true] at h'
        cases done
        · simp only [Bool.cond_false] at h'
          cases hc : (Nat.beq x.edge i && Nat.beq x.quarter w &&
              ile (imul (Int.ofNat x.lo) unit) cur)
          · rw [hc] at h'
            simp at h'
          · simp only [hc, Bool.cond_true] at h'
            obtain ⟨s1, k1⟩ := walkKey_sound hden h'
            refine ⟨fun y hy => List.mem_cons_of_mem x (s1 y hy), fun _ u h1 h2 => ?_⟩
            simp only [Bool.and_eq_true, Nat.beq_eq, ile_eq, imul_eq, Int.ofNat_eq_natCast,
              decide_eq_true_eq] at hc
            obtain ⟨⟨he, hq⟩, hlo⟩ := hc
            have hxlo : (x.lo : ℝ) / den ≤ u := by
              rw [← div_unit_den x.lo hden]
              refine le_trans ?_ h1
              exact div_le_div_of_nonneg_right (by exact_mod_cast hlo) hL.le
            by_cases hux : u ≤ (x.hi : ℝ) / den
            · exact ⟨x, List.mem_cons_self, hk, he, hq, hxlo, hux⟩
            · have hux' : (x.hi : ℝ) / den < u := lt_of_not_ge hux
              have hdone : ile hi (imul (Int.ofNat x.hi) unit) = false := by
                rw [ile_eq, imul_eq, Int.ofNat_eq_natCast]
                by_contra hfin
                simp only [decide_eq_false_iff_not, not_not] at hfin
                have : (hi : ℝ) / ((unit : ℝ) * den) ≤ (x.hi : ℝ) / den := by
                  rw [← div_unit_den x.hi hden]
                  exact div_le_div_of_nonneg_right (by exact_mod_cast hfin) hL.le
                linarith
              have hcur : ((imax cur (imul (Int.ofNat x.hi) unit) : Int) : ℝ) /
                  ((unit : ℝ) * den) ≤ u := by
                rw [imax_eq, imul_eq, Int.ofNat_eq_natCast, Int.cast_max,
                  ← max_div_div_right hL.le, max_le_iff]
                refine ⟨h1, ?_⟩
                rw [div_unit_den x.hi hden]
                exact hux'.le
              obtain ⟨y, hy, hyr⟩ := k1 hdone u hcur h2
              exact ⟨y, List.mem_cons_of_mem x hy, hyr⟩
        · simp only [Bool.cond_true] at h'
          obtain ⟨s1, -⟩ := walkKey_sound hden h'
          exact ⟨fun y hy => List.mem_cons_of_mem x (s1 y hy), fun h => absurd h (by decide)⟩

/-- The rows of key `(s, t, a, r)` at the front of `R` cover `[lo, hi]`; the rest follows. -/
def coverKey (s t i w a : Nat) (r : Bool) (lo hi : Int) (R : List AffineRow) :
    Option (List AffineRow) :=
  walkKey (keyOf s t a r) i w hi R lo (!ile lo hi)

theorem coverKey_sound {den s t i w a : Nat} (hden : 0 < den) {r : Bool} {lo hi : Int}
    {R R' : List AffineRow} (h : coverKey s t i w a r lo hi R = some R') :
    (∀ x ∈ R', x ∈ R) ∧ KeyCovered den s t i w a r lo hi R := by
  obtain ⟨s1, k1⟩ := walkKey_sound hden h
  refine ⟨s1, fun u h1 h2 => ?_⟩
  have hU := unit_pos_real
  have hD : (0 : ℝ) < den := by exact_mod_cast hden
  have hL : (0 : ℝ) < (unit : ℝ) * den := mul_pos hU hD
  cases hle : ile lo hi
  · exfalso
    have hlt : hi < lo := by simpa [ile_eq] using hle
    have : (hi : ℝ) / ((unit : ℝ) * den) < (lo : ℝ) / ((unit : ℝ) * den) :=
      div_lt_div_of_pos_right (by exact_mod_cast hlt) hL
    linarith
  · exact k1 (by simp [hle]) u h1 h2

/-- The keys of the allowed axes and both halves of an arc pair, except the axes `a` with
`ex a`. -/
def coverAxes (den s t i w : Nat) (gap base αs αt : FI) (dlo dhi : Int) (ex : Nat → Bool) :
    List ForwardAxis → List AffineRow → Option (List AffineRow)
  | [], R => some R
  | a :: as, R =>
    bif ex (axisNum a) then coverAxes den s t i w gap base αs αt dlo dhi ex as R else
    match coverKey s t i w (axisNum a) true (reqLo den (rawAngle gap base αs αt true) dlo)
        (reqHi den (rawAngle gap base αs αt true) dhi) R with
    | none => none
    | some R1 =>
      match coverKey s t i w (axisNum a) false
          (reqLo den (rawAngle gap base αs αt false) (-dhi))
          (reqHi den (rawAngle gap base αs αt false) (-dlo)) R1 with
      | none => none
      | some R2 => coverAxes den s t i w gap base αs αt dlo dhi ex as R2

/-- The integer bounds of the required interval of a half. -/
def reqBounds (den : Nat) (gap base αs αt : FI) (dlo dhi : Int) (r : Bool) : Int × Int :=
  if r then
    (reqLo den (rawAngle gap base αs αt true) dlo, reqHi den (rawAngle gap base αs αt true) dhi)
  else (reqLo den (rawAngle gap base αs αt false) (-dhi),
    reqHi den (rawAngle gap base αs αt false) (-dlo))

theorem coverAxes_sound {den s t i w : Nat} (hden : 0 < den) {gap base αs αt : FI}
    {dlo dhi : Int} {ex : Nat → Bool} :
    ∀ {as : List ForwardAxis} {R R' : List AffineRow},
      coverAxes den s t i w gap base αs αt dlo dhi ex as R = some R' →
      (∀ x ∈ R', x ∈ R) ∧ ∀ a ∈ as, ex (axisNum a) = false → ∀ r : Bool,
        KeyCovered den s t i w (axisNum a) r (reqBounds den gap base αs αt dlo dhi r).1
          (reqBounds den gap base αs αt dlo dhi r).2 R
  | [], R, R', h => by
      simp only [coverAxes, Option.some.injEq] at h
      subst h
      exact ⟨fun x hx => hx, fun a ha => absurd ha List.not_mem_nil⟩
  | a :: as, R, R', h => by
      simp only [coverAxes] at h
      cases hex : ex (axisNum a) with
      | true =>
          simp only [hex, cond_true] at h
          obtain ⟨s3, k3⟩ := coverAxes_sound hden h
          refine ⟨s3, fun b hb hb' r => ?_⟩
          rcases List.mem_cons.mp hb with rfl | hb
          · rw [hex] at hb'
            exact absurd hb' (by decide)
          · exact k3 b hb hb' r
      | false =>
      simp only [hex, cond_false] at h
      split at h
      · simp at h
      · rename_i R1 h1
        split at h
        · simp at h
        · rename_i R2 h2
          obtain ⟨s1, k1⟩ := coverKey_sound hden h1
          obtain ⟨s2, k2⟩ := coverKey_sound hden h2
          obtain ⟨s3, k3⟩ := coverAxes_sound hden h
          refine ⟨fun x hx => s1 x (s2 x (s3 x hx)), fun b hb hb' r => ?_⟩
          rcases List.mem_cons.mp hb with rfl | hb
          · cases r
            · exact k2.mono s1
            · exact k1
          · exact (k3 b hb hb' r).mono (fun x hx => s1 x (s2 x hx))

/-- The arc pairs of a source arc `aS` (index `s`) with the arcs of the next role, for the word
`word` and the allowed axes `axes` of the table. -/
def coverT (C : CoverCtx) (word : Fin 7 → ℕ) (axes : Fin 7 → List ForwardAxis) (s : Nat)
    (aS : ArcData) (αs : FI) :
    Nat → List (ArcData × FI) → List AffineRow → Option (List AffineRow)
  | _, [], R => some R
  | t, (aT, αt) :: rest, R =>
    if aT.role = aS.role + 1 then
      match coverAxes C.den s t aS.role (word aS.role) C.gap (nth ⟨0, 0⟩ C.base aS.role) αs αt
          (nth 0 C.dLo aS.role) (nth 0 C.dHi aS.role) (excludedB aS aT) (axes aS.role) R with
      | none => none
      | some R' => coverT C word axes s aS αs (t + 1) rest R'
    else coverT C word axes s aS αs (t + 1) rest R

theorem coverT_sound {C : CoverCtx} {word : Fin 7 → ℕ} {axes : Fin 7 → List ForwardAxis}
    (hden : 0 < C.den) {s : Nat} {aS : ArcData} {αs : FI} :
    ∀ {t₀ : Nat} {L : List (ArcData × FI)} {R R' : List AffineRow},
      coverT C word axes s aS αs t₀ L R = some R' →
      (∀ x ∈ R', x ∈ R) ∧ ∀ j (hj : j < L.length), L[j].1.role = aS.role + 1 →
        ∀ a ∈ axes aS.role, excludedB aS L[j].1 (axisNum a) = false → ∀ r : Bool,
          KeyCovered C.den s (t₀ + j) aS.role (word aS.role) (axisNum a) r
            (reqBounds C.den C.gap (nth ⟨0, 0⟩ C.base aS.role) αs L[j].2
              (nth 0 C.dLo aS.role) (nth 0 C.dHi aS.role) r).1
            (reqBounds C.den C.gap (nth ⟨0, 0⟩ C.base aS.role) αs L[j].2
              (nth 0 C.dLo aS.role) (nth 0 C.dHi aS.role) r).2 R
  | t₀, [], R, R', h => by
      simp only [coverT, Option.some.injEq] at h
      subst h
      exact ⟨fun x hx => hx, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | t₀, (aT, αt) :: rest, R, R', h => by
      simp only [coverT] at h
      split_ifs at h with hrole
      · split at h
        · simp at h
        · rename_i R1 h1
          obtain ⟨s1, k1⟩ := coverAxes_sound hden h1
          obtain ⟨s2, k2⟩ := coverT_sound hden h
          refine ⟨fun x hx => s1 x (s2 x hx), fun j hj hjr a ha hx r => ?_⟩
          cases j with
          | zero => simpa using k1 a ha (by simpa using hx) r
          | succ j =>
              have := (k2 j (by simpa using hj) (by simpa using hjr) a ha
                (by simpa using hx) r).mono s1
              simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
      · obtain ⟨s2, k2⟩ := coverT_sound hden h
        refine ⟨s2, fun j hj hjr a ha hx r => ?_⟩
        cases j with
        | zero => exact absurd (by simpa using hjr) hrole
        | succ j =>
            have := k2 j (by simpa using hj) (by simpa using hjr) a ha (by simpa using hx) r
            simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-- The arc pairs of the sources in `L` (the first with index `s₀`), source by source. -/
def coverS (C : CoverCtx) (word : Fin 7 → ℕ) (axes : Fin 7 → List ForwardAxis)
    (all : List (ArcData × FI)) :
    Nat → List (ArcData × FI) → List AffineRow → Option (List AffineRow)
  | _, [], R => some R
  | s, (aS, αs) :: rest, R =>
    match coverT C word axes s aS αs 0 all R with
    | none => none
    | some R' => coverS C word axes all (s + 1) rest R'

theorem coverS_sound {C : CoverCtx} {word : Fin 7 → ℕ} {axes : Fin 7 → List ForwardAxis}
    (hden : 0 < C.den) {all : List (ArcData × FI)} :
    ∀ {s₀ : Nat} {L : List (ArcData × FI)} {R R' : List AffineRow},
      coverS C word axes all s₀ L R = some R' →
      ∀ j (hj : j < L.length) jt (hjt : jt < all.length), all[jt].1.role = L[j].1.role + 1 →
        ∀ a ∈ axes L[j].1.role, excludedB L[j].1 all[jt].1 (axisNum a) = false → ∀ r : Bool,
          KeyCovered C.den (s₀ + j) jt L[j].1.role (word L[j].1.role) (axisNum a) r
            (reqBounds C.den C.gap (nth ⟨0, 0⟩ C.base L[j].1.role) L[j].2 all[jt].2
              (nth 0 C.dLo L[j].1.role) (nth 0 C.dHi L[j].1.role) r).1
            (reqBounds C.den C.gap (nth ⟨0, 0⟩ C.base L[j].1.role) L[j].2 all[jt].2
              (nth 0 C.dLo L[j].1.role) (nth 0 C.dHi L[j].1.role) r).2 R
  | s₀, [], R, R', h => by
      intro j hj
      exact absurd hj (Nat.not_lt_zero _)
  | s₀, (aS, αs) :: rest, R, R', h => by
      simp only [coverS] at h
      split at h
      · simp at h
      · rename_i R1 h1
        obtain ⟨s1, k1⟩ := coverT_sound hden h1
        intro j hj jt hjt hrole a ha hx r
        cases j with
        | zero =>
            have := k1 jt hjt (by simpa using hrole) a (by simpa using ha) (by simpa using hx) r
            simpa using this
        | succ j =>
            have := coverS_sound hden h j (by simpa using hj) jt hjt (by simpa using hrole) a
              (by simpa using ha) (by simpa using hx) r
            have := this.mono s1
            simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-- The rows from the row `o` of the chunk `c` on. The rows of a table are kept in chunks, so
that the kernel reaches a row deep in the table without walking through all rows before it. -/
def rowsFrom (chunks : List (List AffineRow)) (c o : Nat) : List AffineRow :=
  ((chunks.drop c).flatten).drop o

theorem mem_of_mem_rowsFrom {chunks : List (List AffineRow)} {c o : Nat} {x : AffineRow}
    (h : x ∈ rowsFrom chunks c o) : x ∈ chunks.flatten := by
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp (List.mem_of_mem_drop h)
  exact List.mem_flatten.mpr ⟨l, List.mem_of_mem_drop hl, hx⟩

/-- The walk over the sources `s₀, …, s₀ + n - 1`, from the row `o` of the chunk `c` of the
sorted rows on. -/
def coverBlock (C : CoverCtx) (M : AffineTableMeta) (s₀ n c o : Nat)
    (chunks : List (List AffineRow)) : Bool :=
  (coverS C M.word M.allowedAxes (M.arcs.zip C.alphas) s₀
    (((M.arcs.zip C.alphas).drop s₀).take n) (rowsFrom chunks c o)).isSome

theorem coverBlock_congr {C : CoverCtx} {M M' : AffineTableMeta} (ha : M'.arcs = M.arcs)
    (hw : M'.word = M.word) (hx : M'.allowedAxes = M.allowedAxes) (s₀ n c o : Nat)
    (chunks : List (List AffineRow)) :
    coverBlock C M' s₀ n c o chunks = coverBlock C M s₀ n c o chunks := by
  simp only [coverBlock, ha, hw, hx]

/-- The angle coverage of a table, from walks over blocks of sources covering all arcs. -/
theorem coverBlocks_sound {K : AffineCover} {M : AffineTableMeta} {C : CoverCtx}
    (hC : C.Valid K M) (hlen : C.alphas.length = M.arcs.length)
    {chunks : List (List AffineRow)} {blocks : List (Nat × Nat)}
    (hcov : blocksCover 0 blocks M.arcs.length = true)
    (hb : AllBlocks (fun s₀ n => ∃ c o, coverBlock C M s₀ n c o chunks = true) blocks) :
    K.AngleCovers M (chunks.flatten.map (·.toTableRow M C.den)) := by
  intro s t hst axis haxis hkeep r u hu
  obtain ⟨⟨s₀, n⟩, hmem, h1, h2⟩ := blocksCover_mem hcov s.val (Nat.zero_le _) s.2
  obtain ⟨c, o, hk⟩ := AllBlocks.of_mem hb _ hmem
  obtain ⟨R', hR⟩ := Option.isSome_iff_exists.mp hk
  simp only at h1 h2
  have hzl : (M.arcs.zip C.alphas).length = M.arcs.length := by simp [hlen]
  have ht : t.val < (M.arcs.zip C.alphas).length := by rw [hzl]; exact t.2
  have hsa : s.val < C.alphas.length := by rw [hlen]; exact s.2
  have hta : t.val < C.alphas.length := by rw [hlen]; exact t.2
  have hj : s.val - s₀ < (((M.arcs.zip C.alphas).drop s₀).take n).length := by
    simp only [List.length_take, List.length_drop, hzl]
    omega
  have hLj : (((M.arcs.zip C.alphas).drop s₀).take n)[s.val - s₀] =
      (arcAt M s, nth ⟨0, 0⟩ C.alphas s) := by
    rw [List.getElem_take, List.getElem_drop, List.getElem_zip, arcAt, nth_eq_getD]
    have he : s₀ + (s.val - s₀) = s.val := by omega
    simp only [he]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsa]
  have hzt : (M.arcs.zip C.alphas)[t.val] = (arcAt M t, nth ⟨0, 0⟩ C.alphas t) := by
    rw [List.getElem_zip, arcAt, nth_eq_getD]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hta]
  have hex : excludedB (arcAt M s) (arcAt M t) (axisNum axis) = false := by
    cases h : excludedB (arcAt M s) (arcAt M t) (axisNum axis)
    · rfl
    · exact absurd ((excludedB_iff _ _ _).mp h) hkeep
  have hk' := coverS_sound hC.den_pos hR (s.val - s₀) hj t.val ht
    (by rw [hLj, hzt]; exact hst) axis (by rw [hLj]; exact haxis) (by rw [hLj, hzt]; exact hex) r
  rw [hLj, hzt, show s₀ + (s.val - s₀) = s.val by omega] at hk'
  have hk'' := hk'.mono (fun x hx => mem_of_mem_rowsFrom hx)
  have hb' := required_bounds hC s.2 t.2 r hu
  obtain ⟨x, hx, hkey, he, hq, hlo, hhi⟩ := hk'' u (by cases r <;> exact hb'.1)
    (by cases r <;> exact hb'.2)
  obtain ⟨hxs, hxt, hxa, hxr⟩ := keyOf_eq_true.mp hkey
  have hedge : (Fin.ofNat 7 x.edge : Fin 7) = (arcAt M s).role := by
    ext
    simp [he]
  refine ⟨x.toTableRow M C.den, List.mem_map.mpr ⟨x, hx, rfl⟩,
    (by simpa using hxs : x.source = s.val), hxt, hedge, ?_, hq, hxr, ?_, ?_⟩
  · show axisOf x.axis = axis
    rw [hxa, axisOf_axisNum]
  · constructor <;> simp only [AffineRow.toTableRow] <;> push_cast
    · exact hlo
    · exact hhi
  · simp only [AffineRow.toTableRow, hedge]
    exact le_rfl

/-! ### The data checked once per table -/

/-- The interval of the arctangent of `x`, from the integer bounds of `PairCover.atanLo` and
`PairCover.atanHi` over `10 ^ 20`. -/
def atanInterval (x : ℚ) : QInterval :=
  ⟨(PairCover.atanLo x : ℚ) / PairCover.angleUnit, (PairCover.atanHi x : ℚ) / PairCover.angleUnit⟩

theorem atanInterval_mem (x : ℚ) : (atanInterval x).Mem (Real.arctan x) := by
  constructor
  · have h := PairCover.atanLo_le x
    simp only [atanInterval]
    push_cast
    exact h
  · have h := PairCover.le_atanHi x
    simp only [atanInterval]
    push_cast
    exact h

/-- The arctangent intervals of the tangent endpoints of all arcs. -/
def atanEnds (M : AffineTableMeta) : List (QInterval × QInterval) :=
  M.arcs.map fun a => (atanInterval a.tangent.lo, atanInterval a.tangent.hi)

theorem atanEnds_at (M : AffineTableMeta) (S : StateChains) {k : ℕ} (hk : k < M.arcs.length) :
    AffineCover.endpointAt ⟨atanEnds M, S⟩ k =
      (atanInterval (arcAt M k).tangent.lo, atanInterval (arcAt M k).tangent.hi) := by
  simp [AffineCover.endpointAt, atanEnds, arcAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]

theorem endpointsValid_atanEnds (M : AffineTableMeta) (S : StateChains) :
    (⟨atanEnds M, S⟩ : AffineCover).EndpointsValid M := by
  intro k
  rw [atanEnds_at M S k.2]
  exact ⟨atanInterval_mem _, atanInterval_mem _⟩

/-- The angle interval of an arc, the last two numbers of its data line (`ArcBox.ofData`). -/
def alphaOfData (_s _p _c0 _c1 _p0 _p1 _q0 _q1 _s0 _s1 _r0 _r1 _al0 _al1 _bl0 _bl1 _ah0 _ah1
    _bh0 _bh1 _rl0 _rl1 _rh0 _rh1 lo hi : Int) : FI := ⟨lo, hi⟩

/-- The arctangent interval of an arc (`AffineCover.alphaBox`). -/
def alphaOf (a : ArcData) : QInterval :=
  if a.positive then ⟨(atanInterval a.tangent.lo).lo, (atanInterval a.tangent.hi).hi⟩
  else ⟨-(atanInterval a.tangent.hi).hi, -(atanInterval a.tangent.lo).lo⟩

theorem alphaBox_atanEnds (M : AffineTableMeta) (S : StateChains) {k : ℕ}
    (hk : k < M.arcs.length) :
    AffineCover.alphaBox ⟨atanEnds M, S⟩ M k = alphaOf (arcAt M k) := by
  simp only [AffineCover.alphaBox, atanEnds_at M S hk, alphaOf]

/-- The same interval in fixed point, exactly: `unit = 10 ^ 4 · 10 ^ 20`. -/
def alphaFI (a : ArcData) : FI :=
  bif a.positive then
    ⟨imul (PairCover.atanLo a.tangent.lo) (Int.ofNat 10000),
      imul (PairCover.atanHi a.tangent.hi) (Int.ofNat 10000)⟩
  else ⟨ineg (imul (PairCover.atanHi a.tangent.hi) (Int.ofNat 10000)),
    ineg (imul (PairCover.atanLo a.tangent.lo) (Int.ofNat 10000))⟩

theorem alphaFI_covers {F : FI} {a : ArcData} (h : F.wider (alphaFI a) = true) :
    F.Covers (alphaOf a) := by
  simp only [FI.wider, ile_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  have hU := unit_pos_real
  have e (z : Int) : ((z * 10000 : Int) : ℝ) / unit = ((z : ℚ) / PairCover.angleUnit : ℚ) := by
    simp only [unit, PairCover.angleUnit]
    push_cast
    ring
  have h1 : (F.lo : ℝ) ≤ (alphaFI a).lo := by exact_mod_cast h.1
  have h2 : ((alphaFI a).hi : ℝ) ≤ F.hi := by exact_mod_cast h.2
  cases hp : a.positive <;>
    simp only [alphaFI, hp, cond_true, cond_false, imul_eq, ineg_eq, Int.ofNat_eq_natCast,
      Nat.cast_ofNat] at h1 h2 <;>
    simp only [FI.Covers, alphaOf, atanInterval, hp, Bool.false_eq_true, ↓reduceIte]
  · constructor
    · have := div_le_div_of_nonneg_right h1 hU.le
      rw [show ((-(PairCover.atanHi a.tangent.hi * 10000) : Int) : ℝ) / unit =
        -((((PairCover.atanHi a.tangent.hi * 10000 : Int) : ℝ)) / unit) by push_cast; ring,
        e] at this
      push_cast at this ⊢
      linarith
    · have := div_le_div_of_nonneg_right h2 hU.le
      rw [show ((-(PairCover.atanLo a.tangent.lo * 10000) : Int) : ℝ) / unit =
        -((((PairCover.atanLo a.tangent.lo * 10000 : Int) : ℝ)) / unit) by push_cast; ring,
        e] at this
      push_cast at this ⊢
      linarith
  · constructor
    · have := div_le_div_of_nonneg_right h1 hU.le
      rw [e] at this
      exact this
    · have := div_le_div_of_nonneg_right h2 hU.le
      rw [e] at this
      exact this

/-- The fixed-point arctangent intervals `s, …, s + c - 1` enclose those of the arcs. -/
def alphasRange (arcs : List ArcData) (alphas : List FI) (s c : Nat) : Bool :=
  (List.range' s c).all fun k => (nth ⟨0, 0⟩ alphas k).wider (alphaFI (nth default arcs k))

/-- State chains from data: per role, the chains of the non-outer and of the outer arcs. -/
def chainsOf (d : List (List (List ℕ))) : StateChains :=
  fun i o => nth [] (nth [] d i) (if o then 1 else 0)

/-- The scalar coverage data of a table: the angle scale, the gap, per role the base angle and
the difference range, and the number of arctangent intervals. -/
def CoverCtx.checkScalars (M : AffineTableMeta) (C : CoverCtx) : Bool :=
  decide (0 < C.den) && C.gap.wider (FI.ofQI ⟨19/25, 710/113-114/25⟩) &&
    decide (∀ i : Fin 7,
      (nth ⟨0, 0⟩ C.base i).wider (FI.ofQI (AffineCover.baseBox M i)) = true ∧
      ((nth 0 C.dLo i : Int) : ℚ) = (M.differenceRange i).lo * (unit * C.den) ∧
      ((nth 0 C.dHi i : Int) : ℚ) = (M.differenceRange i).hi * (unit * C.den)) &&
    (C.alphas.length == M.arcs.length)

/-- The coverage data of a table are valid, from the scalar check and the checks of the
arctangent intervals in blocks. -/
theorem CoverCtx.valid_of {M : AffineTableMeta} {C : CoverCtx}
    {S : StateChains} (hs : C.checkScalars M = true)
    {blocks : List (Nat × Nat)} (hcov : blocksCover 0 blocks M.arcs.length = true)
    (hb : AllBlocks (fun s c => alphasRange M.arcs C.alphas s c = true) blocks) :
    C.Valid ⟨atanEnds M, S⟩ M ∧ C.alphas.length = M.arcs.length := by
  simp only [CoverCtx.checkScalars, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  obtain ⟨⟨⟨hden, hgap⟩, hrole⟩, hlen⟩ := hs
  have hall : ∀ k < M.arcs.length,
      (nth ⟨0, 0⟩ C.alphas k).Covers (alphaOf (nth default M.arcs k)) :=
    forall_of_blocks hcov (AllBlocks.imp (fun s c h i h1 h2 => by
      simp only [alphasRange, List.all_eq_true, List.mem_range'_1] at h
      exact alphaFI_covers (h i ⟨h1, h2⟩)) hb)
  refine ⟨⟨hden, FI.covers_of_wider hgap, fun i => FI.covers_of_wider (hrole i).1,
    fun i => ?_, fun i => ?_, fun k hk => ?_⟩, hlen⟩
  · have := congrArg (fun q : ℚ => (q : ℝ)) (hrole i).2.1
    push_cast at this
    exact this
  · have := congrArg (fun q : ℚ => (q : ℝ)) (hrole i).2.2
    push_cast at this
    exact this
  · rw [alphaBox_atanEnds M S hk]
    simpa [arcAt, nth_eq_getD] using hall k hk

end SquaresInCircles.Eight.Arithmetic
