module

public import SquaresInCircles.Eight.Arithmetic.TrigLin
public import SquaresInCircles.Eight.Arithmetic.AffineCoverage

/-!
# A fast check of one affine row

A row of an affine table claims a strict charged inequality for all states of two arcs and all
angles of an interval (`AffineTableRow.Claim`). After the axis reversal of `PreparedRow.core`
the claim follows from the Lagrangian bound `CoreRow.Positive`. In it the source term is
bounded below by a constant (`sourceLower`), and the base and the target term are of the form
`c₀ + c₁ u + c₂ sin u + c₃ cos u` in the angle `u`, so `trigPositive` and `trigNonneg` decide
every inequality the row needs. The circle mode bounds the norm by `√V ≤ (V / h + h) / 2` on
pieces of the angle interval, each with its own `h`.

All numbers are fixed-point intervals (`Fixed.FI`). The data of an arc are computed once per
table (`ArcBox`); a row is a record of natural numbers (`AffineRow`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic
open Fixed

namespace Fixed.FI

/-- The exact interval of `a / unit`. -/
def point (a : Int) : FI := ⟨a, a⟩

theorem mem_point_div (a : Int) : (point a).Mem ((a : ℝ) / unit) := ⟨le_rfl, le_rfl⟩

/-- An outward enclosure of `n / d`. -/
def ofDiv (n : Int) (d : Nat) : FI := ⟨ifloor (imul n unit) d, iceil (imul n unit) d⟩

theorem mem_ofDiv (n : Int) {d : Nat} (hd : 0 < d) : (ofDiv n d).Mem ((n : ℝ) / d) := by
  have hU := unit_pos_real
  have hdI : (0 : Int) < d := by exact_mod_cast hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold Mem ofDiv
  simp only [imul_eq, ifloor_eq _ hd, iceil_eq _ hd]
  constructor
  · rw [div_le_iff₀ hU, div_mul_eq_mul_div, le_div_iff₀ hdR]
    have h := Int.ediv_mul_le (n * unit) (ne_of_gt hdI)
    have h' : (((n * unit) / (d : Int) * (d : Int) : Int) : ℝ) ≤ ((n * unit : Int) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith
  · rw [le_div_iff₀ hU, div_mul_eq_mul_div, div_le_iff₀ hdR]
    have h := Int.ediv_mul_le (-(n * unit)) (ne_of_gt hdI)
    have h' : ((-(n * unit) / (d : Int) * (d : Int) : Int) : ℝ) ≤ ((-(n * unit) : Int) : ℝ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    linarith

/-- `I * n / d` for natural `n` and `d`, rounded outwards. -/
def scaleDiv (I : FI) (n d : Nat) : FI :=
  ⟨ifloor (imul I.lo (Int.ofNat n)) d, iceil (imul I.hi (Int.ofNat n)) d⟩

theorem mem_scaleDiv {I : FI} {x : ℝ} (hx : I.Mem x) (n : Nat) {d : Nat} (hd : 0 < d) :
    (scaleDiv I n d).Mem (x * n / d) := by
  have hU := unit_pos_real
  have hdI : (0 : Int) < d := by exact_mod_cast hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold Mem scaleDiv
  simp only [imul_eq, ifloor_eq _ hd, iceil_eq _ hd, Int.ofNat_eq_natCast]
  constructor
  · have h := Int.ediv_mul_le (I.lo * n) (ne_of_gt hdI)
    have h' : ((I.lo * n / (d : Int) * (d : Int) : Int) : ℝ) ≤ ((I.lo * n : Int) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    have hl : (I.lo : ℝ) / unit * n ≤ x * n := mul_le_mul_of_nonneg_right hx.1 hn
    rw [div_le_iff₀ hU, div_mul_eq_mul_div, le_div_iff₀ hdR]
    rw [div_mul_eq_mul_div, div_le_iff₀ hU] at hl
    nlinarith
  · have h := Int.ediv_mul_le (-(I.hi * n)) (ne_of_gt hdI)
    have h' : ((-(I.hi * n) / (d : Int) * (d : Int) : Int) : ℝ) ≤ ((-(I.hi * n) : Int) : ℝ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    have hl : x * n ≤ (I.hi : ℝ) / unit * n := mul_le_mul_of_nonneg_right hx.2 hn
    rw [le_div_iff₀ hU, div_mul_eq_mul_div, div_le_iff₀ hdR]
    rw [div_mul_eq_mul_div, le_div_iff₀ hU] at hl
    nlinarith

/-- `J ⊆ I`. -/
def wider (I J : FI) : Bool := ile I.lo J.lo && ile J.hi I.hi

theorem mem_of_wider {I J : FI} (h : wider I J = true) {x : ℝ} (hx : J.Mem x) : I.Mem x := by
  simp only [wider, ile_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  have hU := unit_pos_real
  have h1 : (I.lo : ℝ) ≤ J.lo := by exact_mod_cast h.1
  have h2 : (J.hi : ℝ) ≤ I.hi := by exact_mod_cast h.2
  exact ⟨(div_le_div_of_nonneg_right h1 hU.le).trans hx.1,
    hx.2.trans (div_le_div_of_nonneg_right h2 hU.le)⟩

end Fixed.FI

/-- The `i`-th element of a list, by its recursor, which the kernel evaluates directly. -/
def nth {α : Type} (d : α) (l : List α) (i : Nat) : α :=
  (List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun b _ ih k => Nat.rec (motive := fun _ => α) b (fun j _ => ih j) k) l) i

theorem nth_eq_getD {α : Type} (d : α) (l : List α) (i : Nat) : nth d l i = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons b l ih =>
      cases i with
      | zero => rfl
      | succ i => exact (ih i).trans (by simp)

/-! ### Rows and arcs -/

/-- A row of an affine table in natural numbers. The angle interval is `[lo / den, hi / den]`
for the angle scale `den` of the table, the multiplier is `lam / 10 ^ 8` and the radical
parameter `rad / 10 ^ 7`; `axis` is `1, …, 4` and `mode` is `0` (endpoints), `1` (lower),
`2` (upper) or `3` (circle). A circle row lists pieces `(h, upto)`: consecutive angle
intervals, the `j`-th ending at `upto / den`, with the parameter `h / 10 ^ 7`. -/
structure AffineRow where
  edge : Nat
  source : Nat
  target : Nat
  axis : Nat
  quarter : Nat
  positive : Bool
  lo : Nat
  hi : Nat
  lam : Nat
  mode : Nat
  rad : Nat
  pieces : List (Nat × Nat)

def axisOf : Nat → ForwardAxis
  | 1 => .one
  | 2 => .two
  | 3 => .three
  | _ => .four

def modeOf : Nat → SupportMode
  | 0 => .endpoints
  | 1 => .lower
  | 2 => .upper
  | _ => .circle

/-- The table row a record denotes; its lower target is the target of its edge. -/
def AffineRow.toTableRow (M : AffineTableMeta) (den : Nat) (x : AffineRow) : AffineTableRow where
  edge := Fin.ofNat 7 x.edge
  source := x.source
  target := x.target
  axis := axisOf x.axis
  quarter := x.quarter
  positiveHalf := x.positive
  angle := ⟨(x.lo : ℚ) / den, (x.hi : ℚ) / den⟩
  multiplier := (x.lam : ℚ) / 10 ^ 8
  mode := modeOf x.mode
  radicalParameter := (x.rad : ℚ) / 10 ^ 7
  lowerTarget := M.target (Fin.ofNat 7 x.edge)

/-- Fixed-point data of an arc: the side flag, the sign, the label, the circle (shift and
radius), the prepared endpoints and the slope ratios at them. -/
structure ArcBox where
  side : Bool
  positive : Bool
  c : FI
  p : FI
  q : FI
  shift : FI
  rho : FI
  aLo : FI
  bLo : FI
  aHi : FI
  bHi : FI
  rLo : FI
  rHi : FI

instance : Inhabited ArcBox :=
  ⟨⟨false, false, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩,
    ⟨0, 0⟩, ⟨0, 0⟩⟩⟩

/-- The box `i` of boxes stored in consecutive groups of 32: entry `i % 32` of group `i / 32`,
reached in at most `i / 32 + 31` steps of the list recursor. -/
def boxAt (B : List (List ArcBox)) (i : Nat) : ArcBox :=
  nth default (nth [] B (Nat.div i 32)) (Nat.mod i 32)

/-- The box of the reversed arc: opposite sign and label. -/
def ArcBox.reverse (B : ArcBox) : ArcBox :=
  { B with positive := !B.positive, c := B.c.neg, p := B.p.neg, q := B.q.neg }

/-- The box encloses the data of a prepared arc. -/
structure ArcBox.Encloses (B : ArcBox) (P : PreparedArc) : Prop where
  valid : P.NumericValid
  side : B.side = P.data.side
  positive : B.positive = P.data.positive
  c : B.c.Mem P.data.label.c
  p : B.p.Mem P.data.label.p
  q : B.q.Mem P.data.label.q
  shift : B.shift.Mem P.data.shift
  rho : B.rho.Mem P.radiusExpr.value
  aLo : B.aLo.Mem P.aLo.value
  bLo : B.bLo.Mem P.bLo.value
  aHi : B.aHi.Mem P.aHi.value
  bHi : B.bHi.Mem P.bHi.value
  rLo : B.rLo.Mem P.ratioLo.value
  rHi : B.rHi.Mem P.ratioHi.value

theorem ArcBox.Encloses.reverse {B : ArcBox} {P : PreparedArc} (h : B.Encloses P) :
    B.reverse.Encloses P.reverse where
  valid := h.valid
  side := h.side
  positive := by simp [ArcBox.reverse, PreparedArc.reverse, ArcData.reverse, h.positive]
  c := by
    simpa [ArcBox.reverse, PreparedArc.reverse, ArcData.reverse, AffineLabel.neg] using
      FI.mem_neg h.c
  p := by
    simpa [ArcBox.reverse, PreparedArc.reverse, ArcData.reverse, AffineLabel.neg] using
      FI.mem_neg h.p
  q := by
    simpa [ArcBox.reverse, PreparedArc.reverse, ArcData.reverse, AffineLabel.neg] using
      FI.mem_neg h.q
  shift := h.shift
  rho := h.rho
  aLo := h.aLo
  bLo := h.bLo
  aHi := h.aHi
  bHi := h.bHi
  rLo := h.rLo
  rHi := h.rHi

theorem PreparedArc.ofArc_data (Q : ℚ) (a : ArcData) : (PreparedArc.ofArc Q a).data = a := by
  unfold PreparedArc.ofArc
  split <;> rfl

theorem PreparedArc.ofArc_radius (Q : ℚ) (a : ArcData) :
    (PreparedArc.ofArc Q a).radius = Q := by
  unfold PreparedArc.ofArc
  split <;> rfl

/-- Compare a box with the rational enclosures of the prepared arc. -/
def ArcBox.check (Q : ℚ) (a : ArcData) (B : ArcBox) : Bool :=
  let P := PreparedArc.ofArc Q a
  decide P.NumericValid && (B.side == a.side) && (B.positive == a.positive) &&
    B.c.wider (FI.ofQ a.label.c) && B.p.wider (FI.ofQ a.label.p) &&
    B.q.wider (FI.ofQ a.label.q) && B.shift.wider (FI.ofQ a.shift) &&
    B.rho.wider (FI.ofQI (P.radiusExpr.range closedBoxes)) &&
    B.aLo.wider (FI.ofQI (P.aLo.range closedBoxes)) &&
    B.bLo.wider (FI.ofQI (P.bLo.range closedBoxes)) &&
    B.aHi.wider (FI.ofQI (P.aHi.range closedBoxes)) &&
    B.bHi.wider (FI.ofQI (P.bHi.range closedBoxes)) &&
    B.rLo.wider (FI.ofQI (P.ratioLo.range closedBoxes)) &&
    B.rHi.wider (FI.ofQI (P.ratioHi.range closedBoxes))

theorem ArcBox.check_sound {Q : ℚ} {a : ArcData} {B : ArcBox} (h : B.check Q a = true) :
    B.Encloses (PreparedArc.ofArc Q a) := by
  simp only [ArcBox.check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hs⟩, hp⟩, hc⟩, hP⟩, hq⟩, hsh⟩, hr⟩, haL⟩, hbL⟩, haH⟩, hbH⟩, hrL⟩,
    hrH⟩ := h
  have hd := PreparedArc.ofArc_data Q a
  set P := PreparedArc.ofArc Q a
  have sound (e : ScalarExpr 0) (he : e.Valid closedBoxes) :
      (FI.ofQI (e.range closedBoxes)).Mem e.value := FI.mem_ofQI (e.closed_sound he)
  exact
    { valid := hv
      side := by rw [hd]; exact hs
      positive := by rw [hd]; exact hp
      c := by rw [hd]; exact FI.mem_of_wider hc (FI.mem_ofQ _)
      p := by rw [hd]; exact FI.mem_of_wider hP (FI.mem_ofQ _)
      q := by rw [hd]; exact FI.mem_of_wider hq (FI.mem_ofQ _)
      shift := by rw [hd]; exact FI.mem_of_wider hsh (FI.mem_ofQ _)
      rho := FI.mem_of_wider hr (sound _ hv.2.2.2.2.1)
      aLo := FI.mem_of_wider haL (sound _ hv.2.2.1)
      bLo := FI.mem_of_wider hbL (sound _ (P.bLo_valid hv))
      aHi := FI.mem_of_wider haH (sound _ hv.2.2.2.1)
      bHi := FI.mem_of_wider hbH (sound _ (P.bHi_valid hv))
      rLo := FI.mem_of_wider hrL (sound _ (P.ratioLo_valid hv))
      rHi := FI.mem_of_wider hrH (sound _ (P.ratioHi_valid hv)) }

/-! ### The data of a table -/

/-- The fixed-point data of a table: the angle scale, the number of arcs, the arc boxes (in groups
of 32, see `boxAt`), and per edge half the charge and the target. -/
structure TableCtx where
  den : Nat
  n : Nat
  boxes : List (List ArcBox)
  betaHalf : List FI
  gamma : List FI

structure TableCtx.Valid (M : AffineTableMeta) (C : TableCtx) : Prop where
  den_pos : 0 < C.den
  n_eq : C.n = M.arcs.length
  boxes : ∀ i < C.n, (boxAt C.boxes i).Encloses
    (PreparedArc.ofArc M.radius (M.arcs.getD i default))
  beta : ∀ i : Fin 7, (nth (FI.point 0) C.betaHalf i).Mem ((M.charge i : ℝ) / 2)
  gamma : ∀ i : Fin 7, (nth (FI.point 0) C.gamma i).Mem (M.target i)

/-! ### Checks in blocks

A check over the indices `0, …, n - 1` is split into blocks `(start, count)`, each decided by a
theorem of its own, so that the kernel's memory stays small. -/

/-- The blocks are consecutive from `s` and end at `n`. -/
def blocksCover : Nat → List (Nat × Nat) → Nat → Bool
  | s, [], n => s == n
  | s, (a, c) :: rest, n => (a == s) && blocksCover (s + c) rest n

/-- `p` holds on every block. -/
def AllBlocks (p : Nat → Nat → Prop) : List (Nat × Nat) → Prop
  | [] => True
  | (a, c) :: rest => p a c ∧ AllBlocks p rest

theorem blocksCover_mem {n : Nat} : ∀ {s : Nat} {blocks : List (Nat × Nat)},
    blocksCover s blocks n = true → ∀ i, s ≤ i → i < n → ∃ b ∈ blocks, b.1 ≤ i ∧ i < b.1 + b.2
  | s, [], h, i, h1, h2 => by
      simp only [blocksCover, beq_iff_eq] at h
      omega
  | s, (a, c) :: rest, h, i, h1, h2 => by
      simp only [blocksCover, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      by_cases hi : i < a + c
      · exact ⟨(a, c), List.mem_cons_self, h1, hi⟩
      · obtain ⟨b, hb, hb'⟩ := blocksCover_mem h i (by omega) h2
        exact ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

theorem AllBlocks.of_mem {p : Nat → Nat → Prop} :
    ∀ {blocks : List (Nat × Nat)}, AllBlocks p blocks → ∀ b ∈ blocks, p b.1 b.2
  | [], _, b, hb => absurd hb List.not_mem_nil
  | (a, c) :: rest, h, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h.1
      · exact AllBlocks.of_mem h.2 b hb

theorem AllBlocks.imp {p q : Nat → Nat → Prop} (h : ∀ a c, p a c → q a c) :
    ∀ {blocks : List (Nat × Nat)}, AllBlocks p blocks → AllBlocks q blocks
  | [], _ => trivial
  | (a, c) :: _, hb => ⟨h a c hb.1, AllBlocks.imp h hb.2⟩

/-- A property of every index below `n`, from blocks covering `[0, n)`. -/
theorem forall_of_blocks {p : Nat → Prop} {n : Nat} {blocks : List (Nat × Nat)}
    (hcov : blocksCover 0 blocks n = true)
    (hb : AllBlocks (fun a c => ∀ i, a ≤ i → i < a + c → p i) blocks) : ∀ i < n, p i := by
  intro i hi
  obtain ⟨b, hmem, h1, h2⟩ := blocksCover_mem hcov i (Nat.zero_le _) hi
  exact AllBlocks.of_mem hb b hmem i h1 h2

/-- The boxes `s, …, s + c - 1` enclose their prepared arcs. -/
def boxesRange (Q : ℚ) (arcs : List ArcData) (boxes : List (List ArcBox)) (s c : Nat) : Bool :=
  (List.range' s c).all fun i => (boxAt boxes i).check Q (nth default arcs i)

theorem boxesRange_sound {Q : ℚ} {arcs : List ArcData} {boxes : List (List ArcBox)} {s c : Nat}
    (h : boxesRange Q arcs boxes s c = true) :
    ∀ i, s ≤ i → i < s + c →
      (boxAt boxes i).Encloses (PreparedArc.ofArc Q (arcs.getD i default)) := by
  intro i h1 h2
  simp only [boxesRange, List.all_eq_true, List.mem_range'_1] at h
  rw [← nth_eq_getD]
  exact ArcBox.check_sound (h i ⟨h1, h2⟩)

/-- The scalar data of a table: the angle scale, the number of arcs, half the charge and the
target of every edge. -/
def TableCtx.checkScalars (M : AffineTableMeta) (C : TableCtx) : Bool :=
  decide (0 < C.den) && (C.n == M.arcs.length) &&
    decide (∀ i : Fin 7, (nth (FI.point 0) C.betaHalf i).wider (FI.ofQ (M.charge i / 2)) = true ∧
      (nth (FI.point 0) C.gamma i).wider (FI.ofQ (M.target i)) = true)

/-- The data of a table are valid, from its scalar check and the box checks in blocks. -/
theorem TableCtx.valid_of {M : AffineTableMeta} {C : TableCtx} (hs : C.checkScalars M = true)
    {blocks : List (Nat × Nat)} (hcov : blocksCover 0 blocks C.n = true)
    (hb : AllBlocks (fun a c => boxesRange M.radius M.arcs C.boxes a c = true) blocks) :
    C.Valid M := by
  simp only [TableCtx.checkScalars, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  obtain ⟨⟨hden, hn⟩, he⟩ := hs
  refine ⟨hden, hn, ?_, fun i => ?_, fun i => ?_⟩
  · refine forall_of_blocks hcov ?_
    have : ∀ blocks : List (Nat × Nat),
        AllBlocks (fun a c => boxesRange M.radius M.arcs C.boxes a c = true) blocks →
        AllBlocks (fun a c => ∀ i, a ≤ i → i < a + c → (boxAt C.boxes i).Encloses
          (PreparedArc.ofArc M.radius (M.arcs.getD i default))) blocks := by
      intro blocks
      induction blocks with
      | nil => exact fun _ => trivial
      | cons b rest ih => exact fun h => ⟨boxesRange_sound h.1, ih h.2⟩
    exact this blocks hb
  · have hm := FI.mem_ofQ (M.charge i / 2)
    push_cast at hm
    exact FI.mem_of_wider (he i).1 hm
  · exact FI.mem_of_wider (he i).2 (FI.mem_ofQ _)

/-! ### Reading the data -/

/-- The circle pieces `h₁ c₁ h₂ c₂ … h_m`: the `j`-th piece ends at `c_j`, the last at `hi`. -/
def piecesOf (hi : Nat) : List Nat → List (Nat × Nat)
  | [] => []
  | [h] => [(h, hi)]
  | h :: c :: rest => (h, c) :: piecesOf hi rest

/-- A row from its data line `edge source target axis k r lo hi lam mode`, followed for a circle
row by its radical parameter and its pieces. -/
def AffineRow.ofData (edge source target axis quarter r lo hi lam mode : Nat)
    (rest : List Nat) : AffineRow :=
  ⟨edge, source, target, axis, quarter, r == 1, lo, hi, lam, mode, rest.headD 10000000,
    piecesOf hi rest.tail⟩

/-- An arc box from its data line: `side positive`, then the intervals
`c p q shift rho aLo bLo aHi bHi rLo rHi` and the angle interval of the arc (not part of the
box). -/
def ArcBox.ofData (side positive c0 c1 p0 p1 q0 q1 s0 s1 r0 r1 al0 al1 bl0 bl1 ah0 ah1 bh0 bh1
    rl0 rl1 rh0 rh1 _α0 _α1 : Int) : ArcBox :=
  ⟨side == 1, positive == 1, ⟨c0, c1⟩, ⟨p0, p1⟩, ⟨q0, q1⟩, ⟨s0, s1⟩, ⟨r0, r1⟩, ⟨al0, al1⟩,
    ⟨bl0, bl1⟩, ⟨ah0, ah1⟩, ⟨bh0, bh1⟩, ⟨rl0, rl1⟩, ⟨rh0, rh1⟩⟩

/-- A row's claim for larger targets gives its claim for the targets of the table. -/
theorem AffineRow.claim_of_target_le {M : AffineTableMeta} {t : Fin 7 → ℚ} {den : Nat}
    {x : AffineRow} (ht : M.target (Fin.ofNat 7 x.edge) ≤ t (Fin.ofNat 7 x.edge))
    (h : (x.toTableRow {M with target := t} den).Claim {M with target := t}) :
    (x.toTableRow M den).Claim M := by
  intro a b A B u hdom hm
  have ht' : (M.target (Fin.ofNat 7 x.edge) : ℝ) ≤ t (Fin.ofNat 7 x.edge) := by
    exact_mod_cast ht
  exact lt_of_le_of_lt ht' (h a b A B u hdom hm)

/-! ### The circle bound and the source support -/

/-- `√V ≤ (V / h + h) / 2`. -/
theorem sqrt_le_amgm {V h : ℝ} (hV : 0 ≤ V) (hh : 0 < h) : Real.sqrt V ≤ (V / h + h) / 2 := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 ≤ s ∧ V = s ^ 2 :=
    ⟨_, Real.sqrt_nonneg V, (Real.sq_sqrt hV).symm⟩
  rw [Real.sqrt_sq hs0]
  have key : (s ^ 2 / h + h) / 2 - s = (s - h) ^ 2 / (2 * h) := by
    field_simp
    ring
  have : 0 ≤ (s - h) ^ 2 / (2 * h) := by positivity
  linarith

/-- On the circle of a non-side arc, `X x + Y y ≥ v (X + Y) - ρ w` for every `w ≥ √(X² + Y²)`. -/
theorem PreparedArc.circle_lower {P : PreparedArc} (hP : P.NumericValid)
    (hs : P.data.side = false) {x y X Y w : ℝ} (hxy : P.data.Contains P.radius x y)
    (hw : Real.sqrt (X ^ 2 + Y ^ 2) ≤ w) :
    (P.data.shift : ℝ) * (X + Y) - P.radiusExpr.value * w ≤ X * x + Y * y := by
  have hf := P.circleFacts hP hs hxy
  have hρ : 0 ≤ P.radiusExpr.value := by
    rw [PreparedArc.radiusExpr_value]
    split_ifs <;> positivity
  have hc := full_circle_lower hρ hf.point_circle (X := X) (Y := Y)
  have hm := mul_le_mul_of_nonneg_left hw hρ
  linarith

/-- `⌈a / b⌉`. -/
def cdiv (a b : Int) : Int := -((-a) / b)

theorem le_cdiv (a : Int) {b : Int} (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have h := Int.ediv_mul_le (-a) (ne_of_gt hb)
  have h' : (((-a) / b * b : Int) : ℝ) ≤ ((-a : Int) : ℝ) := by exact_mod_cast h
  push_cast at h'
  unfold cdiv
  push_cast
  rw [div_le_iff₀ hbR]
  linarith

/-- Newton steps for `√m`, decreasing from a starting value above it. -/
def newton (m : Int) : Nat → Int → Int
  | 0, h => h
  | n + 1, h => newton m n ((m / h + h) / 2)

/-- An upper bound of `√V` over `unit`, from `√V ≤ (V / h + h) / 2`; `h` comes from five Newton
steps started at `guess`. -/
def sqrtUp (V : FI) (guess : Int) : Int :=
  let h := max 1 (newton (V.hi * unit) 5 guess)
  cdiv (cdiv (V.hi * unit) h + h) 2

theorem sqrtUp_sound {V : FI} {v : ℝ} (hv : V.Mem v) (hv0 : 0 ≤ v) (guess : Int) :
    Real.sqrt v ≤ (sqrtUp V guess : ℝ) / unit := by
  have hU := unit_pos_real
  set h : Int := max 1 (newton (V.hi * unit) 5 guess) with hh
  have h1 : (1 : Int) ≤ h := le_max_left _ _
  have hpos : (0 : Int) < h := by omega
  have hR : (0 : ℝ) < h := by exact_mod_cast hpos
  have hamgm := sqrt_le_amgm hv0 (show (0 : ℝ) < h / unit by positivity)
  set q : Int := cdiv (V.hi * unit) h
  have hq := le_cdiv (V.hi * unit) hpos
  have hr := le_cdiv (q + h) (show (0 : Int) < 2 by norm_num)
  have hsq : sqrtUp V guess = cdiv (q + h) 2 := rfl
  rw [hsq]
  have hvh : v / (h / unit) ≤ (q : ℝ) / unit := by
    rw [div_div_eq_mul_div, div_le_div_iff₀ hR hU]
    have hv2 : v * unit ≤ V.hi := by
      have := hv.2
      rwa [le_div_iff₀ hU] at this
    push_cast at hq
    rw [div_le_iff₀ hR] at hq
    nlinarith
  push_cast at hr
  calc Real.sqrt v ≤ (v / (h / unit) + h / unit) / 2 := hamgm
    _ ≤ ((q : ℝ) / unit + h / unit) / 2 := by linarith
    _ = ((q : ℝ) + h) / 2 / unit := by ring
    _ ≤ _ := by gcongr

/-- A lower bound, as an integer over `unit`, of `X a + Y b` on the arc of `S`: from the two
endpoints when `X ≥ 0` or the arc is a side; from the lower or the upper endpoint when the slope
`Y - X r` has one sign at both ends; otherwise from the whole circle. -/
def sourceLower (S : ArcBox) (X Y : FI) : Int :=
  bif S.side || ile (Int.ofNat 0) X.lo then
    imin ((X.mul S.aLo).add (Y.mul S.bLo)).lo ((X.mul S.aHi).add (Y.mul S.bHi)).lo
  else bif ile (Int.ofNat 0) (Y.sub (X.mul S.rLo)).lo &&
      ile (Int.ofNat 0) (Y.sub (X.mul S.rHi)).lo then
    ((X.mul S.aLo).add (Y.mul S.bLo)).lo
  else bif ile (Y.sub (X.mul S.rLo)).hi (Int.ofNat 0) &&
      ile (Y.sub (X.mul S.rHi)).hi (Int.ofNat 0) then
    ((X.mul S.aHi).add (Y.mul S.bHi)).lo
  else
    ((S.shift.mul (X.add Y)).sub (S.rho.mul ⟨0, sqrtUp ((X.mul X).add (Y.mul Y))
      ((X.lo.natAbs + X.hi.natAbs + Y.lo.natAbs + Y.hi.natAbs : Nat) + 1000000000000)⟩)).lo

theorem sourceLower_sound {S : ArcBox} {P : PreparedArc} (hS : S.Encloses P) {X Y : FI}
    {x y : ℝ} (hX : X.Mem x) (hY : Y.Mem y) {a b : ℝ} (hab : P.data.Contains P.radius a b) :
    ((sourceLower S X Y : Int) : ℝ) / unit ≤ x * a + y * b := by
  have hU := unit_pos_real
  have hL := FI.mem_add (FI.mem_mul hX hS.aLo) (FI.mem_mul hY hS.bLo)
  have hH := FI.mem_add (FI.mem_mul hX hS.aHi) (FI.mem_mul hY hS.bHi)
  have hdL := FI.mem_sub hY (FI.mem_mul hX hS.rLo)
  have hdH := FI.mem_sub hY (FI.mem_mul hX hS.rHi)
  simp only [sourceLower, ile_eq, imin_eq, Bool.cond_eq_ite, Int.ofNat_eq_natCast,
    Nat.cast_zero]
  split_ifs with h1 h2 h3
  · have hmode : P.data.side = true ∨ 0 ≤ x := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
      rcases h1 with h | h
      · left
        rw [← hS.side]
        exact h
      · right
        exact (div_nonneg (by exact_mod_cast h) hU.le).trans hX.1
    apply P.endpoints_lower hS.valid hab hmode
    · refine le_trans ?_ hL.1
      gcongr
      exact_mod_cast min_le_left _ _
    · refine le_trans ?_ hH.1
      gcongr
      exact_mod_cast min_le_right _ _
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    have hl : 0 ≤ y - x * P.ratioLo.value :=
      (div_nonneg (by exact_mod_cast h2.1) hU.le).trans hdL.1
    have hu : 0 ≤ y - x * P.ratioHi.value :=
      (div_nonneg (by exact_mod_cast h2.2) hU.le).trans hdH.1
    exact hL.1.trans (P.lower_endpoint hS.valid hab (by linarith) (by linarith))
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    have hl : y - x * P.ratioLo.value ≤ 0 :=
      hdL.2.trans (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h3.1) hU.le)
    have hu : y - x * P.ratioHi.value ≤ 0 :=
      hdH.2.trans (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h3.2) hU.le)
    exact hH.1.trans (P.upper_endpoint hS.valid hab (by linarith) (by linarith))
  · have hside : P.data.side = false := by
      rw [← hS.side]
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at h1
      exact h1.1
    have hV := FI.mem_add (FI.mem_mul hX hX) (FI.mem_mul hY hY)
    have hroot := sqrtUp_sound hV (add_nonneg (mul_self_nonneg x) (mul_self_nonneg y))
      ((X.lo.natAbs + X.hi.natAbs + Y.lo.natAbs + Y.hi.natAbs : Nat) + 1000000000000)
    have hw : (FI.mk 0 (sqrtUp ((X.mul X).add (Y.mul Y))
        ((X.lo.natAbs + X.hi.natAbs + Y.lo.natAbs + Y.hi.natAbs : Nat) + 1000000000000))).Mem
        (Real.sqrt (x ^ 2 + y ^ 2)) := by
      refine ⟨by simp, ?_⟩
      rw [show x ^ 2 + y ^ 2 = x * x + y * y by ring]
      exact hroot
    have hv := FI.mem_sub (FI.mem_mul hS.shift (FI.mem_add hX hY)) (FI.mem_mul hS.rho hw)
    exact hv.1.trans (P.circle_lower hS.valid hside hab le_rfl)


/-! ### The angle, the base and the target coefficients -/

/-- `1` or `-1`. -/
def sgnR (b : Bool) : ℝ := if b then 1 else -1

theorem sgnR_sq (b : Bool) : sgnR b ^ 2 = 1 := by cases b <;> norm_num [sgnR]

theorem signQ_eq_sgnR (b : Bool) : (AnglePolynomial.signQ b : ℝ) = sgnR b := by
  cases b <;> simp [AnglePolynomial.signQ, sgnR]

theorem sign_eq_sgnR (a : ArcData) : a.sign = sgnR a.positive := by
  cases h : a.positive <;> simp [ArcData.sign, sgnR, h]

/-- `-1` on the quarters two and three, `1` on the quarters zero and one. -/
def flipR (f : Bool) : ℝ := if f then -1 else 1

theorem phi_add_two (k : ℕ) (s : Bool) (u : ℝ) :
    AnglePolynomial.phi (k + 2) s u = AnglePolynomial.phi k s u + Real.pi := by
  simp only [AnglePolynomial.phi]
  push_cast
  ring

/-- `sin φ` and `cos φ` for `φ = k π / 2 ± u`, `k ≤ 3`: the quarters two and three are the
quarters zero and one turned by `π`. -/
theorem phi_sin_cos {k : ℕ} (hk : k ≤ 3) (s : Bool) (u : ℝ) :
    Real.sin (AnglePolynomial.phi k s u) =
      flipR (k / 2 == 1) * (if k % 2 = 1 then Real.cos u else sgnR s * Real.sin u) ∧
    Real.cos (AnglePolynomial.phi k s u) =
      flipR (k / 2 == 1) * (if k % 2 = 1 then -(sgnR s * Real.sin u) else Real.cos u) := by
  have h01 : ∀ j ≤ 1, Real.sin (AnglePolynomial.phi j s u) =
      (if j % 2 = 1 then Real.cos u else sgnR s * Real.sin u) ∧
      Real.cos (AnglePolynomial.phi j s u) =
      (if j % 2 = 1 then -(sgnR s * Real.sin u) else Real.cos u) := by
    intro j hj
    interval_cases j <;> cases s <;>
      simp [AnglePolynomial.phi, AnglePolynomial.signQ, sgnR, Real.sin_add, Real.cos_add]
  interval_cases k
  · simpa [flipR] using h01 0 (by norm_num)
  · simpa [flipR] using h01 1 (by norm_num)
  · obtain ⟨h1, h2⟩ := h01 0 (by norm_num)
    have e : AnglePolynomial.phi 2 s u = AnglePolynomial.phi 0 s u + Real.pi := phi_add_two 0 s u
    rw [e, Real.sin_add_pi, Real.cos_add_pi, h1, h2]
    simp [flipR]
  · obtain ⟨h1, h2⟩ := h01 1 (by norm_num)
    have e : AnglePolynomial.phi 3 s u = AnglePolynomial.phi 1 s u + Real.pi := phi_add_two 1 s u
    rw [e, Real.sin_add_pi, Real.cos_add_pi, h1, h2]
    simp [flipR]

/-- `|sin φ| + |cos φ| = sin u + cos u` for `0 ≤ u ≤ 1`. -/
theorem abs_sin_add_abs_cos {k : ℕ} (hk : k ≤ 3) (s : Bool) {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    |Real.sin (AnglePolynomial.phi k s u)| + |Real.cos (AnglePolynomial.phi k s u)| =
      Real.sin u + Real.cos u := by
  have hpi := Real.pi_gt_three
  have hS : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu.1 (by linarith)
  have hC : 0 ≤ Real.cos u :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  obtain ⟨h1, h2⟩ := phi_sin_cos hk s u
  rw [h1, h2]
  interval_cases k <;> cases s <;>
    simp [flipR, sgnR, abs_of_nonneg hS, abs_of_nonneg hC, add_comm]

/-- The multiple of `g` in `X = -p + x_a g`. -/
def xaR (four k1 flip sgn : Bool) (lam : ℝ) : ℝ :=
  flipR flip * (if four then (if k1 then -(sgnR sgn * lam) else lam)
    else (if k1 then -lam else -(sgnR sgn * lam)))

/-- The multiple of `g'` in `Y = -q + y_a g'`. -/
def yaR (four k1 flip sgn tau : Bool) (lam : ℝ) : ℝ :=
  flipR flip * (if four then (if k1 then sgnR tau * lam else sgnR tau * (sgnR sgn * lam))
    else (if k1 then -(sgnR tau * (sgnR sgn * lam)) else sgnR tau * lam))

/-- `g = sin` and `g' = cos` when `xs`, the other way round otherwise. -/
def gS (xs : Bool) (u : ℝ) : ℝ := if xs then Real.sin u else Real.cos u
def gC (xs : Bool) (u : ℝ) : ℝ := if xs then Real.cos u else Real.sin u

theorem gS_sq_add_gC_sq (xs : Bool) (u : ℝ) : gS xs u ^ 2 + gC xs u ^ 2 = 1 := by
  cases xs <;> simp [gS, gC, Real.sin_sq_add_cos_sq, Real.cos_sq_add_sin_sq]

theorem xaR_sq (four k1 flip sgn : Bool) (lam : ℝ) : xaR four k1 flip sgn lam ^ 2 = lam ^ 2 := by
  cases four <;> cases k1 <;> cases flip <;> cases sgn <;> simp [xaR, sgnR, flipR]

theorem yaR_sq (four k1 flip sgn tau : Bool) (lam : ℝ) :
    yaR four k1 flip sgn tau lam ^ 2 = lam ^ 2 := by
  cases four <;> cases k1 <;> cases flip <;> cases sgn <;> cases tau <;> simp [yaR, sgnR, flipR]

/-- The target coefficients of the Lagrangian on the core axes one and four. -/
theorem target_lin (four : Bool) {k : ℕ} (hk : k ≤ 3) (s tau : Bool) (L : AffineLabel)
    (lam u : ℝ) :
    targetX (if four then .four else .one) L lam (AnglePolynomial.phi k s u) =
      -(L.p : ℝ) + xaR four (k % 2 == 1) (k / 2 == 1) s lam * gS (four == (k % 2 == 1)) u ∧
    targetY (if four then .four else .one) L lam (sgnR tau) (AnglePolynomial.phi k s u) =
      -(L.q : ℝ) + yaR four (k % 2 == 1) (k / 2 == 1) s tau lam * gC (four == (k % 2 == 1)) u := by
  obtain ⟨hs, hc⟩ := phi_sin_cos hk s u
  interval_cases k <;> cases four <;> cases s <;> cases tau <;>
    simp [targetX, targetY, hs, hc, xaR, yaR, gS, gC, sgnR, flipR] <;> ring

/-- The base of the Lagrangian, from `|sin φ| + |cos φ| = sin u + cos u`. -/
theorem base_lin {k : ℕ} (hk : k ≤ 3) (s : Bool) (Ls Lt : AffineLabel) (lam β : ℝ) {u : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1) :
    lagrangianBase Ls Lt lam β (AnglePolynomial.phi k s u) =
      (k : ℝ) * (Real.pi / 2) + sgnR s * u + Ls.c - Lt.c + lam / 2 + β / 2 +
        (lam / 2 - β / 2) * (Real.sin u + Real.cos u) := by
  have ha := abs_sin_add_abs_cos hk s hu
  unfold lagrangianBase frameWidth frameCharge
  have hcos : |Real.cos (AnglePolynomial.phi k s u)| =
      Real.sin u + Real.cos u - |Real.sin (AnglePolynomial.phi k s u)| := by linarith
  rw [hcos]
  have hphi : AnglePolynomial.phi k s u = (k : ℝ) * (Real.pi / 2) + sgnR s * u := by
    rw [AnglePolynomial.phi, signQ_eq_sgnR]
    ring
  rw [hphi]
  ring

/-! ### Fixed-point coefficients -/

/-- The interval of `1` or `-1`. -/
def sgnBox (b : Bool) : FI := bif b then FI.point unit else FI.point (ineg unit)

theorem mem_sgnBox (b : Bool) : (sgnBox b).Mem (sgnR b) := by
  have hU := unit_pos_real
  cases b <;> simp [sgnBox, sgnR, FI.point, FI.Mem, ne_of_gt hU]

theorem mem_zero : (FI.point 0).Mem 0 := by simp [FI.point, FI.Mem]

def xaF (four k1 flip sgn : Bool) (lam : FI) : FI :=
  let v := bif four then (bif k1 then (bif sgn then lam.neg else lam) else lam)
    else (bif k1 then lam.neg else (bif sgn then lam.neg else lam))
  bif flip then v.neg else v

def yaF (four k1 flip sgn tau : Bool) (lam : FI) : FI :=
  let e := bif tau then sgn else !sgn
  let v := bif four then (bif k1 then (bif tau then lam else lam.neg)
      else (bif e then lam else lam.neg))
    else (bif k1 then (bif e then lam.neg else lam) else (bif tau then lam else lam.neg))
  bif flip then v.neg else v

theorem mem_xaF (four k1 flip sgn : Bool) {lam : FI} {l : ℝ} (h : lam.Mem l) :
    (xaF four k1 flip sgn lam).Mem (xaR four k1 flip sgn l) := by
  have hn := FI.mem_neg h
  have hnn := FI.mem_neg hn
  cases four <;> cases k1 <;> cases flip <;> cases sgn <;>
    simp [xaF, xaR, sgnR, flipR] <;> first | exact h | exact hn | simpa using hnn

theorem mem_yaF (four k1 flip sgn tau : Bool) {lam : FI} {l : ℝ} (h : lam.Mem l) :
    (yaF four k1 flip sgn tau lam).Mem (yaR four k1 flip sgn tau l) := by
  have hn := FI.mem_neg h
  have hnn := FI.mem_neg hn
  cases four <;> cases k1 <;> cases flip <;> cases sgn <;> cases tau <;>
    simp [yaF, yaR, sgnR, flipR] <;> first | exact h | exact hn | simpa using hnn

/-- Three coefficient intervals enclose three reals. -/
def Mem3 (t : FI × FI × FI) (r : ℝ × ℝ × ℝ) : Prop :=
  t.1.Mem r.1 ∧ t.2.1.Mem r.2.1 ∧ t.2.2.Mem r.2.2

/-- `t₀ + c₁ u + t₁ sin u + t₂ cos u > 0` on `[lo / den, hi / den]`. -/
def pos3 (den lo hi : Nat) (c1 : FI) (t : FI × FI × FI) : Bool :=
  trigPositive den lo hi t.1 c1 t.2.1 t.2.2

/-- A bound of the absolute values of the reals of `I`, over `unit`. -/
def Fixed.FI.mag (I : FI) : Int := imax (ineg I.lo) I.hi

theorem Fixed.FI.abs_le_mag {I : FI} {x : ℝ} (hx : I.Mem x) : |x| ≤ (I.mag : ℝ) / unit := by
  have hU := unit_pos_real
  have hm : I.mag = max (-I.lo) I.hi := by simp [Fixed.FI.mag]
  have h1 : ((-I.lo : Int) : ℝ) / unit ≤ (I.mag : ℝ) / unit :=
    div_le_div_of_nonneg_right (by rw [hm]; exact_mod_cast le_max_left _ _) hU.le
  have h2 : ((I.hi : Int) : ℝ) / unit ≤ (I.mag : ℝ) / unit :=
    div_le_div_of_nonneg_right (by rw [hm]; exact_mod_cast le_max_right _ _) hU.le
  push_cast at h1
  rw [neg_div] at h1
  rw [abs_le]
  constructor
  · linarith [hx.1]
  · linarith [hx.2]

/-- `t₀ ≥ |t₁| + |t₂|`, enough for `t₀ + t₁ sin u + t₂ cos u ≥ 0` at every `u`. -/
def crude3 (t : FI × FI × FI) : Bool := ile (iadd t.2.1.mag t.2.2.mag) t.1.lo

/-- `t₀ + t₁ sin u + t₂ cos u ≥ 0` on `[lo / den, hi / den]`: by `crude3`, or by the trigonometric
test. -/
def nonneg3 (den lo hi : Nat) (t : FI × FI × FI) : Bool :=
  crude3 t || trigNonneg den lo hi t.1 (FI.point 0) t.2.1 t.2.2

theorem pos3_sound {den lo hi : Nat} {c1 : FI} {t : FI × FI × FI} (h : pos3 den lo hi c1 t = true)
    {c1r : ℝ} {r : ℝ × ℝ × ℝ} (hc1 : c1.Mem c1r) (hr : Mem3 t r) {u : ℝ}
    (hu : (lo : ℝ) / den ≤ u ∧ u ≤ (hi : ℝ) / den) :
    0 < r.1 + c1r * u + r.2.1 * Real.sin u + r.2.2 * Real.cos u :=
  trigPositive_sound h hr.1 hc1 hr.2.1 hr.2.2 hu

theorem nonneg3_sound {den lo hi : Nat} {t : FI × FI × FI} (h : nonneg3 den lo hi t = true)
    {r : ℝ × ℝ × ℝ} (hr : Mem3 t r) {u : ℝ} (hu : (lo : ℝ) / den ≤ u ∧ u ≤ (hi : ℝ) / den) :
    0 ≤ r.1 + r.2.1 * Real.sin u + r.2.2 * Real.cos u := by
  simp only [nonneg3, Bool.or_eq_true] at h
  rcases h with hc | h
  · have hU := unit_pos_real
    simp only [crude3, ile_eq, iadd_eq, decide_eq_true_eq] at hc
    have ha := FI.abs_le_mag hr.2.1
    have hb := FI.abs_le_mag hr.2.2
    have hs : -|r.2.1| ≤ r.2.1 * Real.sin u := by
      have := abs_mul r.2.1 (Real.sin u)
      have h1 := Real.abs_sin_le_one u
      have h2 : |r.2.1 * Real.sin u| ≤ |r.2.1| := by
        rw [this]; exact mul_le_of_le_one_right (abs_nonneg _) h1
      linarith [neg_abs_le (r.2.1 * Real.sin u)]
    have hc' : -|r.2.2| ≤ r.2.2 * Real.cos u := by
      have := abs_mul r.2.2 (Real.cos u)
      have h1 := Real.abs_cos_le_one u
      have h2 : |r.2.2 * Real.cos u| ≤ |r.2.2| := by
        rw [this]; exact mul_le_of_le_one_right (abs_nonneg _) h1
      linarith [neg_abs_le (r.2.2 * Real.cos u)]
    have hk : ((t.2.1.mag + t.2.2.mag : Int) : ℝ) / unit ≤ (t.1.lo : ℝ) / unit :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc) hU.le
    push_cast at hk
    rw [add_div] at hk
    linarith [hr.1.1]
  · have h' := trigNonneg_sound h hr.1 mem_zero hr.2.1 hr.2.2 hu
    linarith

/-- The coefficients of `b₀ + b_T (sin u + cos u) + (x₀ + x_a g) A + (y₀ + y_a g') B`. -/
def atPoint (b0 bT x0 xa y0 ya A B : FI) (xs : Bool) : FI × FI × FI :=
  let k0 := b0.add ((x0.mul A).add (y0.mul B))
  let pa := bT.add (xa.mul A)
  let pb := bT.add (ya.mul B)
  if xs then (k0, pa, pb) else (k0, pb, pa)

def atPointR (b0 bT x0 xa y0 ya A B : ℝ) (xs : Bool) : ℝ × ℝ × ℝ :=
  if xs then (b0 + (x0 * A + y0 * B), bT + xa * A, bT + ya * B)
  else (b0 + (x0 * A + y0 * B), bT + ya * B, bT + xa * A)

theorem mem_atPoint {b0 bT x0 xa y0 ya A B : FI} {b0r bTr x0r xar y0r yar Ar Br : ℝ}
    (hb0 : b0.Mem b0r) (hbT : bT.Mem bTr) (hx0 : x0.Mem x0r) (hxa : xa.Mem xar)
    (hy0 : y0.Mem y0r) (hya : ya.Mem yar) (hA : A.Mem Ar) (hB : B.Mem Br) (xs : Bool) :
    Mem3 (atPoint b0 bT x0 xa y0 ya A B xs) (atPointR b0r bTr x0r xar y0r yar Ar Br xs) := by
  have h0 := FI.mem_add hb0 (FI.mem_add (FI.mem_mul hx0 hA) (FI.mem_mul hy0 hB))
  have ha := FI.mem_add hbT (FI.mem_mul hxa hA)
  have hb := FI.mem_add hbT (FI.mem_mul hya hB)
  cases xs
  · exact ⟨h0, hb, ha⟩
  · exact ⟨h0, ha, hb⟩

theorem atPointR_eval (b0 bT x0 xa y0 ya A B c1 : ℝ) (xs : Bool) (u : ℝ) :
    (atPointR b0 bT x0 xa y0 ya A B xs).1 + c1 * u +
      (atPointR b0 bT x0 xa y0 ya A B xs).2.1 * Real.sin u +
      (atPointR b0 bT x0 xa y0 ya A B xs).2.2 * Real.cos u =
    b0 + c1 * u + bT * (Real.sin u + Real.cos u) + (x0 + xa * gS xs u) * A +
      (y0 + ya * gC xs u) * B := by
  cases xs <;> simp only [atPointR, gS, gC, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The coefficients of `Y - X R`, or of `X R - Y` when `neg`. -/
def slope (x0 xa y0 ya R : FI) (xs neg : Bool) : FI × FI × FI :=
  let k0 := y0.sub (x0.mul R)
  let pa := (xa.mul R).neg
  if neg then (if xs then (k0.neg, pa.neg, ya.neg) else (k0.neg, ya.neg, pa.neg))
  else (if xs then (k0, pa, ya) else (k0, ya, pa))

def slopeR (x0 xa y0 ya R : ℝ) (xs neg : Bool) : ℝ × ℝ × ℝ :=
  if neg then (if xs then (-(y0 - x0 * R), xa * R, -ya) else (-(y0 - x0 * R), -ya, xa * R))
  else (if xs then (y0 - x0 * R, -(xa * R), ya) else (y0 - x0 * R, ya, -(xa * R)))

theorem mem_slope {x0 xa y0 ya R : FI} {x0r xar y0r yar Rr : ℝ} (hx0 : x0.Mem x0r)
    (hxa : xa.Mem xar) (hy0 : y0.Mem y0r) (hya : ya.Mem yar) (hR : R.Mem Rr) (xs neg : Bool) :
    Mem3 (slope x0 xa y0 ya R xs neg) (slopeR x0r xar y0r yar Rr xs neg) := by
  have h0 := FI.mem_sub hy0 (FI.mem_mul hx0 hR)
  have ha := FI.mem_neg (FI.mem_mul hxa hR)
  cases neg <;> cases xs <;> simp only [Mem3, slope, slopeR, Bool.false_eq_true, ↓reduceIte]
  · exact ⟨h0, hya, ha⟩
  · exact ⟨h0, ha, hya⟩
  · exact ⟨FI.mem_neg h0, FI.mem_neg hya, by simpa using FI.mem_neg ha⟩
  · exact ⟨FI.mem_neg h0, by simpa using FI.mem_neg ha, FI.mem_neg hya⟩

theorem slopeR_eval (x0 xa y0 ya R : ℝ) (xs neg : Bool) (u : ℝ) :
    (slopeR x0 xa y0 ya R xs neg).1 + (slopeR x0 xa y0 ya R xs neg).2.1 * Real.sin u +
      (slopeR x0 xa y0 ya R xs neg).2.2 * Real.cos u =
    (if neg then -1 else 1) * ((y0 + ya * gC xs u) - (x0 + xa * gS xs u) * R) := by
  cases neg <;> cases xs <;> simp only [slopeR, gS, gC, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The coefficients of `b₀ + b_T (sin u + cos u) + v (X + Y) - ρ (V / h + h) / 2` with
`V = X² + Y² = x₀² + y₀² + λ² + 2 x₀ x_a g + 2 y₀ y_a g'` and `h = hn / 10 ^ 7`. -/
def circleCoeffs (b0 bT x0 xa y0 ya lam shift rho : FI) (hn : Nat) (xs : Bool) : FI × FI × FI :=
  let w := rho.scaleDiv 10000000 (2 * hn)
  let rh := rho.scaleDiv hn 20000000
  let V0 := ((x0.mul x0).add (y0.mul y0)).add (lam.mul lam)
  let Va := (x0.mul xa).add (x0.mul xa)
  let Vb := (y0.mul ya).add (y0.mul ya)
  let k0 := b0.add ((shift.mul (x0.add y0)).sub ((w.mul V0).add rh))
  let pa := bT.add ((shift.mul xa).sub (w.mul Va))
  let pb := bT.add ((shift.mul ya).sub (w.mul Vb))
  if xs then (k0, pa, pb) else (k0, pb, pa)

def circleR (b0 bT x0 xa y0 ya lam v w rh : ℝ) (xs : Bool) : ℝ × ℝ × ℝ :=
  let k0 := b0 + (v * (x0 + y0) - (w * (x0 * x0 + y0 * y0 + lam * lam) + rh))
  let pa := bT + (v * xa - w * (x0 * xa + x0 * xa))
  let pb := bT + (v * ya - w * (y0 * ya + y0 * ya))
  if xs then (k0, pa, pb) else (k0, pb, pa)

theorem mem_circleCoeffs {b0 bT x0 xa y0 ya lam shift rho : FI}
    {b0r bTr x0r xar y0r yar lamr v ρ : ℝ} (hb0 : b0.Mem b0r) (hbT : bT.Mem bTr)
    (hx0 : x0.Mem x0r) (hxa : xa.Mem xar) (hy0 : y0.Mem y0r) (hya : ya.Mem yar)
    (hlam : lam.Mem lamr) (hv : shift.Mem v) (hρ : rho.Mem ρ) {hn : Nat} (hh : 0 < hn)
    (xs : Bool) :
    Mem3 (circleCoeffs b0 bT x0 xa y0 ya lam shift rho hn xs)
      (circleR b0r bTr x0r xar y0r yar lamr v (ρ * (10000000 : ℕ) / (2 * hn : ℕ))
        (ρ * hn / (20000000 : ℕ)) xs) := by
  have hw := FI.mem_scaleDiv hρ 10000000 (show 0 < 2 * hn by omega)
  have hr := FI.mem_scaleDiv hρ hn (show 0 < 20000000 by norm_num)
  have hV0 := FI.mem_add (FI.mem_add (FI.mem_mul hx0 hx0) (FI.mem_mul hy0 hy0))
    (FI.mem_mul hlam hlam)
  have hVa := FI.mem_add (FI.mem_mul hx0 hxa) (FI.mem_mul hx0 hxa)
  have hVb := FI.mem_add (FI.mem_mul hy0 hya) (FI.mem_mul hy0 hya)
  have h0 := FI.mem_add hb0 (FI.mem_sub (FI.mem_mul hv (FI.mem_add hx0 hy0))
    (FI.mem_add (FI.mem_mul hw hV0) hr))
  have ha := FI.mem_add hbT (FI.mem_sub (FI.mem_mul hv hxa) (FI.mem_mul hw hVa))
  have hb := FI.mem_add hbT (FI.mem_sub (FI.mem_mul hv hya) (FI.mem_mul hw hVb))
  cases xs
  · exact ⟨h0, hb, ha⟩
  · exact ⟨h0, ha, hb⟩

theorem circleR_eval (b0 bT x0 xa y0 ya lam v ρ c1 : ℝ) {hn : ℕ} (hh : 0 < hn) (xs : Bool)
    (u : ℝ) (hxa : xa ^ 2 = lam ^ 2) (hya : ya ^ 2 = lam ^ 2) :
    let r := circleR b0 bT x0 xa y0 ya lam v (ρ * (10000000 : ℕ) / (2 * hn : ℕ))
      (ρ * hn / (20000000 : ℕ)) xs
    r.1 + c1 * u + r.2.1 * Real.sin u + r.2.2 * Real.cos u =
      b0 + c1 * u + bT * (Real.sin u + Real.cos u) +
        (v * ((x0 + xa * gS xs u) + (y0 + ya * gC xs u)) -
          ρ * ((((x0 + xa * gS xs u) ^ 2 + (y0 + ya * gC xs u) ^ 2) / ((hn : ℝ) / 10000000) +
            (hn : ℝ) / 10000000) / 2)) := by
  intro r
  have hp : (0 : ℝ) < hn := by exact_mod_cast hh
  have hsq := gS_sq_add_gC_sq xs u
  have hV : (x0 + xa * gS xs u) ^ 2 + (y0 + ya * gC xs u) ^ 2 =
      x0 * x0 + y0 * y0 + lam * lam + (x0 * xa + x0 * xa) * gS xs u +
        (y0 * ya + y0 * ya) * gC xs u := by
    linear_combination (lam ^ 2) * hsq + (gS xs u ^ 2) * hxa + (gC xs u ^ 2) * hya
  rw [hV]
  have e : r.1 + c1 * u + r.2.1 * Real.sin u + r.2.2 * Real.cos u =
      b0 + c1 * u + bT * (Real.sin u + Real.cos u) + (v * (x0 + y0) + v * xa * gS xs u +
        v * ya * gC xs u) - (ρ * (10000000 : ℕ) / (2 * hn : ℕ)) * (x0 * x0 + y0 * y0 + lam * lam +
        (x0 * xa + x0 * xa) * gS xs u + (y0 * ya + y0 * ya) * gC xs u) -
        ρ * hn / (20000000 : ℕ) := by
    cases xs <;> simp only [r, circleR, gS, gC, Bool.false_eq_true, ↓reduceIte] <;> ring
  rw [e]
  push_cast
  field_simp
  ring

/-! ### The tests of one mode -/

/-- Consecutive pieces from `start` on reach `hi`, and each passes `test h l u`. -/
def piecesFrom (test : Nat → Nat → Nat → Bool) : Nat → List (Nat × Nat) → Nat → Bool
  | start, [], hi => decide (hi ≤ start)
  | start, (h, upto) :: ps, hi => test h start upto && piecesFrom test upto ps hi

theorem piecesFrom_sound {test : Nat → Nat → Nat → Bool} {den : Nat} :
    ∀ {start : Nat} {ps : List (Nat × Nat)} {hi : Nat}, piecesFrom test start ps hi = true →
      ∀ {u : ℝ}, (start : ℝ) / den < u → u ≤ (hi : ℝ) / den →
        ∃ h l up, test h l up = true ∧ (l : ℝ) / den ≤ u ∧ u ≤ (up : ℝ) / den
  | start, [], hi, hp, u, h1, h2 => by
      simp only [piecesFrom, decide_eq_true_eq] at hp
      have : (hi : ℝ) / den ≤ (start : ℝ) / den :=
        div_le_div_of_nonneg_right (by exact_mod_cast hp) (Nat.cast_nonneg _)
      exact absurd (h2.trans this) (not_le.mpr h1)
  | start, (h, upto) :: ps, hi, hp, u, h1, h2 => by
      simp only [piecesFrom, Bool.and_eq_true] at hp
      by_cases hu : u ≤ (upto : ℝ) / den
      · exact ⟨h, start, upto, hp.1, h1.le, hu⟩
      · exact piecesFrom_sound hp.2 (lt_of_not_ge hu) h2

/-- Consecutive pieces cover `[lo, hi]`, and each passes `test h l u`. -/
def piecesOK (test : Nat → Nat → Nat → Bool) (lo : Nat) (ps : List (Nat × Nat)) (hi : Nat) :
    Bool :=
  match ps with
  | [] => false
  | (h, upto) :: rest => test h lo upto && piecesFrom test upto rest hi

theorem piecesOK_sound {test : Nat → Nat → Nat → Bool} {den lo hi : Nat}
    {ps : List (Nat × Nat)} (hp : piecesOK test lo ps hi = true) {u : ℝ}
    (h1 : (lo : ℝ) / den ≤ u) (h2 : u ≤ (hi : ℝ) / den) :
    ∃ h l up, test h l up = true ∧ (l : ℝ) / den ≤ u ∧ u ≤ (up : ℝ) / den := by
  cases ps with
  | nil => simp [piecesOK] at hp
  | cons p ps =>
      obtain ⟨h, upto⟩ := p
      simp only [piecesOK, Bool.and_eq_true] at hp
      by_cases hu : u ≤ (upto : ℝ) / den
      · exact ⟨h, lo, upto, hp.1, h1, hu⟩
      · exact piecesFrom_sound hp.2 (lt_of_not_ge hu) h2


/-- The coefficients of `X = x₀ + x_a g`. -/
def xLin (x0 xa : FI) (xs : Bool) : FI × FI × FI :=
  if xs then (x0, xa, FI.point 0) else (x0, FI.point 0, xa)

theorem xLin_sound {x0 xa : FI} {x0r xar : ℝ} (hx0 : x0.Mem x0r) (hxa : xa.Mem xar) (xs : Bool)
    {den lo hi : Nat} (h : nonneg3 den lo hi (xLin x0 xa xs) = true) {u : ℝ}
    (hu : (lo : ℝ) / den ≤ u ∧ u ≤ (hi : ℝ) / den) : 0 ≤ x0r + xar * gS xs u := by
  cases xs
  · have := nonneg3_sound (r := (x0r, 0, xar)) h ⟨hx0, mem_zero, hxa⟩ hu
    simpa [gS] using this
  · have := nonneg3_sound (r := (x0r, xar, 0)) h ⟨hx0, hxa, mem_zero⟩ hu
    simpa [gS] using this

/-- The tests of one support mode of the target arc `T`: both endpoints (`0`), the lower (`1`)
or the upper (`2`) endpoint with the slope premises, or the circle on pieces (`3`). -/
def modeCheck (den lo hi mode : Nat) (pieces : List (Nat × Nat)) (T : ArcBox)
    (lam b0 bT c1 x0 xa y0 ya : FI) (xs : Bool) : Bool :=
  match mode with
  | 0 => (T.side || nonneg3 den lo hi (xLin x0 xa xs)) &&
      pos3 den lo hi c1 (atPoint b0 bT x0 xa y0 ya T.aLo T.bLo xs) &&
      pos3 den lo hi c1 (atPoint b0 bT x0 xa y0 ya T.aHi T.bHi xs)
  | 1 => nonneg3 den lo hi (slope x0 xa y0 ya T.rLo xs false) &&
      nonneg3 den lo hi (slope x0 xa y0 ya T.rHi xs false) &&
      pos3 den lo hi c1 (atPoint b0 bT x0 xa y0 ya T.aLo T.bLo xs)
  | 2 => nonneg3 den lo hi (slope x0 xa y0 ya T.rLo xs true) &&
      nonneg3 den lo hi (slope x0 xa y0 ya T.rHi xs true) &&
      pos3 den lo hi c1 (atPoint b0 bT x0 xa y0 ya T.aHi T.bHi xs)
  | _ => !T.side && piecesOK (fun h l up => decide (0 < h) &&
      pos3 den l up c1 (circleCoeffs b0 bT x0 xa y0 ya lam T.shift T.rho h xs)) lo pieces hi

theorem modeCheck_sound {den lo hi mode : Nat} {pieces : List (Nat × Nat)} {T : ArcBox}
    {P : PreparedArc} (hT : T.Encloses P) {lam b0 bT c1 x0 xa y0 ya : FI} {xs : Bool}
    {lamr b0r bTr c1r x0r xar y0r yar : ℝ} (hlam : lam.Mem lamr) (hb0 : b0.Mem b0r)
    (hbT : bT.Mem bTr) (hc1 : c1.Mem c1r) (hx0 : x0.Mem x0r) (hxa : xa.Mem xar)
    (hy0 : y0.Mem y0r) (hya : ya.Mem yar) (hxa2 : xar ^ 2 = lamr ^ 2)
    (hya2 : yar ^ 2 = lamr ^ 2)
    (h : modeCheck den lo hi mode pieces T lam b0 bT c1 x0 xa y0 ya xs = true) {u : ℝ}
    (hu : (lo : ℝ) / den ≤ u ∧ u ≤ (hi : ℝ) / den) {A B : ℝ}
    (hAB : P.data.Contains P.radius A B) :
    0 < b0r + c1r * u + bTr * (Real.sin u + Real.cos u) + (x0r + xar * gS xs u) * A +
      (y0r + yar * gC xs u) * B := by
  set X := x0r + xar * gS xs u with hX
  set Y := y0r + yar * gC xs u with hY
  have cost (Af Bf : FI) (Ar Br : ℝ) (hA : Af.Mem Ar) (hB : Bf.Mem Br)
      (hp : pos3 den lo hi c1 (atPoint b0 bT x0 xa y0 ya Af Bf xs) = true) :
      0 < b0r + c1r * u + bTr * (Real.sin u + Real.cos u) + X * Ar + Y * Br := by
    have := pos3_sound hp hc1 (mem_atPoint hb0 hbT hx0 hxa hy0 hya hA hB xs) hu
    rwa [atPointR_eval] at this
  have slopeOK (R : FI) (Rr : ℝ) (hR : R.Mem Rr) (neg : Bool)
      (hp : nonneg3 den lo hi (slope x0 xa y0 ya R xs neg) = true) :
      0 ≤ (if neg then -1 else 1) * (Y - X * Rr) := by
    have := nonneg3_sound hp (mem_slope hx0 hxa hy0 hya hR xs neg) hu
    rwa [slopeR_eval] at this
  rcases mode with _ | _ | _ | mode
  · simp only [modeCheck, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨hX0, hL⟩, hH⟩ := h
    have hmode : P.data.side = true ∨ 0 ≤ X := by
      rcases hX0 with hs | hn
      · left
        rw [← hT.side]
        exact hs
      · exact Or.inr (xLin_sound hx0 hxa xs hn hu)
    have hl := cost _ _ _ _ hT.aLo hT.bLo hL
    have hh := cost _ _ _ _ hT.aHi hT.bHi hH
    have he := P.endpoints_lower hT.valid hAB hmode
      (m := min (X * P.aLo.value + Y * P.bLo.value) (X * P.aHi.value + Y * P.bHi.value))
      (min_le_left _ _) (min_le_right _ _)
    rcases min_choice (X * P.aLo.value + Y * P.bLo.value)
        (X * P.aHi.value + Y * P.bHi.value) with hm | hm <;>
      rw [hm] at he <;> linarith
  · simp only [modeCheck, Bool.and_eq_true] at h
    obtain ⟨⟨hsl, hsh⟩, hc⟩ := h
    have h1 := slopeOK _ _ hT.rLo false hsl
    have h2 := slopeOK _ _ hT.rHi false hsh
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h1 h2
    have he := P.lower_endpoint hT.valid hAB (X := X) (Y := Y) h1 h2
    have hl := cost _ _ _ _ hT.aLo hT.bLo hc
    linarith
  · simp only [modeCheck, Bool.and_eq_true] at h
    obtain ⟨⟨hsl, hsh⟩, hc⟩ := h
    have h1 := slopeOK _ _ hT.rLo true hsl
    have h2 := slopeOK _ _ hT.rHi true hsh
    simp only [↓reduceIte] at h1 h2
    have he := P.upper_endpoint hT.valid hAB (X := X) (Y := Y) (by linarith) (by linarith)
    have hl := cost _ _ _ _ hT.aHi hT.bHi hc
    linarith
  · simp only [modeCheck, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨hside, hp⟩ := h
    obtain ⟨hn, l, up, ht, hl, hup⟩ := piecesOK_sound hp hu.1 hu.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨hpos, hc⟩ := ht
    have hv := pos3_sound hc hc1
      (mem_circleCoeffs hb0 hbT hx0 hxa hy0 hya hlam hT.shift hT.rho hpos xs) ⟨hl, hup⟩
    rw [circleR_eval _ _ _ _ _ _ _ _ _ c1r hpos xs u hxa2 hya2] at hv
    have hP : P.data.side = false := by
      rw [← hT.side]
      exact hside
    have hw := sqrt_le_amgm (add_nonneg (sq_nonneg X) (sq_nonneg Y))
      (show (0 : ℝ) < (hn : ℝ) / 10000000 by positivity)
    have hc := P.circle_lower hT.valid hP hAB hw
    linarith

/-! ### One row -/

/-- The source coefficients after the reversal: `(p - λ, q)` on axis four, `(p, q - λ σ)` on
axis one. -/
def sourceXY (four : Bool) (S : ArcBox) (lam : FI) : FI × FI :=
  bif four then (S.p.sub lam, S.q) else (S.p, bif S.positive then S.q.sub lam else S.q.add lam)

/-- `π / 2`. -/
def piHalf : FI := ⟨1570796326794896619000000, 1570796326794896619500000⟩

theorem mem_piHalf : piHalf.Mem (Real.pi / 2) := by
  have h := pi_hand_enclosure
  constructor <;> simp only [piHalf, unit] <;> push_cast <;> linarith [h.1, h.2]

/-- `k π / 2`. -/
def piQuarter (k : Nat) : FI := ⟨imul (Int.ofNat k) piHalf.lo, imul (Int.ofNat k) piHalf.hi⟩

theorem mem_piQuarter (k : Nat) : (piQuarter k).Mem ((k : ℝ) * (Real.pi / 2)) := by
  have h := mem_piHalf
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 := mul_le_mul_of_nonneg_left h.1 hk
  have h2 := mul_le_mul_of_nonneg_left h.2 hk
  constructor <;> simp only [piQuarter, imul_eq, Int.ofNat_eq_natCast] <;> push_cast <;>
    rw [mul_div_assoc]
  · exact h1
  · exact h2

/-- The tests of a core row in the quarter `k` with source box `S` and target box `T`. -/
def coreCheck (den lo hi : Nat) (four : Bool) (k : Nat) (sgn : Bool) (mode : Nat)
    (pieces : List (Nat × Nat)) (S T : ArcBox) (lam lamHalf betaHalf gamma : FI) : Bool :=
  let k1 := Nat.beq (Nat.mod k 2) 1
  let flip := Nat.beq (Nat.div k 2) 1
  let XY := sourceXY four S lam
  let b0 := ((((S.c.sub T.c).add lamHalf).add betaHalf).add
    (FI.point (sourceLower S XY.1 XY.2))).sub gamma
  modeCheck den lo hi mode pieces T lam (bif Nat.beq k 0 then b0 else b0.add (piQuarter k))
    (lamHalf.sub betaHalf) (sgnBox sgn) T.p.neg (xaF four k1 flip sgn lam) T.q.neg
    (yaF four k1 flip sgn T.positive lam) (bif four then k1 else !k1)

theorem coreCheck_positive {c : CoreRow} {den lo hi mode : Nat} {pieces : List (Nat × Nat)}
    {S T : ArcBox} {lam lamHalf betaHalf gamma : FI} {four sgn : Bool}
    (hS : S.Encloses c.source) (hT : T.Encloses c.target) (hfour : c.axisFour = four)
    (hsgn : c.positiveHalf = sgn) (hk : c.quarter ≤ 3)
    (hden : 0 < den) (hangle : c.angle = ⟨(lo : ℚ) / den, (hi : ℚ) / den⟩)
    (hhi : hi ≤ den) (hlam : lam.Mem c.multiplier)
    (hlh : lamHalf.Mem ((c.multiplier : ℝ) / 2)) (hβ : betaHalf.Mem ((c.charge : ℝ) / 2))
    (hγ : gamma.Mem c.lowerTarget)
    (h : coreCheck den lo hi four c.quarter sgn mode pieces S T lam lamHalf betaHalf gamma =
      true) :
    c.Positive := by
  subst hfour hsgn
  intro a b A B u hsa htA hu
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  have hu' : (lo : ℝ) / den ≤ u ∧ u ≤ (hi : ℝ) / den := by
    rw [hangle] at hu
    obtain ⟨h1, h2⟩ := hu
    push_cast at h1 h2
    exact ⟨h1, h2⟩
  have hu0 : 0 ≤ u := (div_nonneg (Nat.cast_nonneg _) hdR.le).trans hu'.1
  have hu1 : u ≤ 1 := by
    refine hu'.2.trans ?_
    rw [div_le_one hdR]
    exact_mod_cast hhi
  -- the source term
  have hXs : (sourceXY c.axisFour S lam).1.Mem (c.Xs : ℝ) := by
    cases hf : c.axisFour <;> simp only [sourceXY, CoreRow.Xs, hf, Bool.cond_false,
      Bool.cond_true, Bool.false_eq_true, ↓reduceIte]
    · exact hS.p
    · push_cast
      exact FI.mem_sub hS.p hlam
  have hYs : (sourceXY c.axisFour S lam).2.Mem (c.Ys : ℝ) := by
    cases hf : c.axisFour <;> simp only [sourceXY, CoreRow.Ys, hf, Bool.cond_false,
      Bool.cond_true, Bool.false_eq_true, ↓reduceIte]
    · rw [hS.positive]
      cases hp : c.source.data.positive <;>
        simp only [ArcData.signQ, hp, Bool.cond_false, Bool.cond_true, Bool.false_eq_true,
          ↓reduceIte] <;> push_cast
      · simpa [sub_eq_add_neg] using FI.mem_add hS.q hlam
      · simpa using FI.mem_sub hS.q hlam
    · exact hS.q
  have hSL := sourceLower_sound hS hXs hYs hsa
  obtain ⟨hsrcX, hsrcY⟩ := c.source_coefficients u
  -- the base and the target coefficients
  have hB := base_lin hk c.positiveHalf c.source.data.label c.target.data.label c.multiplier
    c.charge ⟨hu0, hu1⟩
  obtain ⟨hTX, hTY⟩ := target_lin c.axisFour hk c.positiveHalf c.target.data.positive
    c.target.data.label c.multiplier u
  set SL : ℝ := ((sourceLower S (sourceXY c.axisFour S lam).1 (sourceXY c.axisFour S lam).2 :
    Int) : ℝ) / unit with hSLdef
  have hb0 : (((((S.c.sub T.c).add lamHalf).add betaHalf).add (FI.point (sourceLower S
      (sourceXY c.axisFour S lam).1 (sourceXY c.axisFour S lam).2))).sub gamma).Mem
      (c.source.data.label.c - c.target.data.label.c + c.multiplier / 2 + c.charge / 2 + SL -
        c.lowerTarget) :=
    FI.mem_sub (FI.mem_add (FI.mem_add (FI.mem_add (FI.mem_sub hS.c hT.c) hlh) hβ)
      (FI.mem_point_div _)) hγ
  have hb0' : (bif (c.quarter == 0) then ((((S.c.sub T.c).add lamHalf).add betaHalf).add
      (FI.point (sourceLower S (sourceXY c.axisFour S lam).1
        (sourceXY c.axisFour S lam).2))).sub gamma
      else (((((S.c.sub T.c).add lamHalf).add betaHalf).add (FI.point (sourceLower S
        (sourceXY c.axisFour S lam).1 (sourceXY c.axisFour S lam).2))).sub gamma).add
        (piQuarter c.quarter)).Mem
      (c.source.data.label.c - c.target.data.label.c + c.multiplier / 2 + c.charge / 2 + SL -
        c.lowerTarget + (c.quarter : ℝ) * (Real.pi / 2)) := by
    by_cases hq : c.quarter = 0
    · simp only [hq, beq_self_eq_true, Bool.cond_true, Nat.cast_zero, zero_mul, add_zero]
      exact hb0
    · have hq' : (c.quarter == 0) = false := by simpa using hq
      simp only [hq', Bool.cond_false]
      exact FI.mem_add hb0 (mem_piQuarter _)
  -- the quarter tests of `coreCheck` are those of `target_lin`
  have hk1 : Nat.beq (Nat.mod c.quarter 2) 1 = (c.quarter % 2 == 1) := rfl
  have hfl : Nat.beq (Nat.div c.quarter 2) 1 = (c.quarter / 2 == 1) := rfl
  have hk0 : Nat.beq c.quarter 0 = (c.quarter == 0) := rfl
  have hxs : ∀ a b : Bool, (bif a then b else !b) = (a == b) := by decide
  simp only [coreCheck, hk1, hfl, hk0, hxs] at h
  have hm := modeCheck_sound hT hlam hb0' (FI.mem_sub hlh hβ) (mem_sgnBox c.positiveHalf)
    (FI.mem_neg hT.p)
    (mem_xaF c.axisFour (c.quarter % 2 == 1) (c.quarter / 2 == 1) c.positiveHalf hlam)
    (FI.mem_neg hT.q)
    (mem_yaF c.axisFour (c.quarter % 2 == 1) (c.quarter / 2 == 1) c.positiveHalf
      c.target.data.positive hlam)
    (xaR_sq _ _ _ _ _) (yaR_sq _ _ _ _ _ _) (by simpa [coreCheck, hT.positive] using h) hu' htA
  have hsx : sourceX c.axis c.source.data.label c.multiplier
      (AnglePolynomial.phi c.quarter c.positiveHalf u) = c.Xs := hsrcX.symm
  have hsy : sourceY c.axis c.source.data.label c.multiplier c.source.data.sign
      (AnglePolynomial.phi c.quarter c.positiveHalf u) = c.Ys := hsrcY.symm
  have hTX' : targetX c.axis c.target.data.label c.multiplier
      (AnglePolynomial.phi c.quarter c.positiveHalf u) = _ := hTX
  have hTY' : targetY c.axis c.target.data.label c.multiplier c.target.data.sign
      (AnglePolynomial.phi c.quarter c.positiveHalf u) =
      -(c.target.data.label.q : ℝ) + yaR c.axisFour (c.quarter % 2 == 1) (c.quarter / 2 == 1)
        c.positiveHalf c.target.data.positive c.multiplier *
          gC (c.axisFour == (c.quarter % 2 == 1)) u := by
    rw [sign_eq_sgnR]
    exact hTY
  rw [CoreRow.phi, hB, hsx, hsy, hTX', hTY']
  have hsrc : SL ≤ (c.Xs : ℝ) * a + (c.Ys : ℝ) * b := hSL
  linarith

/-- The check of one row: indices and angle in range, then the tests of its core row. -/
def checkRow (C : TableCtx) (x : AffineRow) : Bool :=
  match x with
  | ⟨edge, source, target, axis, quarter, positive, lo, hi, lam, mode, _, pieces⟩ =>
    Nat.blt edge 7 && Nat.blt source C.n && Nat.blt target C.n && Nat.ble 1 axis &&
      Nat.ble axis 4 && Nat.ble quarter 3 && Nat.ble hi C.den &&
      coreCheck C.den lo hi (Nat.beq axis 2 || Nat.beq axis 4) quarter positive mode pieces
        (bif Nat.beq axis 2 || Nat.beq axis 3 then (boxAt C.boxes target).reverse
          else boxAt C.boxes source)
        (bif Nat.beq axis 2 || Nat.beq axis 3 then (boxAt C.boxes source).reverse
          else boxAt C.boxes target)
        (FI.ofDiv lam 100000000) (FI.ofDiv lam 200000000)
        (nth (FI.point 0) C.betaHalf edge) (nth (FI.point 0) C.gamma edge)

/-- The prepared row of a record: the table row and its two prepared arcs. -/
def rowPrep (M : AffineTableMeta) (den : Nat) (x : AffineRow) : PreparedRow :=
  ⟨x.toTableRow M den, PreparedArc.ofArc M.radius ((x.toTableRow M den).sourceArc M),
    PreparedArc.ofArc M.radius ((x.toTableRow M den).targetArc M),
    M.charge (x.toTableRow M den).edge, ⟨0, 0⟩⟩

theorem row_claim_of_core {M : AffineTableMeta} {C : TableCtx} (hC : C.Valid M) {x : AffineRow}
    (he : x.edge < 7) (hq : x.quarter ≤ 3) (hhi : x.hi ≤ C.den) {four : Bool}
    {S T : ArcBox} (hS : S.Encloses (rowPrep M C.den x).core.source)
    (hT : T.Encloses (rowPrep M C.den x).core.target)
    (hfour : (rowPrep M C.den x).core.axisFour = four)
    (hcore : coreCheck C.den x.lo x.hi four x.quarter x.positive x.mode x.pieces S T
      (FI.ofDiv x.lam 100000000) (FI.ofDiv x.lam 200000000) (nth (FI.point 0) C.betaHalf x.edge)
      (nth (FI.point 0) C.gamma x.edge) = true) :
    (x.toTableRow M C.den).Claim M := by
  have hm : (rowPrep M C.den x).Matches M :=
    ⟨PreparedArc.ofArc_data _ _, PreparedArc.ofArc_data _ _, PreparedArc.ofArc_radius _ _,
      PreparedArc.ofArc_radius _ _, rfl⟩
  have hedge : ((Fin.ofNat 7 x.edge : Fin 7) : ℕ) = x.edge := by
    simp [Nat.mod_eq_of_lt he]
  have hlam : (FI.ofDiv x.lam 100000000).Mem ((rowPrep M C.den x).core.multiplier : ℝ) := by
    have := FI.mem_ofDiv x.lam (show 0 < 100000000 by norm_num)
    convert this using 1
    simp [rowPrep, PreparedRow.core, AffineRow.toTableRow]
    norm_num
  have hlh : (FI.ofDiv x.lam 200000000).Mem ((rowPrep M C.den x).core.multiplier / 2 : ℝ) := by
    have := FI.mem_ofDiv x.lam (show 0 < 200000000 by norm_num)
    convert this using 1
    simp [rowPrep, PreparedRow.core, AffineRow.toTableRow]
    ring
  have hβ : (nth (FI.point 0) C.betaHalf x.edge).Mem
      ((rowPrep M C.den x).core.charge / 2 : ℝ) := by
    have := hC.beta (Fin.ofNat 7 x.edge)
    rw [hedge] at this
    simpa [rowPrep, PreparedRow.core, AffineRow.toTableRow] using this
  have hγ : (nth (FI.point 0) C.gamma x.edge).Mem
      ((rowPrep M C.den x).core.lowerTarget : ℝ) := by
    have := hC.gamma (Fin.ofNat 7 x.edge)
    rw [hedge] at this
    simpa [rowPrep, PreparedRow.core, AffineRow.toTableRow] using this
  refine PreparedRow.claim_of_positive (p := rowPrep M C.den x) ?_ ?_ hm
  · exact coreCheck_positive hS hT hfour rfl hq hC.den_pos rfl hhi hlam hlh hβ hγ hcore
  · show (0 : ℚ) ≤ (x.lam : ℚ) / 10 ^ 8
    positivity

/-- A row passing the check satisfies its claim. -/
theorem checkRow_claim {M : AffineTableMeta} {C : TableCtx} (hC : C.Valid M) {x : AffineRow}
    (h : checkRow C x = true) : (x.toTableRow M C.den).Claim M := by
  obtain ⟨edge, source, target, axis, quarter, positive, lo, hi, lam, mode, rad, pieces⟩ := x
  simp only [checkRow, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨he, hs⟩, ht⟩, ha1⟩, ha4⟩, hq⟩, hhi⟩, hcore⟩ := h
  have hsrc := hC.boxes source hs
  have htgt := hC.boxes target ht
  rcases (show axis = 1 ∨ axis = 2 ∨ axis = 3 ∨ axis = 4 by omega) with rfl | rfl | rfl | rfl
  · refine row_claim_of_core hC he hq hhi (four := false) ?_ ?_ ?_ (by simpa [nat_beq_eq] using hcore)
    · simpa [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf,
        AffineTableRow.sourceArc] using hsrc
    · simpa [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf,
        AffineTableRow.targetArc] using htgt
    · simp [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf]
  · refine row_claim_of_core hC he hq hhi (four := true) ?_ ?_ ?_ (by simpa [nat_beq_eq] using hcore)
    · simpa [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf,
        AffineTableRow.targetArc] using htgt.reverse
    · simpa [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf,
        AffineTableRow.sourceArc] using hsrc.reverse
    · simp [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf]
  · refine row_claim_of_core hC he hq hhi (four := false) ?_ ?_ ?_ (by simpa [nat_beq_eq] using hcore)
    · simpa [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf,
        AffineTableRow.targetArc] using htgt.reverse
    · simpa [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf,
        AffineTableRow.sourceArc] using hsrc.reverse
    · simp [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf]
  · refine row_claim_of_core hC he hq hhi (four := true) ?_ ?_ ?_ (by simpa [nat_beq_eq] using hcore)
    · simpa [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf,
        AffineTableRow.sourceArc] using hsrc
    · simpa [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf,
        AffineTableRow.targetArc] using htgt
    · simp [rowPrep, PreparedRow.core, AffineRow.toTableRow, axisOf]

/-- Every row of a list passes the check (by the list recursor). -/
def checkRows (C : TableCtx) (rows : List AffineRow) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => checkRow C x && ih) rows

theorem checkRows_sound {C : TableCtx} {rows : List AffineRow} (h : checkRows C rows = true) :
    ∀ x ∈ rows, checkRow C x = true := by
  induction rows with
  | nil => simp
  | cons y rows ih =>
      have h' : checkRow C y = true ∧ checkRows C rows = true := by
        simpa [checkRows] using h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h'.1
      · exact ih h'.2 x hx

theorem checkRows_append (C : TableCtx) (a b : List AffineRow) :
    checkRows C (a ++ b) = (checkRows C a && checkRows C b) := by
  induction a with
  | nil => simp [checkRows]
  | cons x a ih =>
      have e : ∀ l : List AffineRow, checkRows C (x :: l) = (checkRow C x && checkRows C l) :=
        fun _ => rfl
      rw [List.cons_append, e, e, ih, Bool.and_assoc]

theorem checkRows_flatten (C : TableCtx) (L : List (List AffineRow)) :
    checkRows C L.flatten = L.all (checkRows C) := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.flatten_cons, checkRows_append, ih, List.all_cons]

end SquaresInCircles.Eight.Arithmetic
