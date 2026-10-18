module

public import SquaresInCircles.Eight.Arithmetic.Interval

/-!
# Fixed-point intervals for kernel evaluation

The tables of eight squares are checked by evaluating Boolean functions in the
kernel. Rational arithmetic normalizes every result by a gcd, and its numbers
grow with every product, so it is slow there. Here a number is an integer
multiple of `1 / unit`, with `unit = 10 ^ 24`; an interval is a pair of such
integers, and a product is rounded outwards. The table data are decimals with at
most eight places, so they and their sums are represented exactly.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic.Fixed

/-- The fixed-point unit `10 ^ 24`. -/
def unit : Int := 1000000000000000000000000

/-- The unit as a natural number. -/
def unitN : Nat := 1000000000000000000000000

theorem unitN_eq : (unitN : Int) = unit := rfl

theorem unit_pos : (0 : Int) < unit := by decide

theorem unit_pos_real : (0 : ℝ) < unit := by exact_mod_cast unit_pos

theorem unitN_pos : 0 < unitN := by decide

/-! ### Integer operations for the kernel

The kernel computes with natural-number literals directly (`Nat.add`, `Nat.sub`, `Nat.mul`,
`Nat.div`, `Nat.ble`, `Nat.beq`), but it evaluates an operation of `Int` by unfolding its
definition, about ten times as slowly, and an arithmetic operator by unfolding its instances
first. The operations below split an integer by `Int.casesOn` into its sign and magnitude and
call the operations of `Nat` directly; each equals the operation of `Int` it replaces. -/

/-- `-n` for a natural number `n`. -/
def negN (n : Nat) : Int := cond (Nat.beq n 0) (Int.ofNat 0) (Int.negSucc (Nat.sub n 1))

/-- `m - n` for natural numbers `m` and `n`. -/
def subN (m n : Nat) : Int :=
  cond (Nat.ble n m) (Int.ofNat (Nat.sub m n)) (Int.negSucc (Nat.sub (Nat.sub n m) 1))

/-- `-a`. -/
def ineg (a : Int) : Int :=
  Int.casesOn (motive := fun _ => Int) a (fun m => negN m) (fun m => Int.ofNat (Nat.add m 1))

/-- `a + b`. -/
def iadd (a b : Int) : Int :=
  Int.casesOn (motive := fun _ => Int) a
    (fun m => Int.casesOn (motive := fun _ => Int) b
      (fun n => Int.ofNat (Nat.add m n)) (fun n => subN m (Nat.add n 1)))
    (fun m => Int.casesOn (motive := fun _ => Int) b
      (fun n => subN n (Nat.add m 1)) (fun n => Int.negSucc (Nat.add (Nat.add m n) 1)))

/-- `a - b`. -/
def isub (a b : Int) : Int :=
  Int.casesOn (motive := fun _ => Int) a
    (fun m => Int.casesOn (motive := fun _ => Int) b
      (fun n => subN m n) (fun n => Int.ofNat (Nat.add (Nat.add m n) 1)))
    (fun m => Int.casesOn (motive := fun _ => Int) b
      (fun n => Int.negSucc (Nat.add m n)) (fun n => subN n m))

/-- `a * b`. -/
def imul (a b : Int) : Int :=
  Int.casesOn (motive := fun _ => Int) a
    (fun m => Int.casesOn (motive := fun _ => Int) b
      (fun n => Int.ofNat (Nat.mul m n)) (fun n => negN (Nat.mul m (Nat.add n 1))))
    (fun m => Int.casesOn (motive := fun _ => Int) b
      (fun n => negN (Nat.mul (Nat.add m 1) n))
      (fun n => Int.ofNat (Nat.mul (Nat.add m 1) (Nat.add n 1))))

/-- `⌊a / d⌋` for a positive natural number `d`. -/
def ifloor (a : Int) (d : Nat) : Int :=
  Int.casesOn (motive := fun _ => Int) a
    (fun m => Int.ofNat (Nat.div m d)) (fun m => Int.negSucc (Nat.div m d))

/-- `⌈a / d⌉` for a positive natural number `d`. -/
def iceil (a : Int) (d : Nat) : Int :=
  Int.casesOn (motive := fun _ => Int) a
    (fun m => Int.ofNat (Nat.div (Nat.sub (Nat.add m d) 1) d))
    (fun m => negN (Nat.div (Nat.add m 1) d))

/-- `a ≤ b`. -/
def ile (a b : Int) : Bool :=
  Int.casesOn (motive := fun _ => Bool) a
    (fun m => Int.casesOn (motive := fun _ => Bool) b (fun n => Nat.ble m n) (fun _ => false))
    (fun m => Int.casesOn (motive := fun _ => Bool) b (fun _ => true) (fun n => Nat.ble n m))

/-- `a = b`. -/
def ieq (a b : Int) : Bool :=
  Int.casesOn (motive := fun _ => Bool) a
    (fun m => Int.casesOn (motive := fun _ => Bool) b (fun n => Nat.beq m n) (fun _ => false))
    (fun m => Int.casesOn (motive := fun _ => Bool) b (fun _ => false) (fun n => Nat.beq m n))

/-- `min a b`. -/
def imin (a b : Int) : Int := cond (ile a b) a b

/-- `max a b`. -/
def imax (a b : Int) : Int := cond (ile a b) b a

/-- `a.toNat`, the positive part. -/
def ipos (a : Int) : Nat := Int.casesOn (motive := fun _ => Nat) a (fun m => m) (fun _ => 0)

/-- `(-a).toNat`, the negative part. -/
def ineg' (a : Int) : Nat :=
  Int.casesOn (motive := fun _ => Nat) a (fun _ => 0) (fun m => Nat.add m 1)

theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl

theorem nat_ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  apply Bool.eq_iff_iff.mpr
  simp [Nat.ble_eq]

theorem nat_beq_eq (a b : Nat) : Nat.beq a b = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp [Nat.beq_eq]

theorem negN_eq (n : Nat) : negN n = -(n : Int) := by
  cases n with
  | zero => rfl
  | succ k => simp [negN, nat_beq_eq, Int.negSucc_eq]

theorem subN_eq (m n : Nat) : subN m n = (m : Int) - n := by
  unfold subN
  rw [nat_ble_eq]
  by_cases h : n ≤ m
  · simp only [h, decide_true, Bool.cond_true, nat_sub_eq, Int.ofNat_eq_natCast]
    omega
  · simp only [h, decide_false, Bool.cond_false, nat_sub_eq, Int.negSucc_eq]
    omega

@[simp] theorem ineg_eq (a : Int) : ineg a = -a := by
  cases a with
  | ofNat m => exact negN_eq m
  | negSucc m => simp [ineg, Int.negSucc_eq]

@[simp] theorem iadd_eq (a b : Int) : iadd a b = a + b := by
  cases a <;> cases b <;>
    simp only [iadd, subN_eq, nat_add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast] <;> push_cast <;> ring

@[simp] theorem isub_eq (a b : Int) : isub a b = a - b := by
  cases a <;> cases b <;>
    simp only [isub, subN_eq, nat_add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast] <;> push_cast <;> ring

@[simp] theorem imul_eq (a b : Int) : imul a b = a * b := by
  cases a <;> cases b <;>
    simp only [imul, negN_eq, nat_add_eq, nat_mul_eq, Int.negSucc_eq, Int.ofNat_eq_natCast] <;>
    push_cast <;> ring

theorem ifloor_eq (a : Int) {d : Nat} (hd : 0 < d) : ifloor a d = a / (d : Int) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hd)
  cases a <;> rfl

theorem iceil_eq (a : Int) {d : Nat} (hd : 0 < d) : iceil a d = -((-a) / (d : Int)) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hd)
  cases a with
  | ofNat m =>
      cases m with
      | zero =>
          simp only [iceil, nat_div_eq, nat_sub_eq, nat_add_eq]
          rw [Nat.div_eq_of_lt (by omega)]
          simp
      | succ k =>
          have h1 : (k + 1 + (e + 1) - 1) / (e + 1) = k / (e + 1) + 1 := by
            rw [show k + 1 + (e + 1) - 1 = k + 1 * (e + 1) by omega,
              Nat.add_mul_div_right _ _ (Nat.succ_pos e)]
          simp only [iceil, nat_div_eq, nat_sub_eq, nat_add_eq, h1]
          rfl
  | negSucc m =>
      simp only [iceil, negN_eq, nat_div_eq, nat_add_eq]
      rfl

theorem ile_eq (a b : Int) : ile a b = decide (a ≤ b) := by
  cases a <;> cases b <;> simp [ile, nat_ble_eq, Int.negSucc_eq] <;> omega

theorem ieq_eq (a b : Int) : ieq a b = decide (a = b) := by
  cases a <;> cases b <;> simp [ieq, nat_beq_eq]

@[simp] theorem imin_eq (a b : Int) : imin a b = min a b := by
  unfold imin
  rw [ile_eq]
  by_cases h : a ≤ b <;> simp [h, min_def]

@[simp] theorem imax_eq (a b : Int) : imax a b = max a b := by
  unfold imax
  rw [ile_eq]
  by_cases h : a ≤ b <;> simp [h, max_def]

@[simp] theorem ipos_eq (a : Int) : ipos a = a.toNat := by
  cases a <;> rfl

@[simp] theorem ineg'_eq (a : Int) : ineg' a = (-a).toNat := by
  cases a with
  | ofNat m => cases m <;> rfl
  | negSucc m => rfl

/-- The positive and the negative part of `a`, `(a.toNat, (-a).toNat)`. -/
def intPN (a : Int) : Nat × Nat :=
  Int.casesOn (motive := fun _ => Nat × Nat) a (fun m => (m, 0)) (fun m => (0, Nat.add m 1))

/-- The positive and the negative part of `⌊a / d⌋`. -/
def floorPN (a : Int) (d : Nat) : Nat × Nat :=
  Int.casesOn (motive := fun _ => Nat × Nat) a
    (fun m => (Nat.div m d, 0)) (fun m => (0, Nat.add (Nat.div m d) 1))

theorem intPN_eq (a : Int) : intPN a = (a.toNat, (-a).toNat) := by
  cases a with
  | ofNat m => cases m <;> rfl
  | negSucc m => rfl

theorem floorPN_eq (a : Int) {d : Nat} (hd : 0 < d) :
    floorPN a d = ((a / (d : Int)).toNat, (-(a / (d : Int))).toNat) := by
  rw [← ifloor_eq a hd, ← intPN_eq]
  cases a <;> rfl

/-- `⌊a / unit⌋`. -/
def down (a : Int) : Int := ifloor a unitN

/-- `⌈a / unit⌉`. -/
def up (a : Int) : Int := iceil a unitN

theorem down_eq (a : Int) : down a = a / unit := ifloor_eq a unitN_pos

theorem up_eq (a : Int) : up a = -((-a) / unit) := iceil_eq a unitN_pos

theorem down_le (a : Int) : (down a : ℝ) ≤ (a : ℝ) / unit := by
  rw [down_eq, le_div_iff₀ unit_pos_real]
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt unit_pos)

theorem le_up (a : Int) : (a : ℝ) / unit ≤ (up a : ℝ) := by
  have h := Int.ediv_mul_le (-a) (ne_of_gt unit_pos)
  rw [div_le_iff₀ unit_pos_real]
  have h' : ((-a / unit * unit : Int) : ℝ) ≤ ((-a : Int) : ℝ) := by exact_mod_cast h
  push_cast at h' ⊢
  rw [up_eq]
  push_cast
  linarith

/-- A closed interval `[lo / unit, hi / unit]`. -/
structure FI where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

namespace FI

def Mem (I : FI) (x : ℝ) : Prop := (I.lo : ℝ) / unit ≤ x ∧ x ≤ (I.hi : ℝ) / unit

def add (I J : FI) : FI := ⟨iadd I.lo J.lo, iadd I.hi J.hi⟩
def neg (I : FI) : FI := ⟨ineg I.hi, ineg I.lo⟩
def sub (I J : FI) : FI := ⟨isub I.lo J.hi, isub I.hi J.lo⟩

theorem add_eq (I J : FI) : I.add J = ⟨I.lo + J.lo, I.hi + J.hi⟩ := by simp [add]
theorem neg_eq (I : FI) : I.neg = ⟨-I.hi, -I.lo⟩ := by simp [neg]
theorem sub_eq (I J : FI) : I.sub J = ⟨I.lo - J.hi, I.hi - J.lo⟩ := by simp [sub]

/-- The product with the point `a / unit`, rounded outwards. -/
def mulPoint (a : Int) (J : FI) : FI :=
  cond (ile (Int.ofNat 0) a) ⟨down (imul a J.lo), up (imul a J.hi)⟩
    ⟨down (imul a J.hi), up (imul a J.lo)⟩

/-- The four corner products, rounded outwards. -/
def mulCorners (I J : FI) : FI :=
  let a := imul I.lo J.lo
  let b := imul I.lo J.hi
  let c := imul I.hi J.lo
  let d := imul I.hi J.hi
  ⟨down (imin (imin a b) (imin c d)), up (imax (imax a b) (imax c d))⟩

/-- The product, rounded outwards: from two products when a factor is a point (as for the
decimal data), otherwise from the four corner products. -/
def mul (I J : FI) : FI :=
  cond (ieq I.lo I.hi) (mulPoint I.lo J) (cond (ieq J.lo J.hi) (mulPoint J.lo I) (mulCorners I J))

theorem mulPoint_eq (a : Int) (J : FI) : mulPoint a J =
    if 0 ≤ a then ⟨down (a * J.lo), up (a * J.hi)⟩ else ⟨down (a * J.hi), up (a * J.lo)⟩ := by
  simp only [mulPoint, imul_eq, ile_eq, Bool.cond_decide, Int.ofNat_eq_natCast, Nat.cast_zero]

theorem mulCorners_eq (I J : FI) : mulCorners I J =
    ⟨down (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))),
      up (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))⟩ := by
  simp only [mulCorners, imul_eq, imin_eq, imax_eq]

theorem mul_eq (I J : FI) : I.mul J =
    if I.lo = I.hi then mulPoint I.lo J
    else if J.lo = J.hi then mulPoint J.lo I else mulCorners I J := by
  simp only [mul, ieq_eq, Bool.cond_decide]

/-- An outward enclosure of a rational number. -/
def ofQ (q : ℚ) : FI := ⟨(q.num * unit) / q.den, -((-(q.num * unit)) / q.den)⟩

/-- An outward enclosure of a rational interval. -/
def ofQI (I : QInterval) : FI := ⟨(ofQ I.lo).lo, (ofQ I.hi).hi⟩

theorem mem_add {I J : FI} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.add J).Mem (x + y) := by
  rw [add_eq]
  unfold Mem at *
  push_cast
  constructor
  · rw [add_div]; linarith [hx.1, hy.1]
  · rw [add_div]; linarith [hx.2, hy.2]

theorem mem_neg {I : FI} {x : ℝ} (hx : I.Mem x) : I.neg.Mem (-x) := by
  rw [neg_eq]
  unfold Mem at *
  push_cast
  constructor
  · rw [neg_div]; linarith [hx.2]
  · rw [neg_div]; linarith [hx.1]

theorem mem_sub {I J : FI} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.sub J).Mem (x - y) := by
  rw [sub_eq]
  unfold Mem at *
  push_cast
  constructor
  · rw [sub_div]; linarith [hx.1, hy.2]
  · rw [sub_div]; linarith [hx.2, hy.1]

theorem mem_mulPoint (a : Int) {J : FI} {y : ℝ} (hy : J.Mem y) :
    (mulPoint a J).Mem ((a : ℝ) / unit * y) := by
  have hU := unit_pos_real
  rw [mulPoint_eq]
  split_ifs with ha
  · have ha' : (0 : ℝ) ≤ (a : ℝ) / unit := div_nonneg (by exact_mod_cast ha) hU.le
    constructor
    · calc ((down (a * J.lo) : Int) : ℝ) / unit ≤ ((a * J.lo : Int) : ℝ) / unit / unit :=
            div_le_div_of_nonneg_right (down_le _) hU.le
        _ = (a : ℝ) / unit * ((J.lo : ℝ) / unit) := by push_cast; ring
        _ ≤ (a : ℝ) / unit * y := mul_le_mul_of_nonneg_left hy.1 ha'
    · calc (a : ℝ) / unit * y ≤ (a : ℝ) / unit * ((J.hi : ℝ) / unit) :=
            mul_le_mul_of_nonneg_left hy.2 ha'
        _ = ((a * J.hi : Int) : ℝ) / unit / unit := by push_cast; ring
        _ ≤ ((up (a * J.hi) : Int) : ℝ) / unit := div_le_div_of_nonneg_right (le_up _) hU.le
  · have ha' : (a : ℝ) / unit ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (le_of_lt (lt_of_not_ge ha))) hU.le
    constructor
    · calc ((down (a * J.hi) : Int) : ℝ) / unit ≤ ((a * J.hi : Int) : ℝ) / unit / unit :=
            div_le_div_of_nonneg_right (down_le _) hU.le
        _ = (a : ℝ) / unit * ((J.hi : ℝ) / unit) := by push_cast; ring
        _ ≤ (a : ℝ) / unit * y := mul_le_mul_of_nonpos_left hy.2 ha'
    · calc (a : ℝ) / unit * y ≤ (a : ℝ) / unit * ((J.lo : ℝ) / unit) :=
            mul_le_mul_of_nonpos_left hy.1 ha'
        _ = ((a * J.lo : Int) : ℝ) / unit / unit := by push_cast; ring
        _ ≤ ((up (a * J.lo) : Int) : ℝ) / unit := div_le_div_of_nonneg_right (le_up _) hU.le

theorem mem_point_eq {I : FI} (h : I.lo = I.hi) {x : ℝ} (hx : I.Mem x) : x = (I.lo : ℝ) / unit :=
  le_antisymm (by rw [h]; exact hx.2) hx.1

theorem mem_mulCorners {I J : FI} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.mulCorners J).Mem (x * y) := by
  rw [mulCorners_eq]
  have hU := unit_pos_real
  set l : ℝ := (I.lo : ℝ) / unit
  set u : ℝ := (I.hi : ℝ) / unit
  set L : ℝ := (J.lo : ℝ) / unit
  set V : ℝ := (J.hi : ℝ) / unit
  have key (p q m : Int) (hm : m ≤ p * q) :
      (m : ℝ) / unit / unit ≤ ((p : ℝ) / unit) * ((q : ℝ) / unit) := by
    have h : (m : ℝ) ≤ (p : ℝ) * q := by exact_mod_cast hm
    calc (m : ℝ) / unit / unit ≤ ((p : ℝ) * q) / unit / unit := by gcongr
      _ = _ := by ring
  have key' (p q m : Int) (hm : p * q ≤ m) :
      ((p : ℝ) / unit) * ((q : ℝ) / unit) ≤ (m : ℝ) / unit / unit := by
    have h : (p : ℝ) * q ≤ m := by exact_mod_cast hm
    calc ((p : ℝ) / unit) * ((q : ℝ) / unit) = ((p : ℝ) * q) / unit / unit := by ring
      _ ≤ (m : ℝ) / unit / unit := by gcongr
  set mn := min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))
  set mx := max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))
  have hmin : (mn : ℝ) / unit / unit ≤ min (min (l * L) (l * V)) (min (u * L) (u * V)) :=
    le_min (le_min (key _ _ _ ((min_le_left _ _).trans (min_le_left _ _)))
        (key _ _ _ ((min_le_left _ _).trans (min_le_right _ _))))
      (le_min (key _ _ _ ((min_le_right _ _).trans (min_le_left _ _)))
        (key _ _ _ ((min_le_right _ _).trans (min_le_right _ _))))
  have hmax : max (max (l * L) (l * V)) (max (u * L) (u * V)) ≤ (mx : ℝ) / unit / unit :=
    max_le (max_le (key' _ _ _ ((le_max_left _ _).trans (le_max_left _ _)))
        (key' _ _ _ ((le_max_right _ _).trans (le_max_left _ _))))
      (max_le (key' _ _ _ ((le_max_left _ _).trans (le_max_right _ _)))
        (key' _ _ _ ((le_max_right _ _).trans (le_max_right _ _))))
  have hc := QInterval.product_between_corners (l := l) (u := u) (L := L) (U := V) hx hy
    (m := min (min (l * L) (l * V)) (min (u * L) (u * V)))
    (M := max (max (l * L) (l * V)) (max (u * L) (u * V)))
    ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
    ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  constructor
  · have hd := down_le mn
    calc ((down mn : Int) : ℝ) / unit ≤ _ / unit / unit :=
          div_le_div_of_nonneg_right hd hU.le
      _ ≤ _ := hmin
      _ ≤ x * y := hc.1
  · have hd := le_up mx
    calc x * y ≤ _ := hc.2
      _ ≤ _ / unit / unit := hmax
      _ ≤ ((up mx : Int) : ℝ) / unit := div_le_div_of_nonneg_right hd hU.le

theorem mem_mul {I J : FI} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.mul J).Mem (x * y) := by
  rw [mul_eq]
  split_ifs with h1 h2
  · rw [mem_point_eq h1 hx]
    exact mem_mulPoint _ hy
  · rw [mem_point_eq h2 hy, mul_comm]
    exact mem_mulPoint _ hx
  · exact mem_mulCorners hx hy

theorem mem_ofQ (q : ℚ) : (ofQ q).Mem (q : ℝ) := by
  have hU := unit_pos_real
  have hd : (0 : Int) < q.den := by exact_mod_cast q.den_pos
  have hdR : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hq : (q : ℝ) = (q.num : ℝ) / q.den := by
    exact_mod_cast (Rat.num_div_den q).symm
  unfold Mem ofQ
  constructor
  · rw [div_le_iff₀ hU, hq]
    have h := Int.ediv_mul_le (q.num * unit) (ne_of_gt hd)
    have h' : (((q.num * unit) / (q.den : Int) * (q.den : Int) : Int) : ℝ) ≤ ((q.num * unit : Int) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    rw [div_mul_eq_mul_div, le_div_iff₀ hdR]
    linarith
  · rw [le_div_iff₀ hU, hq]
    have h := Int.ediv_mul_le (-(q.num * unit)) (ne_of_gt hd)
    have h' : ((-(q.num * unit) / (q.den : Int) * (q.den : Int) : Int) : ℝ) ≤ ((-(q.num * unit) : Int) : ℝ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    rw [div_mul_eq_mul_div, div_le_iff₀ hdR]
    linarith

theorem mem_ofQI {I : QInterval} {x : ℝ} (hx : I.Mem x) : (ofQI I).Mem x :=
  ⟨(mem_ofQ I.lo).1.trans hx.1, hx.2.trans (mem_ofQ I.hi).2⟩

theorem mem_point (q : ℚ) : (ofQ q).Mem (q : ℝ) := mem_ofQ q

end FI

end SquaresInCircles.Eight.Arithmetic.Fixed
