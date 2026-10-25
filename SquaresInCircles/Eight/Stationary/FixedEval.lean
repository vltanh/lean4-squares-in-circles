module

public import SquaresInCircles.Eight.Stationary.Expression

/-!
# Eight squares: fixed-point interval evaluation of formulas

An interval `DI` is a pair of integers `lo, hi`, read as `[lo / 2 ^ p, hi / 2 ^ p]`, and every
operation rounds outwards to that scale. One pass of `eval` over a `Formula` of `Expression.lean`
encloses its value at every point of a box of such intervals (`eval_sound`). Square roots and
reciprocals are accepted only for arguments with a positive lower end, so a successful pass also
shows that the formula is regular on the box (`Formula.RegularAt`). Every intermediate number is
an integer at the fixed scale `2 ^ p`, so no denominators accumulate along the formula.

On a rational box the Boolean tests `bounded` and `regular` run one pass; their success gives the
bounds, and the regularity, at every real point of the box (`bounded_sound`, `regular_sound`).
`inside` tests that one box lies in another. The generated module
`Generated/LocalStationaryBounds.lean` decides these tests with `decide +kernel`; its generator
runs the same integer arithmetic (`fx_eval` in `scripts/eight/generate_stationary.py`) before it
writes a bound.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Stationary.FixedEval
open Arithmetic

/-- The scale `2 ^ p`, as an integer. -/
def scale (p : ℕ) : Int := ((2 ^ p : ℕ) : Int)

theorem scale_pos (p : ℕ) : 0 < scale p := by
  unfold scale
  exact_mod_cast Nat.pos_of_ne_zero (pow_ne_zero p (by norm_num))

theorem scale_real (p : ℕ) : ((scale p : Int) : ℝ) = 2 ^ p := by
  simp [scale]

theorem two_pow_pos (p : ℕ) : (0 : ℝ) < 2 ^ p := by positivity

/-- `⌊a / 2 ^ p⌋`. -/
def down (p : ℕ) (a : Int) : Int := a / scale p

/-- `⌈a / 2 ^ p⌉`. -/
def up (p : ℕ) (a : Int) : Int := -((-a) / scale p)

/-- `⌊a / d⌋ * d ≤ a` for a positive integer `d`, in the reals. -/
theorem ediv_mul_le_real (a : Int) {d : Int} (hd : 0 < d) : ((a / d : Int) : ℝ) * d ≤ a := by
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hd)

/-- `a ≤ ⌈a / d⌉ * d` for a positive integer `d`, in the reals. -/
theorem le_neg_ediv_mul_real (a : Int) {d : Int} (hd : 0 < d) :
    (a : ℝ) ≤ ((-((-a) / d) : Int) : ℝ) * d := by
  have h := ediv_mul_le_real (-a) hd
  push_cast at h ⊢
  linarith

theorem down_mul_le (p : ℕ) (a : Int) : (down p a : ℝ) * 2 ^ p ≤ a := by
  rw [← scale_real]
  exact ediv_mul_le_real a (scale_pos p)

theorem le_up_mul (p : ℕ) (a : Int) : (a : ℝ) ≤ (up p a : ℝ) * 2 ^ p := by
  rw [← scale_real]
  exact le_neg_ediv_mul_real a (scale_pos p)

/-- An interval `[lo / 2 ^ p, hi / 2 ^ p]` with integer ends; the scale `p` is a parameter of
the operations. -/
structure DI where
  lo : Int
  hi : Int

namespace DI

/-- `x` lies in the interval at the scale `2 ^ p`, stated without division. -/
def Mem (p : ℕ) (I : DI) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x * 2 ^ p ∧ x * 2 ^ p ≤ (I.hi : ℝ)

def add (I J : DI) : DI := ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : DI) : DI := ⟨-I.hi, -I.lo⟩

/-- The product: the least and the greatest corner product, rounded down and up to the scale. -/
def mul (p : ℕ) (I J : DI) : DI :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  ⟨down p (min (min a b) (min c d)), up p (max (max a b) (max c d))⟩

/-- The reciprocal `[⌊2 ^ (2p) / hi⌋, ⌈2 ^ (2p) / lo⌉]` of an interval with positive lower end;
it encloses the reciprocals (`mem_inv`). -/
def inv (p : ℕ) (I : DI) : DI := ⟨scale (2 * p) / I.hi, -((-scale (2 * p)) / I.lo)⟩

/-- The square root `[⌊√(lo 2 ^ p)⌋, ⌊√(hi 2 ^ p)⌋ + 1]` of an interval with nonnegative ends; it
encloses the square roots when the lower end is positive (`mem_sqrt`). -/
def sqrt (p : ℕ) (I : DI) : DI :=
  ⟨((Nat.sqrt (I.lo.toNat * 2 ^ p) : ℕ) : Int), ((Nat.sqrt (I.hi.toNat * 2 ^ p) + 1 : ℕ) : Int)⟩

/-- The point `1`. -/
def one (p : ℕ) : DI := ⟨scale p, scale p⟩

/-- Powers, by repeated multiplication. -/
def pow (p : ℕ) (I : DI) : ℕ → DI
  | 0 => one p
  | k + 1 => mul p (pow p I k) I

/-- An outward enclosure of a rational number. -/
def ofRat (p : ℕ) (q : ℚ) : DI := ⟨(q.num * scale p) / q.den, -((-(q.num * scale p)) / q.den)⟩

theorem mem_add {p : ℕ} {I J : DI} {x y : ℝ} (hx : I.Mem p x) (hy : J.Mem p y) :
    (I.add J).Mem p (x + y) := by
  unfold Mem add at *
  push_cast
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {p : ℕ} {I : DI} {x : ℝ} (hx : I.Mem p x) : I.neg.Mem p (-x) := by
  unfold Mem neg at *
  push_cast
  constructor <;> nlinarith [hx.1, hx.2]

theorem mem_mul {p : ℕ} {I J : DI} {x y : ℝ} (hx : I.Mem p x) (hy : J.Mem p y) :
    (I.mul p J).Mem p (x * y) := by
  have h2 := two_pow_pos p
  set X := x * 2 ^ p
  set Y := y * 2 ^ p
  have hXY : X * Y = (x * y) * 2 ^ p * 2 ^ p := by ring
  obtain ⟨hl, hu⟩ := QInterval.product_between_corners (x := X) (y := Y) hx hy
    (m := min (min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi)) (min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi)))
    (M := max (max ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi)) (max ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi)))
    ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
    ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hmin : (((min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)) : Int)) : ℝ) =
      min (min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi)) (min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi)) := by
    push_cast; rfl
  have hmax : (((max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)) : Int)) : ℝ) =
      max (max ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi)) (max ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi)) := by
    push_cast; rfl
  have hd := down_mul_le p (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)))
  have hu' := le_up_mul p (max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)))
  rw [hmin] at hd
  rw [hmax] at hu'
  constructor
  · show ((down p _ : Int) : ℝ) ≤ x * y * 2 ^ p
    have : ((down p (min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))) : Int) : ℝ)
        * 2 ^ p ≤ x * y * 2 ^ p * 2 ^ p := by linarith
    exact le_of_mul_le_mul_right this h2
  · show x * y * 2 ^ p ≤ ((up p _ : Int) : ℝ)
    have : x * y * 2 ^ p * 2 ^ p ≤ ((up p (max (max (I.lo * J.lo) (I.lo * J.hi))
        (max (I.hi * J.lo) (I.hi * J.hi))) : Int) : ℝ) * 2 ^ p := by linarith
    exact le_of_mul_le_mul_right this h2

/-- For a positive lower end the reciprocal interval encloses `x⁻¹`, and `x` is positive. -/
theorem mem_inv {p : ℕ} {I : DI} {x : ℝ} (hx : I.Mem p x) (hpos : 0 < I.lo) :
    (I.inv p).Mem p x⁻¹ ∧ 0 < x := by
  have h2 := two_pow_pos p
  have hlo : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hX : 0 < x * 2 ^ p := hlo.trans_le hx.1
  have hx0 : 0 < x := by
    by_contra h; push Not at h
    nlinarith
  have hhi : (0 : ℝ) < I.hi := hX.trans_le hx.2
  have hhi' : (0 : Int) < I.hi := by exact_mod_cast hhi
  have hS : ((scale (2 * p) : Int) : ℝ) = 2 ^ p * 2 ^ p := by rw [scale_real]; ring
  refine ⟨⟨?_, ?_⟩, hx0⟩
  · -- `⌊2^(2p) / hi⌋ ≤ 2^(2p) / hi ≤ x⁻¹ 2^p`
    have h := ediv_mul_le_real (scale (2 * p)) hhi'
    rw [hS] at h
    show ((scale (2 * p) / I.hi : Int) : ℝ) ≤ x⁻¹ * 2 ^ p
    have hq : ((scale (2 * p) / I.hi : Int) : ℝ) ≤ 2 ^ p * 2 ^ p / I.hi := by
      rw [le_div_iff₀ hhi]; exact h
    have hq2 : 2 ^ p * 2 ^ p / (I.hi : ℝ) ≤ x⁻¹ * 2 ^ p := by
      rw [div_le_iff₀ hhi]
      have : x * 2 ^ p ≤ I.hi := hx.2
      field_simp
      nlinarith
    exact hq.trans hq2
  · have h := le_neg_ediv_mul_real (scale (2 * p)) hpos
    rw [hS] at h
    show x⁻¹ * 2 ^ p ≤ ((-((-scale (2 * p)) / I.lo) : Int) : ℝ)
    have hq : 2 ^ p * 2 ^ p / (I.lo : ℝ) ≤ ((-((-scale (2 * p)) / I.lo) : Int) : ℝ) := by
      rw [div_le_iff₀ hlo]; exact h
    have hq2 : x⁻¹ * 2 ^ p ≤ 2 ^ p * 2 ^ p / (I.lo : ℝ) := by
      rw [le_div_iff₀ hlo]
      have : (I.lo : ℝ) ≤ x * 2 ^ p := hx.1
      field_simp
      nlinarith
    exact hq2.trans hq

/-- For a positive lower end the square-root interval encloses `√x`, and `x` is positive. -/
theorem mem_sqrt {p : ℕ} {I : DI} {x : ℝ} (hx : I.Mem p x) (hpos : 0 < I.lo) :
    (I.sqrt p).Mem p (Real.sqrt x) ∧ 0 < x := by
  have h2 := two_pow_pos p
  have hlo : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hX : 0 < x * 2 ^ p := hlo.trans_le hx.1
  have hx0 : 0 < x := by
    by_contra h; push Not at h
    nlinarith
  have hhi : (0 : ℝ) < I.hi := hX.trans_le hx.2
  have hlo_nat : ((I.lo.toNat : ℕ) : ℝ) = I.lo := by
    have := Int.toNat_of_nonneg hpos.le
    exact_mod_cast this
  have hhi_nat : ((I.hi.toNat : ℕ) : ℝ) = I.hi := by
    have := Int.toNat_of_nonneg (show (0 : Int) ≤ I.hi by exact_mod_cast hhi.le)
    exact_mod_cast this
  -- `√x · 2^p = √(x 2^p · 2^p)`
  have hkey : Real.sqrt x * 2 ^ p = Real.sqrt (x * 2 ^ p * 2 ^ p) := by
    rw [show x * 2 ^ p * 2 ^ p = x * (2 ^ p) ^ 2 by ring, Real.sqrt_mul hx0.le,
      Real.sqrt_sq h2.le]
  refine ⟨⟨?_, ?_⟩, hx0⟩
  · -- `⌊√(lo 2^p)⌋ ≤ √(lo 2^p) ≤ √(x 2^p 2^p)`
    set N := I.lo.toNat * 2 ^ p
    have hs := Nat.sqrt_le' N
    have hN : (N : ℝ) = I.lo * 2 ^ p := by simp [N, hlo_nat]
    show (((Nat.sqrt N : ℕ) : Int) : ℝ) ≤ Real.sqrt x * 2 ^ p
    rw [hkey]
    have hs' : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ x * 2 ^ p * 2 ^ p := by
      have : ((Nat.sqrt N ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hs
      push_cast at this
      rw [hN] at this
      nlinarith [hx.1]
    push_cast
    exact Real.le_sqrt_of_sq_le hs'
  · set N := I.hi.toNat * 2 ^ p
    have hs := Nat.lt_succ_sqrt' N
    have hN : (N : ℝ) = I.hi * 2 ^ p := by simp [N, hhi_nat]
    show Real.sqrt x * 2 ^ p ≤ (((Nat.sqrt N + 1 : ℕ) : Int) : ℝ)
    rw [hkey]
    have hs' : x * 2 ^ p * 2 ^ p ≤ ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
      have : (N : ℝ) < ((Nat.succ (Nat.sqrt N) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hs
      push_cast at this
      rw [hN] at this
      nlinarith [hx.2]
    push_cast
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hs'⟩

theorem mem_pow {p : ℕ} {I : DI} {x : ℝ} (hx : I.Mem p x) : ∀ k, (I.pow p k).Mem p (x ^ k)
  | 0 => by
    unfold Mem pow one
    rw [scale_real]
    simp
  | k + 1 => by
    rw [pow_succ]
    exact mem_mul (mem_pow hx k) hx

theorem mem_ofRat (p : ℕ) (q : ℚ) : (ofRat p q).Mem p q := by
  have hd : (0 : Int) < q.den := by exact_mod_cast q.den_pos
  have hdR : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hq : (q : ℝ) = (q.num : ℝ) / q.den := by exact_mod_cast (Rat.num_div_den q).symm
  have h1 := ediv_mul_le_real (q.num * scale p) hd
  have h2 := le_neg_ediv_mul_real (q.num * scale p) hd
  push_cast at h1 h2
  rw [scale_real] at h1 h2
  unfold Mem ofRat
  rw [hq]
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hdR]
    push_cast; linarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ hdR]
    push_cast; linarith

end DI

/-- One pass of outward-rounded interval arithmetic over a formula, with the intervals `B` for
the variables; `none` when a reciprocal or a square root meets a lower end that is not
positive. -/
def eval {n : ℕ} (p : ℕ) (B : Fin n → DI) : Formula n → Option DI
  | .const q => some (DI.ofRat p q)
  | .var i => some (B i)
  | .add a b => match eval p B a, eval p B b with
    | some x, some y => some (x.add y)
    | _, _ => none
  | .neg a => match eval p B a with
    | some x => some x.neg
    | none => none
  | .mul a b => match eval p B a, eval p B b with
    | some x, some y => some (x.mul p y)
    | _, _ => none
  | .inv a => match eval p B a with
    | some x => if 0 < x.lo then some (x.inv p) else none
    | none => none
  | .sqrt a => match eval p B a with
    | some x => if 0 < x.lo then some (x.sqrt p) else none
    | none => none
  | .pow a k => match eval p B a with
    | some x => some (x.pow p k)
    | none => none

/-- If every variable lies in its interval, a successful pass encloses the value of the formula,
and the formula is regular there. -/
theorem eval_sound {n p : ℕ} {B : Fin n → DI} {env : Fin n → ℝ}
    (hB : ∀ i, (B i).Mem p (env i)) :
    ∀ (f : Formula n) {I : DI}, eval p B f = some I → I.Mem p (f.eval env) ∧ f.RegularAt env := by
  intro f
  induction f with
  | const q =>
    intro I h
    simp only [eval, Option.some.injEq] at h
    subst h
    exact ⟨DI.mem_ofRat p q, trivial⟩
  | var i =>
    intro I h
    simp only [eval, Option.some.injEq] at h
    subst h
    exact ⟨hB i, trivial⟩
  | add a b ha hb =>
    intro I h
    cases hx : eval p B a <;> cases hy : eval p B b <;> simp [eval, hx, hy] at h
    subst h
    obtain ⟨h1, r1⟩ := ha hx
    obtain ⟨h2, r2⟩ := hb hy
    exact ⟨DI.mem_add h1 h2, r1, r2⟩
  | neg a ha =>
    intro I h
    cases hx : eval p B a <;> simp [eval, hx] at h
    subst h
    obtain ⟨h1, r1⟩ := ha hx
    exact ⟨DI.mem_neg h1, r1⟩
  | mul a b ha hb =>
    intro I h
    cases hx : eval p B a <;> cases hy : eval p B b <;> simp [eval, hx, hy] at h
    subst h
    obtain ⟨h1, r1⟩ := ha hx
    obtain ⟨h2, r2⟩ := hb hy
    exact ⟨DI.mem_mul h1 h2, r1, r2⟩
  | inv a ha =>
    intro I h
    cases hx : eval p B a with
    | none => simp [eval, hx] at h
    | some x =>
      simp only [eval, hx] at h
      split_ifs at h with hpos
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, r1⟩ := ha hx
      obtain ⟨hm, hp⟩ := DI.mem_inv h1 hpos
      exact ⟨hm, r1, ne_of_gt hp⟩
  | sqrt a ha =>
    intro I h
    cases hx : eval p B a with
    | none => simp [eval, hx] at h
    | some x =>
      simp only [eval, hx] at h
      split_ifs at h with hpos
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, r1⟩ := ha hx
      obtain ⟨hm, hp⟩ := DI.mem_sqrt h1 hpos
      exact ⟨hm, r1, hp⟩
  | pow a k ha =>
    intro I h
    cases hx : eval p B a <;> simp [eval, hx] at h
    subst h
    obtain ⟨h1, r1⟩ := ha hx
    exact ⟨DI.mem_pow h1 k, r1⟩

/-- The outward fixed-point enclosure of a rational box. -/
def ofBox {n : ℕ} (p : ℕ) (B : QBox n) (i : Fin n) : DI :=
  ⟨(DI.ofRat p (B i).lo).lo, (DI.ofRat p (B i).hi).hi⟩

theorem mem_ofBox {n p : ℕ} {B : QBox n} {env : Fin n → ℝ} (he : B.Mem env) (i : Fin n) :
    (ofBox p B i).Mem p (env i) := by
  have h2 := two_pow_pos p
  have hl := (DI.mem_ofRat p (B i).lo).1
  have hu := (DI.mem_ofRat p (B i).hi).2
  exact ⟨hl.trans (mul_le_mul_of_nonneg_right (he i).1 h2.le),
    (mul_le_mul_of_nonneg_right (he i).2 h2.le).trans hu⟩

/-- The test that one pass on `B` encloses `f` in `[lo, hi]`, with `lo` and `hi` rounded
inwards. -/
def bounded {n : ℕ} (p : ℕ) (B : QBox n) (f : Formula n) (lo hi : ℚ) : Bool :=
  match eval p (ofBox p B) f with
  | some I => decide ((DI.ofRat p lo).hi ≤ I.lo ∧ I.hi ≤ (DI.ofRat p hi).lo)
  | none => false

/-- The test that one pass over `f` on `B` succeeds. -/
def regular {n : ℕ} (p : ℕ) (B : QBox n) (f : Formula n) : Bool :=
  (eval p (ofBox p B) f).isSome

/-- If `bounded` succeeds, `lo ≤ f ≤ hi` at every real point of the box. -/
theorem bounded_sound {n p : ℕ} {B : QBox n} {f : Formula n} {lo hi : ℚ}
    (h : bounded p B f lo hi = true) {env : Fin n → ℝ} (he : B.Mem env) :
    (lo : ℝ) ≤ f.eval env ∧ f.eval env ≤ hi := by
  have h2 := two_pow_pos p
  cases hI : eval p (ofBox p B) f with
  | none => simp [bounded, hI] at h
  | some I =>
    have hc : (DI.ofRat p lo).hi ≤ I.lo ∧ I.hi ≤ (DI.ofRat p hi).lo := by
      simpa [bounded, hI] using h
    have hm := (eval_sound (mem_ofBox he) f hI).1
    have hl : ((DI.ofRat p lo).hi : ℝ) ≤ I.lo := by exact_mod_cast hc.1
    have hu : (I.hi : ℝ) ≤ (DI.ofRat p hi).lo := by exact_mod_cast hc.2
    have hlo := (DI.mem_ofRat p lo).2
    have hhi := (DI.mem_ofRat p hi).1
    constructor
    · exact le_of_mul_le_mul_right (hlo.trans (hl.trans hm.1)) h2
    · exact le_of_mul_le_mul_right (hm.2.trans (hu.trans hhi)) h2

/-- If `regular` succeeds, `f` is regular at every real point of the box. -/
theorem regular_sound {n p : ℕ} {B : QBox n} {f : Formula n} (h : regular p B f = true)
    {env : Fin n → ℝ} (he : B.Mem env) : f.RegularAt env := by
  cases hI : eval p (ofBox p B) f with
  | none => simp [regular, hI] at h
  | some I => exact (eval_sound (mem_ofBox he) f hI).2

/-- The test that the box `B` lies in `target`, with weak inequalities in every coordinate. -/
def inside (B target : QBox 3) : Bool :=
  decide (∀ i, (target i).lo ≤ (B i).lo ∧ (B i).hi ≤ (target i).hi)

end SquaresInCircles.Eight.Stationary.FixedEval
