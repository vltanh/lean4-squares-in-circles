module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact-rational interval rules

These lemmas prove the real meaning of each arithmetic operation. The
computational part uses only rationals and integers. Root guesses are accepted
only after their squared endpoint inequalities are checked; no property of an
external numerical library, unchecked native evaluation, or oracle is used.
-/

namespace SquaresInCircles.Six.ProofTools

structure RInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace RInterval

def Mem (I : RInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def point (q : ℚ) : RInterval := ⟨q,q⟩
def add (I J : RInterval) : RInterval := ⟨I.lo+J.lo,I.hi+J.hi⟩
def neg (I : RInterval) : RInterval := ⟨-I.hi,-I.lo⟩
def sub (I J : RInterval) : RInterval := add I (neg J)
def hull (I J : RInterval) : RInterval := ⟨min I.lo J.lo,max I.hi J.hi⟩
def meet (I J : RInterval) : RInterval := ⟨max I.lo J.lo,min I.hi J.hi⟩
def minimum (I J : RInterval) : RInterval := ⟨min I.lo J.lo,min I.hi J.hi⟩
def maximum (I J : RInterval) : RInterval := ⟨max I.lo J.lo,max I.hi J.hi⟩

def mul (I J : RInterval) : RInterval :=
  ⟨min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)),
   max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))⟩

def absolute (I : RInterval) : RInterval :=
  if 0 ≤ I.lo then I else if I.hi ≤ 0 then neg I else ⟨0,max (-I.lo) I.hi⟩

def square (I : RInterval) : RInterval :=
  let A := absolute I
  ⟨A.lo^2,A.hi^2⟩

def power (I : RInterval) : ℕ → RInterval
  | 0 => point 1
  | n+1 => mul (power I n) I

def invRaw (I : RInterval) : RInterval := ⟨1/I.hi,1/I.lo⟩

def inverse (I : RInterval) : Option RInterval :=
  if 0 < I.lo then some (invRaw I)
  else if I.hi < 0 then some (neg (invRaw (neg I))) else none

/-- A proposed 80-bit dyadic lower root. Correctness is checked by `root`,
not assumed from the integer-root implementation. -/
def rootGuess (q : ℚ) : ℚ :=
  (Nat.sqrt ((q.num.toNat * (2^80 : ℕ)^2) / q.den) : ℚ) / (2^80 : ℕ)

def root (I : RInterval) : Option RInterval :=
  let l := rootGuess (max I.lo 0)
  let u := rootGuess (max I.hi 0) + 1/(2^80 : ℕ)
  if 0 ≤ l ∧ l^2 ≤ max I.lo 0 ∧ 0 ≤ u ∧ max I.hi 0 ≤ u^2
  then some ⟨l,u⟩ else none

@[simp] lemma cast_min (a b : ℚ) : ((min a b : ℚ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
  · rw [min_eq_right (le_of_not_ge h), min_eq_right (by exact_mod_cast le_of_not_ge h)]

@[simp] lemma cast_max (a b : ℚ) : ((max a b : ℚ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left (le_of_not_ge h), max_eq_left (by exact_mod_cast le_of_not_ge h)]

lemma mem_point (q : ℚ) : (point q).Mem (q : ℝ) := ⟨le_rfl,le_rfl⟩

lemma ordered_of_mem {I : RInterval} {x : ℝ} (hx : I.Mem x) : I.lo ≤ I.hi := by
  exact_mod_cast hx.1.trans hx.2

lemma mem_add {I J : RInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (add I J).Mem (x+y) := by
  constructor <;> simp only [add, Rat.cast_add] <;> linarith [hx.1,hx.2,hy.1,hy.2]

lemma mem_neg {I : RInterval} {x : ℝ} (hx : I.Mem x) : (neg I).Mem (-x) := by
  constructor <;> simp only [neg, Rat.cast_neg] <;> linarith [hx.1,hx.2]

lemma mem_sub {I J : RInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (sub I J).Mem (x-y) := by
  simpa only [sub_eq_add_neg] using mem_add hx (mem_neg hy)

lemma mem_hull_left {I J : RInterval} {x : ℝ} (hx : I.Mem x) : (hull I J).Mem x := by
  constructor
  · exact (by simpa [hull] using (min_le_left (I.lo : ℝ) J.lo)).trans hx.1
  · exact hx.2.trans (by simpa [hull] using (le_max_left (I.hi : ℝ) J.hi))

lemma mem_hull_right {I J : RInterval} {x : ℝ} (hx : J.Mem x) : (hull I J).Mem x := by
  constructor
  · exact (by simpa [hull] using (min_le_right (I.lo : ℝ) J.lo)).trans hx.1
  · exact hx.2.trans (by simpa [hull] using (le_max_right (I.hi : ℝ) J.hi))

lemma mem_meet {I J : RInterval} {x : ℝ} (hx : I.Mem x) (hy : J.Mem x) :
    (meet I J).Mem x := by
  constructor
  · simpa [meet] using max_le hx.1 hy.1
  · simpa [meet] using le_min hx.2 hy.2

lemma mem_minimum {I J : RInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (minimum I J).Mem (min x y) := by
  constructor
  · simpa [minimum] using min_le_min hx.1 hy.1
  · simpa [minimum] using min_le_min hx.2 hy.2

lemma mem_maximum {I J : RInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (maximum I J).Mem (max x y) := by
  constructor
  · simpa [maximum] using max_le_max hx.1 hy.1
  · simpa [maximum] using max_le_max hx.2 hy.2

private lemma rectangle_upper {a b c d x y U : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (h00 : a*c ≤ U) (h01 : a*d ≤ U) (h10 : b*c ≤ U) (h11 : b*d ≤ U) : x*y ≤ U := by
  by_cases hx0 : 0 ≤ x
  · have hxy := mul_le_mul_of_nonneg_left hy.2 hx0
    by_cases hd : 0 ≤ d
    · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hd).trans h11)
    · exact hxy.trans ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hd)).trans h01)
  · have hxy := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hx0)
    by_cases hc : 0 ≤ c
    · exact hxy.trans ((mul_le_mul_of_nonneg_right hx.2 hc).trans h10)
    · exact hxy.trans ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hc)).trans h00)

private lemma rectangle_lower {a b c d x y L : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (h00 : L ≤ a*c) (h01 : L ≤ a*d) (h10 : L ≤ b*c) (h11 : L ≤ b*d) : L ≤ x*y := by
  have hh := rectangle_upper (x := -x) (y := y) (a := -b) (b := -a)
    (c := c) (d := d) (U := -L)
    ⟨by linarith [hx.2],by linarith [hx.1]⟩ hy
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  nlinarith

lemma mem_mul {I J : RInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (mul I J).Mem (x*y) := by
  constructor
  · apply rectangle_lower hx hy
    · exact_mod_cast (min_le_left _ _).trans (min_le_left (I.lo*J.lo) (I.lo*J.hi))
    · exact_mod_cast (min_le_left _ _).trans (min_le_right (I.lo*J.lo) (I.lo*J.hi))
    · exact_mod_cast (min_le_right _ _).trans (min_le_left (I.hi*J.lo) (I.hi*J.hi))
    · exact_mod_cast (min_le_right _ _).trans (min_le_right (I.hi*J.lo) (I.hi*J.hi))
  · apply rectangle_upper hx hy
    · exact_mod_cast (le_max_left (I.lo*J.lo) (I.lo*J.hi)).trans (le_max_left _ _)
    · exact_mod_cast (le_max_right (I.lo*J.lo) (I.lo*J.hi)).trans (le_max_left _ _)
    · exact_mod_cast (le_max_left (I.hi*J.lo) (I.hi*J.hi)).trans (le_max_right _ _)
    · exact_mod_cast (le_max_right (I.hi*J.lo) (I.hi*J.hi)).trans (le_max_right _ _)

lemma mem_absolute {I : RInterval} {x : ℝ} (hx : I.Mem x) : (absolute I).Mem |x| := by
  unfold absolute
  split_ifs with hl hh
  · have h0 : 0 ≤ x := (by exact_mod_cast hl).trans hx.1
    simpa only [abs_of_nonneg h0] using hx
  · have h0 : x ≤ 0 := hx.2.trans (by exact_mod_cast hh)
    simpa only [abs_of_nonpos h0] using mem_neg hx
  · constructor
    · simpa using abs_nonneg x
    · simp only [cast_max, Rat.cast_neg]
      apply abs_le.mpr
      constructor
      · have hh := le_max_left (-(I.lo : ℝ)) (I.hi : ℝ)
        linarith [hx.1]
      · exact hx.2.trans (le_max_right _ _)

lemma absolute_lo_nonneg (I : RInterval) : 0 ≤ (absolute I).lo := by
  unfold absolute
  split_ifs <;> dsimp [neg] <;> linarith

lemma mem_square {I : RInterval} {x : ℝ} (hx : I.Mem x) : (square I).Mem (x^2) := by
  have ha := mem_absolute hx
  have hl : (0 : ℝ) ≤ (absolute I).lo := by exact_mod_cast absolute_lo_nonneg I
  have hlow := pow_le_pow_left₀ hl ha.1 2
  have hhi := pow_le_pow_left₀ (abs_nonneg x) ha.2 2
  constructor <;> simp only [square, Rat.cast_pow] <;> nlinarith [sq_abs x]

lemma mem_power {I : RInterval} {x : ℝ} (hx : I.Mem x) (n : ℕ) :
    (power I n).Mem (x^n) := by
  induction n with
  | zero => simpa [power] using mem_point 1
  | succ n ih => simpa only [power, pow_succ] using mem_mul ih hx

private lemma mem_invRaw {I : RInterval} {x : ℝ} (hx : I.Mem x) (hl : 0 < I.lo) :
    (invRaw I).Mem (1/x) := by
  have hL : (0 : ℝ) < I.lo := by exact_mod_cast hl
  have hx0 : 0 < x := hL.trans_le hx.1
  constructor
  · simpa [invRaw] using one_div_le_one_div_of_le hx0 hx.2
  · simpa [invRaw] using one_div_le_one_div_of_le hL hx.1

lemma mem_inverse {I J : RInterval} {x : ℝ} (hx : I.Mem x)
    (h : inverse I = some J) : J.Mem (1/x) := by
  unfold inverse at h
  split_ifs at h with hl hh
  · cases h
    exact mem_invRaw hx hl
  · cases h
    have hneg : 0 < (neg I).lo := by dsimp [neg]; linarith
    have hh := mem_neg (mem_invRaw (mem_neg hx) hneg)
    simpa only [one_div_neg, neg_neg] using hh
  · cases h

lemma mem_root {I J : RInterval} {x : ℝ} (hx : I.Mem x)
    (h : root I = some J) : J.Mem (Real.sqrt x) := by
  unfold root at h
  split_ifs at h with hv
  · cases h
    rcases hv with ⟨hl0,hlsq,hu0,husq⟩
    have hl0' : (0 : ℝ) ≤ rootGuess (max I.lo 0) := by exact_mod_cast hl0
    have hu0' : (0 : ℝ) ≤ rootGuess (max I.hi 0)+1/(2^80 : ℕ) := by exact_mod_cast hu0
    have hlsq' : ((rootGuess (max I.lo 0) : ℚ) : ℝ)^2 ≤ max (I.lo : ℝ) 0 := by
      exact_mod_cast hlsq
    have husq' : max (I.hi : ℝ) 0 ≤
        (((rootGuess (max I.hi 0)+1/(2^80 : ℕ) : ℚ) : ℝ))^2 := by
      exact_mod_cast husq
    by_cases hx0 : 0 ≤ x
    · have hlow : max (I.lo : ℝ) 0 ≤ x := max_le hx.1 hx0
      have hhigh : x ≤ max (I.hi : ℝ) 0 := hx.2.trans (le_max_left _ _)
      have hs := Real.sq_sqrt hx0
      have hn := Real.sqrt_nonneg x
      constructor <;> dsimp [Mem] <;> push_cast at * <;> nlinarith
    · have hIlo : (I.lo : ℝ) ≤ 0 := by linarith [hx.1]
      rw [max_eq_right hIlo] at hlsq'
      rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx0)]
      constructor <;> dsimp [Mem] <;> push_cast at * <;> nlinarith
  · cases h

end RInterval
end SquaresInCircles.Six.ProofTools
