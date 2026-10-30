module

public import SquaresInCircles.Eight.Arithmetic.RowCheck

/-!
# Eight squares: integer bounds for the arctangent

The gap leaves of the coverage trees (`PairCover.lean`) bound `arctan` at the ends of the tangent
intervals. For a rational `x`, `atanLo x` and `atanHi x` are integers with
`atanLo x / 10²⁰ ≤ arctan x ≤ atanHi x / 10²⁰` (`atanLo_le`, `le_atanHi`).

For `x ≥ 0` and the anchor `c = j / 16` nearest to `x`, with `j ≤ 16`, the addition formula gives
`arctan x = arctan c + arctan z` with `z = (x - c) / (1 + x c)` (`atan_split`), and `|z| ≤ 1/32`
when `x ≤ 1`. For `z ≥ 0` the alternating series gives
`z - z³/3 + ⋯ - z¹¹/11 ≤ arctan z ≤ z - z³/3 + ⋯ + z⁹/9`, for `z < 0` the bounds follow by
oddness, and both are rounded outwards to integers over `10²⁰` (`seriesLo`, `seriesHi`). For
`x < 0` the bounds are `-2` and `2`.

The anchors `arctan (j / 16)` are integers over `10²⁰`, rounded down and up (`anchorLo`,
`anchorHi`). The anchor of `j + 1` follows from that of `j` by the same addition formula with
`z = 16 / (256 + j (j + 1))`; one `decide` checks the sixteen steps (`anchors_check`), and
induction on `j` gives the bounds of all seventeen anchors (`anchor_bounds`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic.PairCover

open Arithmetic

/-- `10²⁰`, the scale of the angle bounds. -/
def angleUnit : Int := 100000000000000000000

theorem angleUnit_pos : (0 : ℝ) < angleUnit := by norm_num [angleUnit]

/-- `⌊q⌋`. -/
def floorQ (q : ℚ) : Int := q.num / (q.den : Int)

/-- `⌈q⌉`. -/
def ceilQ (q : ℚ) : Int := -floorQ (-q)

theorem floorQ_le (q : ℚ) : (floorQ q : ℝ) ≤ q := by
  have hd : (0 : Int) < q.den := by exact_mod_cast q.pos
  have hdR : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have h := Int.ediv_mul_le q.num (ne_of_gt hd)
  have h' : ((q.num / (q.den : Int) * (q.den : Int) : Int) : ℝ) ≤ (q.num : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  rw [Rat.cast_def, floorQ, le_div_iff₀ hdR]
  exact h'

theorem le_ceilQ (q : ℚ) : (q : ℝ) ≤ ceilQ q := by
  have h := floorQ_le (-q)
  simp only [ceilQ, Int.cast_neg, Rat.cast_neg] at h ⊢
  linarith

/-! ### The alternating series -/

/-- `z - z³/3 + z⁵/5 - z⁷/7 + z⁹/9 - z¹¹/11`, below `arctan z` for `z ≥ 0`. -/
def atanPolyLo (z : ℚ) : ℚ :=
  z * (1 - z * z * (1 / 3 - z * z * (1 / 5 - z * z * (1 / 7 - z * z * (1 / 9 - z * z / 11)))))

/-- `z - z³/3 + z⁵/5 - z⁷/7 + z⁹/9`, above `arctan z` for `z ≥ 0`. -/
def atanPolyHi (z : ℚ) : ℚ :=
  z * (1 - z * z * (1 / 3 - z * z * (1 / 5 - z * z * (1 / 7 - z * z / 9))))

theorem atanPolyLo_cast (z : ℚ) :
    (atanPolyLo z : ℝ) = z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 + z ^ 9 / 9 - z ^ 11 / 11 := by
  simp only [atanPolyLo]
  push_cast
  ring

theorem atanPolyHi_cast (z : ℚ) :
    (atanPolyHi z : ℝ) = z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 + z ^ 9 / 9 := by
  simp only [atanPolyHi]
  push_cast
  ring

theorem atanPolyLo_le {z : ℝ} (hz : 0 ≤ z) :
    z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 + z ^ 9 / 9 - z ^ 11 / 11 ≤ Real.arctan z := by
  have hh := nonneg_of_deriv_nonneg
    (fun t => Real.arctan t - (t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 - t ^ 11 / 11))
    (Real.differentiable_arctan.sub (by fun_prop)) (by norm_num)
    (fun x _ => by
      have hd : (0 : ℝ) < 1 + x ^ 2 := by positivity
      have hid : 1 / (1 + x ^ 2) - (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10) =
          x ^ 12 / (1 + x ^ 2) := by
        field_simp
        ring
      have hp : deriv (fun t : ℝ => t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 -
          t ^ 11 / 11) x = 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 := by
        simp (disch := fun_prop)
        ring
      rw [deriv_fun_sub (Real.differentiableAt_arctan x) (by fun_prop), Real.deriv_arctan, hp,
        hid]
      positivity) hz
  linarith

theorem arctan_le_atanPolyHi {z : ℝ} (hz : 0 ≤ z) :
    Real.arctan z ≤ z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 + z ^ 9 / 9 := by
  have hh := nonneg_of_deriv_nonneg
    (fun t => (t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9) - Real.arctan t)
    ((by fun_prop : Differentiable ℝ fun t : ℝ => t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 +
      t ^ 9 / 9).sub Real.differentiable_arctan) (by norm_num)
    (fun x _ => by
      have hd : (0 : ℝ) < 1 + x ^ 2 := by positivity
      have hid : (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8) - 1 / (1 + x ^ 2) =
          x ^ 10 / (1 + x ^ 2) := by
        field_simp
        ring
      have hp : deriv (fun t : ℝ => t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9) x =
          1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 := by
        simp (disch := fun_prop)
        ring
      rw [deriv_fun_sub (by fun_prop) (Real.differentiableAt_arctan x), Real.deriv_arctan, hp,
        hid]
      positivity) hz
  linarith

/-- A lower bound of `arctan z` over `angleUnit`: the series rounded down, by oddness for
`z < 0`. -/
def seriesLo (z : ℚ) : Int :=
  if 0 ≤ z then floorQ (atanPolyLo z * angleUnit) else -ceilQ (atanPolyHi (-z) * angleUnit)

/-- An upper bound of `arctan z` over `angleUnit`: the series rounded up, by oddness for
`z < 0`. -/
def seriesHi (z : ℚ) : Int :=
  if 0 ≤ z then ceilQ (atanPolyHi z * angleUnit) else -floorQ (atanPolyLo (-z) * angleUnit)

theorem seriesLo_le (z : ℚ) : (seriesLo z : ℝ) / angleUnit ≤ Real.arctan z := by
  have hA := angleUnit_pos
  unfold seriesLo
  split_ifs with hz
  · have h1 := floorQ_le (atanPolyLo z * angleUnit)
    have h2 := atanPolyLo_le (z := (z : ℝ)) (by exact_mod_cast hz)
    rw [div_le_iff₀ hA]
    push_cast at h1
    rw [atanPolyLo_cast] at h1
    nlinarith
  · have hz' : (0 : ℝ) ≤ ((-z : ℚ) : ℝ) := by exact_mod_cast (le_of_lt (neg_pos.mpr (lt_of_not_ge hz)))
    have h1 := le_ceilQ (atanPolyHi (-z) * angleUnit)
    have h2 := arctan_le_atanPolyHi hz'
    rw [div_le_iff₀ hA]
    push_cast at h1 h2 hz' ⊢
    rw [atanPolyHi_cast] at h1
    push_cast at h1
    rw [Real.arctan_neg] at h2
    nlinarith

theorem le_seriesHi (z : ℚ) : Real.arctan z ≤ (seriesHi z : ℝ) / angleUnit := by
  have hA := angleUnit_pos
  unfold seriesHi
  split_ifs with hz
  · have h1 := le_ceilQ (atanPolyHi z * angleUnit)
    have h2 := arctan_le_atanPolyHi (z := (z : ℝ)) (by exact_mod_cast hz)
    rw [le_div_iff₀ hA]
    push_cast at h1
    rw [atanPolyHi_cast] at h1
    nlinarith
  · have hz' : (0 : ℝ) ≤ ((-z : ℚ) : ℝ) := by exact_mod_cast (le_of_lt (neg_pos.mpr (lt_of_not_ge hz)))
    have h1 := floorQ_le (atanPolyLo (-z) * angleUnit)
    have h2 := atanPolyLo_le hz'
    rw [le_div_iff₀ hA]
    push_cast at h1 h2 hz' ⊢
    rw [atanPolyLo_cast] at h1
    push_cast at h1
    rw [Real.arctan_neg] at h2
    nlinarith

/-! ### The anchors -/

/-- `arctan (j / 16)` for `j ≤ 16`, rounded down, over `angleUnit`. -/
def anchorLo : List Int :=
  [0, 6241880999595733145, 12435499454676140262, 18534794999569471987, 24497866312686409976,
   30288486837497134474, 35877067027057215554, 41241044159738723967, 46364760900080604768,
   51238946031073763745, 55859931534356236641, 60228734613496411195, 64350110879328431699,
   68231655487474800840, 71882999962162443554, 75315128096219431964, 78539816339744823972]

/-- `arctan (j / 16)` for `j ≤ 16`, rounded up, over `angleUnit`. -/
def anchorHi : List Int :=
  [0, 6241880999596249904, 12435499454677131384, 18534794999570863620, 24497866312688113819,
   30288486837499064224, 35877067027059298026, 41241044159740903614, 46364760900082843060,
   51238946031076035869, 55859931534358527563, 60228734613498712249, 64350110879330738085,
   68231655487477109982, 71882999962164754102, 75315128096221743223, 78539816339747135590]

/-- The `j`-th lower anchor. -/
def anchorL (j : ℕ) : Int := nth 0 anchorLo j

/-- The `j`-th upper anchor. -/
def anchorH (j : ℕ) : Int := nth 0 anchorHi j

/-- `(cⱼ₊₁ - cⱼ) / (1 + cⱼ cⱼ₊₁)` for `cⱼ = j / 16`. -/
def anchorStep (j : ℕ) : ℚ := 16 / (256 + j * (j + 1))

/-- The anchors start at `0`, and the anchor of `j + 1` follows from that of `j` by the addition
formula, with the series bounds at `anchorStep j`. -/
def anchorsCheck : Bool :=
  (anchorL 0 == 0) && (anchorH 0 == 0) &&
    (List.range 16).all fun j =>
      decide (((anchorL (j + 1) : Int) : ℚ) ≤ (anchorL j : ℚ) + atanPolyLo (anchorStep j) *
        angleUnit) &&
      decide (((anchorH j : Int) : ℚ) + atanPolyHi (anchorStep j) * angleUnit ≤
        (anchorH (j + 1) : ℚ))

theorem anchors_check : anchorsCheck = true := by decide +kernel

/-- `arctan x = arctan c + arctan ((x - c) / (1 + x c))` for `x, c ≥ 0`. -/
theorem arctan_eq_add {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    Real.arctan x = Real.arctan c + Real.arctan ((x - c) / (1 + x * c)) := by
  have hd : 0 < 1 + x * c := by positivity
  have hlt : c * ((x - c) / (1 + x * c)) < 1 := by
    rw [mul_div_assoc', div_lt_one hd]
    nlinarith [sq_nonneg c]
  rw [Real.arctan_add hlt]
  congr 1
  have hd2 : 1 - c * ((x - c) / (1 + x * c)) = (1 + c ^ 2) / (1 + x * c) := by
    field_simp
    ring
  have hn : c + (x - c) / (1 + x * c) = x * (1 + c ^ 2) / (1 + x * c) := by
    field_simp
    ring
  rw [hd2, hn]
  field_simp

/-- The anchors bound `arctan (j / 16)` for `j ≤ 16`. -/
theorem anchor_bounds : ∀ j ≤ 16,
    ((anchorL j : Int) : ℝ) / angleUnit ≤ Real.arctan ((j : ℝ) / 16) ∧
      Real.arctan ((j : ℝ) / 16) ≤ ((anchorH j : Int) : ℝ) / angleUnit := by
  have hA := angleUnit_pos
  have hc := anchors_check
  simp only [anchorsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hc
  obtain ⟨⟨h0, h0'⟩, hstep⟩ := hc
  intro j hj
  induction j with
  | zero => simp [h0, h0']
  | succ j ih =>
      obtain ⟨ihl, ihh⟩ := ih (by omega)
      obtain ⟨sl, sh⟩ := hstep j (by omega)
      have sl' : (((anchorL (j + 1) : Int) : ℚ) : ℝ) ≤
          (((anchorL j : Int) : ℚ) + atanPolyLo (anchorStep j) * angleUnit : ℚ) := by
        exact_mod_cast sl
      have sh' : ((((anchorH j : Int) : ℚ) + atanPolyHi (anchorStep j) * angleUnit : ℚ) : ℝ) ≤
          (((anchorH (j + 1) : Int) : ℚ) : ℝ) := by
        exact_mod_cast sh
      push_cast at sl' sh'
      have hz : (0 : ℝ) ≤ (anchorStep j : ℝ) := by
        have : (0 : ℚ) ≤ anchorStep j := by unfold anchorStep; positivity
        exact_mod_cast this
      have hzR : ((anchorStep j : ℚ) : ℝ) = ((j + 1 : ℕ) / 16 - j / 16) / (1 + (j + 1 : ℕ) / 16 *
          (j / 16)) := by
        simp only [anchorStep]
        push_cast
        field_simp
        ring
      have hadd := arctan_eq_add (x := ((j + 1 : ℕ) : ℝ) / 16) (c := (j : ℝ) / 16)
        (by positivity) (by positivity)
      rw [← hzR] at hadd
      have hlo := atanPolyLo_le hz
      have hhi := arctan_le_atanPolyHi hz
      rw [atanPolyLo_cast] at sl'
      rw [atanPolyHi_cast] at sh'
      constructor
      · rw [div_le_iff₀ hA] at ihl ⊢
        rw [hadd]
        nlinarith
      · rw [le_div_iff₀ hA] at ihh ⊢
        rw [hadd]
        nlinarith

/-! ### Bounds at a rational point -/

/-- The anchor nearest to `x`, at most `16`. -/
def anchorIndex (x : ℚ) : ℕ := min 16 (floorQ (16 * x + 1 / 2)).toNat

/-- `(x - c) / (1 + x c)` for the anchor `c` of `x`: the argument of the series after the
addition formula. -/
def anchorArg (x : ℚ) : ℚ := (x - anchorIndex x / 16) / (1 + x * (anchorIndex x / 16))

/-- A lower bound of `arctan x` over `angleUnit`: the lower anchor of `x` plus the lower series
bound at `anchorArg x`, and `-2` for `x < 0`. -/
def atanLo (x : ℚ) : Int :=
  if 0 ≤ x then anchorL (anchorIndex x) + seriesLo (anchorArg x) else -2 * angleUnit

/-- An upper bound of `arctan x` over `angleUnit`: the upper anchor of `x` plus the upper series
bound at `anchorArg x`, and `2` for `x < 0`. -/
def atanHi (x : ℚ) : Int :=
  if 0 ≤ x then anchorH (anchorIndex x) + seriesHi (anchorArg x) else 2 * angleUnit

/-- The addition formula at the anchor of `x`. -/
theorem atan_split {x : ℚ} (hx : 0 ≤ x) :
    Real.arctan x = Real.arctan ((anchorIndex x : ℝ) / 16) + Real.arctan (anchorArg x) := by
  have h := arctan_eq_add (x := (x : ℝ)) (c := (anchorIndex x : ℝ) / 16) (by exact_mod_cast hx)
    (by positivity)
  rw [h]
  congr 2
  simp only [anchorArg]
  push_cast
  ring

/-- `atanLo x` over `angleUnit` is a lower bound of `arctan x`. -/
theorem atanLo_le (x : ℚ) : (atanLo x : ℝ) / angleUnit ≤ Real.arctan x := by
  have hA := angleUnit_pos
  unfold atanLo
  split_ifs with hx
  · have ha := (anchor_bounds (anchorIndex x) (min_le_left _ _)).1
    have hs := seriesLo_le (anchorArg x)
    rw [atan_split hx]
    push_cast
    rw [add_div]
    linarith
  · have h := Real.neg_pi_div_two_lt_arctan x
    have hpi := Real.pi_le_four
    push_cast
    rw [mul_div_assoc, div_self (ne_of_gt hA)]
    linarith

/-- `atanHi x` over `angleUnit` is an upper bound of `arctan x`. -/
theorem le_atanHi (x : ℚ) : Real.arctan x ≤ (atanHi x : ℝ) / angleUnit := by
  have hA := angleUnit_pos
  unfold atanHi
  split_ifs with hx
  · have ha := (anchor_bounds (anchorIndex x) (min_le_left _ _)).2
    have hs := le_seriesHi (anchorArg x)
    rw [atan_split hx]
    push_cast
    rw [add_div]
    linarith
  · have h := Real.arctan_lt_pi_div_two x
    have hpi := Real.pi_le_four
    push_cast
    rw [mul_div_assoc, div_self (ne_of_gt hA)]
    linarith

end SquaresInCircles.Eight.Arithmetic.PairCover
