import SquaresInCircles.Six.Normalization.ChartBounds

/-!
# Lemma B6: exclude both secondary central separators

The strong central box and B3's transverse bound suffice. The proof uses the
coarser `U0 + 2*c0 < 1`, avoiding an additional square-root scalar leaf.
These are the genuine signed secondary margins from T2. The strong box is
an explicit hypothesis, not an assumption that Proposition A is complete.
Compiler validation remains pending.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

lemma one_le_abs_cos_add_abs_sin (t : ℝ) :
    1 ≤ |Real.cos t| + |Real.sin t| := by
  have hc := abs_nonneg (Real.cos t)
  have hs := abs_nonneg (Real.sin t)
  have hu := Real.sin_sq_add_cos_sq t
  have hp := mul_nonneg hc hs
  by_contra! h
  have hprod := mul_pos (sub_pos.mpr h)
    (show 0 < 1 + (|Real.cos t| + |Real.sin t|) by linarith)
  nlinarith [sq_abs (Real.cos t), sq_abs (Real.sin t)]

lemma transverse_distance_lt_one {b cx cy t : ℝ}
    (hb : |b| ≤ U0) (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy)
    (hx : cx ≤ c0) (hy : cy ≤ c0) :
    |b - (-cx * Real.sin t + cy * Real.cos t)| < 1 := by
  have hb' := abs_le.mp hb
  have hslo := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin t) hx0
  have hshi := mul_le_mul_of_nonneg_left (Real.sin_le_one t) hx0
  have hclo := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos t) hy0
  have hchi := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hy0
  apply abs_lt.mpr
  constructor <;> nlinarith [U0_lt_117_250, c0_lt_23_200]

/-- Both secondary SAT margins are strictly negative, including signed `b`.
There is no preferred-cardinal or pin hypothesis in this lemma. -/
theorem secondary_separators_fail {b cx cy t : ℝ}
    (hb : |b| ≤ U0) (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy)
    (hx : cx ≤ c0) (hy : cy ≤ c0) :
    b - 1 / 2 - (-cx * Real.sin t + cy * Real.cos t) -
        (|Real.cos t| + |Real.sin t|) / 2 < 0 ∧
      (-cx * Real.sin t + cy * Real.cos t) - 1 / 2 - b -
        (|Real.cos t| + |Real.sin t|) / 2 < 0 := by
  have hd := abs_lt.mp (transverse_distance_lt_one (t := t) hb hx0 hy0 hx hy)
  have hw := one_le_abs_cos_add_abs_sin t
  constructor <;> linarith

/-- B6 after the same explicit geometric core premise as B1--B5. -/
theorem ContainedChart.secondary_separators_fail {a b cx cy t : ℝ}
    (hc : ContainedChart a |b|) (hcore : AvoidsCore a |b|)
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx : cx ≤ c0) (hy : cy ≤ c0) :
    b - 1 / 2 - (-cx * Real.sin t + cy * Real.cos t) -
        (|Real.cos t| + |Real.sin t|) / 2 < 0 ∧
      (-cx * Real.sin t + cy * Real.cos t) - 1 / 2 - b -
        (|Real.cos t| + |Real.sin t|) / 2 < 0 :=
  Normalization.secondary_separators_fail (hc.u_le_U0 hcore) hx0 hy0 hx hy

end SquaresInCircles.Six.Normalization
