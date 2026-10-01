import SquaresInCircles.Six.Stress.ExactSupport
import SquaresInCircles.Six.Stress.Reverse

/-!
# Strict support

A square strictly inside the disk, `(|a| + 1/2)² + (|b| + 1/2)² < R²`, has
`x a + y b < σ_R(x, y)` for every nonzero force `(x, y)`. In the vertex case
this is the strict Cauchy–Schwarz inequality; in the cap case it comes from
the supporting line of the disk at `(√(R² - 1/4), 1/2)`, by the slope condition
of the cap.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

lemma dot_lt_radius {v p : Point} {R : ℝ} (hR : 0 ≤ R)
    (hv : v ≠ (0, 0)) (hp : normSq p < R ^ 2) :
    dot v p < R * vectorLength v := by
  have hn := normSq_pos_of_ne hv
  have hcs := cauchy_sq v p
  have hm := mul_lt_mul_of_pos_left hp hn
  have hs : (dot v p) ^ 2 < (R * vectorLength v) ^ 2 := by
    calc
      (dot v p) ^ 2 ≤ normSq v * normSq p := hcs
      _ < normSq v * R ^ 2 := hm
      _ = (R * vectorLength v) ^ 2 := by rw [← vectorLength_sq]; ring
  have hnonneg : 0 ≤ R * vectorLength v := mul_nonneg hR (vectorLength_nonneg v)
  by_contra! h
  have hprod := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ dot v p + R * vectorLength v by linarith)
  nlinarith

private lemma corner_support_strict {A B a b U V q : ℝ}
    (ha : 0 < a) (hB : b ≤ B) (hU : 0 < U)
    (hcircle : a ^ 2 + b ^ 2 = q) (hbox : A ^ 2 + B ^ 2 < q)
    (hslope : a * V ≤ b * U) : A * U + B * V < a * U + b * V := by
  have ht : a * (A - a) + b * (B - b) < 0 := by
    nlinarith [sq_nonneg (A - a), sq_nonneg (B - b)]
  have hct := mul_neg_of_pos_of_neg hU ht
  have hsl := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hB)
  have hp : a * (A * U + B * V - (a * U + b * V)) < 0 := by nlinarith
  by_contra! h
  have hpos := mul_nonneg ha.le (sub_nonneg.mpr h)
  linarith

private lemma strict_cap_slope {R U V : ℝ}
    (hR : 1 / 2 < R) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (h : 2 * R * V ≤ Real.sqrt (U ^ 2 + V ^ 2)) :
    Real.sqrt (R ^ 2 - 1 / 4) * V ≤ U / 2 := by
  have hR0 : 0 ≤ R := by linarith
  have hrad : 0 ≤ R ^ 2 - 1 / 4 := by nlinarith [sq_nonneg (R - 1 / 2)]
  have hs := Real.sq_sqrt hrad
  have hn := Real.sq_sqrt (show 0 ≤ U ^ 2 + V ^ 2 by positivity)
  have hp := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ Real.sqrt (U ^ 2 + V ^ 2) + 2 * R * V by positivity)
  have hmul := congrArg (fun z : ℝ => z * V ^ 2) hs
  have hsquare : (2 * Real.sqrt (R ^ 2 - 1 / 4) * V) ^ 2 ≤ U ^ 2 := by nlinarith
  have hnn : 0 ≤ 2 * Real.sqrt (R ^ 2 - 1 / 4) * V := by positivity
  by_contra! hbad
  have hprod := mul_pos
    (show 0 < 2 * Real.sqrt (R ^ 2 - 1 / 4) * V - U by linarith)
    (show 0 < 2 * Real.sqrt (R ^ 2 - 1 / 4) * V + U by linarith)
  nlinarith

lemma ordered_center_support_strict {R a b U V : ℝ}
    (hR : 1 / 2 < R) (hU : 0 < U) (hV : 0 ≤ V)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 < R ^ 2) :
    |a| * U + |b| * V < orderedSupport R U V := by
  unfold orderedSupport
  split_ifs with hswitch
  · have hrad : 0 < R ^ 2 - 1 / 4 := by nlinarith [sq_nonneg (R - 1 / 2)]
    have ha0 := Real.sqrt_pos.mpr hrad
    have hid := Real.sq_sqrt hrad.le
    have hslope := strict_cap_slope hR hU.le hV hswitch
    have hc := corner_support_strict
      (A := |a| + 1 / 2) (B := |b| + 1 / 2)
      (a := Real.sqrt (R ^ 2 - 1 / 4)) (b := (1 : ℝ) / 2) (U := U) (V := V)
      ha0 (by linarith [abs_nonneg b]) hU (by nlinarith) hbox (by linarith)
    dsimp [rhoAt]
    nlinarith
  · have hv : (U, V) ≠ (0, 0) := by
      intro he
      have heU := congrArg Prod.fst he
      dsimp only at heU
      linarith
    have hr := dot_lt_radius (v := (U, V)) (p := (|a| + 1 / 2, |b| + 1 / 2))
      (by linarith : 0 ≤ R) hv hbox
    dsimp [dot, vectorLength, normSq] at hr
    nlinarith

lemma scalar_center_support_strict {R a b x y : ℝ}
    (hR : 1 / 2 < R) (hv : x ≠ 0 ∨ y ≠ 0)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 < R ^ 2) :
    x * a + y * b < scalarSupport R x y := by
  have hx : x * a ≤ |a| * |x| := by
    simpa only [abs_mul, mul_comm] using le_abs_self (x * a)
  have hy : y * b ≤ |b| * |y| := by
    simpa only [abs_mul, mul_comm] using le_abs_self (y * b)
  unfold scalarSupport
  split_ifs with horder
  · have hU : 0 < |x| := by
      rcases hv with hx0 | hy0
      · exact abs_pos.mpr hx0
      · exact (abs_pos.mpr hy0).trans_le horder
    have h := ordered_center_support_strict hR hU (abs_nonneg y) hbox
    linarith
  · have hU : 0 < |y| := (abs_nonneg x).trans_lt (lt_of_not_ge horder)
    have hbox' : (|b| + 1 / 2) ^ 2 + (|a| + 1 / 2) ^ 2 < R ^ 2 := by linarith
    have h := ordered_center_support_strict hR hU (abs_nonneg x) hbox'
    linarith

end SquaresInCircles.Six.Stress
