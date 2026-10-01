import SquaresInCircles.Common.ExteriorArcs
import SquaresInCircles.Common.Trigonometry
import SquaresInCircles.Six.Constants

/-!
# Six squares: the exterior squares

On the circle of radius `9/10` about the disk centre, a square that avoids the
disk centre, in a disk of squared radius at most `Q0`, holds an open arc of
half-width more than `14/25 > π/6`: the circle crosses its near edge at the
chart angles `± A` and its lower and upper edges at `-V` and `U`, and each of
`2A`, `A + U`, `A + V` and `U + V` exceeds `28/25`, by arcsine bounds on the
region `(a + 1/2)² + (b + 1/2)² ≤ Q0`.
-/
noncomputable section
open Set
namespace SquaresInCircles.Six

/-- Two crossings above the centre line: with `x = (a - 1/2)/(9/10)` and
`y = (b - 1/2)/(9/10)`, the cubic bound on the arcsine gives
`arcsin x + arcsin y ≤ 9/20` on the disk. -/
private lemma arcsin_pair_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 3 / 5)
    (hy1 : y ≤ 3 / 5) (hQ : (9 / 10 * x + 1) ^ 2 + (9 / 10 * y + 1) ^ 2 ≤ Q0) :
    Real.arcsin x + Real.arcsin y ≤ 9 / 20 := by
  have hX := arcsin_le_cubic hx hx1
  have hY := arcsin_le_cubic hy hy1
  have hxy := mul_nonneg hx hy
  norm_num [Q0] at hQ
  nlinarith [mul_nonneg hxy (add_nonneg hx hy), sq_nonneg (x - y)]

/-- The circle of radius `9/10` crosses the near edge of a square with
`a ≤ 119/100` at chart angles beyond `± 3/5`. -/
private lemma capA_gt {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 119 / 100) :
    3 / 5 < capA (9 / 10) a := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := 3 / 5)
  calc (3 : ℝ) / 5 = Real.arccos (Real.cos (3 / 5)) :=
        (Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])).symm
    _ < capA (9 / 10) a := Real.arccos_lt_arccos
        (by rw [le_div_iff₀ (by norm_num)]; linarith)
        (by rw [div_lt_iff₀ (by norm_num)]; nlinarith) (Real.cos_le_one _)

/-- The circle of radius `9/10` crosses the upper edge beyond the chart angle
`5/9`. -/
private lemma capU_ge {b : ℝ} (hb : 0 ≤ b) : 5 / 9 ≤ capU (9 / 10) b := by
  rcases le_total 1 ((b + 1 / 2) / (9 / 10)) with h | h
  · rw [capU, Real.arcsin_of_one_le h]
    linarith [Real.pi_gt_three]
  · calc (5 : ℝ) / 9 ≤ (b + 1 / 2) / (9 / 10) := by
          rw [le_div_iff₀ (by norm_num)]; linarith
      _ ≤ capU (9 / 10) b := arcsin_ge_self (by positivity) h

/-- The lower and upper edges: `U + V > 28/25` for `0 ≤ b ≤ 7/10`. -/
private lemma capUV_gt {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 7 / 10) :
    28 / 25 < capU (9 / 10) b + capV (9 / 10) b := by
  rcases le_total (9 / 10) (b + 1 / 2) with h | h
  · have hU1 : capU (9 / 10) b = Real.pi / 2 :=
      Real.arcsin_of_one_le ((le_div_iff₀ (by norm_num)).mpr (by linarith))
    have hm := arcsin_le_cubic (x := 1 / 4) (by norm_num) (by norm_num)
    have hmono := Real.arcsin_le_arcsin (show -(1 / 4 : ℝ) ≤ (1 / 2 - b) / (9 / 10) by
      rw [le_div_iff₀ (by norm_num)]; linarith)
    rw [Real.arcsin_neg] at hmono
    rw [hU1]
    unfold capV
    linarith [Real.pi_gt_d2]
  · have hs := sin_upper_five (x := 14 / 25) (by norm_num)
    have hh := arcsin_sum_gt_of_sin_lt (u := (b + 1 / 2) / (9 / 10))
      (v := (1 / 2 - b) / (9 / 10)) (θ := 14 / 25)
      ⟨by positivity, (div_le_one (by norm_num)).mpr h⟩
      ⟨by rw [le_div_iff₀ (by norm_num)]; linarith,
        (div_le_one (by norm_num)).mpr (by linarith)⟩
      ⟨by norm_num, by linarith [Real.pi_gt_three]⟩ (by
        rw [show ((b + 1 / 2) / (9 / 10) + (1 / 2 - b) / (9 / 10)) / 2 = 5 / 9 by ring]
        norm_num at hs ⊢
        linarith)
    unfold capU capV
    linarith

/-- The near and lower edges of a square above the centre line, `b ≥ 1/2`. -/
private lemma capAV_high {a b : ℝ} (hb2 : 1 / 2 ≤ b) (hsort : b ≤ a)
    (hQ : (a + 1 / 2) ^ 2 + (b + 1 / 2) ^ 2 ≤ Q0) :
    Real.arcsin ((a - 1 / 2) / (9 / 10)) - capV (9 / 10) b ≤ 9 / 20 := by
  have hV : capV (9 / 10) b = -Real.arcsin ((b - 1 / 2) / (9 / 10)) := by
    rw [capV, ← Real.arcsin_neg]
    congr 1
    ring
  rw [hV, sub_neg_eq_add]
  norm_num [Q0] at hQ
  apply arcsin_pair_le (by apply div_nonneg <;> linarith) (by apply div_nonneg <;> linarith)
  · rw [div_le_iff₀ (by norm_num)]; nlinarith
  · rw [div_le_iff₀ (by norm_num)]; nlinarith
  · norm_num [Q0]; linarith

/-- The near and lower edges of a square below the centre line, `b ≤ 1/2`. -/
private lemma capAV_low {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : 0 ≤ b) (hb2 : b ≤ 1 / 2)
    (ha1 : a ≤ 1.113) (hQ : (a + 1 / 2) ^ 2 + (b + 1 / 2) ^ 2 ≤ Q0) :
    Real.arcsin ((a - 1 / 2) / (9 / 10)) - capV (9 / 10) b ≤ 9 / 20 := by
  norm_num [Q0] at hQ
  have hV : (1 / 2 - b) / (9 / 10) ≤ capV (9 / 10) b :=
    arcsin_ge_self (by apply div_nonneg <;> linarith)
      (by rw [div_le_one (by norm_num)]; linarith)
  rcases le_total a (1 / 2 + 27 / 50) with ha2 | ha2
  · have hX := arcsin_le_cubic (x := (a - 1 / 2) / (9 / 10)) (by apply div_nonneg <;> linarith)
      (by rw [div_le_iff₀ (by norm_num)]; linarith)
    have hx0 : 0 ≤ a - 1 / 2 := by linarith
    have hx2 : (a - 1 / 2) ^ 2 ≤ (27 / 50) ^ 2 := by nlinarith
    have hx3 : (a - 1 / 2) ^ 3 ≤ (27 / 50) ^ 2 * (a - 1 / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hx2 hx0]
    -- `1.09 (a + 1/2) + (b + 1/2) ≤ 2.495` on the disk below `b = 1/2`
    have hlin : 109 / 100 * (a + 1 / 2) + (b + 1 / 2) ≤ 2.495 := by
      nlinarith [sq_nonneg (109 / 100 * (a + 1 / 2) - 2.495 + (b + 1 / 2))]
    have hX' : Real.arcsin ((a - 1 / 2) / (9 / 10)) ≤
        (a - 1 / 2) / (9 / 10) + (27 / 50) ^ 2 * (a - 1 / 2) / (4 * (9 / 10) ^ 3) := by
      have he : ((a - 1 / 2) / (9 / 10)) ^ 3 / 4 = (a - 1 / 2) ^ 3 / (4 * (9 / 10) ^ 3) := by
        ring
      rw [he] at hX
      have hd : (a - 1 / 2) ^ 3 / (4 * (9 / 10) ^ 3) ≤
          (27 / 50) ^ 2 * (a - 1 / 2) / (4 * (9 / 10) ^ 3) :=
        div_le_div_of_nonneg_right hx3 (by norm_num)
      linarith
    have hval : (a - 1 / 2) / (9 / 10) + (27 / 50) ^ 2 * (a - 1 / 2) / (4 * (9 / 10) ^ 3) -
        (1 / 2 - b) / (9 / 10) ≤ 9 / 20 := by
      rw [show (a - 1 / 2) / (9 / 10) + (27 / 50) ^ 2 * (a - 1 / 2) / (4 * (9 / 10) ^ 3) -
          (1 / 2 - b) / (9 / 10) = (1090 * (a - 1 / 2) - 1000 * (1 / 2 - b)) / 900 by ring]
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith
  · -- a far square sits low: `b + 1/2 ≤ 7/10`
    have hlow : b + 1 / 2 ≤ 7 / 10 := by nlinarith
    have hvlow : 1 / 3 ≤ (1 / 2 - b) / (9 / 10) := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    have hasin : Real.arcsin ((a - 1 / 2) / (9 / 10)) ≤ 77 / 100 := by
      have hs := Real.sin_ge_sub_cube (x := 77 / 100) (by norm_num)
      rw [Real.arcsin_le_iff_le_sin
        ⟨by rw [le_div_iff₀ (by norm_num)]; linarith, by rw [div_le_iff₀ (by norm_num)]; linarith⟩
        ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩]
      norm_num at hs
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith

/-- On the circle of radius `9/10`, an exterior square with
`(a + 1/2)² + (b + 1/2)² ≤ Q0` has each of `2A`, `A + U`, `A + V` and `U + V`
above `28/25`. -/
lemma arc_length {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : 0 ≤ b) (hsort : b ≤ a)
    (hQ : (a + 1 / 2) ^ 2 + (b + 1 / 2) ^ 2 ≤ Q0) :
    14 / 25 < capA (9 / 10) a ∧ 2 * (14 / 25) < capA (9 / 10) a + capU (9 / 10) b ∧
      2 * (14 / 25) < capA (9 / 10) a + capV (9 / 10) b ∧
      2 * (14 / 25) < capU (9 / 10) b + capV (9 / 10) b := by
  have hrho := rho0_bounds
  have harho : a ≤ rho0 := by
    have hs : (a + 1 / 2) ^ 2 ≤ Q0 - 1 / 4 := by nlinarith
    have hr := Real.le_sqrt_of_sq_le hs
    dsimp [rho0]
    linarith
  have hA35 := capA_gt ha (by linarith)
  have hU := capU_ge hb
  have hUV := capUV_gt hb (by norm_num [Q0] at hQ; nlinarith)
  have hAV : 28 / 25 < capA (9 / 10) a + capV (9 / 10) b := by
    rw [capA, Real.arccos_eq_pi_div_two_sub_arcsin]
    have h : Real.arcsin ((a - 1 / 2) / (9 / 10)) - capV (9 / 10) b ≤ 9 / 20 := by
      rcases le_total (1 / 2) b with hb2 | hb2
      · exact capAV_high hb2 hsort hQ
      · exact capAV_low ha hb hb2 (by linarith) hQ
    linarith [Real.pi_gt_d4]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- An exterior square in the disk of squared radius `Q0` holds an arc of the
circle of radius `9/10` of half-width more than `14/25`. -/
theorem exterior_arc (S : UnitSquare) (o : Point) (hQ : phi (alpha S o) (beta S o) ≤ Q0)
    (hout : ¬ openSquare S o) :
    ∃ A : OpenArc o (9 / 10) {p | openSquare S p}, 14 / 25 < A.halfWidth := by
  obtain ⟨C, hsort⟩ := sorted_square_chart S o
  have ha := C.exterior hsort hout
  have hC : (C.a + 1 / 2) ^ 2 + (C.b + 1 / 2) ^ 2 ≤ Q0 := chart_phi C hQ
  have ha1 : C.a ≤ 7 / 5 := by norm_num [Q0] at hC; nlinarith [C.nonneg.2]
  obtain ⟨h₁, h₂, h₃, h₄⟩ := arc_length ha C.nonneg.2 hsort hC
  exact C.edge_arc_gt (by norm_num) ha (by linarith) (by linarith) (by norm_num) h₁ h₂ h₃ h₄

end SquaresInCircles.Six
