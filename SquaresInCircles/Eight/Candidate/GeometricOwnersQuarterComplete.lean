module

public import SquaresInCircles.Eight.Candidate.GeometricOwnersForbiddenB

/-!
# Eight squares: a forbidden `B` direction is impossible

Suppose that a forbidden axis separates `B → T` at mismatch `S ≤ 3/200`. The `G` axis is then
`0` or `1` (`G_axis_two_forbidden_quarter_excluded`, `G_axis_three_forbidden_B_excluded`),
`b_A ≥ 29/50`, `a_A ≤ 29/25` and `a_H ≤ 29/25` (`forbidden_B_A_coordinates`,
`H_primary_twenty_nine`), and the tilt satisfies `sin t > -3/8` (`global_negative_tilt_bound`).
For a nonnegative tilt the chain `H → G` gives `sin t ≤ 1/10` (`forbidden_B_positive_tilt`).

A three-edge chain through `H`, `G` and `E`, weighted for each pair of axes, excludes the `E` axes
`2` and `3`: demand minus force is at least `13/100`, the error at most `7S/2`
(`forbidden_B_E_axis_two_three`). The `E` axes `0` and `1` are excluded by one seven-edge stress,
with weights `(h, 1, 7/10, 7/10, 1/4, 3/10, 11/10)` on `H, G, A, B, T, D, E` and `h = 1` or
`cos t`, and the corner disks of `A`, `T`, `D`, `H` completed with weights `3/10, 3/16, 1/10, 3/8`:
demand minus force is at least `467/4800 - 31/1000`, the error at most `37S/10`
(`forbidden_B_stress`). So no forbidden axis separates `B → T` (`forbidden_B_excluded`), and with
`D_quarter_owners` every axis that separates `B → T` or `D → E` at mismatch at most `3/200` is a
quarter owner (`quarter_owners`). Each separating axis is treated on its own, so ties between axes
are included.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate
open _root_.SquaresInCircles.Eight.Candidate.Dual

/-- Completing the square in a corner disk, for the force `(x, y)` and the weight `μ = 1/(4k)`. -/
theorem circle_support {a b x y q μ k : ℝ} (hμ : 0 < μ) (hk : 4*μ*k = 1)
    (hcircle : (a+1/2)^2+(b+1/2)^2 ≤ q) :
    x*a+y*b ≤ μ*q+k*(x^2+y^2)-(x+y)/2 := by
  have h := circle_linear_upper (C := x) (D := y) hμ hcircle
  have hk' : (x^2+y^2)/(4*μ) = k*(x^2+y^2) := by
    rw [div_eq_iff (by positivity)]
    linear_combination (-(x^2+y^2))*hk
  linarith

theorem fin_four_lt_two {g : Fin 4} (hg : g < 2) : g = 0 ∨ g = 1 := by
  revert g; decide

theorem fin_four_two_le {e : Fin 4} (he : 2 ≤ e) : e = 2 ∨ e = 3 := by
  revert e; decide

theorem nominal_G_projection_formula {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) (j : Fin 4) :
    actualProjection C G j (nominalPhase t G) =
      ![C.a A*Real.cos t-C.b A*Real.sin t-C.b G, C.a A-C.a G*Real.sin t-C.b G*Real.cos t,
        C.a G*Real.cos t-C.b G*Real.sin t-C.b A, C.a G-C.a A*Real.sin t-C.b A*Real.cos t] j := by
  have hs := hc.signed_coordinates
  fin_cases j <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalPhase, zeroEdges, otherQuarterEdges, next, G, A, hs, Dual.signs,
      Real.sin_sub, Real.cos_sub] <;> ring

theorem nominal_E_projection_formula {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) (j : Fin 4) :
    actualProjection C E j (nominalPhase t E) =
      ![C.a H*Real.cos t+C.b H*Real.sin t-C.b E, C.a H+C.a E*Real.sin t-C.b E*Real.cos t,
        C.a E*Real.cos t+C.b E*Real.sin t-C.b H, C.a E+C.a H*Real.sin t-C.b H*Real.cos t] j := by
  rw [nominal_E_negative_projection_formula hc]
  fin_cases j <;> simp

theorem nominal_G_width {t : ℝ} (hc : 0 ≤ Real.cos t) :
    pairWidth (nominalPhase t G) = (1+Real.cos t+|Real.sin t|)/2 := by
  simp [pairWidth, nominalPhase, G, zeroEdges, otherQuarterEdges, Real.sin_sub, Real.cos_sub,
    abs_of_nonneg hc]

theorem nominal_E_width {t : ℝ} (hc : 0 ≤ Real.cos t) :
    pairWidth (nominalPhase t E) = (1+Real.cos t+|Real.sin t|)/2 := by
  rw [GeometricOwners.nominal_E, pairWidth_half_pi_add]
  simp [pairWidth, abs_of_nonneg hc]
  ring

/-- For a direction `(c, s)` of the unit circle with `3/4 ≤ c ≤ 1` and `-3/8 ≤ s ≤ 0`: `c ≥ 9/10`,
`1 - c ≤ (4/7) s²` and `s² ≤ (3/8)(-s)`. -/
theorem negative_arc_geometry {c s : ℝ} (hc : 3/4 ≤ c) (hc1 : c ≤ 1) (hs : s ≤ 0)
    (hsL : -(3/8) ≤ s) (hunit : c^2+s^2=1) :
    9/10 ≤ c ∧ 1-c ≤ (4/7)*s^2 ∧ s^2 ≤ (3/8)*(-s) := by
  have hr2 : s^2 ≤ (3/8)*(-s) := by
    nlinarith only [mul_nonneg (neg_nonneg.2 hs) (by linarith : (0:ℝ) ≤ s+3/8)]
  refine ⟨by nlinarith only [hunit, hr2, hsL, hc], ?_, hr2⟩
  nlinarith only [hunit, mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hc)]

/-- The chain `H → G` on the `G` axis `0` or `1` confines a nonnegative tilt to `sin t ≤ 1/10`,
and then `cos t ≥ 99/100`. -/
theorem forbidden_B_positive_tilt {aA bA aG bG bH c s eH : ℝ} {g : Fin 4} (hg : g < 2)
    (hAa : aA ≤ 29/25) (hAb : 29/50 ≤ bA) (hGa : 7/12 ≤ aG) (hHb : bH ≤ 9/10)
    (hc : 3/4 ≤ c) (hc1 : c ≤ 1) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (heH : 0 ≤ eH)
    (heHU : eH ≤ 3/200) (hH : 1-(3/2)*eH ≤ bH+bG)
    (hG : (1+c+s)/2 ≤ ![aA*c-bA*s-bG, aA-aG*s-bG*c, aG*c-bG*s-bA, aG-aA*s-bA*c] g) :
    s ≤ 1/10 ∧ 99/100 ≤ c := by
  have hc0 : 0 ≤ c := by linarith
  have hs10 : s ≤ 1/10 := by
    by_contra! hn
    rcases fin_four_lt_two hg with rfl | rfl <;> norm_num at hG
    · linarith only [hc1, heHU, hHb, hH, hG, hn, mul_le_mul_of_nonneg_right hAa hc0,
        mul_le_mul_of_nonneg_right hAb hs]
    · have hs7 : s ≤ 7/10 := by nlinarith only [hunit, hc, hs]
      linarith only [heHU, hAa, hG, hn, hunit, mul_le_mul_of_nonneg_left hH hc0,
        mul_le_mul_of_nonneg_right hGa hs, mul_le_mul_of_nonneg_left hHb hc0,
        mul_le_mul_of_nonneg_right hc1 heH, mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hc),
        mul_le_mul_of_nonneg_left hs7 hs]
  have hc99 : 99/100 ≤ c := by
    linarith only [hunit, hs10, mul_nonneg hc0 (sub_nonneg.2 hc1),
      mul_nonneg hs (sub_nonneg.2 hs10)]
  exact ⟨hs10, hc99⟩

/-- For the `G` axes `0` and `1`, a three-edge chain through `H`, `G` and `E` excludes the `E` axes
`2` and `3`, with the weights `(1, 1, 1)`, `(c, c, 1)`, `(c, 1, c)` and `(c, 1, 1)` on `H`, `G`,
`E` for the pairs `(0, 2)`, `(0, 3)`, `(1, 2)`, `(1, 3)` of the axes of `G` and `E`. The
transverse coordinates of `G` and `H` cancel, demand minus force is at least `13/100`, and the
error is at most `7S/2`. -/
theorem forbidden_B_E_axis_two_three {aA bA aG bG aH bH aE bE c s eH S : ℝ} {g e : Fin 4}
    (hg : g < 2) (he : 2 ≤ e)
    (hAa : aA ≤ 29/25) (hAb : 29/50 ≤ bA) (hAb' : bA ≤ 9/10)
    (hGa : 7/12 ≤ aG) (hGu : aG ≤ 349/250) (hHa : 447/800 ≤ aH) (hHu : aH ≤ 29/25)
    (hEu : aE ≤ 283/200) (hEb : 0 ≤ bE) (hEb' : bE ≤ 9/10)
    (hc : 3/4 ≤ c) (hc1 : c ≤ 1) (hunit : c^2+s^2=1) (hsL : -(3/8) < s)
    (hpos : 0 ≤ s → s ≤ 1/10 ∧ 99/100 ≤ c)
    (heH : 0 ≤ eH) (heHS : eH ≤ S) (hS : S ≤ 3/200)
    (hH : 1-(3/2)*eH ≤ bH+bG)
    (hG : (1+c+|s|)/2 ≤ ![aA*c-bA*s-bG, aA-aG*s-bG*c, aG*c-bG*s-bA, aG-aA*s-bA*c] g)
    (hE : (1+c+|s|)/2-2*S ≤ ![aH*c+bH*s-bE, aH+aE*s-bE*c, aE*c+bE*s-bH, aE+aH*s-bH*c] e) :
    False := by
  have hc0 : 0 ≤ c := by linarith
  have hbA : 0 ≤ bA := by linarith
  have hceH := mul_le_mul_of_nonneg_right hc1 heH
  have hcS := mul_le_mul_of_nonneg_right hc1 (heH.trans heHS)
  have hHc := mul_le_mul_of_nonneg_left hH hc0
  have hA2 := mul_le_mul_of_nonneg_right hAa (sq_nonneg c)
  have hE2 := mul_le_mul_of_nonneg_right hEu (sq_nonneg c)
  rcases le_total 0 s with hs | hs
  · obtain ⟨hs10, hc99⟩ := hpos hs
    rw [abs_of_nonneg hs] at hG hE
    have hss := mul_le_mul_of_nonneg_left hs10 hs
    rcases fin_four_lt_two hg with rfl | rfl <;> rcases fin_four_two_le he with rfl | rfl <;>
      norm_num at hG hE
    · linarith only [hc1, heHS, hS, hs, hH, hG, hE, mul_le_mul_of_nonneg_right hAa hc0,
        mul_le_mul_of_nonneg_right hEu hc0, mul_le_mul_of_nonneg_right hEb' hs, mul_nonneg hbA hs]
    · linarith only [heHS, hS, hEu, hs10, hc99, hunit, hHc, mul_le_mul_of_nonneg_left hG hc0, hE,
        hceH, hA2, sq_nonneg s, mul_nonneg (mul_nonneg hc0 hbA) hs,
        mul_le_mul_of_nonneg_right hHu hs, hss, mul_nonneg hc0 hs]
    · linarith only [heHS, hS, hAa, hs, hc99, hunit, hHc, hG, mul_le_mul_of_nonneg_left hE hc0,
        hceH, hcS, hE2, sq_nonneg s, mul_nonneg (by linarith : 0 ≤ aG) hs,
        mul_le_mul_of_nonneg_right hEb' (mul_nonneg hc0 hs), mul_le_mul_of_nonneg_right hc1 hs,
        hss]
    · linarith only [heHS, hS, hAa, hEu, hs, hc99, hHc, hG, hE, hceH,
        mul_le_mul_of_nonneg_right hHu hs, mul_le_mul_of_nonneg_right hGa hs]
  · obtain ⟨hc9, -, -⟩ := negative_arc_geometry hc hc1 hs hsL.le hunit
    rw [abs_of_nonpos hs] at hG hE
    have hr : 0 ≤ -s := neg_nonneg.2 hs
    rcases fin_four_lt_two hg with rfl | rfl <;> rcases fin_four_two_le he with rfl | rfl <;>
      norm_num at hG hE
    · linarith only [hc1, heHS, hS, hr, hH, hG, hE, mul_le_mul_of_nonneg_right hAa hc0,
        mul_le_mul_of_nonneg_right hEu hc0, mul_nonneg hEb hr, mul_le_mul_of_nonneg_right hAb' hr]
    · have hcb : c*bA ≤ 9/10 := by linarith only [hAb', mul_le_mul_of_nonneg_right hc1 hbA]
      linarith only [heHS, hS, hEu, hr, hc9, hunit, hHc, mul_le_mul_of_nonneg_left hG hc0, hE,
        hceH, hA2, sq_nonneg s, mul_le_mul_of_nonneg_right hcb hr,
        mul_le_mul_of_nonneg_right hHa hr, mul_le_mul_of_nonneg_right hc9 hc0,
        mul_le_mul_of_nonneg_right hc9 hr]
    · linarith only [heHS, hS, hAa, hsL, hc9, hHc, hG, mul_le_mul_of_nonneg_left hE hc0, hceH,
        hcS, hE2, mul_le_mul_of_nonneg_right hGu hr, mul_nonneg (mul_nonneg hc0 hr) hEb,
        mul_nonneg (sub_nonneg.2 hc9) (sub_nonneg.2 hc1), mul_le_mul_of_nonneg_right hc9 hr]
    · linarith only [heHS, hS, hAa, hEu, hr, hc9, hHc, hG, hE, hceH,
        mul_le_mul_of_nonneg_right hHa hr, mul_le_mul_of_nonneg_right hGu hr]

/-- One seven-edge stress excludes the `E` axes `0` and `1`. The edges `H, G, A, B, T, D, E` carry
the weights `(h, 1, 7/10, 7/10, 1/4, 3/10, 11/10)`, with `h = 1` for the `G` axis `0` and `h = c`
for the `G` axis `1`, so that the transverse coordinates of `G` and `B` cancel. The corner disks
of `A`, `T`, `D` and `H` are completed with the weights `3/10, 3/16, 1/10, 3/8`, for the forces
`(c, 7/10 - s)` or `(1, 7/10)` at `A`, `(7/10, 1/4)` at `T`, `(3/10, 1/4)` at `D`, and
`(11c/10, h + 11s/10)` or `(11/10, h)` at `H`. Demand minus force is then at least
`9281/2400 - 77q/80 - 31/1000 ≥ 467/4800 - 31/1000`, while the shared error is at most
`37S/10 ≤ 111/2000`. -/
theorem forbidden_B_stress {aH bH aG bG aA bA bB aT bT aD bD aE bE c s q eH eA eB eT eD S : ℝ}
    {g e : Fin 4} (hg : g < 2) (he : e < 2) (hq : q ≤ Q0)
    (hcA : (aA+1/2)^2+(bA+1/2)^2 ≤ q) (hcT : (aT+1/2)^2+(bT+1/2)^2 ≤ q)
    (hcD : (aD+1/2)^2+(bD+1/2)^2 ≤ q) (hcH : (aH+1/2)^2+(bH+1/2)^2 ≤ q)
    (hGa : 7/12 ≤ aG) (hGu : aG ≤ 349/250)
    (hEa : 447/800 ≤ aE) (hEu : aE ≤ 283/200) (hEb : 0 ≤ bE)
    (hc : 3/4 ≤ c) (hc1 : c ≤ 1) (hunit : c^2+s^2=1) (hsL : -(3/8) < s)
    (hpos : 0 ≤ s → s ≤ 1/10 ∧ 99/100 ≤ c)
    (heH : 0 ≤ eH) (heA : 0 ≤ eA) (heB : 0 ≤ eB) (heT : 0 ≤ eT) (heD : 0 ≤ eD)
    (hsum : eH+eA+eB+eT+eD ≤ S) (hS : S ≤ 3/200)
    (hH : 1-(3/2)*eH ≤ bH+bG) (hA : 1-(3/2)*eA ≤ bA+bB) (hB : 1-(3/2)*eB ≤ aT-bB)
    (hT : 1-(3/2)*eT ≤ bT+bD) (hD : 1-(3/2)*eD ≤ aD+bE)
    (hG : (1+c+|s|)/2 ≤ ![aA*c-bA*s-bG, aA-aG*s-bG*c, aG*c-bG*s-bA, aG-aA*s-bA*c] g)
    (hE : (1+c+|s|)/2-2*S ≤ ![aH*c+bH*s-bE, aH+aE*s-bE*c, aE*c+bE*s-bH, aE+aH*s-bH*c] e) :
    False := by
  have hc0 : 0 ≤ c := by linarith
  have hT' := circle_support (x := 7/10) (y := 1/4) (μ := 3/16) (k := 4/3)
    (by norm_num) (by norm_num) hcT
  have hD' := circle_support (x := 3/10) (y := 1/4) (μ := 1/10) (k := 5/2)
    (by norm_num) (by norm_num) hcD
  have hA0 := circle_support (x := c) (y := 7/10-s) (μ := 3/10) (k := 5/6)
    (by norm_num) (by norm_num) hcA
  have hA1 := circle_support (x := 1) (y := 7/10) (μ := 3/10) (k := 5/6)
    (by norm_num) (by norm_num) hcA
  have hH00 := circle_support (x := 11/10*c) (y := 1+11/10*s) (μ := 3/8) (k := 2/3)
    (by norm_num) (by norm_num) hcH
  have hH01 := circle_support (x := 11/10) (y := 1) (μ := 3/8) (k := 2/3)
    (by norm_num) (by norm_num) hcH
  have hH10 := circle_support (x := 11/10*c) (y := c+11/10*s) (μ := 3/8) (k := 2/3)
    (by norm_num) (by norm_num) hcH
  have hH11 := circle_support (x := 11/10) (y := c) (μ := 3/8) (k := 2/3)
    (by norm_num) (by norm_num) hcH
  have hceH := mul_le_mul_of_nonneg_right hc1 heH
  have hHc := mul_le_mul_of_nonneg_left hH hc0
  have hEl := mul_nonneg (by linarith : (0:ℝ) ≤ 11/10*c-3/10) hEb
  dsimp [Q0] at hq
  rcases le_total 0 s with hs | hs
  · obtain ⟨hs10, hc99⟩ := hpos hs
    rw [abs_of_nonneg hs] at hG hE
    have hEs := mul_le_mul_of_nonneg_left hEu hs
    have hGs := mul_le_mul_of_nonneg_left hGa hs
    have hcs := mul_nonneg (sub_nonneg.2 hc1) hs
    rcases fin_four_lt_two hg with rfl | rfl <;> rcases fin_four_lt_two he with rfl | rfl <;>
      norm_num at hG hE
    · linarith only [hq, hEb, hS, hsum, heA, heB, heT, heD, hs, hc99, hunit, hH, hG, hA, hB, hT,
        hD, hE, hA0, hT', hD', hH00]
    · linarith only [hq, hS, hsum, heA, heB, heT, heD, hs, hc99, hunit, hH, hG, hA, hB, hT, hD,
        hE, hA0, hT', hD', hH01, hEl, hEs]
    · linarith only [hq, hEb, hS, hsum, heA, heB, heT, heD, hs, hc99, hunit, hHc, hG, hA, hB, hT,
        hD, hE, hA1, hT', hD', hH10, hceH, hGs, sq_nonneg s, hcs]
    · linarith only [hq, hS, hsum, heA, heB, heT, heD, hs, hc99, hunit, hHc, hG, hA, hB, hT, hD,
        hE, hA1, hT', hD', hH11, hceH, hGs, hEl, hEs, sq_nonneg s]
  · obtain ⟨hc9, hchord, hr2⟩ := negative_arc_geometry hc hc1 hs hsL.le hunit
    rw [abs_of_nonpos hs] at hG hE
    have hr : 0 ≤ -s := neg_nonneg.2 hs
    have hEs := mul_le_mul_of_nonneg_left hEa hr
    have hGs := mul_le_mul_of_nonneg_left hGu hr
    have hcr := mul_nonneg (sub_nonneg.2 hc9) hr
    rcases fin_four_lt_two hg with rfl | rfl <;> rcases fin_four_lt_two he with rfl | rfl <;>
      norm_num at hG hE
    · linarith only [hq, hEb, hS, hsum, heA, heB, heT, heD, hr, hunit, hchord, hr2, hH, hG, hA, hB,
        hT, hD, hE, hA0, hT', hD', hH00]
    · linarith only [hq, hS, hsum, heA, heB, heT, heD, hr, hunit, hchord, hr2, hH, hG, hA, hB, hT,
        hD, hE, hA0, hT', hD', hH01, hEl, hEs]
    · linarith only [hq, hEb, hS, hsum, heA, heB, heT, heD, hr, hunit, hchord, hr2, hcr, hHc, hG,
        hA, hB, hT, hD, hE, hA1, hT', hD', hH10, hceH, hGs]
    · linarith only [hq, hS, hsum, heA, heB, heT, heD, hsL, hunit, hchord, hr2, hHc, hG, hA, hB,
        hT, hD, hE, hA1, hT', hD', hH11, hceH, hGs, hEl, hEs]

/-- With a forbidden `B → T` axis at mismatch at most `3/200`, the `G` axes `0` and `1` do not
separate `G → A`, for every axis of `E`. -/
theorem forbidden_B_G_axis_zero_one_excluded {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200) {jB : Fin 4} (hB : jB ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    {g : Fin 4} (hg : g < 2)
    (hGsep : (forwardAxis g).Feasible (C.square G) (C.square (next G))) : False := by
  obtain ⟨hAb, hAa⟩ := forbidden_B_A_coordinates F hq hc hzero hS hB hBsep
  have hHu := H_primary_twenty_nine hq hc
  have hsL := global_negative_tilt_bound F hq hc hS
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  have hcL := half_angle_cos_three_quarters (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht
  have hc0 : 0 ≤ Real.cos (tilt F.theta) := by linarith
  have hc1 := Real.cos_le_one (tilt F.theta)
  have hunit : Real.cos (tilt F.theta)^2+Real.sin (tilt F.theta)^2=1 := by
    linarith [Real.sin_sq_add_cos_sq (tilt F.theta)]
  obtain ⟨p,hp⟩ := F.choose_owners
  have hD := D_quarter_owners F hq hc hzero hS (p D) (hp D)
  have hH0 := hzero H (by norm_num [H, zeroEdges]) (p H) (hp H)
  have hA0 := hzero A (by norm_num [A, zeroEdges]) (p A) (hp A)
  have hT0 := hzero T (by norm_num [T, zeroEdges]) (p T) (hp T)
  have hHp := aligned_projection_loss F hq (by norm_num [H, charged]) (p H) (hp H)
  have hAp := aligned_projection_loss F hq (by norm_num [A, charged]) (p A) (hp A)
  have hBp := aligned_projection_loss F hq (by norm_num [B, charged]) jB hBsep
  have hTp := aligned_projection_loss F hq (by norm_num [T, charged]) (p T) (hp T)
  have hDp := aligned_projection_loss F hq (by norm_num [D, charged]) (p D) (hp D)
  rw [nominal_zero_projection hc _ (by norm_num [H, zeroEdges]) hH0] at hHp
  rw [nominal_zero_projection hc _ (by norm_num [A, zeroEdges]) hA0] at hAp
  rw [nominal_B_forbidden_projection hc _ hB] at hBp
  rw [nominal_zero_projection hc _ (by norm_num [T, zeroEdges]) hT0] at hTp
  rw [nominal_D_intended_projection hc _ hD] at hDp
  have hGp := mixed_G_projection F g hGsep
  rw [nominal_G_projection_formula hc, nominal_G_width hc0] at hGp
  have hEp := mixed_E_projection F hq (p E) (hp E) (ε := mismatch F.theta) hS le_rfl
  rw [nominal_E_projection_formula hc, nominal_E_width hc0] at hEp
  have hsum : |delta F.theta H|+|delta F.theta A|+|delta F.theta B|+|delta F.theta T|+
      |delta F.theta D| ≤ mismatch F.theta := by
    simp [mismatch, charged, H, A, B, T, D]
    linarith
  have hHp' : 1-(3/2)*|delta F.theta H| ≤ C.b H+C.b G := hHp
  have hAp' : 1-(3/2)*|delta F.theta A| ≤ C.b A+C.b B := hAp
  have hTp' : 1-(3/2)*|delta F.theta T| ≤ C.b T+C.b D := hTp
  have hbH := canonical_bounds C hq H
  have hbA := canonical_bounds C hq A
  have hbE := canonical_bounds C hq E
  have hconeG := hc.cones hq G
  norm_num [Dual.lowerPrimary, Dual.upperPrimary] at hconeG
  have hcircle (i : Vertex) : (C.a i+1/2)^2+(C.b i+1/2)^2 ≤ q := by
    simpa [SquaresInCircles.phi] using canonical_containment C i
  have he0 := abs_nonneg (delta F.theta H)
  have he2 := abs_nonneg (delta F.theta A)
  have he3 := abs_nonneg (delta F.theta B)
  have he4 := abs_nonneg (delta F.theta T)
  have he5 := abs_nonneg (delta F.theta D)
  have hHloss : |delta F.theta H| ≤ 3/200 := by linarith
  have hpos : 0 ≤ Real.sin (tilt F.theta) →
      Real.sin (tilt F.theta) ≤ 1/10 ∧ 99/100 ≤ Real.cos (tilt F.theta) := by
    intro hs
    rw [abs_of_nonneg hs] at hGp
    exact forbidden_B_positive_tilt hg hAa hAb hconeG.1 hbH.2.2.2.le hcL hc1 hs hunit he0
      hHloss hHp' hGp
  by_cases he : 2 ≤ p E
  · exact forbidden_B_E_axis_two_three hg he hAa hAb hbA.2.2.2.le hconeG.1 hconeG.2.1
      hbH.1.le hHu hbE.2.1.le hbE.2.2.1 hbE.2.2.2.le hcL hc1 hunit hsL hpos he0
      (by linarith) hS hHp' hGp hEp
  · exact forbidden_B_stress hg (not_le.mp he) hq (hcircle A) (hcircle T) (hcircle D)
      (hcircle H) hconeG.1 hconeG.2.1 hbE.1.le hbE.2.1.le hbE.2.2.1 hcL hc1 hunit hsL hpos
      he0 he2 he3 he4 he5 hsum hS hHp' hAp' hBp hTp' hDp hGp hEp

/-- At mismatch at most `3/200` no forbidden axis separates `B → T`, also when an intended axis
separates as well. -/
theorem forbidden_B_excluded {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200) {jB : Fin 4} (hB : jB ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B))) : False := by
  obtain ⟨p,hp⟩ := F.choose_owners
  have hG := hp G
  revert hG
  generalize p G = g
  intro hG
  fin_cases g
  · exact forbidden_B_G_axis_zero_one_excluded F hq hc hzero hS hB hBsep (by decide) hG
  · exact forbidden_B_G_axis_zero_one_excluded F hq hc hzero hS hB hBsep (by decide) hG
  · exact G_axis_two_forbidden_quarter_excluded F hq hc hzero hS hB hBsep hG
  · exact G_axis_three_forbidden_B_excluded F hq hc hzero hS hB hBsep hG

/-- Every axis that separates `B → T` or `D → E` at mismatch at most `3/200` is a quarter owner. -/
theorem quarter_owners {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200) : QuarterOwners C := by
  intro i hi j hj
  have hi' : i = B ∨ i = D := by simpa [otherQuarterEdges, B, D] using hi
  rcases hi' with rfl | rfl
  · by_contra hB
    exact forbidden_B_excluded F hq hc hzero hS hB hj
  · exact D_quarter_owners F hq hc hzero hS j hj

end SquaresInCircles.Eight.Candidate
