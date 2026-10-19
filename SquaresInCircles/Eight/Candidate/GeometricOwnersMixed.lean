module

public import SquaresInCircles.Eight.Candidate.GeometricOwnersQuarterComplete

/-!
# Eight squares: the `E` axes `2` and `3` at mismatch `1/1000`

With the quarter owners at mismatch `S ≤ 1/1000`, every aligned projection loses at most
`(1001/1000)|δᵢ|`. The chain `B → T → D` and the corner disk of `B` give `b_B < 69/100`, and then
the chain `A → B` and the corner disk of `A` give `b_A ≥ 3/10` and `a_A ≤ 131/100`
(`quarter_A_coordinates`).

For each axis of `G`, a three-edge chain through `H`, `G` and `E` excludes the `E` axes `2` and
`3`. The chains of the `G` axes `2` and `3` complete the corner disk of `G` once, with the force
`(c, 1 - s)`, `(1, 1)`, `(c, c - s)` or `(1, c)`. A nonpositive tilt with the `E` axis `2`
satisfies `sin t > -1/4`, and a nonnegative tilt with the `G` axis `2` or `3` satisfies
`sin t ≤ 1/5` or `sin t ≤ 3/20`. Demand minus force is at least `3/400` and the error at most
`3001S/1000` (`mixed_E_axis_two_three`). So every axis that separates `E → H` is `0` or `1`
(`mixed_E_owners`), also when another axis separates as well.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate
open _root_.SquaresInCircles.Eight.Candidate.Dual

/-- A corner disk excludes the quadrant above and to the right of a corner outside it. -/
theorem corner_outside {a b a₀ b₀ q : ℝ} (ha : a₀ ≤ a) (hb : b₀ ≤ b) (ha₀ : 0 ≤ a₀+1/2)
    (hb₀ : 0 ≤ b₀+1/2) (hcircle : (a+1/2)^2+(b+1/2)^2 ≤ q)
    (hq : q < (a₀+1/2)^2+(b₀+1/2)^2) : False := by
  have h₁ := pow_le_pow_left₀ ha₀ (by linarith : a₀+1/2 ≤ a+1/2) 2
  have h₂ := pow_le_pow_left₀ hb₀ (by linarith : b₀+1/2 ≤ b+1/2) 2
  linarith

/-- With the quarter owners, the chain `B → T → D` gives `a_B > 109/100`, the corner disk of `B`
then `b_B < 69/100`, the chain `A → B` gives `b_A ≥ 3/10`, and the corner disk of `A` gives
`a_A ≤ 131/100`. -/
theorem quarter_A_coordinates {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C) (hquarter : QuarterOwners C)
    (hS : mismatch F.theta ≤ 1/1000) : 3/10 ≤ C.b A ∧ C.a A ≤ 131/100 := by
  obtain ⟨p,hp⟩ := F.choose_owners
  have hA0 := hzero A (by norm_num [A, zeroEdges]) (p A) (hp A)
  have hT0 := hzero T (by norm_num [T, zeroEdges]) (p T) (hp T)
  have hB := hquarter B (by norm_num [B, otherQuarterEdges]) (p B) (hp B)
  have hAp := aligned_first_order_projection F hq (by norm_num [A, charged]) (p A) (hp A)
    (by linarith)
  have hBp := aligned_first_order_projection F hq (by norm_num [B, charged]) (p B) (hp B)
    (by linarith)
  have hTp := aligned_first_order_projection F hq (by norm_num [T, charged]) (p T) (hp T)
    (by linarith)
  rw [nominal_zero_projection hc _ (by norm_num [A, zeroEdges]) hA0] at hAp
  rw [nominal_B_intended_projection hc _ hB] at hBp
  rw [nominal_zero_projection hc _ (by norm_num [T, zeroEdges]) hT0] at hTp
  have hAp' : 1-(1001/1000)*|delta F.theta A| ≤ C.b A+C.b B := hAp
  have hTp' : 1-(1001/1000)*|delta F.theta T| ≤ C.b T+C.b D := hTp
  have hsum : |delta F.theta A|+|delta F.theta B|+|delta F.theta T| ≤ mismatch F.theta := by
    simp [mismatch, charged, A, B, T]
    linarith [abs_nonneg (delta F.theta 0), abs_nonneg (delta F.theta 5)]
  have heA := abs_nonneg (delta F.theta A)
  have heB := abs_nonneg (delta F.theta B)
  have heT := abs_nonneg (delta F.theta T)
  have hcircle (i : Vertex) : (C.a i+1/2)^2+(C.b i+1/2)^2 ≤ q := by
    simpa [SquaresInCircles.phi] using canonical_containment C i
  have hQ : Q0 = 9789/2500 := rfl
  have hBb : C.b B < 69/100 := by
    by_contra! hn
    exact corner_outside (a₀ := 109/100) (b₀ := 69/100)
      (by linarith [(canonical_bounds C hq D).2.2.2]) hn (by norm_num) (by norm_num)
      (hcircle B) (by linarith)
  have hAb : 3/10 ≤ C.b A := by linarith
  refine ⟨hAb, ?_⟩
  by_contra! hn
  exact corner_outside (a₀ := 131/100) (b₀ := 3/10) hn.le hAb (by norm_num) (by norm_num)
    (hcircle A) (by linarith)

/-- For every axis of `G`, a three-edge chain through `H`, `G` and `E`, with weights `(h, w, v)`,
excludes the `E` axes `2` and `3`: `(1, 1, 1)` for the axis pairs `(0, 2)`, `(2, 2)`, `(3, 2)`,
`(c, 1, c)` for `(1, 2)`, `(c, c, 1)` for `(0, 3)` and `(c, 1, 1)` for `(1, 3)`, `(2, 3)`, `(3, 3)`.
The chains of the `G` axes `2` and `3` complete the corner disk of `G`, with weight `3/8` or, for
the force `(1, 1)`, `5/14`. Demand minus force is at least `3/400` and the error at most
`3001S/1000`. -/
theorem mixed_E_axis_two_three {aH bH aG bG aA bA aE bE c s q eH S : ℝ} {g e : Fin 4}
    (he : 2 ≤ e) (hq : q ≤ Q0) (hcG : (aG+1/2)^2+(bG+1/2)^2 ≤ q)
    (hAa : aA ≤ 131/100) (hAaL : 447/800 ≤ aA) (hAb : 3/10 ≤ bA) (hAb' : bA ≤ 9/10)
    (hGa : 7/12 ≤ aG) (hGu : aG ≤ 349/250) (hGb : aG/20 ≤ bG)
    (hHa : 447/800 ≤ aH) (hHu : aH ≤ 29/25) (hHb : aH/2 ≤ bH)
    (hEu : aE ≤ 283/200) (hEb : 0 ≤ bE) (hEb' : bE ≤ 9/10)
    (hc : 3/4 ≤ c) (hc1 : c ≤ 1) (hunit : c^2+s^2=1) (hsL : -(3/8) < s)
    (heH : 0 ≤ eH) (heHS : eH ≤ S) (hS : S ≤ 1/1000)
    (hH : 1-(1001/1000)*eH ≤ bH+bG)
    (hG : (1+c+|s|)/2 ≤ ![aA*c-bA*s-bG, aA-aG*s-bG*c, aG*c-bG*s-bA, aG-aA*s-bA*c] g)
    (hE : (1+c+|s|)/2-2*S ≤ ![aH*c+bH*s-bE, aH+aE*s-bE*c, aE*c+bE*s-bH, aE+aH*s-bH*c] e) :
    False := by
  have hc0 : 0 ≤ c := by linarith
  have hceH := mul_le_mul_of_nonneg_right hc1 heH
  have hcS := mul_le_mul_of_nonneg_right hc1 (heH.trans heHS)
  have hHc := mul_le_mul_of_nonneg_left hH hc0
  have hcc := mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hc)
  have hg : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 := by fin_cases g <;> simp
  dsimp [Q0] at hq
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs] at hG hE
    have hs7 : s ≤ 7/10 := by nlinarith only [hunit, hc, hs]
    rcases fin_four_two_le he with rfl | rfl <;> norm_num at hE <;>
      rcases hg with rfl | rfl | rfl | rfl <;> norm_num at hG
    · linarith only [hc1, heHS, hS, hs, hH, hG, hE, mul_le_mul_of_nonneg_right hAa hc0,
        mul_le_mul_of_nonneg_right hEu hc0, mul_le_mul_of_nonneg_right hEb' hs,
        mul_le_mul_of_nonneg_right hAb hs]
    · linarith only [heHS, hS, hAa, hc, hs, hHc, hG, mul_le_mul_of_nonneg_left hE hc0, hceH,
        hcS, hcc, mul_le_mul_of_nonneg_right hGa hs, mul_le_mul_of_nonneg_right hEu (sq_nonneg c),
        mul_le_mul_of_nonneg_right hEb' (mul_nonneg hc0 hs), mul_nonneg (sub_nonneg.2 hc1) hs]
    · linarith only [heHS, hS, hq, hAb, hc, hs, hunit, hH, hG, hE,
        circle_support (x := c) (y := 1-s) (μ := 3/8) (k := 2/3) (by norm_num) (by norm_num) hcG,
        mul_le_mul_of_nonneg_right hEu hc0, mul_le_mul_of_nonneg_right hEb' hs]
    · linarith only [hc1, heHS, hS, hq, hs, hH, hG, hE,
        circle_support (x := 1) (y := 1) (μ := 5/14) (k := 7/10) (by norm_num) (by norm_num) hcG,
        mul_le_mul_of_nonneg_right hEu hc0, mul_le_mul_of_nonneg_right hAb hc0,
        mul_le_mul_of_nonneg_right hEb' hs, mul_le_mul_of_nonneg_right hAaL hs]
    · linarith only [heHS, hS, hEu, hc, hs, hs7, hHc, mul_le_mul_of_nonneg_left hG hc0, hE, hceH,
        hcc, mul_le_mul_of_nonneg_right hAa (sq_nonneg c),
        mul_le_mul_of_nonneg_right hAb (mul_nonneg hc0 hs), mul_le_mul_of_nonneg_right hHu hs,
        mul_nonneg hs (sub_nonneg.2 hc)]
    · have hs23 : s ≤ 2/3 := by nlinarith only [hunit, hc, hs]
      linarith only [heHS, hS, hAa, hEu, hs, hs23, hunit, hHc, hG, hE, hceH, hcc,
        mul_le_mul_of_nonneg_right hHu hs, mul_le_mul_of_nonneg_right hGa hs,
        mul_le_mul_of_nonneg_left hs23 hs]
    · have hs5 : s ≤ 1/5 := by
        linarith only [hc1, hG, hAb, mul_le_mul_of_nonneg_right hGb hs,
          mul_nonneg (sub_nonneg.2 hGu) (by linarith : (0:ℝ) ≤ c-s/20)]
      have hc97 : 97/100 ≤ c := by
        linarith only [hcc, hunit, hs5, mul_nonneg hs (sub_nonneg.2 hs5)]
      linarith only [heHS, hS, hq, hAb, hEu, hc97, hs, hunit, hHc, hG, hE, hceH,
        circle_support (x := c) (y := c-s) (μ := 3/8) (k := 2/3) (by norm_num) (by norm_num) hcG,
        mul_le_mul_of_nonneg_right hHu hs,
        mul_nonneg (by linarith : (0:ℝ) ≤ 2*c-1) (sub_nonneg.2 hc1),
        mul_nonneg hs (sub_nonneg.2 hc97)]
    · have hs3 : s ≤ 3/20 := by
        linarith only [hG, hGu, hcc, hunit, mul_le_mul_of_nonneg_right hAaL hs,
          mul_le_mul_of_nonneg_right hAb hc0, mul_le_mul_of_nonneg_left hs7 hs]
      have hc49 : 49/50 ≤ c := by
        linarith only [hcc, hunit, hs3, mul_nonneg hs (sub_nonneg.2 hs3)]
      linarith only [heHS, hS, hq, hEu, hc49, hs, hHc, hG, hE, hceH,
        circle_support (x := 1) (y := c) (μ := 3/8) (k := 2/3) (by norm_num) (by norm_num) hcG,
        mul_le_mul_of_nonneg_right hHu hs, mul_le_mul_of_nonneg_right hAaL hs,
        mul_le_mul_of_nonneg_right hAb hc0,
        mul_nonneg (by linarith : (0:ℝ) ≤ 5*c-1) (sub_nonneg.2 hc1)]
  · obtain ⟨hc9, hchord, hr2⟩ := negative_arc_geometry hc hc1 hs hsL.le hunit
    rw [abs_of_nonpos hs] at hG hE
    have hr : 0 ≤ -s := neg_nonneg.2 hs
    rcases fin_four_two_le he with rfl | rfl <;> norm_num at hE
    · have hr4 : -s < 1/4 := by
        by_contra! hn
        linarith only [hS, hE, hHb, hHa, hn, hunit, mul_le_mul_of_nonneg_right hEu hc0,
          mul_nonneg hEb hr, sq_nonneg (1-c), mul_nonneg hr (by linarith : (0:ℝ) ≤ -s-1/4)]
      have hc19 : 19/20 ≤ c := by
        linarith only [hchord, hr4, mul_nonneg hr (by linarith : (0:ℝ) ≤ s+1/4)]
      rcases hg with rfl | rfl | rfl | rfl <;> norm_num at hG
      · linarith only [hc1, heHS, hS, hr, hH, hG, hE, mul_le_mul_of_nonneg_right hAa hc0,
          mul_le_mul_of_nonneg_right hEu hc0, mul_nonneg hEb hr, mul_le_mul_of_nonneg_right hAb' hr]
      · linarith only [heHS, hS, hAa, hc19, hr4, hHc, hG, mul_le_mul_of_nonneg_left hE hc0, hceH,
          hcS, mul_le_mul_of_nonneg_right hGu hr, mul_le_mul_of_nonneg_right hEu (sq_nonneg c),
          mul_nonneg (mul_nonneg hc0 hr) hEb, mul_nonneg (sub_nonneg.2 hc19) (sub_nonneg.2 hc1),
          mul_le_mul_of_nonneg_right hc19 hr]
      · linarith only [heHS, hS, hq, hAb, hc, hr, hunit, hH, hG, hE,
          circle_support (x := c) (y := 1-s) (μ := 3/8) (k := 2/3) (by norm_num) (by norm_num) hcG,
          mul_le_mul_of_nonneg_right hEu hc0, mul_nonneg hEb hr]
      · linarith only [hc1, heHS, hS, hq, hr4, hH, hG, hE,
          circle_support (x := 1) (y := 1) (μ := 5/14) (k := 7/10) (by norm_num) (by norm_num) hcG,
          mul_le_mul_of_nonneg_right hEu hc0, mul_le_mul_of_nonneg_right hAb hc0,
          mul_nonneg hEb hr, mul_le_mul_of_nonneg_right hAa hr]
    · rcases hg with rfl | rfl | rfl | rfl <;> norm_num at hG
      · have hcb : c*bA ≤ 9/10 := by
          linarith only [hAb', mul_le_mul_of_nonneg_right hc1 (by linarith : (0:ℝ) ≤ bA)]
        linarith only [heHS, hS, hEu, hc9, hr, hHc, mul_le_mul_of_nonneg_left hG hc0, hE, hceH,
          mul_le_mul_of_nonneg_right hAa (sq_nonneg c), mul_le_mul_of_nonneg_right hcb hr,
          mul_le_mul_of_nonneg_right hHa hr, mul_nonneg (sub_nonneg.2 hc9) (sub_nonneg.2 hc1),
          mul_nonneg hc0 hr]
      · linarith only [heHS, hS, hAa, hEu, hchord, hr2, hsL, hHc, hG, hE, hceH,
          mul_le_mul_of_nonneg_right hHa hr, mul_le_mul_of_nonneg_right hGu hr]
      · linarith only [heHS, hS, hq, hAb, hEu, hchord, hr2, hr, hunit, hHc, hG, hE, hceH,
          circle_support (x := c) (y := c-s) (μ := 3/8) (k := 2/3) (by norm_num) (by norm_num) hcG,
          mul_le_mul_of_nonneg_right hHa hr,
          mul_nonneg (by linarith : (0:ℝ) ≤ 2*c-1) (sub_nonneg.2 hc1),
          mul_nonneg (sub_nonneg.2 hc1) hr]
      · linarith only [heHS, hS, hq, hEu, hGa, hchord, hr2, hunit, hHc, hG, hE, hceH,
          circle_support (x := 1) (y := c) (μ := 3/8) (k := 2/3) (by norm_num) (by norm_num) hcG,
          mul_le_mul_of_nonneg_right hHa hr, mul_le_mul_of_nonneg_right hAa hr,
          mul_le_mul_of_nonneg_right hAb hc0,
          mul_nonneg (by linarith : (0:ℝ) ≤ 5*c-1) (sub_nonneg.2 hc1)]

/-- At mismatch at most `1/1000`, the `E` axes `2` and `3` do not separate `E → H`, whatever the
axis of `G`. -/
theorem mixed_E_axis_two_three_excluded {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C) (hquarter : QuarterOwners C)
    (hS : mismatch F.theta ≤ 1/1000) {e : Fin 4} (he : 2 ≤ e)
    (hEsep : (forwardAxis e).Feasible (C.square E) (C.square (next E))) : False := by
  obtain ⟨hAb, hAa⟩ := quarter_A_coordinates F hq hc hzero hquarter hS
  have hHu := H_primary_twenty_nine hq hc
  have hsL := global_negative_tilt_bound F hq hc (by linarith)
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  have hcL := half_angle_cos_three_quarters (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht
  have hc0 : 0 ≤ Real.cos (tilt F.theta) := by linarith
  have hunit : Real.cos (tilt F.theta)^2+Real.sin (tilt F.theta)^2=1 := by
    linarith [Real.sin_sq_add_cos_sq (tilt F.theta)]
  obtain ⟨p,hp⟩ := F.choose_owners
  have hH0 := hzero H (by norm_num [H, zeroEdges]) (p H) (hp H)
  have hHp := aligned_first_order_projection F hq (by norm_num [H, charged]) (p H) (hp H)
    (by linarith)
  rw [nominal_zero_projection hc _ (by norm_num [H, zeroEdges]) hH0] at hHp
  have hHp' : 1-(1001/1000)*|delta F.theta H| ≤ C.b H+C.b G := hHp
  have hGp := mixed_G_projection F (p G) (hp G)
  rw [nominal_G_projection_formula hc, nominal_G_width hc0] at hGp
  have hEp := mixed_E_projection F hq e hEsep (ε := mismatch F.theta) (by linarith) le_rfl
  rw [nominal_E_projection_formula hc, nominal_E_width hc0] at hEp
  have hbA := canonical_bounds C hq A
  have hbH := canonical_bounds C hq H
  have hbE := canonical_bounds C hq E
  have hconeG := hc.cones hq G
  norm_num [Dual.lowerPrimary, Dual.upperPrimary, Dual.lowerRatio, G] at hconeG
  have hconeH := (hc.cones hq H).2.2.1
  norm_num [Dual.lowerRatio, H] at hconeH
  have hcircle : (C.a G+1/2)^2+(C.b G+1/2)^2 ≤ q := by
    simpa [SquaresInCircles.phi] using canonical_containment C G
  have hHloss := delta_le_mismatch F.theta (i := H) (by norm_num [H, charged])
  exact mixed_E_axis_two_three he hq hcircle hAa hbA.1.le hAb hbA.2.2.2.le
    (by simpa [G] using hconeG.1) (by simpa [G] using hconeG.2.1)
    (by simp only [G] at hconeG ⊢; linarith [hconeG.2.2.1]) hbH.1.le hHu
    (by simp only [H] at hconeH ⊢; linarith) hbE.2.1.le hbE.2.2.1 hbE.2.2.2.le hcL
    (Real.cos_le_one _) hunit hsL (abs_nonneg _) hHloss hS hHp' hGp hEp

/-- Every axis that separates `E → H` at mismatch at most `1/1000` is `0` or `1`. -/
theorem mixed_E_owners {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C) (hquarter : QuarterOwners C)
    (hS : mismatch F.theta ≤ 1/1000) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square E) (C.square (next E))) : j < 2 := by
  by_contra! hn
  exact mixed_E_axis_two_three_excluded F hq hc hzero hquarter hS hn hj

end SquaresInCircles.Eight.Candidate
