module

public import SquaresInCircles.Eight.Candidate.GeometricOwnersDoubleComplete

/-!
# A global short negative arc and four-circle exclusion of forbidden B

The H cone and corner disk bound its primary coordinate by 29/25.
All four E axes then force sin(t)>-3/8, without any owner premise.
For forbidden B and G-axis 3, positive tilt is impossible directly;
one four-circle stress covers every E axis on the remaining short arc.
The stress has a uniform gap 1/20 and spends at most 12S/5.
This source is uncompiled and imports no generated owner table.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate
open Dual

/-- The corner (29/25,29/50) already lies strictly outside Q0. -/
theorem corner_primary_twenty_nine {a b q : ℝ} (hq : q ≤ Q0)
    (hb : 29/50 ≤ b) (hcircle : (a+1/2)^2+(b+1/2)^2 ≤ q) :
    a ≤ 29/25 := by
  by_contra! ha
  have hsa := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 29/25+1/2)
    (by linarith : (29/25:ℝ)+1/2 ≤ a+1/2) 2
  have hsb := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 29/50+1/2)
    (by linarith : (29/50:ℝ)+1/2 ≤ b+1/2) 2
  dsimp [Q0] at hq
  norm_num at hsa hsb
  linarith

theorem H_primary_twenty_nine {q : ℝ} {C : BoundaryCycle q}
    (hq : q ≤ Q0) (hc : TangentCuts C) : C.a H ≤ 29/25 := by
  have hratio := (hc.cones hq H).2.2.1
  norm_num [Dual.lowerRatio, H] at hratio
  have hcircle : (C.a H+1/2)^2+(C.b H+1/2)^2 ≤ q := by
    simpa [SquaresInCircles.phi] using canonical_containment C H
  by_contra! ha
  have hb : 29/50 ≤ C.b H := by simp only [H] at *; linarith
  exact (not_le.mpr ha) (corner_primary_twenty_nine hq hb hcircle)

/-- Every E axis fails on this entire rectangle, including its boundary.
The H primary bound is the consequence of its cone and corner disk. -/
theorem global_negative_E_axis_upper {aE bE aH bH c r : ℝ}
    (hEa : 447/800 ≤ aE) (hEu : aE ≤ 283/200) (hEb : 0 ≤ bE)
    (hHa : 447/800 ≤ aH) (hHu : aH ≤ 29/25) (hHb : aH/2 ≤ bH)
    (hcL : 3/4 ≤ c) (hcU : c ≤ 1) (hrL : 3/8 ≤ r) (hrU : r ≤ 1)
    (j : Fin 4) :
    ![aH*c-bH*r-bE,aH-aE*r-bE*c,aE*c-bE*r-bH,aE-aH*r-bH*c] j <
      (1+c+r)/2-3/100 := by
  have hc0 : 0 ≤ c := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hHb' : 447/1600 ≤ bH := by linarith
  fin_cases j
  · have hprod := mul_le_mul_of_nonneg_right hHu (by linarith : 0 ≤ c-r/2)
    have hratio := mul_le_mul_of_nonneg_right hHb hr0
    norm_num
    nlinarith
  · have hprod := mul_le_mul_of_nonneg_right hEa hr0
    have hsign := mul_nonneg hEb hc0
    norm_num
    nlinarith
  · have hprod := mul_le_mul_of_nonneg_right hEu hc0
    have hsign := mul_nonneg hEb hr0
    norm_num
    nlinarith
  · have hprodA := mul_le_mul_of_nonneg_right hHa hr0
    have hprodB := mul_le_mul_of_nonneg_right hHb' hc0
    norm_num
    nlinarith

/-- No quarter or mixed-owner conclusion is needed for this global bound. -/
theorem global_negative_tilt_bound {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C)
    (hS : mismatch F.theta ≤ 3/200) : -(3/8:ℝ) < Real.sin (tilt F.theta) := by
  by_contra! hsin
  obtain ⟨p,hp⟩ := F.choose_owners
  have hEp := mixed_E_projection F hq (p E) (hp E)
    (ε := mismatch F.theta) hS le_rfl
  rw [nominal_E_negative_projection_formula hc] at hEp
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  have hcL := half_angle_cos_three_quarters (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht
  have hc0 : 0 ≤ Real.cos (tilt F.theta) := by linarith
  have hs0 : Real.sin (tilt F.theta) ≤ 0 := by linarith
  have hwidth : pairWidth (nominalPhase (tilt F.theta) E) =
      (1+Real.cos (tilt F.theta)+(-Real.sin (tilt F.theta)))/2 := by
    simp [pairWidth, nominalPhase, E, G, zeroEdges, otherQuarterEdges,
      Real.sin_add, Real.cos_add, abs_of_nonneg hc0, abs_of_nonpos hs0] <;> ring
  rw [hwidth] at hEp
  have hratio := (hc.cones hq H).2.2.1
  norm_num [Dual.lowerRatio, H] at hratio
  have hHb : C.a H/2 ≤ C.b H := by simp only [H]; linarith
  have hbound := global_negative_E_axis_upper (canonical_bounds C hq E).1.le
    (canonical_bounds C hq E).2.1.le (C.b_nonneg E)
    (canonical_bounds C hq H).1.le (H_primary_twenty_nine hq hc) hHb
    hcL (Real.cos_le_one _) (by linarith : 3/8 ≤ -Real.sin (tilt F.theta))
    (by linarith [Real.neg_one_le_sin (tilt F.theta)] : -Real.sin (tilt F.theta) ≤ 1)
    (p E)
  linarith

/-- The original T upper bound makes the forbidden B chain quantitatively
large on A's transverse side. Only the actual A and B errors are spent. -/
theorem forbidden_B_A_coordinates {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200) {jB : Fin 4} (hB : jB ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B))) :
    29/50 ≤ C.b A ∧ C.a A ≤ 29/25 := by
  obtain ⟨p,hp⟩ := F.choose_owners
  have hA := hzero A (by norm_num [A, zeroEdges]) (p A) (hp A)
  have hAp := aligned_projection_loss F hq (by norm_num [A, charged]) (p A) (hp A)
  have hBp := aligned_projection_loss F hq (by norm_num [B, charged]) jB hBsep
  rw [nominal_zero_projection hc _ (by norm_num [A, zeroEdges]) hA] at hAp
  rw [nominal_B_forbidden_projection hc _ hB] at hBp
  have hpartial : |delta F.theta A|+|delta F.theta B| ≤ mismatch F.theta := by
    simp [mismatch, charged, H, A, B, T, D] <;>
      linarith [abs_nonneg (delta F.theta 0), abs_nonneg (delta F.theta 4),
        abs_nonneg (delta F.theta 5)]
  have hTu := (hc.cones hq T).2.1
  norm_num [Dual.upperPrimary, T, G] at hTu
  have hb : 29/50 ≤ C.b A := by
    norm_num [A, B, next] at hAp
    simp only [A, B, T] at hBp hpartial ⊢
    linarith
  have hcircle : (C.a A+1/2)^2+(C.b A+1/2)^2 ≤ q := by
    simpa [SquaresInCircles.phi] using canonical_containment C A
  exact ⟨hb,corner_primary_twenty_nine hq hb hcircle⟩

theorem nominal_D_intended_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) {j : Fin 4} (hj : j ∈ quarterOwners) :
    actualProjection C D j (nominalPhase t D) = C.a D+C.b E := by
  have hs := hc.signed_coordinates
  fin_cases j <;> norm_num [quarterOwners] at hj ⊢ <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalPhase, zeroEdges, otherQuarterEdges, next, D, E, G, hs, Dual.signs] <;> ring

namespace ForbiddenBStress

def edgeWeight (c : ℝ) : Vertex → ℝ := ![2/5,1,c,c,2/5,9/20,9/20]

def demand (c r : ℝ) : ℝ := (29/20)*(1+c+r)/2+2*c+5/4

def force (a b : Vertex → ℝ) (c r : ℝ) (j : Fin 4) : ℝ :=
  a G+(2/5)*b G+r*a A+c*a T+(2/5)*b T+(9/20)*a D+(2/5)*b D+
    ![(9/20)*c*a H+(2/5-(9/20)*r)*b H,
      (9/20)*a H+(2/5)*b H-(9/20)*r*a E+(9/20)*(1-c)*b E,
      (2/5-9/20)*b H+(9/20)*c*a E+(9/20)*(1-r)*b E,
      -(9/20)*r*a H+(2/5-(9/20)*c)*b H+(9/20)*a E+(9/20)*b E] j

theorem shared_loss (θ : Vertex → ℝ) {c : ℝ} (hc : c ≤ 1) :
    (∑ j : Fin 5, edgeWeight c (alignedEdge j)*|delta θ (alignedEdge j)|) ≤
      mismatch θ := by
  have hh := weighted_total_error (fun j : Fin 5 => edgeWeight c (alignedEdge j))
    (fun j : Fin 5 => delta θ (alignedEdge j)) (M := 1) (ε := mismatch θ)
    (by norm_num) (by
      intro j
      fin_cases j <;> norm_num [edgeWeight, alignedEdge] <;> exact hc)
    (by simp [mismatch, charged, alignedEdge, Fin.sum_univ_succ])
  simpa using hh

/-- A single four-circle argument with four explicit E force directions.
The G and T weights are 11/40; the D and H-or-E weights are 3/20.
Their total is 17/20. All four forces have a uniform geometric gap 1/20. -/
theorem four_circle_gap (a b : Vertex → ℝ) {q c r : ℝ}
    (hq : q ≤ Q0) (hcircle : ∀ i, (a i+1/2)^2+(b i+1/2)^2 ≤ q)
    (hAa : a A ≤ 29/25) (hEa : 447/800 ≤ a E) (hHa : 447/800 ≤ a H)
    (hEb : b E ≤ 9/10) (hHb : 0 ≤ b H)
    (hc : 3/4 ≤ c) (hr : 0 ≤ r) (hrU : r ≤ 3/8)
    (hunit : c^2+r^2=1) (j : Fin 4) : force a b c r j+1/20 ≤ demand c r := by
  have hc0 : 0 ≤ c := by linarith
  have hcU : c ≤ 1 := by nlinarith [sq_nonneg r,sq_nonneg (c-1)]
  have hrSq := pow_le_pow_left₀ hr hrU 2
  have hcL : 9/10 ≤ c := by
    by_contra! hh
    have hcSq := pow_le_pow_left₀ hc0 hh.le 2
    nlinarith
  have hchord : 1-c ≤ (4/7)*r^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hcU) (sub_nonneg.mpr hc)
    nlinarith
  have hAprod := mul_le_mul_of_nonneg_right hAa hr
  have hG := Dual.circle_linear_upper (a := a G) (b := b G)
    (C := 1) (D := 2/5) (μ := 11/40) (by norm_num) (hcircle G)
  have hT := Dual.circle_linear_upper (a := a T) (b := b T)
    (C := c) (D := 2/5) (μ := 11/40) (by norm_num) (hcircle T)
  have hD := Dual.circle_linear_upper (a := a D) (b := b D)
    (C := 9/20) (D := 2/5) (μ := 3/20) (by norm_num) (hcircle D)
  dsimp [Q0] at hq
  norm_num at hG hT hD
  fin_cases j
  · have hH := Dual.circle_linear_upper (a := a H) (b := b H)
      (C := (9/20)*c) (D := 2/5-(9/20)*r) (μ := 3/20) (by norm_num) (hcircle H)
    norm_num at hH
    simp only [force,demand,Matrix.cons_val_zero]
    nlinarith only [hq,hAprod,hG,hT,hD,hH,hunit,hchord,hrU,hrSq]
  · have hEprimary := mul_le_mul_of_nonneg_right hEa hr
    have hEtransverse := mul_le_mul_of_nonneg_right hEb (sub_nonneg.mpr hcU)
    have hH := Dual.circle_linear_upper (a := a H) (b := b H)
      (C := 9/20) (D := 2/5) (μ := 3/20) (by norm_num) (hcircle H)
    norm_num at hH
    simp only [force,demand,Matrix.cons_val_succ,Matrix.cons_val_zero]
    nlinarith only [hq,hAprod,hG,hT,hD,hH,hEprimary,hEtransverse,hunit,hchord,hrU,hrSq]
  · have hE := Dual.circle_linear_upper (a := a E) (b := b E)
      (C := (9/20)*c) (D := (9/20)*(1-r)) (μ := 3/20) (by norm_num) (hcircle E)
    norm_num at hE
    simp only [force,demand,Matrix.cons_val_succ,Matrix.cons_val_zero]
    nlinarith only [hq,hAprod,hG,hT,hD,hE,hHb,hunit,hchord,hr,hrSq]
  · have hHprimary := mul_le_mul_of_nonneg_right hHa hr
    have hHsign := mul_nonneg (by linarith : 0 ≤ (9/20)*c-2/5) hHb
    have hE := Dual.circle_linear_upper (a := a E) (b := b E)
      (C := 9/20) (D := 9/20) (μ := 3/20) (by norm_num) (hcircle E)
    norm_num at hE
    simp only [force,demand,Matrix.cons_val_succ,Matrix.cons_val_zero]
    nlinarith only [hq,hAprod,hG,hT,hD,hE,hHprimary,hHsign,hunit,hchord,hrU,hrSq]

end ForbiddenBStress

/-- A whole-chart exclusion for every E axis, under one forbidden B axis.
D is captured by the earlier geometric theorem before its projection is used. -/
theorem G_axis_three_forbidden_B_excluded {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200) {jB : Fin 4} (hB : jB ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hGsep : (forwardAxis 3).Feasible (C.square G) (C.square (next G))) : False := by
  obtain ⟨hAb,hAa⟩ := forbidden_B_A_coordinates F hq hc hzero hS hB hBsep
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  have hcL := half_angle_cos_three_quarters (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht
  have hc0 : 0 ≤ Real.cos (tilt F.theta) := by linarith
  have hGp := mixed_G_projection F 3 hGsep
  rw [nominal_G_axis_three_projection hc] at hGp
  have hsin : Real.sin (tilt F.theta) < 0 := by
    by_contra! hs0
    have hAprod := mul_nonneg (C.a_pos A).le hs0
    have hBprod := mul_le_mul_of_nonneg_right hAb hc0
    have hGa := (canonical_bounds C hq G).2.1
    have hw := width_one_le (nominalPhase (tilt F.theta) G)
    nlinarith
  have hrU := global_negative_tilt_bound F hq hc hS
  have hwidthG : pairWidth (nominalPhase (tilt F.theta) G) =
      (1+Real.cos (tilt F.theta)+(-Real.sin (tilt F.theta)))/2 := by
    simp [pairWidth, nominalPhase, G, zeroEdges, otherQuarterEdges,
      Real.sin_sub, Real.cos_sub, abs_of_nonneg hc0, abs_of_nonpos hsin.le] <;> ring
  have hwidthE : pairWidth (nominalPhase (tilt F.theta) E) =
      (1+Real.cos (tilt F.theta)+(-Real.sin (tilt F.theta)))/2 := by
    simp [pairWidth, nominalPhase, E, G, zeroEdges, otherQuarterEdges,
      Real.sin_add, Real.cos_add, abs_of_nonneg hc0, abs_of_nonpos hsin.le] <;> ring
  rw [hwidthG] at hGp
  obtain ⟨p,hp⟩ := F.choose_owners
  have hD := D_quarter_owners F hq hc hzero hS (p D) (hp D)
  have hH := hzero H (by norm_num [H, zeroEdges]) (p H) (hp H)
  have hA := hzero A (by norm_num [A, zeroEdges]) (p A) (hp A)
  have hT := hzero T (by norm_num [T, zeroEdges]) (p T) (hp T)
  have hHp := aligned_projection_loss F hq (by norm_num [H, charged]) (p H) (hp H)
  have hAp := aligned_projection_loss F hq (by norm_num [A, charged]) (p A) (hp A)
  have hBp := aligned_projection_loss F hq (by norm_num [B, charged]) jB hBsep
  have hTp := aligned_projection_loss F hq (by norm_num [T, charged]) (p T) (hp T)
  have hDp := aligned_projection_loss F hq (by norm_num [D, charged]) (p D) (hp D)
  rw [nominal_zero_projection hc _ (by norm_num [H, zeroEdges]) hH] at hHp
  rw [nominal_zero_projection hc _ (by norm_num [A, zeroEdges]) hA] at hAp
  rw [nominal_B_forbidden_projection hc _ hB] at hBp
  rw [nominal_zero_projection hc _ (by norm_num [T, zeroEdges]) hT] at hTp
  rw [nominal_D_intended_projection hc _ hD] at hDp
  have hAc := mul_le_mul_of_nonneg_right hAp hc0
  have hBc := mul_le_mul_of_nonneg_right hBp hc0
  have hEp := mixed_E_projection F hq (p E) (hp E)
    (ε := mismatch F.theta) hS le_rfl
  rw [nominal_E_negative_projection_formula hc,hwidthE] at hEp
  have hweight := ForbiddenBStress.shared_loss F.theta (Real.cos_le_one (tilt F.theta))
  simp only [ForbiddenBStress.edgeWeight,alignedEdge,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ] at hweight
  have hforce : ForbiddenBStress.demand (Real.cos (tilt F.theta)) (-Real.sin (tilt F.theta))-
        (12/5)*mismatch F.theta ≤
      ForbiddenBStress.force C.a C.b (Real.cos (tilt F.theta)) (-Real.sin (tilt F.theta)) (p E) := by
    dsimp [ForbiddenBStress.force,ForbiddenBStress.demand]
    norm_num [H,G,A,B,T,D,E,next] at hHp hAc hBc hTp hDp hGp hEp
    simp only [H,G,A,B,T,D,E]
    fin_cases p E <;> norm_num at hEp ⊢ <;> nlinarith
  have hgap := ForbiddenBStress.four_circle_gap C.a C.b hq
    (fun i => by simpa [SquaresInCircles.phi] using canonical_containment C i)
    hAa (canonical_bounds C hq E).1.le (canonical_bounds C hq H).1.le
    (canonical_bounds C hq E).2.2.2.le (C.b_nonneg H) hcL
    (by linarith : 0 ≤ -Real.sin (tilt F.theta)) (by linarith)
    (by nlinarith [Real.sin_sq_add_cos_sq (tilt F.theta)]) (p E)
  linarith

end SquaresInCircles.Eight.Candidate
