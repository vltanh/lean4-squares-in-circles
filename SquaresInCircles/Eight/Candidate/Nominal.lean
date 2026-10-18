module

public import SquaresInCircles.Eight.Candidate.Projection

/-!
# Eight squares: nominal angles and the forces of the duals

The nominal angle of an edge is its angle at zero mismatch: `0` or `π/2` on the aligned edges, and
`π/2 - t` and `π/2 + t` on the mixed edges `G → A` and `E → H`, for the tilt `t`
(`nominalPhase`). The actual angle is the nominal one plus the frame difference on an aligned
edge, the nominal one on `G → A`, and the nominal one less the total signed error on `E → H`
(`phase_decomposition`). Under the tangent cuts the states satisfy the cone inequalities of the
duals (`TangentCuts.cones`), and the projections on the separating axes, at the nominal angles
and in the half-angle variable `z`, are the rational forces of the duals divided by `1 + z²`
(`nominal_projection_identity`, `nominal_derivative_identity`, `nominal_width_identity`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate
open Dual

structure TangentCuts {q : ℝ} (C : BoundaryCycle q) : Prop where
  signs : Signs C
  e_half : EHalf C
  g_cut : GCut C
  t_cut : TCut C
  hd_cut : HDCut C

theorem tangent_mul {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    C.tangent i * C.a i = C.sigma i * C.b i := by
  simp [BoundaryCycle.tangent, ne_of_gt (C.a_pos i)]

theorem positive_tangent_coordinate {q : ℝ} (C : BoundaryCycle q) {i : Vertex}
    (ht : 0 < C.tangent i) : C.sigma i * C.b i = C.b i := by
  have hp := mul_pos ht (C.a_pos i)
  rw [tangent_mul] at hp
  rcases C.sigma_sign i with hs | hs
  · have hb := C.b_nonneg i
    simp [hs] at hp
    linarith
  · simp [hs]

theorem nonpositive_tangent_coordinate {q : ℝ} (C : BoundaryCycle q) {i : Vertex}
    (ht : C.tangent i ≤ 0) : C.sigma i * C.b i = -C.b i := by
  have hp := mul_nonpos_of_nonpos_of_nonneg ht (C.a_pos i).le
  rw [tangent_mul] at hp
  rcases C.sigma_sign i with hs | hs
  · simp [hs]
  · have hb := C.b_nonneg i
    simp [hs] at hp
    have he : C.b i=0 := le_antisymm hp hb
    simp [hs, he]

theorem TangentCuts.signed_coordinates {q : ℝ} {C : BoundaryCycle q} (hc : TangentCuts C) :
    ∀ i, C.sigma i * C.b i = (Dual.signs i : ℝ) * C.b i := by
  rcases hc.signs with ⟨hH,hG,hA,hB,hT,hD⟩
  intro i
  fin_cases i
  · simpa [Dual.signs,H] using positive_tangent_coordinate C hH
  · simpa [Dual.signs,G] using nonpositive_tangent_coordinate C hG.le
  · simpa [Dual.signs,A] using positive_tangent_coordinate C hA
  · simpa [Dual.signs,B] using nonpositive_tangent_coordinate C hB.le
  · simpa [Dual.signs,T] using positive_tangent_coordinate C hT
  · simpa [Dual.signs,D] using nonpositive_tangent_coordinate C hD.le
  · simpa [Dual.signs,E] using nonpositive_tangent_coordinate C hc.e_half

theorem slider_primary_bounds {a b q : ℝ} (ha : 1/2 < a) (hb : 0 ≤ b)
    (hcone : a/20 ≤ b ∧ b ≤ (4/5)*a)
    (hcore : (1/12:ℝ)^2 ≤ (max (a-1/2) 0)^2+(max (b-1/2) 0)^2)
    (hcircle : (a+1/2)^2+(b+1/2)^2 ≤ q) (hq : q ≤ Q0) :
    7/12 ≤ a ∧ a ≤ 349/250 := by
  constructor
  · by_contra! hn
    have hbb : b < 1/2 := by linarith only [hcone.2, ha, hn]
    rw [max_eq_left (by linarith only [ha] : 0 ≤ a-1/2),
      max_eq_right (by linarith only [ha, hcone, hn] : b-1/2 ≤ 0)] at hcore
    nlinarith only [hcore, hn, ha]
  · by_contra! hn
    have hbl : 349/5000 < b := by linarith only [hcone.1, hn]
    have hs₁ : (349/250+1/2:ℝ)^2 < (a+1/2)^2 :=
      (sq_lt_sq₀ (by norm_num) (by linarith only [hn])).2 (by linarith only [hn])
    have hs₂ : (349/5000+1/2:ℝ)^2 < (b+1/2)^2 :=
      (sq_lt_sq₀ (by norm_num) (by linarith only [hcone, hn])).2 (by linarith only [hcone, hn])
    dsimp [Q0] at hq
    norm_num at hs₁ hs₂
    linarith only [hcircle, hq, hs₁, hs₂]

theorem TangentCuts.cones {q : ℝ} {C : BoundaryCycle q} (hc : TangentCuts C)
    (hq : q ≤ Q0) : ConeBounds C.a C.b := by
  have hs := hc.signed_coordinates
  have hg := hc.g_cut
  have ht := hc.t_cut
  have hhd := hc.hd_cut
  have hGratio : C.a G/20 ≤ C.b G ∧ C.b G ≤ (4/5)*C.a G := by
    have h₁ := mul_lt_mul_of_pos_right hg.1 (C.a_pos G)
    have h₂ := mul_lt_mul_of_pos_right hg.2 (C.a_pos G)
    rw [tangent_mul] at h₁ h₂
    rw [hs] at h₁ h₂
    norm_num [Dual.signs,G] at h₁ h₂
    simp only [G]
    constructor <;> linarith only [h₂, h₁]
  have hTratio : C.a T/20 ≤ C.b T ∧ C.b T ≤ (4/5)*C.a T := by
    have h₁ := mul_lt_mul_of_pos_right ht.1 (C.a_pos T)
    have h₂ := mul_lt_mul_of_pos_right ht.2 (C.a_pos T)
    rw [tangent_mul] at h₁ h₂
    rw [hs] at h₁ h₂
    norm_num [Dual.signs,T] at h₁ h₂
    simp only [T]
    constructor <;> linarith only [h₁, h₂]
  have hHr : (1/2)*C.a H ≤ C.b H := by
    have hh := mul_lt_mul_of_pos_right hhd.1 (C.a_pos H)
    rw [tangent_mul, hs] at hh
    norm_num [Dual.signs,H] at hh
    simp only [H]
    linarith only [hh]
  have hDr : (1/2)*C.a D ≤ C.b D := by
    have hh := mul_lt_mul_of_pos_right hhd.2 (C.a_pos D)
    rw [tangent_mul, hs] at hh
    norm_num [Dual.signs,D] at hh
    simp only [D]
    linarith only [hh]
  have hG := slider_primary_bounds
    (a := C.a G) (b := C.b G) (q := q)
    (by have hh := (canonical_bounds C hq G).1; linarith only [hh]) (C.b_nonneg G)
    hGratio (canonical_core_distance C G) (canonical_containment C G) hq
  have hT := slider_primary_bounds
    (a := C.a T) (b := C.b T) (q := q)
    (by have hh := (canonical_bounds C hq T).1; linarith only [hh]) (C.b_nonneg T)
    hTratio (canonical_core_distance C T) (canonical_containment C T) hq
  simp only [H, G, A, B, T, D, E] at hGratio hTratio hHr hDr hG hT
  obtain ⟨hG1, hG2⟩ := hGratio
  obtain ⟨hT1, hT2⟩ := hTratio
  obtain ⟨hG3, hG4⟩ := hG
  obtain ⟨hT3, hT4⟩ := hT
  intro i
  obtain ⟨hb1, hb2, hb3, hb4⟩ := canonical_bounds C hq i
  have hba := C.b_le_a i
  fin_cases i <;>
    (try simp [lowerPrimary, upperPrimary, lowerRatio, upperRatio, G, T] at hb1 hb2 hb3 hb4 hba ⊢) <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | assumption
    | linarith only [hb1, hb2, hHr, hba, hb4, hG3, hG4, hG1, hG2, hb3, hT3, hT4, hT1, hT2, hDr]

def nominalPhase (t : ℝ) (i : Vertex) : ℝ :=
  if i ∈ zeroEdges then 0 else if i ∈ otherQuarterEdges then Real.pi/2
  else if i=G then Real.pi/2-t else Real.pi/2+t

def totalSignedError (θ : Vertex → ℝ) : ℝ := ∑ j : Fin 5, delta θ (alignedEdge j)

theorem totalSignedError_abs (θ : Vertex → ℝ) : |totalSignedError θ| ≤ mismatch θ := by
  have hh := Finset.abs_sum_le_sum_abs (fun j : Fin 5 => delta θ (alignedEdge j)) Finset.univ
  simpa [totalSignedError, mismatch, charged, alignedEdge, Fin.sum_univ_succ] using hh

theorem phase_decomposition {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Vertex) :
    phi F.theta i = nominalPhase (tilt F.theta) i +
      (if i ∈ charged then delta F.theta i else if i=G then 0 else -totalSignedError F.theta) := by
  have hA := F.theta_A
  fin_cases i <;>
    simp only [A, Fin.isValue, phi, word, Fin.zero_eta, Matrix.cons_val_zero, Int.cast_zero,
      zero_mul, zero_div, delta, next, zero_add, nominalPhase, zeroEdges, Finset.mem_insert,
      Fin.reduceEq, Finset.mem_singleton, or_self, or_false, ↓reduceIte, charged, Fin.mk_one,
      Matrix.cons_val_one, Int.cast_one, one_mul, Fin.reduceAdd, one_ne_zero, otherQuarterEdges, G,
      tilt, add_zero, Fin.reduceFinMk, Matrix.cons_val, or_true, totalSignedError, alignedEdge,
      Finset.sum_sub_distrib, Fin.sum_univ_succ, Matrix.cons_val_succ, Finset.univ_unique,
      Fin.default_eq_zero, Matrix.cons_val_fin_one, Finset.sum_const, Finset.card_singleton,
      one_smul, neg_sub] at hA ⊢ <;> linarith

def actualProjection {q : ℝ} (C : BoundaryCycle q) (i : Vertex) (j : Fin 4) (x : ℝ) : ℝ :=
  projection (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
    (C.sigma i) (C.sigma (next i)) j x

def actualDerivative {q : ℝ} (C : BoundaryCycle q) (i : Vertex) (j : Fin 4) (x : ℝ) : ℝ :=
  projectionDeriv (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
    (C.sigma i) (C.sigma (next i)) j x

theorem actualProjection_feasible {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    pairWidth (phi F.theta i) ≤ actualProjection C i j (phi F.theta i) := by
  have hm := (F.margin_nonneg_iff i j).1 hj
  rw [actualProjection, projection_margin]
  exact le_add_of_nonneg_left hm

theorem actualProjection_lipschitz {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0)
    (i : Vertex) (j : Fin 4) (x y : ℝ) :
    |actualProjection C i j x-actualProjection C i j y| ≤ (3/2:ℝ)*|x-y| :=
  sinusoid_lipschitz (by norm_num) (projection_amplitude C hq i j) _ x y

theorem actualProjection_taylor {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0)
    (i : Vertex) (j : Fin 4) (x d : ℝ) :
    actualProjection C i j x + actualDerivative C i j x*d - (3/4:ℝ)*d^2 ≤
      actualProjection C i j (x+d) ∧
    actualProjection C i j (x+d) ≤ actualProjection C i j x +
      actualDerivative C i j x*d + (3/4:ℝ)*d^2 := by
  have h := sinusoid_taylor (by norm_num) (projection_amplitude C hq i j)
    (projectionCoefficients (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      (C.sigma i) (C.sigma (next i)) j 0) x d
  simp only [actualProjection, actualDerivative, projection, projectionDeriv]
  constructor <;> linarith [h.1, h.2]

theorem actualDerivative_abs {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0)
    (i : Vertex) (j : Fin 4) (x : ℝ) : |actualDerivative C i j x| ≤ 3/2 :=
  sinusoid_derivative_bound (by norm_num) (projection_amplitude C hq i j) x

private theorem peval_add (p q : Poly) (z : ℝ) : peval (p + q) z = peval p z + peval q z := by
  simp [peval]
private theorem peval_sub (p q : Poly) (z : ℝ) : peval (p - q) z = peval p z - peval q z := by
  simp [peval]
private theorem peval_neg (p : Poly) (z : ℝ) : peval (-p) z = -peval p z := by
  simp [peval]
private theorem peval_zero (z : ℝ) : peval 0 z = 0 := by
  simp [peval]
private theorem peval_C_mul (c : ℚ) (p : Poly) (z : ℝ) :
    peval (Polynomial.C c * p) z = (c : ℝ) * peval p z := by
  simp [peval]

/-- A coefficient vector concentrated at `m` picks out the value at `m`. -/
private theorem sum_peval_coefficient (m : Vertex) (p : Poly) (z : ℝ) (f : Vertex → ℝ) :
    ∑ k, peval (coefficient m k p) z * f k = peval p z * f m := by
  rw [Finset.sum_eq_single m (fun k _ hk => by simp [coefficient, Ne.symm hk, peval])
    (fun h => absurd (Finset.mem_univ m) h)]
  simp [coefficient]

/-- The sine and cosine numerators are the sine and cosine of the nominal angle, times
`1 + z²`. -/
private theorem nominal_sin_cos (z : ℝ) (i : Vertex) :
    peval (sinNumerator i) z = peval Dpoly z * Real.sin (nominalPhase (2*Real.arctan z) i) ∧
    peval (cosNumerator i) z = peval Dpoly z * Real.cos (nominalPhase (2*Real.arctan z) i) := by
  have hid := half_angle_identities z
  have hd : (1+z^2:ℝ) ≠ 0 := by positivity
  fin_cases i <;>
    simp [sinNumerator, cosNumerator, nominalPhase, zeroEdges, otherQuarterEdges, G,
      Real.sin_sub, Real.cos_sub, Real.sin_add, Real.cos_add, hid.1, hid.2, peval_neg,
      peval_zero] <;>
    exact ⟨by field_simp, by field_simp⟩

theorem nominal_projection_identity {q : ℝ} {C : BoundaryCycle q} (hc : TangentCuts C)
    (z : ℝ) (i : Vertex) (j : Fin 4) :
    projectionNumerator C.a C.b z i j / peval Dpoly z =
      actualProjection C i j (nominalPhase (2*Real.arctan z) i) := by
  have hd := D_positive z
  have hs := hc.signed_coordinates
  obtain ⟨hsin, hcos⟩ := nominal_sin_cos z i
  rw [div_eq_iff (ne_of_gt hd)]
  fin_cases j <;>
    simp only [projectionNumerator, nominalA, nominalB, actualProjection, projection,
      projectionCoefficients, sinusoid, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, peval_add, peval_sub, peval_neg, add_mul, sub_mul,
      neg_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      sum_peval_coefficient, peval_C_mul, hsin, hcos, hs] <;>
    ring

theorem nominal_derivative_identity {q : ℝ} {C : BoundaryCycle q} (hc : TangentCuts C)
    (z : ℝ) (i : Vertex) (j : Fin 4) :
    derivativeNumerator C.a C.b z i j / peval Dpoly z =
      actualDerivative C i j (nominalPhase (2*Real.arctan z) i) := by
  have hd := D_positive z
  have hs := hc.signed_coordinates
  obtain ⟨hsin, hcos⟩ := nominal_sin_cos z i
  rw [div_eq_iff (ne_of_gt hd)]
  fin_cases j <;>
    simp only [derivativeNumerator, derivativeA, derivativeB, actualDerivative, projectionDeriv,
      projectionCoefficients, sinusoidDeriv, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, peval_neg, sub_mul, neg_mul,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_peval_coefficient, peval_C_mul, hsin,
      hcos, hs] <;>
    ring

theorem nominal_width_identity {z : ℝ} {positive : Bool}
    (hz : |z| ≤ 3/8) (hsign : if positive then 0 ≤ z else z ≤ 0) (i : Vertex) :
    peval (edgeWidth positive i) z / peval Dpoly z =
      pairWidth (nominalPhase (2*Real.arctan z) i) := by
  have hid := half_angle_identities z
  have hd := D_positive z
  have hnum : 0 ≤ 1-z^2 := by have hh := abs_le.mp hz; nlinarith only [hh]
  have hc : 0 ≤ Real.cos (2*Real.arctan z) := by rw [hid.2]; positivity
  have hs : if positive then 0 ≤ Real.sin (2*Real.arctan z)
      else Real.sin (2*Real.arctan z) ≤ 0 := by
    cases positive <;> simp at hsign ⊢ <;> rw [hid.1]
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    · positivity
  have hz2 : (1 + z ^ 2 : ℝ) ≠ 0 := by positivity
  have hcabs : |Real.cos (2*Real.arctan z)| = (1 - z ^ 2) / (1 + z ^ 2) := by
    rw [abs_of_nonneg hc, hid.2]
  have hsabs : |Real.sin (2*Real.arctan z)| =
      (signValue positive : ℝ) * (2 * z / (1 + z ^ 2)) := by
    cases positive
    · have hs' : Real.sin (2*Real.arctan z) ≤ 0 := by simpa using hs
      rw [abs_of_nonpos hs', hid.1]
      simp [signValue]
    · have hs' : 0 ≤ Real.sin (2*Real.arctan z) := by simpa using hs
      rw [abs_of_nonneg hs', hid.1]
      simp [signValue]
  by_cases hm : i ∈ mixedEdges
  · have hW : peval (edgeWidth positive i) z =
        (1 / 2) * ((1 + z ^ 2) + (1 - z ^ 2) + (signValue positive : ℝ) * (2 * z)) := by
      simp [edgeWidth, hm, widthNumerator, peval, Dpoly, Cpoly, Spoly]
    have hi : i = G ∨ i = E := by
      simp only [mixedEdges, Finset.mem_insert, Finset.mem_singleton] at hm
      exact hm
    have hzero : i ∉ zeroEdges := by
      rcases hi with rfl | rfl <;> decide
    have hquarter : i ∉ otherQuarterEdges := by
      rcases hi with rfl | rfl <;> decide
    rw [hW, eval_D]
    rcases hi with rfl | rfl
    · simp only [nominalPhase, hzero, hquarter, ite_false, ite_true, pairWidth,
        Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hcabs, hsabs]
      field_simp
    · have hEG : E ≠ G := by decide
      have hsE : Real.sin (Real.pi / 2 + 2 * Real.arctan z) = Real.cos (2 * Real.arctan z) := by
        rw [add_comm, Real.sin_add_pi_div_two]
      have hcE : Real.cos (Real.pi / 2 + 2 * Real.arctan z) = -Real.sin (2 * Real.arctan z) := by
        rw [add_comm, Real.cos_add_pi_div_two]
      simp only [nominalPhase, hzero, hquarter, hEG, ite_false, pairWidth,
        hsE, hcE, abs_neg, hcabs, hsabs]
      field_simp
  · have hl : peval (edgeWidth positive i) z / peval Dpoly z = 1 := by
      simp only [edgeWidth, hm, ite_false]
      exact div_self (ne_of_gt hd)
    rw [hl]
    by_cases hz0 : i ∈ zeroEdges
    · simp [nominalPhase, hz0, pairWidth]
    · have hq : i ∈ otherQuarterEdges := by
        revert hm hz0
        fin_cases i <;> decide
      simp [nominalPhase, hz0, hq, pairWidth]

theorem nominal_width_derivative_identity {z : ℝ} {positive : Bool} :
    peval (lastWidthDerivative positive) z / peval Dpoly z =
      widthSlope positive (2*Real.arctan z) := by
  have hid := half_angle_identities z
  cases positive <;>
    simp [lastWidthDerivative, widthSlope, peval, Cpoly, Spoly, Dpoly, hid.1, hid.2] <;>
    field_simp [show (1+z^2:ℝ)≠0 by positivity] <;> ring

def FeasibleOwners {q : ℝ} (C : BoundaryCycle q) (p : Vertex → Fin 4) : Prop :=
  ∀ i, (forwardAxis (p i)).Feasible (C.square i) (C.square (next i))

theorem Frame.choose_owners {q : ℝ} {C : BoundaryCycle q} (F : Frame C) :
    ∃ p, FeasibleOwners C p := by
  have hh : ∀ i, ∃ j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    intro i
    obtain ⟨j,hj⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨j,hj ▸ C.feasible i⟩
  exact Classical.skolem.mp hh

theorem Frame.choose_owners_at {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (i : Vertex) (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ∃ p, FeasibleOwners C p ∧ p i=j := by
  obtain ⟨p,hp⟩ := F.choose_owners
  refine ⟨Function.update p i j, ?_, by simp⟩
  intro k
  by_cases hk : k=i
  · subst k; simpa using hj
  · simpa [Function.update_of_ne hk] using hp k

def collapseOwner (i : Vertex) (j : Fin 4) : Fin 4 :=
  if i ∈ zeroEdges then 0 else if i ∈ otherQuarterEdges then (if j<2 then 0 else 2) else j

theorem collapsed_projection {q : ℝ} {C : BoundaryCycle q} (hc : TangentCuts C)
    (i : Vertex) (j : Fin 4) (t : ℝ)
    (hz : i ∈ zeroEdges → j ∈ zeroOwners) :
    actualProjection C i (collapseOwner i j) (nominalPhase t i) =
      actualProjection C i j (nominalPhase t i) := by
  have hs := hc.signed_coordinates
  fin_cases i <;> fin_cases j <;>
    norm_num [zeroEdges, zeroOwners] at hz <;>
    simp only [actualProjection, projection, sinusoid, projectionCoefficients, Nat.succ_eq_add_one,
      Nat.reduceAdd, Fin.zero_eta, Fin.isValue, hs, neg_mul, collapseOwner, zeroEdges,
      Finset.mem_insert, Fin.reduceEq, Finset.mem_singleton, or_self, or_false, ↓reduceIte,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      nominalPhase, Real.sin_zero, mul_zero, add_zero, Matrix.cons_val, Real.cos_zero, mul_one,
      Fin.reduceFinMk, Fin.mk_one, one_ne_zero, otherQuarterEdges, G, or_true, Fin.reduceLT,
      Real.sin_pi_div_two, Real.cos_pi_div_two, lt_self_iff_false] <;> ring

end SquaresInCircles.Eight.Candidate
