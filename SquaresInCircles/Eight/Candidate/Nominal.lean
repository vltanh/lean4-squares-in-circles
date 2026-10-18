module

public import SquaresInCircles.Eight.Candidate.Projection

/-! The exact nominal-angle map, common cone inequalities, and the connection
between the original signed SAT projections and the rational dual forces. -/

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
  · simp [hs]
  · have hb := C.b_nonneg i
    simp [hs] at hp
    linarith

theorem nonpositive_tangent_coordinate {q : ℝ} (C : BoundaryCycle q) {i : Vertex}
    (ht : C.tangent i ≤ 0) : C.sigma i * C.b i = -C.b i := by
  have hp := mul_nonpos_of_nonpos_of_nonneg ht (C.a_pos i).le
  rw [tangent_mul] at hp
  rcases C.sigma_sign i with hs | hs
  · have hb := C.b_nonneg i
    simp [hs] at hp
    have he : C.b i=0 := le_antisymm hp hb
    simp [he]
  · simp [hs]

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
    have hbb : b < 1/2 := by linarith [hcone.2]
    rw [max_eq_left (by linarith : 0 ≤ a-1/2), max_eq_right (by linarith : b-1/2 ≤ 0)] at hcore
    nlinarith
  · by_contra! hn
    have hbl : 349/5000 < b := by linarith [hcone.1]
    have hs₁ : (349/250+1/2:ℝ)^2 < (a+1/2)^2 :=
      sq_lt_sq₀ (by norm_num) (by linarith) (by linarith)
    have hs₂ : (349/5000+1/2:ℝ)^2 < (b+1/2)^2 :=
      sq_lt_sq₀ (by norm_num) (by linarith) (by linarith)
    dsimp [Q0] at hq
    norm_num at hs₁ hs₂
    linarith

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
    constructor <;> linarith
  have hTratio : C.a T/20 ≤ C.b T ∧ C.b T ≤ (4/5)*C.a T := by
    have h₁ := mul_lt_mul_of_pos_right ht.1 (C.a_pos T)
    have h₂ := mul_lt_mul_of_pos_right ht.2 (C.a_pos T)
    rw [tangent_mul] at h₁ h₂
    rw [hs] at h₁ h₂
    norm_num [Dual.signs,T] at h₁ h₂
    constructor <;> linarith
  have hHr : (1/2)*C.a H ≤ C.b H := by
    have hh := mul_lt_mul_of_pos_right hhd.1 (C.a_pos H)
    rw [tangent_mul, hs] at hh
    norm_num [Dual.signs,H] at hh
    linarith
  have hDr : (1/2)*C.a D ≤ C.b D := by
    have hh := mul_lt_mul_of_pos_right hhd.2 (C.a_pos D)
    rw [tangent_mul, hs] at hh
    norm_num [Dual.signs,D] at hh
    linarith
  have hG := slider_primary_bounds
    (a := C.a G) (b := C.b G) (q := q)
    (by have hh := (canonical_bounds C hq G).1; linarith) (C.b_nonneg G)
    hGratio (canonical_core_distance C G) (canonical_containment C G) hq
  have hT := slider_primary_bounds
    (a := C.a T) (b := C.b T) (q := q)
    (by have hh := (canonical_bounds C hq T).1; linarith) (C.b_nonneg T)
    hTratio (canonical_core_distance C T) (canonical_containment C T) hq
  intro i
  have hb := canonical_bounds C hq i
  have hba := C.b_le_a i
  fin_cases i <;>
    simp [lowerPrimary, upperPrimary, lowerRatio, upperRatio, H, G, A, B, T, D, E] at * <;>
    constructor <;> try constructor <;> try constructor <;> try constructor <;> linarith

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
    simp [phi, nominalPhase, tilt, totalSignedError, charged, zeroEdges,
      otherQuarterEdges, word, alignedEdge, delta, next, H, G, A, B, T, D, E,
      Fin.sum_univ_succ] at hA ⊢ <;> linarith

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
  simpa [margin] using le_add_of_nonneg_left hm

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
  exact sinusoid_taylor (by norm_num) (projection_amplitude C hq i j) _ x d

theorem actualDerivative_abs {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0)
    (i : Vertex) (j : Fin 4) (x : ℝ) : |actualDerivative C i j x| ≤ 3/2 :=
  sinusoid_derivative_bound (by norm_num) (projection_amplitude C hq i j) x

theorem nominal_projection_identity {q : ℝ} {C : BoundaryCycle q} (hc : TangentCuts C)
    (z : ℝ) (i : Vertex) (j : Fin 4) :
    projectionNumerator C.a C.b z i j / peval Dpoly z =
      actualProjection C i j (nominalPhase (2*Real.arctan z) i) := by
  have hid := half_angle_identities z
  have hd := D_positive z
  have hs := hc.signed_coordinates
  fin_cases i <;> fin_cases j <;>
    simp [projectionNumerator, nominalA, nominalB, coefficient, sinNumerator,
      cosNumerator, zeroEdges, otherQuarterEdges, signs, next, peval,
      Dpoly, Cpoly, Spoly, nominalPhase, actualProjection, projection,
      projectionCoefficients, sinusoid, G, Real.sin_sub, Real.cos_sub,
      Real.sin_add, Real.cos_add, Fin.sum_univ_succ, hid.1, hid.2, hs] <;>
    field_simp [ne_of_gt hd, show (1+z^2:ℝ)≠0 by positivity] <;> ring

theorem nominal_derivative_identity {q : ℝ} {C : BoundaryCycle q} (hc : TangentCuts C)
    (z : ℝ) (i : Vertex) (j : Fin 4) :
    derivativeNumerator C.a C.b z i j / peval Dpoly z =
      actualDerivative C i j (nominalPhase (2*Real.arctan z) i) := by
  have hid := half_angle_identities z
  have hd := D_positive z
  have hs := hc.signed_coordinates
  fin_cases i <;> fin_cases j <;>
    simp [derivativeNumerator, derivativeA, derivativeB, coefficient, sinNumerator,
      cosNumerator, zeroEdges, otherQuarterEdges, signs, next, peval,
      Dpoly, Cpoly, Spoly, nominalPhase, actualDerivative, projectionDeriv,
      projectionCoefficients, sinusoidDeriv, G, Real.sin_sub, Real.cos_sub,
      Real.sin_add, Real.cos_add, Fin.sum_univ_succ, hid.1, hid.2, hs] <;>
    field_simp [ne_of_gt hd, show (1+z^2:ℝ)≠0 by positivity] <;> ring

theorem nominal_width_identity {z : ℝ} {positive : Bool}
    (hz : |z| ≤ 3/8) (hsign : if positive then 0 ≤ z else z ≤ 0) (i : Vertex) :
    peval (edgeWidth positive i) z / peval Dpoly z =
      pairWidth (nominalPhase (2*Real.arctan z) i) := by
  have hid := half_angle_identities z
  have hd := D_positive z
  have hnum : 0 ≤ 1-z^2 := by have hh := abs_le.mp hz; nlinarith
  have hc : 0 ≤ Real.cos (2*Real.arctan z) := by rw [hid.2]; positivity
  have hs : if positive then 0 ≤ Real.sin (2*Real.arctan z)
      else Real.sin (2*Real.arctan z) ≤ 0 := by
    cases positive <;> simp at hsign ⊢ <;> rw [hid.1]
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    · positivity
  fin_cases i <;> cases positive <;>
    simp [edgeWidth, widthNumerator, nominalPhase, pairWidth, mixedEdges,
      zeroEdges, otherQuarterEdges, G, peval, Dpoly, Cpoly, Spoly,
      signValue, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub,
      abs_of_nonneg hc, abs_of_nonneg, abs_of_nonpos, hs, hid.1, hid.2] <;>
    field_simp [show (1+z^2:ℝ)≠0 by positivity] <;> ring

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
    simp [collapseOwner, zeroEdges, otherQuarterEdges, nominalPhase, actualProjection,
      projection, projectionCoefficients, sinusoid, hs, G] <;> ring

end SquaresInCircles.Eight.Candidate
