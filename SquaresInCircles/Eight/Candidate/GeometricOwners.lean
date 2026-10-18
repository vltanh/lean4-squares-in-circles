module

public import SquaresInCircles.Eight.Candidate.Nominal

/-!
# Eight squares: projection estimates and the nonpositive tilt

On an aligned edge, the projection of a separating axis at the nominal angle is at least
`1 - (3/2) ε` at mismatch `ε`, with first- and second-order forms in the frame difference
(`aligned_coarse_projection`, `aligned_first_order_projection`,
`aligned_second_order_projection`); on the mixed edges it is compared with the nominal threshold
(`mixed_G_projection`, `mixed_E_projection`, `mixed_E_second_order`). With the terminal owners
every edge has the projection of its nominal owner (`terminal_nominal_projection`).

These seven inequalities exclude the whole nonpositive half-angle chart `-3/8 ≤ z ≤ 0` at
mismatch at most `1/1000` (`negative_tilt_excluded`). Weighted by
`(ω, ω, α, ω, ω, ε, ε) = (1271/1728, 1271/1728, 31/72, 1271/1728, 1271/1728, 41/48, 41/48)`,
their sum cancels the transverse coordinates of `G` and `T`. Completing the square in the four
circles of `A`, `B`, `D`, `H`, with weights `31/144, 31/144, 41/144, 41/144` taken from the aligned
configuration whose four far corners have squared norm `2257/576`, gives
`2257/576 + (451/4608)(-sin t) - (3001/1000)(41/48) S ≤ q` (`negative_tilt_quantitative`), which
exceeds `Q0` by at least `34477/144000000`. The aligned errors are charged once, through their
shared sum `S`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate
open _root_.SquaresInCircles.Eight.Candidate.Dual

/-- The phase of a charged edge is its nominal phase plus its own difference. -/
theorem GeometricOwners.phase_charged {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    {i : Vertex} (hi : i ∈ charged) :
    phi F.theta i = nominalPhase (tilt F.theta) i + delta F.theta i := by
  have h := phase_decomposition F i
  rwa [ite_eq_left hi] at h

theorem GeometricOwners.phase_G {q : ℝ} {C : BoundaryCycle q} (F : Frame C) :
    phi F.theta G = nominalPhase (tilt F.theta) G := by
  have h := phase_decomposition F G
  have hG : G ∉ charged := by decide
  rwa [ite_eq_right hG, ite_eq_left rfl, add_zero] at h

theorem GeometricOwners.phase_E {q : ℝ} {C : BoundaryCycle q} (F : Frame C) :
    phi F.theta E = nominalPhase (tilt F.theta) E + -totalSignedError F.theta := by
  have h := phase_decomposition F E
  have hE : E ∉ charged := by decide
  have hEG : E ≠ G := by decide
  rwa [ite_eq_right hE, ite_eq_right hEG] at h

theorem GeometricOwners.nominal_E (t : ℝ) : nominalPhase t E = Real.pi / 2 + t := by
  have h1 : E ∉ zeroEdges := by decide
  have h2 : E ∉ otherQuarterEdges := by decide
  have h3 : E ≠ G := by decide
  simp only [nominalPhase, h1, h2, h3, ite_false]

theorem pairWidth_half_pi_add (t : ℝ) : pairWidth (Real.pi/2+t)=pairWidth t := by
  simp only [pairWidth, Real.sin_add, Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two,
    one_mul, zero_mul, add_zero, zero_sub, abs_neg]
  ring

theorem aligned_width {q : ℝ} {C : BoundaryCycle q} (F : Frame C) {i : Vertex}
    (hi : i ∈ charged) :
    pairWidth (nominalPhase (tilt F.theta) i)=1 ∧
      pairWidth (phi F.theta i)=pairWidth (delta F.theta i) := by
  have h0 : pairWidth 0 = 1 := by norm_num [pairWidth]
  have h1 : pairWidth (Real.pi/2) = 1 := by norm_num [pairWidth]
  fin_cases i <;> norm_num [charged] at hi <;>
    simp [nominalPhase, zeroEdges, otherQuarterEdges, phi, word,
      pairWidth_half_pi_add, h0, h1]

theorem aligned_coarse_projection {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) {i : Vertex} (hi : i ∈ charged) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i)))
    {ε : ℝ} (hS : mismatch F.theta ≤ ε) :
    1-(3/2)*ε ≤ actualProjection C i j (nominalPhase (tilt F.theta) i) := by
  have hp := actualProjection_feasible F i j hj
  have hw := width_one_le (phi F.theta i)
  have hd := (delta_le_mismatch F.theta hi).trans hS
  have hl := actualProjection_lipschitz C hq i j
    (phi F.theta i) (nominalPhase (tilt F.theta) i)
  have hdiff : phi F.theta i - nominalPhase (tilt F.theta) i = delta F.theta i := by
    rw [GeometricOwners.phase_charged F hi, add_sub_cancel_left]
  rw [hdiff] at hl
  have hh := (abs_le.mp hl).2
  linarith

theorem aligned_first_order_projection {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) {i : Vertex} (hi : i ∈ charged) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i)))
    (hS : mismatch F.theta ≤ 1/500) :
    1-(1001/1000)*|delta F.theta i| ≤
      actualProjection C i j (nominalPhase (tilt F.theta) i) := by
  have hd := (delta_le_mismatch F.theta hi).trans hS
  have hp := actualProjection_feasible F i j hj
  rw [(aligned_width F hi).2] at hp
  have hw := width_cusp_lower hd
  have hl := actualProjection_lipschitz C hq i j
    (phi F.theta i) (nominalPhase (tilt F.theta) i)
  have hdiff : phi F.theta i - nominalPhase (tilt F.theta) i = delta F.theta i := by
    rw [GeometricOwners.phase_charged F hi, add_sub_cancel_left]
  rw [hdiff] at hl
  have hh := (abs_le.mp hl).2
  have h₂ := mul_le_mul_of_nonneg_right hd (abs_nonneg (delta F.theta i))
  have h₃ := mul_le_mul_of_nonneg_right h₂ (abs_nonneg (delta F.theta i))
  have h₄ := mul_le_mul_of_nonneg_left h₂ (show (0:ℝ) ≤ 1/500 by norm_num)
  nlinarith [sq_abs (delta F.theta i)]

theorem aligned_second_order_projection {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) {i : Vertex} (hi : i ∈ charged) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i)))
    (hS : mismatch F.theta ≤ 1/500) :
    |delta F.theta i|/2 -
      actualDerivative C i j (nominalPhase (tilt F.theta) i)*delta F.theta i -
      (1001/1000)*(delta F.theta i)^2 ≤
    actualProjection C i j (nominalPhase (tilt F.theta) i)-1 := by
  have hd := (delta_le_mismatch F.theta hi).trans hS
  have hp := actualProjection_feasible F i j hj
  rw [(aligned_width F hi).2] at hp
  have hw := width_cusp_lower hd
  have hT := (actualProjection_taylor C hq i j
    (nominalPhase (tilt F.theta) i) (delta F.theta i)).2
  rw [← GeometricOwners.phase_charged F hi] at hT
  have h₃ := mul_le_mul_of_nonneg_right hd (sq_nonneg (delta F.theta i))
  nlinarith [sq_abs (delta F.theta i)]

theorem mixed_G_projection {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square G) (C.square (next G))) :
    pairWidth (nominalPhase (tilt F.theta) G) ≤
      actualProjection C G j (nominalPhase (tilt F.theta) G) := by
  have he := GeometricOwners.phase_G F
  rw [← he]
  exact actualProjection_feasible F G j hj

theorem mixed_E_projection {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square E) (C.square (next E)))
    {ε : ℝ} (hε : ε ≤ 3/200) (hS : mismatch F.theta ≤ ε) :
    pairWidth (nominalPhase (tilt F.theta) E)-2*ε ≤
      actualProjection C E j (nominalPhase (tilt F.theta) E) := by
  have hδ := (totalSignedError_abs F.theta).trans hS
  have ht := F.tilt_small
  have he := GeometricOwners.phase_E F
  have hn := GeometricOwners.nominal_E (tilt F.theta)
  have hp := actualProjection_feasible F E j hj
  have hl := actualProjection_lipschitz C hq E j
    (phi F.theta E) (nominalPhase (tilt F.theta) E)
  have hw := width_lipschitz_small
    (x := tilt F.theta-totalSignedError F.theta) (y := tilt F.theta)
    (by have hh := abs_sub (tilt F.theta) (totalSignedError F.theta); linarith [abs_lt.mp ht])
    (by linarith)
  have hw' : pairWidth (tilt F.theta) - |totalSignedError F.theta|/2 ≤
      pairWidth (tilt F.theta-totalSignedError F.theta) := by
    have hh := (abs_le.mp hw).1
    simp only [sub_sub_cancel_left,abs_neg] at hh
    linarith
  have hdiff : phi F.theta E - nominalPhase (tilt F.theta) E = -totalSignedError F.theta := by
    rw [he, add_sub_cancel_left]
  rw [hdiff, abs_neg] at hl
  have hh := (abs_le.mp hl).2
  have hpw : pairWidth (phi F.theta E) = pairWidth (tilt F.theta-totalSignedError F.theta) := by
    rw [he, hn, show Real.pi/2+tilt F.theta+ -totalSignedError F.theta =
      Real.pi/2+(tilt F.theta-totalSignedError F.theta) by ring, pairWidth_half_pi_add]
  have hnw : pairWidth (nominalPhase (tilt F.theta) E) = pairWidth (tilt F.theta) := by
    rw [hn, pairWidth_half_pi_add]
  rw [hpw] at hp
  rw [hnw]
  linarith

theorem mixed_E_second_order {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square E) (C.square (next E)))
    (hS : mismatch F.theta ≤ 1/1000) {positive : Bool}
    (hsign : if positive then 0 ≤ tilt F.theta else tilt F.theta ≤ 0) :
    (actualDerivative C E j (nominalPhase (tilt F.theta) E)-widthSlope positive (tilt F.theta))*
        totalSignedError F.theta - (9/8)*(totalSignedError F.theta)^2 ≤
      actualProjection C E j (nominalPhase (tilt F.theta) E)-
        pairWidth (nominalPhase (tilt F.theta) E) := by
  have hδ := (totalSignedError_abs F.theta).trans hS
  have he := GeometricOwners.phase_E F
  have hp := actualProjection_feasible F E j hj
  have hT := (actualProjection_taylor C hq E j
    (nominalPhase (tilt F.theta) E) (-totalSignedError F.theta)).2
  rw [← he] at hT
  have hw := width_semiconvex F.tilt_small.le
    (v := -totalSignedError F.theta) (by rw [abs_neg]; linarith) hsign
  have hn := GeometricOwners.nominal_E (tilt F.theta)
  have hpw : pairWidth (phi F.theta E) = pairWidth (tilt F.theta+ -totalSignedError F.theta) := by
    rw [he, hn, show (Real.pi/2+tilt F.theta)+ -totalSignedError F.theta =
      Real.pi/2+(tilt F.theta+ -totalSignedError F.theta) by ring, pairWidth_half_pi_add]
  have hnw : pairWidth (nominalPhase (tilt F.theta) E) = pairWidth (tilt F.theta) := by
    rw [hn, pairWidth_half_pi_add]
  rw [hpw] at hp
  rw [hnw]
  nlinarith

theorem terminal_nominal_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (ho : OwnerRestriction C terminalOwners)
    (p : Vertex → Fin 4) (hp : FeasibleOwners C p) (t : ℝ) (i : Vertex) :
    actualProjection C i (nominalOwner i) (nominalPhase t i) =
      actualProjection C i (p i) (nominalPhase t i) := by
  have hi := ho i (p i) (hp i)
  have hz : i ∈ zeroEdges → p i ∈ zeroOwners := by
    intro hz
    revert hi hz
    generalize p i = a
    fin_cases i <;> fin_cases a <;> decide
  rw [← collapsed_projection hc i (p i) t hz]
  congr 1
  revert hi
  generalize p i = a
  fin_cases i <;> fin_cases a <;> decide

/-- The two transverse coordinates cancel in a fixed weighted sum. The identity holds at every tilt.
-/
theorem intended_projection_formula {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) (i : Vertex) :
    actualProjection C i (nominalOwner i) (nominalPhase t i) =
      ![C.b H + C.b G,
        -C.b G + C.a A * Real.cos t - C.b A * Real.sin t,
        C.b A + C.b B,
        C.a B - C.b T,
        C.b T + C.b D,
        C.a D + C.b E,
        C.a H + C.a E * Real.sin t - C.b E * Real.cos t] i := by
  have hs := hc.signed_coordinates
  fin_cases i <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalOwner, nominalPhase, zeroEdges, otherQuarterEdges, next,
      H, G, A, B, T, D, E, hs, Dual.signs,
      Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub] <;> ring

namespace AlignedStress

/-- Weights from the rational configuration at zero tilt. Unnormalized they are `24/41`, `1` and
`36/31`, with circle-weight mass `1728/1271`. -/
def alpha : ℝ := 31 / 72
def omega : ℝ := 1271 / 1728
def epsilon : ℝ := 41 / 48

def force (a b : Vertex → ℝ) (r c : ℝ) : ℝ :=
  omega * c * a A + (alpha + omega * r) * b A +
  omega * a B + alpha * b B +
  epsilon * a D + omega * b D +
  epsilon * a H + omega * b H +
  epsilon * (-a E * r + b E * (1 - c))

def demand (r c : ℝ) : ℝ :=
  3 * omega + alpha + epsilon + (omega + epsilon) * ((1 + c + r) / 2)

def edgeWeight : Vertex → ℝ :=
  ![omega, omega, alpha, omega, omega, epsilon, epsilon]

/-- One identity on the whole negative half-chart. The four completed circles have weights `31/144,
31/144, 41/144, 41/144`, summing to one. The force of `E` is bounded by its quadrant and needs no
circle weight. -/
theorem four_circle_bound (a b : Vertex → ℝ) {q r c loss : ℝ}
    (hcircle : ∀ i, (a i + 1/2)^2 + (b i + 1/2)^2 ≤ q)
    (hEa : 1/2 ≤ a E) (hEb : b E ≤ 1)
    (hr : 0 ≤ r) (hc : c ≤ 1) (hunit : c^2 + r^2 = 1)
    (hchord : 1-c ≤ (3/8)*r)
    (hforce : demand r c-loss ≤ force a b r c) :
    2257/576 + (451/4608)*r-loss ≤ q := by
  have hA := circle_linear_upper (a := a A) (b := b A)
    (C := omega*c) (D := alpha+omega*r) (μ := 31/144)
    (by norm_num) (hcircle A)
  have hB := circle_linear_upper (a := a B) (b := b B)
    (C := omega) (D := alpha) (μ := 31/144)
    (by norm_num) (hcircle B)
  have hD := circle_linear_upper (a := a D) (b := b D)
    (C := epsilon) (D := omega) (μ := 41/144)
    (by norm_num) (hcircle D)
  have hH := circle_linear_upper (a := a H) (b := b H)
    (C := epsilon) (D := omega) (μ := 41/144)
    (by norm_num) (hcircle H)
  have hEa' := mul_le_mul_of_nonneg_right hEa hr
  have hEb' := mul_le_mul_of_nonneg_right hEb (sub_nonneg.mpr hc)
  dsimp [demand, force, alpha, omega, epsilon] at hforce hA hB hD hH
  norm_num at hA hB hD hH
  /- After adding the four circle inequalities, the exact remainder is
     2257/576 + epsilon*r - (omega+3*epsilon/2)*(1-c) - loss.
     The chord inequality leaves (451/4608)*r. -/
  nlinarith

theorem shared_loss (θ : Vertex → ℝ) :
    (∑ j : Fin 5, edgeWeight (alignedEdge j) * |delta θ (alignedEdge j)|) ≤
      epsilon * mismatch θ := by
  apply weighted_total_error
  · norm_num [epsilon]
  · intro j
    fin_cases j <;> norm_num [edgeWeight, alignedEdge, alpha, omega, epsilon]
  · simp [mismatch, charged, alignedEdge, Fin.sum_univ_succ]

end AlignedStress

/-- Half-angle geometry, including both endpoints and `z = 0`. The chord identity is `1 - cos t =
(-z)(-sin t)`. -/
theorem negative_half_angle_geometry {z t : ℝ}
    (hz : -(3/8 : ℝ) ≤ z ∧ z ≤ 0) (ht : t=2*Real.arctan z) :
    0 ≤ -Real.sin t ∧ 0 ≤ Real.cos t ∧
      1-Real.cos t ≤ (3/8)*(-Real.sin t) := by
  have hid := half_angle_identities z
  have hd : 0 < 1+z^2 := by positivity
  have hs : Real.sin t ≤ 0 := by
    rw [ht, hid.1]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  have hc : 0 ≤ Real.cos t := by
    rw [ht, hid.2]
    apply div_nonneg _ hd.le
    nlinarith [hz.1, hz.2]
  have hchord : 1-Real.cos t = (-z)*(-Real.sin t) := by
    rw [ht, hid.1, hid.2]
    field_simp [ne_of_gt hd]
    ring
  refine ⟨neg_nonneg.mpr hs, hc, ?_⟩
  rw [hchord]
  exact mul_le_mul_of_nonneg_right (by linarith [hz.1]) (neg_nonneg.mpr hs)

/-- The seven separating-axis inequalities enter one geometric stress. The owners are arbitrary and
may tie. The aligned loss is charged once, through the shared sum of absolute errors. -/
theorem negative_tilt_quantitative {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C)
    (ho : OwnerRestriction C terminalOwners)
    (hS : mismatch F.theta ≤ 1/1000) {z : ℝ}
    (hz : -(3/8 : ℝ) ≤ z ∧ z ≤ 0)
    (ht : tilt F.theta=2*Real.arctan z) :
    2257/576 + (451/4608)*(-Real.sin (tilt F.theta)) -
      ((3001/1000)*(41/48))*mismatch F.theta ≤ q := by
  obtain ⟨p,hp⟩ := F.choose_owners
  have hn := terminal_nominal_projection hc ho p hp (tilt F.theta)
  have hgeom := negative_half_angle_geometry hz ht
  have hsin : Real.sin (tilt F.theta) ≤ 0 := by linarith [hgeom.1]
  have hw : pairWidth (nominalPhase (tilt F.theta) G) =
      (1+Real.cos (tilt F.theta)-Real.sin (tilt F.theta))/2 := by
    simp [nominalPhase, G, zeroEdges, otherQuarterEdges, pairWidth,
      Real.sin_sub, Real.cos_sub, abs_of_nonneg hgeom.2.1, abs_of_nonpos hsin]
    ring
  have hwE : pairWidth (nominalPhase (tilt F.theta) E) =
      (1+Real.cos (tilt F.theta)-Real.sin (tilt F.theta))/2 := by
    simp [nominalPhase, E, G, zeroEdges, otherQuarterEdges, pairWidth,
      Real.sin_add, Real.cos_add, abs_of_nonneg hgeom.2.1, abs_of_nonpos hsin]
    ring
  have hproj (i : Vertex) (hi : i ∈ charged) :
      1-(1001/1000)*|delta F.theta i| ≤
        actualProjection C i (nominalOwner i) (nominalPhase (tilt F.theta) i) := by
    rw [hn i]
    exact aligned_first_order_projection F hq hi (p i) (hp i) (by linarith)
  have h0 := hproj H (by norm_num [H, charged])
  have h2 := hproj A (by norm_num [A, charged])
  have h3 := hproj B (by norm_num [B, charged])
  have h4 := hproj T (by norm_num [T, charged])
  have h5 := hproj D (by norm_num [D, charged])
  have hG := mixed_G_projection F (p G) (hp G)
  have hE := mixed_E_projection F hq (p E) (hp E)
    (ε := mismatch F.theta) (by linarith) le_rfl
  rw [← hn G, hw] at hG
  rw [← hn E, hwE] at hE
  rw [intended_projection_formula hc] at h0 h2 h3 h4 h5 hG hE
  norm_num [H, G, A, B, T, D, E] at h0 h2 h3 h4 h5 hG hE
  have hweight := AlignedStress.shared_loss F.theta
  simp only [AlignedStress.edgeWeight, alignedEdge, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ] at hweight
  have hforce : AlignedStress.demand (-Real.sin (tilt F.theta))
        (Real.cos (tilt F.theta)) -
        ((3001/1000)*(41/48))*mismatch F.theta ≤
      AlignedStress.force C.a C.b (-Real.sin (tilt F.theta))
        (Real.cos (tilt F.theta)) := by
    dsimp [AlignedStress.demand, AlignedStress.force, AlignedStress.alpha,
      AlignedStress.omega, AlignedStress.epsilon]
    dsimp [AlignedStress.alpha, AlignedStress.omega, AlignedStress.epsilon] at hweight
    simp only [H, A, B, D, E]
    nlinarith
  have hb := canonical_bounds C hq E
  exact AlignedStress.four_circle_bound C.a C.b
    (fun i => canonical_containment C i)
    (by linarith [hb.1]) (by linarith [hb.2.2.2])
    hgeom.1 (Real.cos_le_one _) (by nlinarith [Real.sin_sq_add_cos_sq (tilt F.theta)])
    hgeom.2.2 hforce

/-- The whole nonpositive half-angle chart is excluded, including `z = 0` and both endpoints:
the bound of `negative_tilt_quantitative` exceeds `Q0` by at least `34477/144000000`. -/
theorem negative_tilt_excluded {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C)
    (ho : OwnerRestriction C terminalOwners)
    (hS : mismatch F.theta ≤ 1/1000) {z : ℝ}
    (hz : -(3/8 : ℝ) ≤ z ∧ z ≤ 0)
    (ht : tilt F.theta=2*Real.arctan z) : False := by
  have hbound := negative_tilt_quantitative F hq hc ho hS hz ht
  have hr := (negative_half_angle_geometry hz ht).1
  norm_num [Q0] at hq
  nlinarith

end SquaresInCircles.Eight.Candidate
