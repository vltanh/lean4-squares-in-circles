module

public import SquaresInCircles.Eight.Candidate.GeometricOwnersForbiddenB
public import SquaresInCircles.Eight.Generated.OwnerCompleteness

/-!
# Eight squares: owners and tilt from the circle duals

The quartic rows of `Candidate/Dual.lean` are applied to boundary cycles with a candidate frame.
The projection estimates of `Candidate/GeometricOwners.lean` turn the separations of a cycle into
the necessary inequality of a row (`Dual.Row.original_of_continuous`).

At mismatch at most `3/200` every axis that separates `B → T` or `D → E` is the forward axis `2`
or `3` (`quarter_owners`): the axis of `D` by `D_quarter_owners`, and a forbidden axis of `B` by
the geometric exclusions of `G`-axes `2` and `3` and by the quarter tables of `G`-axes `0` and `1`.
At mismatch at most `1/1000` every separating axis lies in the terminal owner set of its edge
(`mixed_owners`). Each separating axis is treated on its own, so an excluded axis is excluded
whichever witness was chosen. The nonpositive half-angle chart is excluded by
`negative_tilt_excluded`, and the tilt bundles exclude the positive half-angle tangents outside
`(1001/20000, 2/25)`, which gives `1/10 < t < 4/25` for the tilt (`tilt_window`); in each bundle
the weights are fixed on its closed interval before an error alternative is chosen.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate
open Dual

private theorem DualApplication.peval_add (p q : Poly) (z : ℝ) :
    peval (p + q) z = peval p z + peval q z := by
  simp [peval]

private theorem DualApplication.peval_sub (p q : Poly) (z : ℝ) :
    peval (p - q) z = peval p z - peval q z := by
  simp [peval]

private theorem DualApplication.peval_mul (p q : Poly) (z : ℝ) :
    peval (p * q) z = peval p z * peval q z := by
  simp [peval]

private theorem DualApplication.peval_neg (p : Poly) (z : ℝ) : peval (-p) z = -peval p z := by
  simp [peval]

private theorem DualApplication.peval_C (c : ℚ) (z : ℝ) : peval (Polynomial.C c) z = (c : ℝ) := by
  simp [peval]

private theorem DualApplication.peval_zero (z : ℝ) : peval 0 z = 0 := by
  simp [peval]

def weightedSlack {q : ℝ} (C : BoundaryCycle q) (t : ℝ)
    (p : Vertex → Fin 4) (lam : Vertex → ℚ) : ℝ :=
  ∑ i, (lam i : ℝ) * (actualProjection C i (p i) (nominalPhase t i)-pairWidth (nominalPhase t i))

def errorCoefficient {q : ℝ} (C : BoundaryCycle q) (t : ℝ) (positive : Bool)
    (lam : Vertex → ℚ) (i : Vertex) (j : Fin 4) : ℝ :=
  (lam i : ℝ)*actualDerivative C i j (nominalPhase t i) -
    (lam E : ℝ)*actualDerivative C E 1 (nominalPhase t E) +
    (lam E : ℝ)*widthSlope positive t

def Dual.Row.continuousNecessary {q : ℝ} (r : Row) (C : BoundaryCycle q) (t : ℝ) : Prop :=
  match r.alternative with
  | .zero => 0 ≤ weightedSlack C t r.owners r.lambda + (r.loss : ℝ)
  | .spike i second positive =>
    0 ≤ weightedSlack C t r.owners r.lambda + (r.loss : ℝ) + (r.epsilon : ℝ)*
      ((signValue positive : ℝ)*errorCoefficient C t r.positive r.lambda (alignedEdge i)
        (Alternative.owner i second) - (r.lambda (alignedEdge i) : ℝ)/2)

theorem Dual.Row.sign_at {r : Row} (hr : r.Valid) {z : ℝ} (hz : r.interval.Mem z) :
    if r.positive then 0 ≤ z else z ≤ 0 := by
  cases hp : r.positive
  · have hs : (r.interval.hi : ℝ) ≤ 0 := by exact_mod_cast (by simpa [hp] using hr.interval_sign)
    simpa [hp] using hz.2.trans hs
  · have hs : (0 : ℝ) ≤ r.interval.lo := by exact_mod_cast (by simpa [hp] using hr.interval_sign)
    simpa [hp] using hs.trans hz.1

theorem Dual.Row.phase_sign {r : Row} (hr : r.Valid) {z t : ℝ} (hz : r.interval.Mem z)
    (ht : t=2*Real.arctan z) : if r.positive then 0 ≤ t else t ≤ 0 := by
  have hs := Dual.Row.sign_at hr hz
  cases hp : r.positive <;> simp [hp] at hs ⊢
  · have hh := Real.arctan_strictMono.monotone hs
    rw [Real.arctan_zero] at hh
    rw [ht]
    linarith
  · have hh := Real.arctan_strictMono.monotone hs
    rw [Real.arctan_zero] at hh
    rw [ht]
    linarith

theorem Dual.Row.original_of_continuous {q : ℝ} {C : BoundaryCycle q} (hc : TangentCuts C)
    {r : Row} (hr : r.Valid) {z t : ℝ} (hz : r.interval.Mem z)
    (hchart : |z| ≤ 3/8) (ht : t=2*Real.arctan z)
    (hnecessary : r.continuousNecessary C t) : r.originalNecessary C.a C.b z := by
  have hd := D_positive z
  have hp := nominal_projection_identity hc z
  have hdp := nominal_derivative_identity hc z
  have hw := nominal_width_identity hchart (Dual.Row.sign_at hr hz)
  have hwp := nominal_width_derivative_identity (z := z) (positive := r.positive)
  have hp' (i : Vertex) (j : Fin 4) : projectionNumerator C.a C.b z i j =
      peval Dpoly z * actualProjection C i j (nominalPhase t i) := by
    rw [ht]
    exact (div_eq_iff (ne_of_gt hd)).1 (hp i j) |>.trans (mul_comm _ _)
  have hdp' (i : Vertex) (j : Fin 4) : derivativeNumerator C.a C.b z i j =
      peval Dpoly z * actualDerivative C i j (nominalPhase t i) := by
    rw [ht]
    exact (div_eq_iff (ne_of_gt hd)).1 (hdp i j) |>.trans (mul_comm _ _)
  have hw' (i : Vertex) : peval (edgeWidth r.positive i) z =
      peval Dpoly z * pairWidth (nominalPhase t i) := by
    rw [ht]
    exact (div_eq_iff (ne_of_gt hd)).1 (hw i) |>.trans (mul_comm _ _)
  have hwp' : peval (lastWidthDerivative r.positive) z = peval Dpoly z * widthSlope r.positive t := by
    rw [ht]
    exact (div_eq_iff (ne_of_gt hd)).1 hwp |>.trans (mul_comm _ _)
  -- the nominal part of the necessary inequality is the weighted slack, times `1 + z ^ 2`
  have hslack : (∑ i, (r.lambda i : ℝ) * projectionNumerator C.a C.b z i (r.owners i)) -
      (∑ i, (r.lambda i : ℝ) * peval (edgeWidth r.positive i) z) =
      peval Dpoly z * weightedSlack C t r.owners r.lambda := by
    rw [weightedSlack, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hp', hw']
    ring
  unfold Dual.Row.originalNecessary
  unfold Dual.Row.continuousNecessary at hnecessary
  cases ha : r.alternative with
  | zero =>
    simp only [ha] at hnecessary
    have hA : ∀ i, r.errorA i = 0 := fun i => by simp [Row.errorA, ha]
    have hB : ∀ i, r.errorB i = 0 := fun i => by simp [Row.errorB, ha]
    have hR : r.errorRhs = 0 := by simp [Row.errorRhs, ha]
    simp only [hA, hB, hR, DualApplication.peval_zero, zero_mul, add_zero,
      Finset.sum_const_zero]
    have hm := mul_nonneg hd.le hnecessary
    linarith
  | spike j second positive =>
    simp only [ha] at hnecessary
    unfold errorCoefficient at hnecessary
    -- the error part is the signed derivative numerator, times `1 + z ^ 2`
    have hsum : ∀ (c u v : ℝ), (∑ i, ((c * (u * peval (derivativeA (alignedEdge j)
          (Alternative.owner j second) i) z - v * peval (derivativeA E 1 i) z)) * C.a i +
        (c * (u * peval (derivativeB (alignedEdge j) (Alternative.owner j second) i) z -
          v * peval (derivativeB E 1 i) z)) * C.b i)) =
        c * (u * derivativeNumerator C.a C.b z (alignedEdge j) (Alternative.owner j second) -
          v * derivativeNumerator C.a C.b z E 1) := by
      intro c u v
      simp only [derivativeNumerator, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp only [Row.errorA, Row.errorB, Row.errorRhs, ha, DualApplication.peval_add,
      DualApplication.peval_sub, DualApplication.peval_mul, DualApplication.peval_neg,
      DualApplication.peval_C]
    rw [hsum, hdp', hdp', hwp']
    have hm := mul_nonneg hd.le hnecessary
    push_cast at hm ⊢
    linarith

theorem maxLambda_bound (r : Row) (j : Fin 5) : r.lambda (alignedEdge j) ≤ r.maxLambda := by
  have h₀ := le_max_left (r.lambda 0) (max (r.lambda 2) (max (r.lambda 3) (max (r.lambda 4) (r.lambda 5))))
  have h₁ := le_max_right (r.lambda 0) (max (r.lambda 2) (max (r.lambda 3) (max (r.lambda 4) (r.lambda 5))))
  have h₂ := le_max_left (r.lambda 2) (max (r.lambda 3) (max (r.lambda 4) (r.lambda 5)))
  have h₃ := le_max_right (r.lambda 2) (max (r.lambda 3) (max (r.lambda 4) (r.lambda 5)))
  have h₄ := le_max_left (r.lambda 3) (max (r.lambda 4) (r.lambda 5))
  have h₅ := le_max_right (r.lambda 3) (max (r.lambda 4) (r.lambda 5))
  have h₆ := le_max_left (r.lambda 4) (r.lambda 5)
  have h₇ := le_max_right (r.lambda 4) (r.lambda 5)
  fin_cases j <;> simp [alignedEdge,Row.maxLambda] <;> linarith

theorem quarter_continuous_necessary {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (p : Vertex → Fin 4) (hp : FeasibleOwners C p) (hS : mismatch F.theta ≤ 3/200)
    {r : Row} (hr : r.Valid) (hmode : r.mode=.quarter) (halt : r.alternative=.zero)
    (howners : ∀ i, r.owners i=collapseOwner i (p i)) :
    r.continuousNecessary C (tilt F.theta) := by
  have hw (i : Vertex) :
      pairWidth (nominalPhase (tilt F.theta) i) -
        (if i ∈ charged then (3/2)*(3/200) else if i=G then 0 else 2*(3/200)) ≤
      actualProjection C i (r.owners i) (nominalPhase (tilt F.theta) i) := by
    rw [howners,collapsed_projection hc _ _ _ (fun hi => hzero i hi (p i) (hp i))]
    by_cases hi : i ∈ charged
    · rw [if_pos hi,(aligned_width F hi).1]
      exact aligned_coarse_projection F hq hi (p i) (hp i) hS
    · rw [if_neg hi]
      fin_cases i <;> norm_num [charged] at hi <;>
        first | simpa [G] using mixed_G_projection F (p G) (hp G)
              | simpa [G,E] using mixed_E_projection F hq (p E) (hp E) (by norm_num) hS
  have hm := Finset.sum_le_sum (s := (Finset.univ : Finset Vertex))
    (fun i _ => mul_le_mul_of_nonneg_left (hw i)
      (show (0:ℝ) ≤ r.lambda i by exact_mod_cast hr.lambda_nonneg i))
  unfold Row.continuousNecessary
  rw [halt]
  simp [weightedSlack,Row.loss,Row.epsilon,hmode,charged,alignedEdge,G,E,
    Fin.sum_univ_succ] at hm ⊢
  linarith

theorem mixed_continuous_necessary {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (p : Vertex → Fin 4) (hp : FeasibleOwners C p) (hS : mismatch F.theta ≤ 1/1000)
    {r : Row} (hr : r.Valid) (hmode : r.mode=.mixed) (halt : r.alternative=.zero)
    (howners : ∀ i, r.owners i=collapseOwner i (p i)) :
    r.continuousNecessary C (tilt F.theta) := by
  have hw (i : Vertex) :
      pairWidth (nominalPhase (tilt F.theta) i) -
        (if i ∈ charged then (1001/1000)*|delta F.theta i| else if i=G then 0 else 2*(1/1000)) ≤
      actualProjection C i (r.owners i) (nominalPhase (tilt F.theta) i) := by
    rw [howners,collapsed_projection hc _ _ _ (fun hi => hzero i hi (p i) (hp i))]
    by_cases hi : i ∈ charged
    · rw [if_pos hi,(aligned_width F hi).1]
      exact aligned_first_order_projection F hq hi (p i) (hp i) (by linarith)
    · rw [if_neg hi]
      fin_cases i <;> norm_num [charged] at hi <;>
        first | simpa [G] using mixed_G_projection F (p G) (hp G)
              | simpa [G,E] using mixed_E_projection F hq (p E) (hp E) (by norm_num) hS
  have hm := Finset.sum_le_sum (s := (Finset.univ : Finset Vertex))
    (fun i _ => mul_le_mul_of_nonneg_left (hw i)
      (show (0:ℝ) ≤ r.lambda i by exact_mod_cast hr.lambda_nonneg i))
  have hmax : (0:ℝ) ≤ r.maxLambda := by
    exact_mod_cast (hr.lambda_nonneg 0).trans (maxLambda_bound r 0)
  have he := weighted_total_error
    (fun j : Fin 5 => (r.lambda (alignedEdge j) : ℝ))
    (fun j => delta F.theta (alignedEdge j)) hmax
    (fun j => by exact_mod_cast maxLambda_bound r j)
    (by simpa [mismatch,charged,alignedEdge,Fin.sum_univ_succ] using hS)
  unfold Row.continuousNecessary
  rw [halt]
  simp [weightedSlack,Row.loss,Row.epsilon,hmode,charged,alignedEdge,G,E,
    Fin.sum_univ_succ] at hm he ⊢
  linarith

theorem quarter_owners {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200) : QuarterOwners C := by
  intro i hi j hj
  by_contra hbad
  obtain ⟨p,hp,hpi⟩ := F.choose_owners_at i j hj
  have hDgood := D_quarter_owners F hq hc hzero hS (p D) (hp D)
  have hBbad : p B ∉ quarterOwners := by
    intro hB
    have hi' : i=B ∨ i=D := by simpa [otherQuarterEdges, B, D] using hi
    rcases hi' with rfl | rfl
    · exact hbad (hpi ▸ hB)
    · exact hbad (hpi ▸ hDgood)
  have hBsmall : p 3 < 2 := by
    have hh : p 3 ∉ quarterOwners := by simpa [B] using hBbad
    revert hh
    generalize p 3 = a
    fin_cases a <;> decide
  have hGnot : p 1 ≠ 2 := by
    intro heq
    have hGsep : (forwardAxis 2).Feasible (C.square G) (C.square (next G)) := by
      simpa [G, heq] using hp G
    exact G_axis_two_forbidden_quarter_excluded F hq hc hzero hS hBbad (hp B) hGsep
  have hGthree : p 1 ≠ 3 := by
    intro heq
    have hGsep : (forwardAxis 3).Feasible (C.square G) (C.square (next G)) := by
      simpa [G, heq] using hp G
    exact G_axis_three_forbidden_B_excluded F hq hc hzero hS hBbad (hp B) hGsep
  have hGsmall : p 1 < 2 := by
    revert hGnot hGthree
    generalize p 1 = a
    fin_cases a <;> decide
  have hDlarge : ¬p 5 < 2 := by
    have hh : p 5 ∈ quarterOwners := by simpa [D] using hDgood
    revert hh
    generalize p 5 = a
    fin_cases a <;> decide
  let p' : Vertex → Fin 4 := fun k => collapseOwner k (p k)
  have hpattern : Generated.Owner.QuarterPattern p' := by
    simp [Generated.Owner.QuarterPattern, p', collapseOwner,
      zeroEdges, otherQuarterEdges, hBsmall, hDlarge, hGsmall]
  obtain ⟨T,hTm,hTo⟩ := Generated.Owner.quarter_certificate hpattern
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  obtain ⟨r,hrm,hzr⟩ := T.select ⟨hzl.le,hzu.le⟩
  have hr := T.valid r hrm
  have hcont := quarter_continuous_necessary F hq hc hzero p hp hS hr
    ((T.same_mode r hrm).trans hTm) (T.no_error r hrm)
    (fun k => congrFun ((T.same_owners r hrm).trans hTo) k)
  apply hr.excludes_original hzr C.a C.b (hc.cones hq)
  · intro k
    have hh := (canonical_containment C k).trans hq
    simpa [Row.Q,(T.same_mode r hrm).trans hTm,Q0,SquaresInCircles.phi] using hh
  · exact Row.original_of_continuous hc hr hzr (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht hcont

theorem mixed_owners {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hquarter : QuarterOwners C) (hS : mismatch F.theta ≤ 1/1000) :
    OwnerRestriction C terminalOwners := by
  intro i j hj
  by_cases hi0 : i ∈ zeroEdges
  · have hh := hzero i hi0 j hj
    revert hh hi0
    fin_cases i <;> fin_cases j <;> decide
  by_cases hiq : i ∈ otherQuarterEdges
  · have hh := hquarter i hiq j hj
    revert hh hiq
    fin_cases i <;> fin_cases j <;> decide
  by_contra hbad
  obtain ⟨p,hp,hpi⟩ := F.choose_owners_at i j hj
  let p' : Vertex → Fin 4 := fun k => collapseOwner k (p k)
  have hp3 := hquarter 3 (by decide) (p 3) (hp 3)
  have hp5 := hquarter 5 (by decide) (p 5) (hp 5)
  have hpattern : Generated.Owner.MixedPattern p' := by
    have hz : ∀ k ∈ zeroEdges, p' k = 0 := by
      intro k hk
      simp only [p', collapseOwner, hk, ite_true]
    have hq' : ∀ k ∈ otherQuarterEdges, p k ∈ quarterOwners → p' k = 2 := by
      intro k hk hpk
      have hk0 : k ∉ zeroEdges := by
        revert hk
        fin_cases k <;> decide
      have hge : ¬ (p k < 2) := by
        revert hpk
        generalize p k = a
        fin_cases a <;> decide
      simp only [p', collapseOwner, hk0, hk, hge, ite_false, ite_true]
    have hm : ∀ k, k ∉ zeroEdges → k ∉ otherQuarterEdges → p' k = p k := by
      intro k h0 hq
      simp only [p', collapseOwner, h0, hq, ite_false]
    have hi' : i = 1 ∨ i = 6 := by
      revert hi0 hiq
      fin_cases i <;> decide
    refine ⟨hz 0 (by decide), hz 2 (by decide), hz 4 (by decide),
      hq' 3 (by decide) hp3, hq' 5 (by decide) hp5, ?_⟩
    rcases hi' with rfl | rfl
    · left
      rw [hm 1 (by decide) (by decide), hpi]
      intro h
      apply hbad
      rw [h]
      decide
    · right
      rw [hm 6 (by decide) (by decide), hpi]
      intro h
      apply hbad
      rw [h]
      decide
  obtain ⟨T,hTm,hTo⟩ := Generated.Owner.mixed_certificate hpattern
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  obtain ⟨r,hrm,hzr⟩ := T.select ⟨hzl.le,hzu.le⟩
  have hr := T.valid r hrm
  have hcont := mixed_continuous_necessary F hq hc hzero p hp hS hr
    ((T.same_mode r hrm).trans hTm) (T.no_error r hrm)
    (fun k => congrFun ((T.same_owners r hrm).trans hTo) k)
  apply hr.excludes_original hzr C.a C.b (hc.cones hq)
  · intro k
    have hh := (canonical_containment C k).trans hq
    simpa [Row.Q,(T.same_mode r hrm).trans hTm,Q0,SquaresInCircles.phi] using hh
  · exact Row.original_of_continuous hc hr hzr (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht hcont

theorem l1_square_bound {ι : Type*} [Fintype ι] (d : ι → ℝ) {ε : ℝ}
    (hε : ∑ i, |d i| ≤ ε) : ∑ i, (d i)^2 ≤ ε^2 := by
  classical
  have hfinite (s : Finset ι) : ∑ i ∈ s, (d i)^2 ≤ (∑ i ∈ s, |d i|)^2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have hs : 0 ≤ ∑ j ∈ s, |d j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      nlinarith [sq_abs (d i),mul_nonneg (abs_nonneg (d i)) hs]
  have hs : 0 ≤ ∑ i, |d i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  exact (hfinite Finset.univ).trans (pow_le_pow_left₀ hs hε 2)

theorem terminal_alternative_owner {q : ℝ} {C : BoundaryCycle q}
    (ho : OwnerRestriction C terminalOwners) (p : Vertex → Fin 4)
    (hp : FeasibleOwners C p) (j : Fin 5) :
    ∃ second : Bool, Alternative.owner j second = p (alignedEdge j) := by
  have hh := ho (alignedEdge j) (p (alignedEdge j)) (hp (alignedEdge j))
  revert hh
  generalize p (alignedEdge j) = a
  fin_cases j <;> fin_cases a <;> decide

theorem TiltBundle.loss_eq (B : TiltBundle) (a : Alternative) :
    (B.row a).loss=(B.row .zero).loss := by
  simp [Row.loss,Row.epsilon,Row.maxLambda,B.same_mode,B.same_lambda]

theorem tilt_weighted_necessary {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C) (ho : OwnerRestriction C terminalOwners)
    (hS : mismatch F.theta ≤ 1/1000) (B : TiltBundle)
    (hsign : if (B.row .zero).positive then 0 ≤ tilt F.theta else tilt F.theta ≤ 0)
    (p : Vertex → Fin 4) (hp : FeasibleOwners C p) :
    0 ≤ weightedSlack C (tilt F.theta) nominalOwner B.lambda +
      (∑ j : Fin 5, (errorCoefficient C (tilt F.theta) (B.row .zero).positive
        B.lambda (alignedEdge j) (p (alignedEdge j))*delta F.theta (alignedEdge j) -
        (B.lambda (alignedEdge j) : ℝ)/2*|delta F.theta (alignedEdge j)|)) +
      ((B.row .zero).loss : ℝ) := by
  have hlam (i : Vertex) : (0:ℝ) ≤ B.lambda i := by
    have hh := (B.valid .zero).lambda_nonneg i
    rw [B.same_lambda] at hh
    exact_mod_cast hh
  have halign (j : Fin 5) := mul_le_mul_of_nonneg_left
    (aligned_second_order_projection F hq
      (i := alignedEdge j) (by fin_cases j <;> decide)
      (p (alignedEdge j)) (hp (alignedEdge j)) (by linarith)) (hlam (alignedEdge j))
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5))) (fun j _ => halign j)
  have hG := mul_le_mul_of_nonneg_left (mixed_G_projection F (p G) (hp G)) (hlam G)
  have hpE : p E=1 := by
    have hh := ho E (p E) (hp E)
    revert hh
    generalize p E = a
    fin_cases a <;> decide
  have hE := mul_le_mul_of_nonneg_left
    (mixed_E_second_order F hq 1 (hpE ▸ hp E) hS hsign) (hlam E)
  have hM : (0:ℝ) ≤ (B.row .zero).maxLambda := by
    have hh := maxLambda_bound (B.row .zero) 0
    have h₀ := (B.valid .zero).lambda_nonneg (alignedEdge 0)
    exact_mod_cast h₀.trans hh
  have hsquare := l1_square_bound (fun j : Fin 5 => delta F.theta (alignedEdge j))
    (ε := 1/1000) (by simpa [mismatch,charged,alignedEdge,Fin.sum_univ_succ] using hS)
  have hweighted := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5)))
    (fun j _ => mul_le_mul_of_nonneg_right
      (show (B.lambda (alignedEdge j) : ℝ) ≤ (B.row .zero).maxLambda by
        have hh := maxLambda_bound (B.row .zero) j
        rw [B.same_lambda] at hh
        exact_mod_cast hh) (sq_nonneg (delta F.theta (alignedEdge j))))
  rw [← Finset.mul_sum] at hweighted
  have hweighted' := hweighted.trans (mul_le_mul_of_nonneg_left hsquare hM)
  have hδ := (totalSignedError_abs F.theta).trans hS
  have hδsq : (totalSignedError F.theta)^2 ≤ (1/1000:ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (totalSignedError F.theta)) hδ 2
  have hδweight := mul_le_mul_of_nonneg_left hδsq (hlam E)
  have hnom := terminal_nominal_projection hc ho p hp (tilt F.theta)
  -- the nominal slack with the actual owners, the tilt-mode loss, and the aligned widths
  have hWS : weightedSlack C (tilt F.theta) nominalOwner B.lambda =
      ∑ i, (B.lambda i : ℝ) * (actualProjection C i (p i) (nominalPhase (tilt F.theta) i) -
        pairWidth (nominalPhase (tilt F.theta) i)) := by
    simp only [weightedSlack, hnom]
  have hloss : ((B.row .zero).loss : ℝ) =
      (1/1000)^2 * ((1001/1000) * ((B.row .zero).maxLambda : ℝ) + (9/8) * (B.lambda E : ℝ)) := by
    simp [Row.loss, Row.epsilon, B.same_mode, B.same_lambda]
  have hpw : ∀ k ∈ charged, pairWidth (nominalPhase (tilt F.theta) k) = 1 :=
    fun k hk => (aligned_width F hk).1
  have hpw0 := hpw 0 (by decide)
  have hpw2 := hpw 2 (by decide)
  have hpw3 := hpw 3 (by decide)
  have hpw4 := hpw 4 (by decide)
  have hpw5 := hpw 5 (by decide)
  rw [hWS, hloss]
  simp only [G, E] at hG hE hδweight hpE ⊢
  simp only [Fin.sum_univ_seven, Fin.sum_univ_five, alignedEdge, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, errorCoefficient, totalSignedError, E, hpE,
    hpw0, hpw2, hpw3, hpw4, hpw5] at hsum hE hweighted' hδweight ⊢
  linarith

theorem tilt_bundle_excludes {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q1) (hc : TangentCuts C) (ho : OwnerRestriction C terminalOwners)
    (hS : mismatch F.theta ≤ 1/1000) (B : TiltBundle) {z : ℝ}
    (hz : B.interval.Mem z) (hchart : |z| ≤ 3/8)
    (ht : tilt F.theta=2*Real.arctan z) : False := by
  have hq0 : q ≤ Q0 := hq.trans (by norm_num [Q1,Q0])
  have hz0 : (B.row .zero).interval.Mem z := by simpa [B.same_interval] using hz
  have hs := Dual.Row.phase_sign (B.valid .zero) hz0 ht
  obtain ⟨p,hp⟩ := F.choose_owners
  have hnecessary := tilt_weighted_necessary F hq0 hc ho hS B hs p hp
  have hball : (∑ j : Fin 5, |delta F.theta (alignedEdge j)|) ≤ (1/1000:ℝ) := by
    simpa [mismatch,charged,alignedEdge,Fin.sum_univ_succ] using hS
  have hcircle : ∀ a : Alternative, ∀ i,
      (C.a i + 1 / 2) ^ 2 + (C.b i + 1 / 2) ^ 2 ≤ ((B.row a).Q : ℝ) := by
    intro a i
    have hci := (canonical_containment C i).trans hq
    simpa [Row.Q,B.same_mode,Q1,SquaresInCircles.phi] using hci
  obtain hzero | ⟨j,s,hsign,hspike⟩ := error_vertex_disjunction
    (fun j : Fin 5 => errorCoefficient C (tilt F.theta) (B.row .zero).positive
      B.lambda (alignedEdge j) (p (alignedEdge j)))
    (fun j : Fin 5 => (B.lambda (alignedEdge j) : ℝ))
    (fun j : Fin 5 => delta F.theta (alignedEdge j))
    (by norm_num : (0:ℝ) ≤ 1/1000) hball hnecessary
  · have hh : (B.row .zero).continuousNecessary C (tilt F.theta) := by
      unfold Row.continuousNecessary
      rw [B.same_alternative, B.same_owners, B.same_lambda]
      exact hzero
    apply (B.valid .zero).excludes_original hz0 C.a C.b (hc.cones hq0) (hcircle .zero)
    exact Row.original_of_continuous hc (B.valid .zero) hz0 hchart ht hh
  · obtain ⟨second,howner⟩ := terminal_alternative_owner ho p hp j
    obtain ⟨positive,hvalue⟩ : ∃ positive : Bool, (signValue positive : ℝ)=s := by
      rcases hsign with rfl | rfl
      · exact ⟨false,by norm_num [signValue]⟩
      · exact ⟨true,by norm_num [signValue]⟩
    have hza : (B.row (.spike j second positive)).interval.Mem z := by
      simpa [B.same_interval] using hz
    have hepsilon : ((B.row (.spike j second positive)).epsilon : ℝ) = 1/1000 := by
      simp [Row.epsilon, B.same_mode]
    have hh : (B.row (.spike j second positive)).continuousNecessary C (tilt F.theta) := by
      unfold Row.continuousNecessary
      rw [B.same_alternative]
      dsimp only
      rw [B.same_owners, B.same_lambda, TiltBundle.loss_eq B, B.same_sign, howner, hvalue, hepsilon]
      linarith
    apply (B.valid (.spike j second positive)).excludes_original hza C.a C.b (hc.cones hq0)
      (hcircle (.spike j second positive))
    exact Row.original_of_continuous hc (B.valid (.spike j second positive)) hza hchart ht hh

theorem tilt_window {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q1) (hc : TangentCuts C) (ho : OwnerRestriction C terminalOwners)
    (hS : mismatch F.theta ≤ 1/1000) :
    ∃ z : ℝ, 1001/20000 < z ∧ z < 2/25 ∧ tilt F.theta=2*Real.arctan z ∧
      1/10 < tilt F.theta ∧ tilt F.theta < 4/25 := by
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  have hzpos : 0 < z := by
    by_contra! hn
    exact negative_tilt_excluded F (hq.trans (by norm_num [Q1, Q0])) hc ho hS ⟨hzl.le, hn⟩ ht
  have hzwindow : 1001/20000 < z ∧ z < 2/25 := by
    by_contra! hn
    have htail : z ≤ 1001/20000 ∨ 2/25 ≤ z := by
      by_cases hz : 1001/20000 < z
      · exact Or.inr (hn hz)
      · exact Or.inl (le_of_not_gt hz)
    obtain ⟨B,hB⟩ := Generated.Owner.positive_tilt_tail_certificate ⟨hzpos.le,hzu.le⟩ htail
    exact tilt_bundle_excludes F hq hc ho hS B hB (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht
  exact ⟨z,hzwindow.1,hzwindow.2,ht,
    (half_angle_terminal_window hzwindow.1 hzwindow.2 ht).1,
    (half_angle_terminal_window hzwindow.1 hzwindow.2 ht).2⟩

end SquaresInCircles.Eight.Candidate
