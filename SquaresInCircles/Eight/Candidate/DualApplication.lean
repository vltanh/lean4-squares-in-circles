module

public import SquaresInCircles.Eight.Candidate.GeometricOwnersQuarter
public import SquaresInCircles.Eight.Generated.OwnerCompleteness

/-!
# Applying the rational circle duals to genuine candidate cycles

The weight vector is chosen by a closed interval before a signed-error
alternative is selected. Feasible axes are quantified individually: an
excluded owner cannot survive merely because another owner was selected.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate
open Dual

def weightedSlack {q : ℝ} (C : BoundaryCycle q) (t : ℝ)
    (p : Vertex → Fin 4) (λ : Vertex → ℚ) : ℝ :=
  ∑ i, (λ i : ℝ) * (actualProjection C i (p i) (nominalPhase t i)-pairWidth (nominalPhase t i))

def errorCoefficient {q : ℝ} (C : BoundaryCycle q) (t : ℝ) (positive : Bool)
    (λ : Vertex → ℚ) (i : Vertex) (j : Fin 4) : ℝ :=
  (λ i : ℝ)*actualDerivative C i j (nominalPhase t i) -
    (λ E : ℝ)*actualDerivative C E 1 (nominalPhase t E) +
    (λ E : ℝ)*widthSlope positive t

def Row.continuousNecessary {q : ℝ} (r : Row) (C : BoundaryCycle q) (t : ℝ) : Prop :=
  match r.alternative with
  | .zero => 0 ≤ weightedSlack C t r.owners r.lambda + (r.loss : ℝ)
  | .spike i second positive =>
    0 ≤ weightedSlack C t r.owners r.lambda + (r.loss : ℝ) + (r.epsilon : ℝ)*
      ((signValue positive : ℝ)*errorCoefficient C t r.positive r.lambda (alignedEdge i)
        (Alternative.owner i second) - (r.lambda (alignedEdge i) : ℝ)/2)

theorem Row.sign_at {r : Row} (hr : r.Valid) {z : ℝ} (hz : r.interval.Mem z) :
    if r.positive then 0 ≤ z else z ≤ 0 := by
  cases hp : r.positive
  · have hs : (r.interval.hi : ℝ) ≤ 0 := by exact_mod_cast (by simpa [hp] using hr.interval_sign)
    simpa [hp] using hz.2.trans hs
  · have hs : (0 : ℝ) ≤ r.interval.lo := by exact_mod_cast (by simpa [hp] using hr.interval_sign)
    simpa [hp] using hs.trans hz.1

theorem Row.phase_sign {r : Row} (hr : r.Valid) {z t : ℝ} (hz : r.interval.Mem z)
    (ht : t=2*Real.arctan z) : if r.positive then 0 ≤ t else t ≤ 0 := by
  have hs := hr.sign_at hz
  cases hp : r.positive <;> simp [hp] at hs ⊢
  · have hh := Real.arctan_strictMono.monotone hs
    simpa [ht] using mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤2 by norm_num) (by simpa using hh)
  · have hh := Real.arctan_strictMono.monotone hs
    simpa [ht] using mul_nonneg (show (0:ℝ)≤2 by norm_num) (by simpa using hh)

theorem Row.original_of_continuous {q : ℝ} {C : BoundaryCycle q} (hc : TangentCuts C)
    {r : Row} (hr : r.Valid) {z t : ℝ} (hz : r.interval.Mem z)
    (hchart : |z| ≤ 3/8) (ht : t=2*Real.arctan z)
    (hnecessary : r.continuousNecessary C t) : r.originalNecessary C.a C.b z := by
  have hd := D_positive z
  have hp := nominal_projection_identity hc z
  have hdp := nominal_derivative_identity hc z
  have hw := nominal_width_identity hchart (hr.sign_at hz)
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
  have he :
      ((∑ i, (r.lambda i : ℝ)*projectionNumerator C.a C.b z i (r.owners i)) +
          ∑ i, (peval (r.errorA i) z*C.a i+peval (r.errorB i) z*C.b i)) -
      ((∑ i, (r.lambda i : ℝ)*peval (edgeWidth r.positive i) z) -
          (r.loss : ℝ)*peval Dpoly z+peval r.errorRhs z) =
      peval Dpoly z *
      (match r.alternative with
       | .zero => weightedSlack C t r.owners r.lambda+(r.loss : ℝ)
       | .spike i second positive => weightedSlack C t r.owners r.lambda+(r.loss : ℝ)+
          (r.epsilon : ℝ)*((signValue positive : ℝ)*
            errorCoefficient C t r.positive r.lambda (alignedEdge i) (Alternative.owner i second)-
            (r.lambda (alignedEdge i) : ℝ)/2)) := by
    cases ha : r.alternative with
    | zero => simp [Row.errorA, Row.errorB, Row.errorRhs, ha, hp', hw', weightedSlack,
        peval, Finset.mul_sum, Finset.sum_sub_distrib]; ring
    | spike i second positive =>
      simp [Row.errorA,Row.errorB,Row.errorRhs,ha,peval,Polynomial.eval₂_finset_sum,
        weightedSlack,errorCoefficient,derivativeNumerator,Finset.mul_sum,Finset.sum_mul,
        Finset.sum_add_distrib,Finset.sum_sub_distrib,hp',hw',hwp',← hdp']
      ring
  have hm := mul_nonneg hd.le hnecessary
  change _ ≤ _
  rw [← sub_nonneg,he]
  exact hm

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
  have hBbad : p B ∉ quarterOwners := by
    intro hB
    have hi' : i=B ∨ i=D := by simpa [otherQuarterEdges, B, D] using hi
    rcases hi' with rfl | rfl
    · exact hbad (hpi ▸ hB)
    · have hD : p D ∉ quarterOwners := by simpa only [hpi] using hbad
      exact quarter_mixed_direction_excluded F hq hc hzero (by linarith)
        hB hD (hp B) (hp D)
  have hBsmall : p 3 < 2 := by
    have hh : p 3 ∉ quarterOwners := by simpa [B] using hBbad
    fin_cases p 3 <;> norm_num [quarterOwners] at hh ⊢
  let p' : Vertex → Fin 4 := fun k => collapseOwner k (p k)
  have hpattern : Generated.Owner.QuarterPattern p' := by
    by_cases h5 : p 5 < 2 <;>
      simp [Generated.Owner.QuarterPattern, p', collapseOwner,
        zeroEdges, otherQuarterEdges, hBsmall, h5]
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
    simpa [Row.Q,(T.same_mode r hrm).trans hTm,Q0] using hh
  · exact Row.original_of_continuous hc hr hzr (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht hcont

theorem mixed_owners {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hquarter : QuarterOwners C) (hS : mismatch F.theta ≤ 1/1000) :
    OwnerRestriction C terminalOwners := by
  intro i j hj
  by_cases hi0 : i ∈ zeroEdges
  · have hh := hzero i hi0 j hj
    fin_cases i <;> norm_num [zeroEdges] at hi0 <;> simpa [terminalOwners,zeroOwners] using hh
  by_cases hiq : i ∈ otherQuarterEdges
  · have hh := hquarter i hiq j hj
    fin_cases i <;> norm_num [otherQuarterEdges] at hiq <;> simpa [terminalOwners,quarterOwners] using hh
  by_contra hbad
  obtain ⟨p,hp,hpi⟩ := F.choose_owners_at i j hj
  let p' : Vertex → Fin 4 := fun k => collapseOwner k (p k)
  have hp3 := hquarter 3 (by norm_num [otherQuarterEdges]) (p 3) (hp 3)
  have hp5 := hquarter 5 (by norm_num [otherQuarterEdges]) (p 5) (hp 5)
  have hpattern : Generated.Owner.MixedPattern p' := by
    fin_cases i <;> norm_num [zeroEdges,otherQuarterEdges] at hi0 hiq <;>
      simp [terminalOwners] at hbad <;>
      simp [Generated.Owner.MixedPattern,p',collapseOwner,zeroEdges,otherQuarterEdges,hpi] <;>
      fin_cases p 3 <;> fin_cases p 5 <;> norm_num [quarterOwners] at hp3 hp5 ⊢ <;> aesop
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
    simpa [Row.Q,(T.same_mode r hrm).trans hTm,Q0] using hh
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
  fin_cases j <;> simp [alignedEdge,terminalOwners] at hh ⊢ <;>
    rcases hh with hh | hh <;>
    first | exact ⟨false,by simpa [Alternative.owner] using hh.symm⟩
          | exact ⟨true,by simpa [Alternative.owner] using hh.symm⟩

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
  have hλ (i : Vertex) : (0:ℝ) ≤ B.lambda i := by
    have hh := (B.valid .zero).lambda_nonneg i
    rw [B.same_lambda] at hh
    exact_mod_cast hh
  have halign (j : Fin 5) := mul_le_mul_of_nonneg_left
    (aligned_second_order_projection F hq
      (i := alignedEdge j) (by fin_cases j <;> norm_num [alignedEdge,charged])
      (p (alignedEdge j)) (hp (alignedEdge j)) (by linarith)) (hλ (alignedEdge j))
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5))) (fun j _ => halign j)
  have hG := mul_le_mul_of_nonneg_left (mixed_G_projection F (p G) (hp G)) (hλ G)
  have hpE : p E=1 := by simpa [terminalOwners,E] using ho E (p E) (hp E)
  have hE := mul_le_mul_of_nonneg_left
    (mixed_E_second_order F hq 1 (hpE ▸ hp E) hS hsign) (hλ E)
  have hM : (0:ℝ) ≤ (B.row .zero).maxLambda := by
    have hh := maxLambda_bound (B.row .zero) 0
    have h₀ := (B.valid .zero).lambda_nonneg 0
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
  have hδweight := mul_le_mul_of_nonneg_left hδsq (hλ E)
  have hnom := terminal_nominal_projection hc ho p hp (tilt F.theta)
  simp [weightedSlack,errorCoefficient,totalSignedError,alignedEdge,Fin.sum_univ_succ,
    hnom,Row.loss,Row.epsilon,Row.maxLambda,B.same_mode,B.same_lambda,
    nominalPhase,zeroEdges,otherQuarterEdges,nominalOwner,G,E,charged,pairWidth,
    hpE] at hsum hG hE hweighted' hδweight ⊢
  nlinarith

theorem tilt_bundle_excludes {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q1) (hc : TangentCuts C) (ho : OwnerRestriction C terminalOwners)
    (hS : mismatch F.theta ≤ 1/1000) (B : TiltBundle) {z : ℝ}
    (hz : B.interval.Mem z) (hchart : |z| ≤ 3/8)
    (ht : tilt F.theta=2*Real.arctan z) : False := by
  have hq0 : q ≤ Q0 := hq.trans (by norm_num [Q1,Q0])
  have hz0 : (B.row .zero).interval.Mem z := by simpa [B.same_interval] using hz
  have hs := (B.valid .zero).phase_sign hz0 ht
  obtain ⟨p,hp⟩ := F.choose_owners
  have hnecessary := tilt_weighted_necessary F hq0 hc ho hS B hs p hp
  have hball : (∑ j : Fin 5, |delta F.theta (alignedEdge j)|) ≤ (1/1000:ℝ) := by
    simpa [mismatch,charged,alignedEdge,Fin.sum_univ_succ] using hS
  obtain hzero | ⟨j,s,hsign,hspike⟩ := error_vertex_disjunction
    (fun j : Fin 5 => errorCoefficient C (tilt F.theta) (B.row .zero).positive
      B.lambda (alignedEdge j) (p (alignedEdge j)))
    (fun j : Fin 5 => (B.lambda (alignedEdge j) : ℝ))
    (fun j : Fin 5 => delta F.theta (alignedEdge j))
    (by norm_num : (0:ℝ) ≤ 1/1000) hball hnecessary
  · have hh : (B.row .zero).continuousNecessary C (tilt F.theta) := by
      simpa [Row.continuousNecessary,B.same_alternative,B.same_owners,B.same_lambda] using hzero
    apply (B.valid .zero).excludes_original hz0 C.a C.b (hc.cones hq0)
    · intro i
      have hci := (canonical_containment C i).trans hq
      simpa [Row.Q,B.same_mode,Q1] using hci
    · exact Row.original_of_continuous hc (B.valid .zero) hz0 hchart ht hh
  · obtain ⟨second,howner⟩ := terminal_alternative_owner ho p hp j
    obtain ⟨positive,hvalue⟩ : ∃ positive : Bool, (signValue positive : ℝ)=s := by
      rcases hsign with rfl | rfl
      · exact ⟨false,by norm_num [signValue]⟩
      · exact ⟨true,by norm_num [signValue]⟩
    let a : Alternative := .spike j second positive
    have hza : (B.row a).interval.Mem z := by simpa [B.same_interval] using hz
    have hh : (B.row a).continuousNecessary C (tilt F.theta) := by
      simpa [Row.continuousNecessary,B.same_alternative,B.same_owners,B.same_lambda,
        B.same_sign,B.loss_eq,Row.epsilon,B.same_mode,a,howner,hvalue,add_assoc] using hspike
    apply (B.valid a).excludes_original hza C.a C.b (hc.cones hq0)
    · intro i
      have hci := (canonical_containment C i).trans hq
      simpa [Row.Q,B.same_mode,Q1] using hci
    · exact Row.original_of_continuous hc (B.valid a) hza hchart ht hh

theorem tilt_window {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q1) (hc : TangentCuts C) (ho : OwnerRestriction C terminalOwners)
    (hS : mismatch F.theta ≤ 1/1000) :
    ∃ z : ℝ, 1001/20000 < z ∧ z < 2/25 ∧ tilt F.theta=2*Real.arctan z ∧
      1/10 < tilt F.theta ∧ tilt F.theta < 4/25 := by
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  have hzpos : 0 < z := by
    by_contra! hn
    exact negative_tilt_excluded F (hq.trans (by norm_num [Q1, Q0]))
      hc ho hS ⟨hzl.le, hn⟩ ht
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
