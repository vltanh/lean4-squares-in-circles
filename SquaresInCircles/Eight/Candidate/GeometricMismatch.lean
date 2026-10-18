module

public import SquaresInCircles.Eight.Candidate.Projection
public import SquaresInCircles.Eight.Candidate.GeometricPrimaryExclusion

/-!
# Exact contact frontiers for the candidate mismatch problem

The signed half-angle coordinate turns every actual SAT condition into a
quadratic.  On either sign branch the charged angular cost is monotone.
Consequently its minimum over feasible angles occurs at the left endpoint
or at a SAT contact root.  This replaces the *angular* subdivision problem
by at most two contact roots, for arbitrary state-dependent labels.

The state-dependent endpoint/contact inequalities still have to be proved.
This file does not assert the coarse or any later charged bound.  It imports
no generated table and contains no numerical certificate.  It is an
uncompiled source draft, as requested for PR #10.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.Candidate.Geometric

def phase (quarter : Bool) (z : ℝ) : ℝ :=
  (if quarter then Real.pi / 2 else 0) + 2 * Real.arctan z

def branchSign (positive : Bool) : ℝ := if positive then 1 else -1

def quadratic (a b c z : ℝ) : ℝ := a * z ^ 2 + b * z + c

/-- Coefficients are ordered constant, linear, quadratic.  The coordinates
and signs are the original canonical square coordinates. -/
def coefficients (a b A B σ τ : ℝ) (quarter positive : Bool)
    (j : Fin 4) : Fin 3 → ℝ :=
  let r := branchSign positive
  if quarter then
    ![![σ*b+A-1, 2*τ*B-r, σ*b-A],
      ![A+σ*b-1, 2*a-r, A-σ*b],
      ![a-τ*B-1, -2*σ*b-r, -a-τ*B],
      ![a-τ*B-1, 2*A-r, a+τ*B]] j
  else
    ![![σ*b-τ*B-1, 2*A-r, σ*b+τ*B],
      ![A-a-1, 2*σ*b-r, A+a],
      ![σ*b-τ*B-1, 2*a-r, -σ*b-τ*B],
      ![a-A-1, -2*τ*B-r, a+A]] j

def numerator (a b A B σ τ : ℝ) (quarter positive : Bool)
    (j : Fin 4) (z : ℝ) : ℝ :=
  let v := coefficients a b A B σ τ quarter positive j
  quadratic (v 2) (v 1) (v 0) z

theorem width_eq_one_add_h (x : ℝ) : pairWidth x = 1 + h x := by
  unfold pairWidth h
  ring

theorem phase_sin (quarter : Bool) (z : ℝ) :
    Real.sin (phase quarter z) =
      (if quarter then 1-z^2 else 2*z) / (1+z^2) := by
  have hh := half_angle_identities z
  cases quarter <;> simp [phase, Real.sin_add, hh.1, hh.2]

theorem phase_cos (quarter : Bool) (z : ℝ) :
    Real.cos (phase quarter z) =
      (if quarter then -2*z else 1-z^2) / (1+z^2) := by
  have hh := half_angle_identities z
  cases quarter <;> simp [phase, Real.cos_add, hh.1, hh.2] <;> ring

/-- The support width is rational in the signed half-angle coordinate. -/
theorem phase_width (quarter : Bool) {z : ℝ} (hz : |z| ≤ 3/8) :
    pairWidth (phase quarter z) = (1+|z|)/(1+z^2) := by
  have hd : 0 < 1+z^2 := by positivity
  have hn : 0 ≤ 1-z^2 := by
    have hh := abs_le.mp hz
    nlinarith
  have hh := half_angle_identities z
  have hw : pairWidth (2*Real.arctan z) = (1+|z|)/(1+z^2) := by
    simp only [pairWidth, hh.1, hh.2, abs_div, abs_mul,
      abs_of_pos hd, abs_of_nonneg hn, show |(2:ℝ)|=2 by norm_num]
    field_simp [ne_of_gt hd]
    ring
  cases quarter
  · simpa [phase] using hw
  · simpa [phase, pairWidth, Real.sin_add, Real.cos_add, abs_neg,
      add_comm, add_left_comm] using hw

theorem phase_h (quarter : Bool) {z : ℝ} (hz : |z| ≤ 3/8) :
    h (phase quarter z) = (|z|-z^2)/(1+z^2) := by
  have hd : 0 < 1+z^2 := by positivity
  calc
    h (phase quarter z) = pairWidth (phase quarter z)-1 := by
      rw [width_eq_one_add_h]
      ring
    _ = (|z|-z^2)/(1+z^2) := by
      rw [phase_width quarter hz]
      field_simp [ne_of_gt hd]
      ring

/-- All sixteen quarter/sign/axis formulas follow by algebra from the
actual SAT margins.  No circle relaxation is used in this identity. -/
theorem margin_numerator (a b A B σ τ : ℝ) (quarter positive : Bool)
    (j : Fin 4) {z : ℝ} (hz : |z| ≤ 3/8)
    (hside : if positive then 0 ≤ z else z ≤ 0) :
    (1+z^2) * forwardMargin j a b A B σ τ (phase quarter z) =
      numerator a b A B σ τ quarter positive j z := by
  have hd : 0 < 1+z^2 := by positivity
  have hs := phase_sin quarter z
  have hc := phase_cos quarter z
  have hw := phase_width quarter hz
  have ha : |z| = branchSign positive * z := by
    cases positive <;> simp [branchSign] at hside ⊢
    · exact abs_of_nonpos hside
    · exact abs_of_nonneg hside
  cases quarter <;> cases positive <;> fin_cases j <;>
    simp [forwardMargin, hs, hc, hw, ha, numerator, coefficients,
      quadratic, branchSign] <;>
    field_simp [ne_of_gt hd] <;> ring

theorem margin_nonneg_iff (a b A B σ τ : ℝ) (quarter positive : Bool)
    (j : Fin 4) {z : ℝ} (hz : |z| ≤ 3/8)
    (hside : if positive then 0 ≤ z else z ≤ 0) :
    0 ≤ forwardMargin j a b A B σ τ (phase quarter z) ↔
      0 ≤ numerator a b A B σ τ quarter positive j z := by
  have hd : 0 < 1+z^2 := by positivity
  have he := margin_numerator a b A B σ τ quarter positive j hz hside
  constructor
  · intro hm
    rw [← he]
    exact mul_nonneg hd.le hm
  · intro hn
    by_contra! hm
    have hh := mul_neg_of_pos_of_neg hd hm
    rw [he] at hh
    linarith

theorem h_lipschitz {x y : ℝ} (hx : |x| ≤ 3/4) (hy : |y| ≤ 3/4) :
    |h x-h y| ≤ (1/2:ℝ)*|x-y| := by
  have hh := width_lipschitz_small hx hy
  simpa only [width_eq_one_add_h, add_sub_add_left_eq_sub] using hh

/-- This estimate is uniform in the coordinate state and in the labels.
In particular every charge in the four mismatch stages is below 2. -/
theorem charged_angle_growth {β x y : ℝ} (hβ : 0 ≤ β)
    (hx : |x| ≤ 3/4) (hy : |y| ≤ 3/4) (hxy : x ≤ y) :
    (1-β/2)*(y-x) ≤ (y-β*h y)-(x-β*h x) := by
  have hh := (abs_le.mp (h_lipschitz hy hx)).2
  rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
  have hp := mul_le_mul_of_nonneg_left hh hβ
  nlinarith

theorem double_arctan_small {z : ℝ} (hz : z ∈ Icc (-(3/8:ℝ)) (3/8)) :
    |2*Real.arctan z| ≤ 3/4 := by
  have hu := arctan_le_self (x := 3/8) (by norm_num)
  have hl := Real.arctan_strictMono.monotone hz.1
  have hh := Real.arctan_strictMono.monotone hz.2
  rw [Real.arctan_neg] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def cost (β : ℝ) (quarter : Bool) (sourceLabel targetLabel z : ℝ) : ℝ :=
  phase quarter z - β*h (phase quarter z) + sourceLabel-targetLabel

theorem h_phase_period (quarter : Bool) (z : ℝ) :
    h (phase quarter z) = h (2*Real.arctan z) := by
  cases quarter <;> simp [phase, h_half_pi_add]

theorem cost_monotone {β : ℝ} (hβ : 0 ≤ β ∧ β ≤ 2)
    (quarter : Bool) (sourceLabel targetLabel : ℝ) :
    MonotoneOn (cost β quarter sourceLabel targetLabel)
      (Icc (-(3/8:ℝ)) (3/8)) := by
  intro x hx y hy hxy
  have ha : 2*Real.arctan x ≤ 2*Real.arctan y :=
    mul_le_mul_of_nonneg_left (Real.arctan_strictMono.monotone hxy) (by norm_num)
  have hg := charged_angle_growth hβ.1 (double_arctan_small hx)
    (double_arctan_small hy) ha
  have hp := mul_nonneg (by linarith : 0 ≤ 1-β/2) (sub_nonneg.mpr ha)
  unfold cost
  rw [h_phase_period, h_phase_period]
  unfold phase
  linarith

theorem cost_formula (β : ℝ) (quarter : Bool) (sourceLabel targetLabel : ℝ)
    {z : ℝ} (hz : |z| ≤ 3/8) :
    cost β quarter sourceLabel targetLabel z =
      (if quarter then Real.pi/2 else 0) + 2*Real.arctan z -
      β*(|z|-z^2)/(1+z^2) + sourceLabel-targetLabel := by
  rw [cost, phase_h quarter hz]
  unfold phase
  ring

/-! ## A finite contact frontier -/

/-- There are two quadratic candidates; the linear candidate is used only
when the quadratic coefficient vanishes.  Membership alone does not assert
that a candidate is a root. -/
def rootCandidates (a b c : ℝ) : Finset ℝ := by
  classical
  exact if a=0 then {-c/b} else
    {(-b+Real.sqrt (b^2-4*a*c))/(2*a), (-b-Real.sqrt (b^2-4*a*c))/(2*a)}

theorem contact_mem {a b c z : ℝ} (hcoeff : a ≠ 0 ∨ b ≠ 0)
    (hzero : quadratic a b c z = 0) : z ∈ rootCandidates a b c := by
  classical
  by_cases ha : a=0
  · have hb : b ≠ 0 := hcoeff.resolve_left (by simpa [ha])
    have hz : z = -c/b := by
      apply (eq_div_iff hb).2
      simp [quadratic, ha] at hzero
      nlinarith
    simp [rootCandidates, ha, hz]
  · let Δ := b^2-4*a*c
    have hid : (2*a*z+b)^2 = Δ+4*a*quadratic a b c z := by
      unfold Δ quadratic
      ring
    rw [hzero, mul_zero, add_zero] at hid
    have hΔ : 0 ≤ Δ := by rw [← hid]; positivity
    have hs := Real.sq_sqrt hΔ
    have hp : (2*a*z+b-Real.sqrt Δ)*(2*a*z+b+Real.sqrt Δ)=0 := by
      nlinarith
    have hden : 2*a ≠ 0 := mul_ne_zero (by norm_num) ha
    rcases mul_eq_zero.mp hp with hp | hp
    · have hz : z=(-b+Real.sqrt Δ)/(2*a) := by
        apply (eq_div_iff hden).2
        linarith
      simp [rootCandidates, ha, hz, Δ]
    · have hz : z=(-b-Real.sqrt Δ)/(2*a) := by
        apply (eq_div_iff hden).2
        linarith
      simp [rootCandidates, ha, hz, Δ]

/-- A monotone cost over a closed feasible interval is controlled by the
left endpoint and contact points.  The intermediate value theorem covers
disconnected feasible sets and tangential contact as well. -/
theorem frontier_bound {l u γ : ℝ} {f p : ℝ → ℝ}
    (hf : MonotoneOn f (Icc l u)) (hp : ContinuousOn p (Icc l u))
    (hleft : 0 ≤ p l → γ < f l)
    (hcontact : ∀ z ∈ Icc l u, p z=0 → γ < f z)
    {z : ℝ} (hz : z ∈ Icc l u) (hfeasible : 0 ≤ p z) : γ < f z := by
  by_cases hl : 0 ≤ p l
  · exact (hleft hl).trans_le (hf ⟨le_rfl, hz.1.trans hz.2⟩ hz hz.1)
  · have hl' : p l ≤ 0 := (lt_of_not_ge hl).le
    obtain ⟨r, hr, he⟩ := intermediate_value_Icc hz.1
      (hp.mono (Icc_subset_Icc le_rfl hz.2)) ⟨hl', hfeasible⟩
    have hru : r ∈ Icc l u := ⟨hr.1, hr.2.trans hz.2⟩
    exact (hcontact r hru he).trans_le (hf hru hz hr.2)

/-- No subdivision of [l,u] is needed.  Constant polynomials are handled
by the left endpoint; nonconstant ones have at most the stated roots. -/
theorem quadratic_frontier_bound {l u γ a b c : ℝ} {f : ℝ → ℝ}
    (hf : MonotoneOn f (Icc l u))
    (hleft : 0 ≤ quadratic a b c l → γ < f l)
    (hroots : ∀ r ∈ rootCandidates a b c,
      r ∈ Icc l u → quadratic a b c r=0 → γ < f r)
    {z : ℝ} (hz : z ∈ Icc l u) (hfeasible : 0 ≤ quadratic a b c z) :
    γ < f z := by
  apply frontier_bound hf (show ContinuousOn (quadratic a b c) (Icc l u) by
    unfold quadratic; fun_prop) hleft ?_ hz hfeasible
  intro r hr he
  by_cases ha : a=0
  · by_cases hb : b=0
    · have hl : 0 ≤ quadratic a b c l := by simpa [quadratic, ha, hb] using he.ge
      exact (hleft hl).trans_le (hf ⟨le_rfl, hr.1.trans hr.2⟩ hr hr.1)
    · exact hroots r (contact_mem (Or.inr hb) he) hr he
  · exact hroots r (contact_mem (Or.inl ha) he) hr he

/-- A complete one-pair charged inequality from its finite geometric
frontier.  The remaining hypotheses are exact endpoint/contact inequalities
for the state-dependent labels, not a claim that those inequalities hold. -/
theorem pair_bound_of_frontier (a b A B σ τ : ℝ) (quarter positive : Bool)
    (j : Fin 4) {β l u γ sourceLabel targetLabel : ℝ}
    (hβ : 0 ≤ β ∧ β ≤ 2) (hchart : -(3/8:ℝ) ≤ l ∧ u ≤ 3/8)
    (hside : if positive then 0 ≤ l else u ≤ 0)
    (hleft : 0 ≤ numerator a b A B σ τ quarter positive j l →
      γ < cost β quarter sourceLabel targetLabel l)
    (hroots : let v := coefficients a b A B σ τ quarter positive j
      ∀ r ∈ rootCandidates (v 2) (v 1) (v 0), r ∈ Icc l u →
        numerator a b A B σ τ quarter positive j r=0 →
        γ < cost β quarter sourceLabel targetLabel r)
    {z : ℝ} (hz : z ∈ Icc l u)
    (hfeasible : 0 ≤ forwardMargin j a b A B σ τ (phase quarter z)) :
    γ < cost β quarter sourceLabel targetLabel z := by
  have hzc : |z| ≤ 3/8 := abs_le.mpr
    ⟨hchart.1.trans hz.1, hz.2.trans hchart.2⟩
  have hzs : if positive then 0 ≤ z else z ≤ 0 := by
    cases positive <;> simp at hside ⊢ <;> linarith [hz.1, hz.2]
  have hn := (margin_nonneg_iff a b A B σ τ quarter positive j hzc hzs).1 hfeasible
  have hmono : MonotoneOn (cost β quarter sourceLabel targetLabel) (Icc l u) := by
    intro x hx y hy hxy
    exact cost_monotone hβ quarter sourceLabel targetLabel
      ⟨hchart.1.trans hx.1, hx.2.trans hchart.2⟩
      ⟨hchart.1.trans hy.1, hy.2.trans hchart.2⟩ hxy
  exact quadratic_frontier_bound hmono hleft hroots hz hn

/-! ## Connection to the original frame and every feasible axis -/

def quarterOf (i : Vertex) : Bool := decide (word i=1)

theorem quarterOf_base (i : Vertex) :
    (if quarterOf i then Real.pi/2 else 0) = (word i:ℝ)*Real.pi/2 := by
  fin_cases i <;> norm_num [quarterOf, word]

theorem frame_coordinate {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (i : Vertex) : ∃ z : ℝ, -(3/8:ℝ) < z ∧ z < 3/8 ∧
      phi F.theta i=phase (quarterOf i) z := by
  obtain ⟨z, hz₁, hz₂, he⟩ := half_angle_chart (F.delta_small i)
  refine ⟨z, hz₁, hz₂, ?_⟩
  unfold phase
  rw [quarterOf_base, ← he]
  rfl

theorem frame_feasible_iff {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (i : Vertex) (j : Fin 4) (positive : Bool) {z : ℝ}
    (hz : |z| ≤ 3/8) (hside : if positive then 0 ≤ z else z ≤ 0)
    (hphase : phi F.theta i=phase (quarterOf i) z) :
    (forwardAxis j).Feasible (C.square i) (C.square (next i)) ↔
      0 ≤ numerator (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
        (C.sigma i) (C.sigma (next i)) (quarterOf i) positive j z := by
  rw [F.margin_nonneg_iff]
  simpa only [margin, hphase] using
    margin_nonneg_iff (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      (C.sigma i) (C.sigma (next i)) (quarterOf i) positive j hz hside

end SquaresInCircles.Eight.Candidate.Geometric
