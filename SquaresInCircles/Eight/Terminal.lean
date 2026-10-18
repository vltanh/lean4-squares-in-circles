module

public import SquaresInCircles.Eight.Model
public import SquaresInCircles.Eight.ExactFamily.Weights

/-!
# Center completion and the stationary original-position dual

Uncompiled source draft.  All center identities below hold for arbitrary
centers.  In particular, the zero-error dual does not assume that original
centers are near a radially deformed center or inside a slider rectangle.

Sources: `HAND_EXACT_CENTER_SQUARE_COMPLETION.md`, Sections 2 and 6;
`HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md`, Sections 3--5; and
`EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md`, Sections 3--4.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight
open ExactFamily

theorem complete_center_square (μ : ℝ) (hμ : μ ≠ 0) (p o F : Point) :
    μ*normSq (add p o)+dot F p =
      μ*normSq (add (add p o) (scale (1/(2*μ)) F))-
      dot F o-normSq F/(4*μ) := by
  dsimp [normSq,add,dot,scale]
  field_simp [hμ]
  ring

theorem center_square_difference (μ : ℝ) (p r o : Point) :
    μ*normSq (add p o)-μ*normSq (add r o)+
      dot (scale (-2*μ) (add r o)) (sub p r) =
      μ*normSq (sub p r) := by
  dsimp [normSq,add,dot,scale,sub]
  ring

theorem zero_normSq_iff (p : Point) : normSq p = 0 ↔ p = (0,0) := by
  constructor
  · intro hp
    have hx := sq_nonneg p.1
    have hy := sq_nonneg p.2
    ext <;> dsimp [normSq] at hp <;> nlinarith
  · rintro rfl
    norm_num [normSq]

def terminalQuadratic : ℝ :=
  26453303561590200213 / 2850910772000000000
def terminalCubic : ℝ := 5176729803 / 3455440000
def firstOrderReserve : ℝ := 56793 / 5000000
def terminalReserve : ℝ := 10293 / 5000000

theorem terminal_constants :
    0 < terminalQuadratic ∧ terminalQuadratic < 232/25 ∧
    0 < terminalCubic ∧ terminalCubic < 3/2 ∧
    0 < terminalReserve ∧
    firstOrderReserve-93/10000 = terminalReserve := by
  norm_num [terminalQuadratic,terminalCubic,terminalReserve,firstOrderReserve]

theorem enlarged_owner_reserves :
    (1869/100000 : ℝ) > firstOrderReserve ∧
    (34656/100000 : ℝ) > firstOrderReserve ∧
    (3112575/10000000 : ℝ) > firstOrderReserve ∧
    (3984975/10000000 : ℝ) > firstOrderReserve ∧
    641425/10000000-(17/1000)*(4209/5000 : ℝ) > firstOrderReserve ∧
    3072/100000-(23/1000)*(4209/5000 : ℝ) = firstOrderReserve ∧
    (21785/1000000 : ℝ) > firstOrderReserve ∧
    345425/10000000-(22/1000)*(4209/5000 : ℝ) > firstOrderReserve ∧
    521875/10000000-(15/1000)*(4209/5000 : ℝ) > firstOrderReserve := by
  norm_num [firstOrderReserve]

theorem terminal_remainder_absorption {S : ℝ} (hS : 0 ≤ S) (hS' : S ≤ 1/1000) :
    firstOrderReserve*S-terminalQuadratic*S^2-terminalCubic*S^3 ≥
      terminalReserve*S := by
  obtain ⟨h₂,h₂',h₃,h₃',hρ,hid⟩ := terminal_constants
  have hS₂ : S^2 ≤ S/1000 := by nlinarith
  have hS₃ : S^3 ≤ S^2/1000 := by nlinarith [mul_nonneg hS hS₂]
  have h₁ := mul_le_mul_of_nonneg_right h₂'.le (sq_nonneg S)
  have h₂ := mul_le_mul_of_nonneg_right h₃'.le (pow_nonneg hS 3)
  have h₃ := mul_le_mul_of_nonneg_left hS₃ (by norm_num : (0:ℝ) ≤ 3/2)
  have h₄ := mul_le_mul_of_nonneg_left hS₂ (by norm_num : (0:ℝ) ≤ 93/10)
  nlinarith [mul_nonneg hS (sq_nonneg S)]

/-- The final rational absorption step, separated from the geometric estimates
which supply its four summands. -/
theorem combine_terminal_terms {q qstar μ t tstar S C L : ℝ}
    (hμ : 0 ≤ μ) (hS : 0 ≤ S) (hS' : S ≤ 1/1000)
    (hdual : C+L ≤ q)
    (hL : qstar+(3*μ/8)*(t-tstar)^2+firstOrderReserve*S-
      terminalQuadratic*S^2-terminalCubic*S^3 ≤ L) :
    qstar+(3*μ/8)*(t-tstar)^2+C+terminalReserve*S ≤ q := by
  have h := terminal_remainder_absorption hS hS'
  linarith

theorem terminal_equality_forces {q μ t tstar S C : ℝ}
    (hμ : 0 < μ) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (h : q+(3*μ/8)*(t-tstar)^2+C+terminalReserve*S ≤ q) :
    t = tstar ∧ S = 0 ∧ C = 0 := by
  have hρ : 0 < terminalReserve := terminal_constants.2.2.2.2.1
  have ht : 0 ≤ (3*μ/8)*(t-tstar)^2 := mul_nonneg (by positivity) (sq_nonneg _)
  have hs : 0 ≤ terminalReserve*S := mul_nonneg hρ.le hS
  have hC0 : C = 0 := by linarith
  have hS0 : S = 0 := by nlinarith
  have ht0 : (t-tstar)^2 = 0 := by nlinarith
  exact ⟨by nlinarith,hS0,hC0⟩

namespace OriginalDual
open ExactFamily.Coordinates

/-- Positions are indexed A,B,D,E,H,T,G in this algebra-only module.  The
adapter to the canonical cycle is the explicit permutation below. -/
abbrev Positions := Fin 7 → Point

def cycleIndex : Fin 7 → Fin 7 := ![2,3,5,6,0,4,1]
def ofCycle (p : Fin 7 → Point) : Positions := fun i => p (cycleIndex i)

def reference (d : Coordinates) (Z η : ℝ) : Positions :=
  ![d.pA,d.pB,d.pD,d.pE,d.pH,d.pT Z,d.pG η]

def gap (d : Coordinates) (p : Positions) : Fin 7 → ℝ :=
  ![(p 1).2-(p 0).2-1,
    (p 1).1-(p 5).1-1,
    (p 5).1-(p 2).1-1,
    (p 2).2-(p 3).2-1,
    dot d.e (sub (p 0) (p 6))-(1+d.c+d.s)/2,
    dot d.e (sub (p 6) (p 4))-1,
    dot d.f (sub (p 3) (p 4))-(1+d.c+d.s)/2]

def value (d : Coordinates) (p : Positions) : ℝ :=
  (∑ i : Fin 5, d.mu i*normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i)))-
  ∑ e : Fin 7, d.lam e*gap d p e

theorem reference_gap (d : Coordinates) (Z η : ℝ) (e : Fin 7) :
    gap d (reference d Z η) e = 0 := by
  have hstandard := d.standard_contacts Z
  fin_cases e
  · simpa [gap,reference] using sub_eq_zero.mpr hstandard.1
  · simpa [gap,reference] using sub_eq_zero.mpr hstandard.2.1
  · simpa [gap,reference] using sub_eq_zero.mpr hstandard.2.2.1
  · simpa [gap,reference] using sub_eq_zero.mpr hstandard.2.2.2
  · simpa [gap,reference] using sub_eq_zero.mpr (d.GA_contact η)
  · simpa [gap,reference] using sub_eq_zero.mpr (d.HG_contact η)
  · simpa [gap,reference] using sub_eq_zero.mpr d.HE_contact

theorem weighted_gap_difference (d : Coordinates) (p r : Positions) :
    -(∑ e : Fin 7, d.lam e*gap d p e)+
       (∑ e : Fin 7, d.lam e*gap d r e) =
      ∑ i : Fin 7, dot (d.forces i) (sub (p i) (r i)) := by
  simp [Fin.sum_univ_succ,gap,lam,rawLambda,forces,rawForces,
    dot,sub,scale,e,f]
  ring

theorem reference_value {d : Coordinates} (hd : d.IsChain)
    (hw : d.WeightDomain) (hz : d.defect = 0) (Z η : ℝ) :
    value d (reference d Z η) = d.q := by
  have href (i : Fin 5) : reference d Z η i.castSucc.castSucc = d.anchorCenters i := by
    fin_cases i <;> rfl
  simp only [value,reference_gap,mul_zero,Finset.sum_const_zero,sub_zero,href,d.anchor_vertex]
  simp only [d.anchor_circle hd hz]
  rw [← Finset.sum_mul,hw.mu_sum,one_mul]

theorem exact_identity {d : Coordinates} (hd : d.IsChain) (hw : d.WeightDomain)
    (hz : d.defect = 0) (hstation : d.positionDerivative = 0)
    (p : Positions) :
    value d p = d.q+
      ∑ i : Fin 5, d.mu i*normSq (sub (p i.castSucc.castSucc) (d.anchorCenters i)) := by
  let r := reference d 0 0
  have href (i : Fin 5) : r i.castSucc.castSucc = d.anchorCenters i := by
    fin_cases i <;> rfl
  have hforce (i : Fin 5) : d.forces i.castSucc.castSucc =
      scale (-2*d.mu i) (add (r i.castSucc.castSucc) (d.anchorOffsets i)) := by
    rw [href,d.anchor_vertex]
    exact d.force_balance hw hstation i
  have hsum (i : Fin 5) := center_square_difference (d.mu i)
    (p i.castSucc.castSucc) (r i.castSucc.castSucc) (d.anchorOffsets i)
  have hsum' := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => hsum i)
  have hgap := weighted_gap_difference d p r
  have hzero := d.slider_forces_zero
  have hrefl := reference_value hd hw hz 0 0
  have hforces : (∑ i : Fin 7, dot (d.forces i) (sub (p i) (r i))) =
      ∑ i : Fin 5, dot (d.forces i.castSucc.castSucc)
        (sub (p i.castSucc.castSucc) (r i.castSucc.castSucc)) := by
    simp [Fin.sum_univ_succ,hzero.1,hzero.2,dot]
  rw [hforces] at hgap
  simp only [hforce] at hgap
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hsum'
  simp only [href] at hsum' hgap
  dsimp [value] at hrefl ⊢
  linarith

theorem value_le {d : Coordinates} (hw : d.WeightDomain) {p : Positions} {q : ℝ}
    (hc : ∀ i : Fin 5, normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i)) ≤ q)
    (hg : ∀ e : Fin 7, 0 ≤ gap d p e) : value d p ≤ q := by
  have hvertices := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
    mul_le_mul_of_nonneg_left (hc i) (hw.mu_pos i).le)
  have hgaps : 0 ≤ ∑ e : Fin 7, d.lam e*gap d p e :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hw.lam_pos e).le (hg e))
  rw [← Finset.sum_mul,hw.mu_sum,one_mul] at hvertices
  dsimp [value]
  linarith

/-- Original-center rigidity, with no displacement or slider-size hypothesis. -/
theorem original_centers_rigid {d : Coordinates} (hd : d.IsChain)
    (hw : d.WeightDomain) (hz : d.defect = 0) (hstation : d.positionDerivative = 0)
    {p : Positions}
    (hc : ∀ i : Fin 5, normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i)) ≤ d.q)
    (hg : ∀ e : Fin 7, 0 ≤ gap d p e) :
    (∀ i : Fin 5, p i.castSucc.castSucc = d.anchorCenters i) ∧
    (∀ e : Fin 7, gap d p e = 0) := by
  have hdual := value_le hw hc hg
  have hid := exact_identity hd hw hz hstation p
  have hsnonneg : 0 ≤ ∑ i : Fin 5,
      d.mu i*normSq (sub (p i.castSucc.castSucc) (d.anchorCenters i)) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw.mu_pos i).le (normSq_nonneg _))
  have hs : (∑ i : Fin 5,
      d.mu i*normSq (sub (p i.castSucc.castSucc) (d.anchorCenters i))) = 0 := by linarith
  have hcenters (i : Fin 5) : p i.castSucc.castSucc = d.anchorCenters i := by
    have hone := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
        mul_nonneg (hw.mu_pos j).le (normSq_nonneg
          (sub (p j.castSucc.castSucc) (d.anchorCenters j)))) (Finset.mem_univ i)
    rw [hs] at hone
    have hnorm : normSq (sub (p i.castSucc.castSucc) (d.anchorCenters i)) = 0 := by
      nlinarith [hw.mu_pos i,normSq_nonneg (sub (p i.castSucc.castSucc) (d.anchorCenters i))]
    have hpoint := (zero_normSq_iff _).mp hnorm
    ext <;> have hh := congrArg Prod.fst hpoint <;>
      have hh' := congrArg Prod.snd hpoint <;> dsimp [sub] at hh hh' <;> linarith
  have hvalue : value d p = d.q := by rw [hid,hs,add_zero]
  have hgapSum : (∑ e : Fin 7, d.lam e*gap d p e) = 0 := by
    have hvert : (∑ i : Fin 5,
        d.mu i*normSq (add (p i.castSucc.castSucc) (d.anchorOffsets i))) = d.q := by
      simp only [hcenters,d.anchor_vertex,d.anchor_circle hd hz]
      rw [← Finset.sum_mul,hw.mu_sum,one_mul]
    dsimp [value] at hvalue
    linarith
  refine ⟨hcenters,fun e => ?_⟩
  have hone := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 7))) =>
      mul_nonneg (hw.lam_pos j).le (hg j)) (Finset.mem_univ e)
  rw [hgapSum] at hone
  nlinarith [hw.lam_pos e,hg e]

theorem frame_reconstruction (d : Coordinates) (p : Point) :
    d.inFrame (dot d.e p) (dot d.f p) = p := by
  ext <;> dsimp [Coordinates.inFrame,Coordinates.e,Coordinates.f,dot]
  · linear_combination p.1*d.unit
  · linear_combination p.2*d.unit

theorem slider_coordinates {d : Coordinates} {p : Positions}
    (hB : p 1 = d.pB) (hH : p 4 = d.pH)
    (hTB : gap d p 1 = 0) (hHG : gap d p 5 = 0) :
    ∃ Z η : ℝ, p 5 = d.pT Z ∧ p 6 = d.pG η := by
  refine ⟨(p 5).2,dot d.f (p 6)-d.h₂-1/2,?_,?_⟩
  · have h := hTB
    simp only [gap,Matrix.cons_val_succ,Matrix.cons_val_zero,hB,Coordinates.pB] at h
    ext <;> dsimp [Coordinates.pT]
    · linarith
    · rfl
  · have h := hHG
    simp only [gap,Matrix.cons_val_succ,Matrix.cons_val_zero,hH,dot_sub_right,
      Coordinates.pH,d.dot_e_inFrame] at h
    have hx : dot d.e (p 6) = d.h₁+3/2 := by linarith
    rw [← frame_reconstruction d (p 6),hx]
    congr 1 <;> dsimp [Coordinates.pG] <;> ring

end OriginalDual
end SquaresInCircles.Eight
