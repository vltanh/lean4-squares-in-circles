module

public import SquaresInCircles.Eight.Candidate.GeometricCoreCoverage

/-!
# The coarse cyclic budget excludes every adjacent core pair

The same coherent labels give cost > 9/10 on a core/core edge and
> 89727/100000 on the other six edges. Their sum exceeds 2π. The
conclusion concerns actual primary coordinates, not a radial tag, so it
applies to every later closed state cover. Uncompiled source.
-/

@[expose] public section
open scoped BigOperators

namespace SquaresInCircles.Eight.Candidate.GeometricCoreCycle
open Arithmetic

def NoAdjacentCore {q : ℝ} (C : BoundaryCycle q) : Prop :=
  ∀ i, ¬ (C.a i ≤ 7/12 ∧ C.a (next i) ≤ 7/12)

theorem arc_core_of_small_primary {s : ArcData} {q a b : ℝ}
    (hs : s.Contains q a b) (hq : (169/72:ℝ) < q) (ha : a ≤ 7/12) :
    s.outer = false := by
  cases ho : s.outer with
  | false => rfl
  | true =>
      exfalso
      have hc := hs.2.2.2.2
      simp only [ArcData.OnCurve, ho, if_true] at hc
      have hb : b ≤ 7/12 := hs.2.2.1.trans ha
      have ha₂ := mul_nonneg (sub_nonneg.mpr ha)
        (show (0:ℝ) ≤ a+19/12 by linarith [hs.1])
      have hb₂ := mul_nonneg (sub_nonneg.mpr hb)
        (show (0:ℝ) ≤ b+19/12 by linarith [hs.2.1])
      nlinarith

def strongCoreMeta (M : AffineTableMeta) : AffineTableMeta :=
  {M with target := fun _ => 9/10}

theorem coarse_no_adjacent_core {K : AffineCover} {M : AffineTableMeta}
    {rows : List AffineTableRow}
    (hK : GeometricCoreCoverage.NumericValid K M rows)
    (hrows : ∀ r ∈ rows, r.Claim M)
    (hstrong : GeometricCoreMarker.BudgetsValid (strongCoreMeta M))
    (hbaseline : ∀ i, (M.target i:ℝ) = 89727/100000)
    (hq : (169/72:ℝ) < (M.radius:ℝ))
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C) (β : ℝ) (hβ : 0 ≤ β)
    (hword : ∀ i, (M.word i:ℝ) = (Candidate.word i:ℝ))
    (hcharge : ∀ i, (M.charge i:ℝ) = Candidate.charge β i)
    (hcuts : ∀ i, (M.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j ∈ M.allowedAxes i) : NoAdjacentCore C := by
  intro i hsmall
  choose selected hrole hcontains hproducts using fun k => K.states.covers hK.2.1 C hcuts k
  have hsource := arc_core_of_small_primary (hcontains i) hq hsmall.1
  have htarget := arc_core_of_small_primary (hcontains (next i)) hq hsmall.2
  let γ : Vertex → ℝ := fun k => if k=i then 9/10 else (M.target k:ℝ)
  have P : ChargedBound C F β γ := by
    refine {label := fun k => (arcAt M (selected k)).label.eval (C.a k) (C.b k),
      pair_bound := ?_}
    intro k j hj
    by_cases hk : k=i
    · subst k
      have hp : (9/10:ℝ) < chargedCost (arcAt M (selected i)).label
          (arcAt M (selected (next i))).label (M.charge i)
          (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (phi F.theta i) :=
        GeometricCoreMarker.pair_bound (M := strongCoreMeta M)
          hK.1 hK.2.2.1 hstrong C F
          (hrole i) (hrole (next i)) (hcontains i) (hcontains (next i))
          (hproducts i) (hproducts (next i)) hsource htarget j hj
      simpa [γ, chargedCost, frameCharge, Candidate.h, hcharge,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hp
    · have hp := GeometricCoreCoverage.pair_bound hK hrows C F hword hdiff haxes
        (hrole k) (hrole (next k)) (hcontains k) (hcontains (next k))
        (hproducts k) (hproducts (next k)) j hj
      simpa [γ, hk, chargedCost, frameCharge, Candidate.h, hcharge,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hp
  have hsum : (∑ k, γ k) = (314181/50000:ℝ) := by
    simp only [γ, hbaseline]
    fin_cases i <;> norm_num [Fin.sum_univ_succ]
  have hcost : 0 ≤ hSum F.theta := Finset.sum_nonneg (fun _ _ => h_nonneg _)
  have hchargeCost := mul_nonneg hβ hcost
  have hcyclic := P.cyclic
  rw [hsum] at hcyclic
  have hpi := two_pi_lt_710_over_113
  linarith

theorem NoAdjacentCore.outer_pair {q : ℝ} {C : BoundaryCycle q}
    (hC : NoAdjacentCore C) {i : Vertex} {s t : ArcData}
    (hs : s.Contains q (C.a i) (C.b i))
    (ht : t.Contains q (C.a (next i)) (C.b (next i))) :
    s.outer = true ∨ t.outer = true := by
  cases hsource : s.outer with
  | true => exact Or.inl hsource
  | false =>
      cases htarget : t.outer with
      | true => exact Or.inr htarget
      | false =>
          exact (hC i ⟨GeometricAffine.arc_core_primary_upper hs hsource,
            GeometricAffine.arc_core_primary_upper ht htarget⟩).elim

end SquaresInCircles.Eight.Candidate.GeometricCoreCycle

namespace SquaresInCircles.Eight.Candidate.GeometricOuterCoverage
open Arithmetic GeometricCoreCycle

def NumericValid (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  K.EndpointsValid M ∧ K.states.NumericValid M ∧ GeometricCoreCoverage.AngleValid K M rows

instance (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) :
    Decidable (NumericValid K M rows) := by unfold NumericValid; infer_instance

noncomputable def chargedBound {K : AffineCover} {M : AffineTableMeta}
    {rows : List AffineTableRow} (hK : NumericValid K M rows)
    (hrows : ∀ r ∈ rows, r.Claim M)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C) (hC : NoAdjacentCore C) (β : ℝ)
    (hword : ∀ i, (M.word i:ℝ) = (Candidate.word i:ℝ))
    (hcharge : ∀ i, (M.charge i:ℝ) = Candidate.charge β i)
    (hcuts : ∀ i, (M.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j ∈ M.allowedAxes i) :
    ChargedBound C F β (fun i => (M.target i:ℝ)) := by
  choose selected hrole hcontains hproducts using fun i => K.states.covers hK.2.1 C hcuts i
  refine {label := fun i => (arcAt M (selected i)).label.eval (C.a i) (C.b i), pair_bound := ?_}
  intro i j hj
  have houter := hC.outer_pair (hcontains i) (hcontains (next i))
  have hp := GeometricCoreCoverage.outer_pair_bound hK.1 hK.2.2 hrows C F hword hdiff haxes
    (hrole i) (hrole (next i)) (hcontains i) (hcontains (next i))
    (hproducts i) (hproducts (next i)) houter j hj
  simpa [chargedCost, frameCharge, Candidate.h, hcharge,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hp

end SquaresInCircles.Eight.Candidate.GeometricOuterCoverage
