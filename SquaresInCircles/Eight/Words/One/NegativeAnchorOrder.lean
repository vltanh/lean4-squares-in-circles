module

public import SquaresInCircles.Eight.Owners.Direct.NegativeTCycle
public import SquaresInCircles.Eight.Words.Middle.Order
public import SquaresInCircles.Eight.Words.One.NegativeAnchorPenalty
public import SquaresInCircles.Eight.Words.One.NegativeBTReference
public import SquaresInCircles.Eight.Words.One.NegativeHGCharge

/-!
# Eight squares: original anchor order at the remaining negative BT primary

The unchanged scalar BT reference first forces G strictly above B, using the signed endpoint
budget of the original cycle (`negative_BT_intermediate_order`). Under a proposed order H ≤ D,
the stronger positive HG charge and the endpoint budget with coefficient `41/40` then contradict
the original A/B middle stress (`negative_BT_middle_bound`, `negative_BT_anchor_order`). Both
AB owners and all four original mixed-owner pairs are kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace SignedCycle
open Candidate PositiveAngularEnvelope EndpointBudgetScalars
open OneNegativeBTReference OneNegativeAnchorConcentration

private theorem r60_feasible_zero {C : SignedCycle} {i : Vertex} (hw : Candidate.word i=0)
    (j : Fin 4) : C.Feasible i j ↔
      zeroFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,zeroFeasible,delta,sub_nonneg]

private theorem r60_feasible_quarter {C : SignedCycle} {i : Vertex} (hw : Candidate.word i≠0)
    (j : Fin 4) : C.Feasible i j ↔
      quarterFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,quarterFeasible,delta,sub_nonneg]

private theorem reference_GA_AB {C : SignedCycle} (w : C.Witnesses)
    (hGA : C.Feasible G 0) :
    quarterFeasible (C.point G) (C.point A) (C.theta A-C.theta G) 0 ∧
      (zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) 0 ∨
        zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) 2) := by
  refine ⟨?_,?_⟩
  · have h := (r60_feasible_quarter (C := C) (i := G) (by decide) 0).1 hGA
    rwa [show next G=A by decide] at h
  · have ho : w.owner A=0 ∨ w.owner A=2 := by
      simpa [normalOwners,A] using w.allowed A
    have hf := (r60_feasible_zero (C := C) (i := A) (by decide) _).1 (w.feasible A)
    rw [show next A=B by decide] at hf
    rcases ho with ho | ho
    · left
      rwa [ho] at hf
    · right
      rwa [ho] at hf

/-- The reference has only a scalar tangent; the original A and B
circles and physical frame differences are the inputs to this estimate. -/
theorem negative_BT_reference_reverse {q te : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hGA : C.Feasible G 0)
    (hBTref : 1+te≤(C.point B).a) (hGB : C.theta G≤C.theta B) :
    -(C.point G).y+te≤S0+(3/4)*(C.theta B-C.theta G) := by
  let Tref : SignedPoint := ⟨0,te⟩
  obtain ⟨hga,hab⟩ := reference_GA_AB w hGA
  have hbt : quarterFeasible (C.point B) Tref 0 2 := by
    show edgeWidth 0≤(C.point B).a*Real.cos 0-(C.point B).y*Real.sin 0-Tref.y
    simp only [edgeWidth_zero,Real.cos_zero,Real.sin_zero,Tref]
    linarith
  have hsum : |(C.theta A-C.theta G)+(C.theta B-C.theta A)|≤frameCap := by
    convert hC.spread B G using 2
    ring
  have hh := MiddleOrder.actual_middle ((hC.contained A).trans hq)
    ((hC.contained B).trans hq) ha.A_nonneg ha.B_nonpos
    (hC.spread A G) (hC.spread B A)
    (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
    (by simpa only [add_zero] using hC.spread B A) hsum
    (show 0≤(C.theta A-C.theta G)+(C.theta B-C.theta A)+0 by linarith)
    hga hab hbt
  dsimp [Tref] at hh
  linarith

/-- An unavailable aligned negative BT2 owner forces G above the
original B frame.  The argument uses the unchanged all-sign charge. -/
theorem negative_BT_intermediate_order {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (ha : C.NormalAnchors)
    (hyE : (C.point E).y≤0) (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3)
    (hnot : ¬C.Feasible B 2) (hGA : C.Feasible G 0) :
    C.theta B<C.theta G := by
  by_contra! hGB
  let I := DirectNegativeT.sourceOfCycle hC ha w halign ht hyT hBT hnot
  have hBTref : 1+effective (C.point T).y (C.theta B-C.theta D)≤(C.point B).a := by
    simpa only [SignedPoint.reflect,neg_neg] using (I.scalar_reference hq).1
  have hinc : (21/20 : ℝ)*(C.theta B-C.theta D)<
      increment (C.point T).y (C.theta B-C.theta D) := by
    simpa only [SignedPoint.reflect,neg_neg] using (I.scalar_reference hq).2.1
  obtain ⟨hHG,hTD⟩ := signed_outer_charges hq hC ha w hz
  have hbudget := endpoint_budget hq hC ha hyE w
  have hmiddle := negative_BT_reference_reverse hq hC ha w hGA hBTref hGB
  rw [halign] at hTD
  dsimp [EndpointRotationPenalty.charge,epsilon,increment] at hHG hTD hbudget hinc
  linarith

theorem negative_BT_reference_middle {q l mu te : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hGA : C.Feasible G 0)
    (hw : Weights l mu (C.theta G-C.theta B))
    (hBTref : 1+te≤(C.point B).a) :
    -(C.point G).y+mu*te≤
      max (endpointB l mu (C.theta G-C.theta B))
        (endpointG l mu (C.theta G-C.theta B))-1/2-3*mu/2-l := by
  obtain ⟨hga,hab⟩ := reference_GA_AB w hGA
  have hA : (C.point A).Contained (R^2) := by
    change (C.point A).circle≤EndpointRotationPenalty.R^2
    rw [EndpointRotationPenalty.R_sq]
    exact (hC.contained A).trans hq
  have hB : (C.point B).Contained (R^2) := by
    change (C.point B).circle≤EndpointRotationPenalty.R^2
    rw [EndpointRotationPenalty.R_sq]
    exact (hC.contained B).trans hq
  exact reference_middle hw hA hB ha.A_nonneg ha.B_nonpos
    (hC.spread A G) (hC.spread B A) (by ring) hga hab hBTref

/-- The correction of the virtual reference restores the original signed T tangent and the
original G--D span. The output is exactly the maximum of the two scalar endpoint expressions
`OneNegativeAnchorPolynomial.MB` and `OneNegativeAnchorPolynomial.MG`. -/
theorem negative_BT_middle_bound {q l mu : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (ha : C.NormalAnchors)
    (w : C.Witnesses) (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3)
    (hnot : ¬C.Feasible B 2) (hGA : C.Feasible G 0)
    (hw : Weights l mu (C.theta G-C.theta B)) :
    -(C.point G).y+(C.point T).y+(41/40)*(C.theta G-C.theta D)-S0≤
      max (OneNegativeAnchorPolynomial.MB l mu (C.theta G-C.theta B))
        (OneNegativeAnchorPolynomial.MG l mu (C.theta G-C.theta B)) := by
  let I := DirectNegativeT.sourceOfCycle hC ha w halign ht hyT hBT hnot
  let L : ℝ := C.theta G-C.theta B
  let k : ℝ := -1/2-3*mu/2-l+(1-mu)*(39/250)+(41/40)*L-S0
  have hBTref : 1+effective (C.point T).y (C.theta B-C.theta D)≤(C.point B).a := by
    simpa only [SignedPoint.reflect,neg_neg] using (I.scalar_reference hq).1
  have hcorrection : (1-mu)*(C.point T).y+(41/40)*(C.theta B-C.theta D)-
      mu*increment (C.point T).y (C.theta B-C.theta D)≤(1-mu)*(39/250) := by
    simpa only [SignedPoint.reflect,neg_neg] using I.reference_correction hq hw
  have hmiddle := negative_BT_reference_middle hq hC ha w hGA hw hBTref
  change -(C.point G).y+mu*effective (C.point T).y (C.theta B-C.theta D)≤
    max (endpointB l mu L) (endpointG l mu L)-1/2-3*mu/2-l at hmiddle
  have hB : endpointB l mu L+k=OneNegativeAnchorPolynomial.MB l mu L := by
    dsimp [endpointB,k,OneNegativeAnchorPolynomial.MB,
      OneNegativeAnchorPolynomial.p,OneNegativeAnchorCharge.p]
    ring
  have hG : endpointG l mu L+k=OneNegativeAnchorPolynomial.MG l mu L := by
    dsimp [endpointG,k,OneNegativeAnchorPolynomial.MG,
      OneNegativeAnchorPolynomial.p,OneNegativeAnchorCharge.p]
    ring
  have hmax : max (endpointB l mu L) (endpointG l mu L)+k≤
      max (OneNegativeAnchorPolynomial.MB l mu L) (OneNegativeAnchorPolynomial.MG l mu L) := by
    rcases le_total (endpointB l mu L) (endpointG l mu L) with hh | hh
    · rw [max_eq_right hh,hG]
      exact le_max_right _ _
    · rw [max_eq_left hh,hB]
      exact le_max_left _ _
  change -(C.point G).y+(C.point T).y+(41/40)*(C.theta G-C.theta D)-S0≤
    max (OneNegativeAnchorPolynomial.MB l mu L) (OneNegativeAnchorPolynomial.MG l mu L)
  dsimp [increment] at hcorrection
  dsimp [k,L] at hmax hmiddle ⊢
  linarith

/-- The anchor order of the original data at the remaining aligned negative BT primary. There
is no sign premise at G, AB alignment, mixed-error restriction, or endpoint radial-boundary
hypothesis. -/
theorem negative_BT_anchor_order {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (ha : C.NormalAnchors)
    (hyE : (C.point E).y≤0) (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3)
    (hnot : ¬C.Feasible B 2) (hGA : C.Feasible G 0) :
    C.theta D<C.theta H := by
  by_contra! hHD
  have hGB := negative_BT_intermediate_order hq hC ha hyE w hz halign ht hyT hBT hnot hGA
  have hv : C.theta G-C.theta H∈Ioc 0 frameCap :=
    ⟨by linarith,(le_abs_self _).trans (hC.spread G H)⟩
  have hL : C.theta G-C.theta B∈Icc 0 frameCap :=
    ⟨by linarith,(le_abs_self _).trans (hC.spread G B)⟩
  have hcharge := positive_one_negative_excess hq hC ha hyE w halign
    (show C.theta H≤C.theta G by linarith)
  by_cases hsmall : C.theta G-C.theta B≤1/25
  · have hw : Weights (121/200) (47/50) (C.theta G-C.theta B) :=
      Or.inl ⟨⟨hL.1,hsmall⟩,rfl,rfl⟩
    have hmiddle := negative_BT_middle_bound hq hC ha w halign ht hyT hBT hnot hGA hw
    have he := OneNegativeAnchorPolynomial.small_endpoints ⟨hL.1,hsmall⟩
    have hmax := max_lt_iff.mpr he
    have hf := OneNegativeAnchorCharge.f_pos hv
    dsimp [OneNegativeAnchorCharge.p] at hcharge
    linarith
  · have hlarge : C.theta G-C.theta B∈Icc (1/25 : ℝ) frameCap :=
      ⟨(lt_of_not_ge hsmall).le,hL.2⟩
    have hw : Weights (59/100+(C.theta G-C.theta B)/2) 1 (C.theta G-C.theta B) :=
      Or.inr ⟨hlarge,rfl,rfl⟩
    have hmiddle := negative_BT_middle_bound hq hC ha w halign ht hyT hBT hnot hGA hw
    have he := OneNegativeAnchorPolynomial.large_endpoints hlarge
    have hmax := max_lt_iff.mpr he
    have hf := OneNegativeAnchorCharge.f_reserve
      (show C.theta G-C.theta H∈Icc (1/25 : ℝ) frameCap by
        exact ⟨by linarith [hlarge.1],hv.2⟩)
    dsimp [OneNegativeAnchorCharge.p] at hcharge
    linarith

end SignedCycle
end SquaresInCircles.Eight
