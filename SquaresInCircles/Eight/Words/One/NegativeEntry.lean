module

public import SquaresInCircles.Eight.Owners.Direct.NegativeTCoupledArc
public import SquaresInCircles.Eight.Owners.Direct.NegativeTCycle
public import SquaresInCircles.Eight.Owners.Full.ERates
public import SquaresInCircles.Eight.Owners.TD2Span
public import SquaresInCircles.Eight.Words.Aligned.NegativeEH1Arc
public import SquaresInCircles.Eight.Words.FirstNegativeSlack
public import SquaresInCircles.Eight.Words.Middle.Order
public import SquaresInCircles.Eight.Words.One.NegativeBarrierEndpoints
public import SquaresInCircles.Eight.Words.One.NegativeAnchorSlopes

/-!
# Eight squares: complete actual one-negative primary entry at the original radius

The original .22 span follows from the actual
negative contact, and the H≤D alternative is excluded by the original
anchor-order theorem.  Every E radial kind and original E position is
already included in the constructive transport.  The result retains the
strict original-D circle loss and the complete actual hard input.
-/

section
/-!
## The original negative BT contact as a scalar middle reference

The unchanged negative-primary contact implies the exact radial reference and its signed
correction (`Source.scalar_reference`, `Source.reference_correction`). The whole-domain affine
cut `t+.63u<.156` suffices for both chosen stresses; the `.94` stress keeps a strict reserve
greater than `.0019u`. The reference is only a scalar: it adds no T point, circle hypothesis or
geometric move.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace OneNegativeBTReference
open PrimaryCap PositiveAngularEnvelope

def effective (t u : ℝ) : ℝ := (t+1/2)*Real.cos u+K*Real.sin u-1/2
def increment (t u : ℝ) : ℝ := effective t u-t

theorem increment_lower {t u : ℝ}
    (ht : t∈Icc 0 (39/250 : ℝ)) (hu : u∈Icc 0 (9/100 : ℝ)) :
    (10523/10000 : ℝ)*u≤ increment t u := by
  have hc := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (x := u)) (show 0≤t+1/2 by linarith [ht.1])
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hu.1)
    (show 0≤K by norm_num [K])
  have hcoeff := mul_nonneg (show 0≤82/125-(t+1/2) by linarith [ht.2]) (sq_nonneg u)
  have h2 : u^2≤(9/100)*u := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  have h3 : u^3≤(81/10000)*u := by
    have hm := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu.1 hu.2 2) hu.1
    nlinarith
  dsimp only [increment,effective]
  simp only [K] at hs ⊢
  linarith [hu.1]

theorem increment_positive {t u : ℝ}
    (ht : t∈Icc 0 (39/250 : ℝ)) (hu : u∈Ioc 0 (9/100 : ℝ)) :
    (21/20 : ℝ)*u< increment t u := by
  have h := increment_lower ht ⟨hu.1.le,hu.2⟩
  nlinarith [hu.1]

theorem correction {t u mu : ℝ}
    (ht : t∈Icc 0 (39/250 : ℝ)) (hu : u∈Ioc 0 (9/100 : ℝ))
    (hline : t+(63/100)*u<39/250) (hmu : mu=47/50 ∨ mu=1) :
    (1-mu)*t+(41/40)*u-mu*increment t u≤(1-mu)*(39/250) := by
  have hs := increment_lower ht ⟨hu.1.le,hu.2⟩
  rcases hmu with rfl | rfl <;> nlinarith [hu.1]

end OneNegativeBTReference

namespace AlignedNegative
open PrimaryCap OneNegativeBTReference

/-- All three reference facts follow from the aligned source at its own original circle
ceiling. -/
theorem Source.scalar_reference {q u : ℝ} {H G A : SignedPoint}
    (I : Source q u H G A) (hq : q≤qCap) :
    1+effective (-G.y) u≤A.a ∧
      (21/20 : ℝ)*u< increment (-G.y) u ∧
      -G.y+(63/100)*u<39/250 := by
  obtain ⟨hGa,hg0,hg1,hH,hHa,hu,hR,hq0⟩ := I.cuts hq
  obtain ⟨hAlo,hAhi,hvalue,hvaluele⟩ := I.cap_data hq
  have hc : 0<Real.cos u := transport_cos_pos
    (show |u|≤(7/10 : ℝ) by rw [abs_of_pos I.tilt_pos]; exact I.tilt_cap)
  have hcontact := value_contact_identity (A.a-1/2) u hc.ne'
  have hm := mul_le_mul_of_nonneg_right hvalue hc.le
  have hfirst : 1+effective (-G.y) u≤A.a := by
    dsimp [effective]
    linarith
  have hinc := increment_positive
    (show -G.y∈Icc 0 (39/250 : ℝ) by exact ⟨by linarith,hg1.le⟩)
    ⟨I.tilt_pos,hu.le⟩
  have hline := intrinsic_affine_cut
    (show 3/5< -G.y+1/2 ∧ -G.y+1/2≤183/200 by constructor <;> linarith)
    ⟨I.tilt_pos.le,I.tilt_cap⟩ (hR.trans_le hq)
  exact ⟨hfirst,hinc,by linarith⟩

theorem Source.reference_correction {q u l mu L : ℝ} {H G A : SignedPoint}
    (I : Source q u H G A) (hq : q≤qCap)
    (hw : OneNegativeAnchorConcentration.Weights l mu L) :
    (1-mu)*(-G.y)+(41/40)*u-mu*OneNegativeBTReference.increment (-G.y) u≤
      (1-mu)*(39/250) := by
  obtain ⟨_,hg0,hg1,_,_,hu,_,_⟩ := I.cuts hq
  apply OneNegativeBTReference.correction
    ⟨by linarith,hg1.le⟩ ⟨I.tilt_pos,hu.le⟩ (I.scalar_reference hq).2.2
  rcases hw with ⟨_,_,hmu⟩ | ⟨_,_,hmu⟩
  · exact Or.inl hmu
  · exact Or.inr hmu

end AlignedNegative
end SquaresInCircles.Eight
end
end
end

section
/-!
## Original anchor order at the remaining negative BT primary

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
end
end
end

section
/-!
## Composition of the actual negative-T stages

These constructors pull local endpoints back through
the already proved E-only alignment and same-circle D/T contact. Original
circle comparisons and frame intervals are composed explicitly; no loss
at T is substituted for the strict loss at D.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeT

def LocalEndpoint.prepend_E_motion {q t e h : ℝ} {D T B E E' H : SignedPoint}
    {I : Source q t D T B} {jDE jEH : Fin 4}
    (K : LocalEndpoint I E' H (-t) h jDE jEH)
    (he : e≤ -t) (hcircle : E'.circle≤E.circle) :
    LocalEndpoint I E H e h jDE jEH where
  angle := K.angle
  angle_mem := K.angle_mem
  Dpoint := K.Dpoint
  Tpoint := K.Tpoint
  Epoint := K.Epoint
  Etheta := K.Etheta
  E_frame := by
    right
    rcases K.E_frame with hh | hh
    · rw [hh]; exact ⟨le_rfl,neg_nonpos.mpr I.tilt_pos.le⟩
    · exact hh
  E_advance := he.trans K.E_advance
  D_sorted := K.D_sorted
  T_sorted := K.T_sorted
  E_sorted := K.E_sorted
  D_core := K.D_core
  T_core := K.T_core
  E_core := K.E_core
  D_circle_loss := K.D_circle_loss
  T_inside := K.T_inside
  E_contained := K.E_contained
  E_radial := K.E_radial
  E_circle_nonincrease := K.E_circle_nonincrease.trans hcircle
  D_negative := K.D_negative
  T_positive := K.T_positive
  E_nonpos := K.E_nonpos
  D_nondiagonal := K.D_nondiagonal
  T_nondiagonal := K.T_nondiagonal
  D_tangent_decreases := K.D_tangent_decreases
  TD0 := K.TD0
  TD2 := K.TD2
  BT2 := K.BT2
  DE := K.DE
  EH := K.EH

def LocalBarrier.prepend_E_motion {q t e h : ℝ} {D T B E E' H : SignedPoint}
    {I : Source q t D T B} {jDE jEH : Fin 4}
    (K : LocalBarrier I E' H (-t) h jDE jEH)
    (he : e≤ -t) (hcircle : E'.circle≤E.circle) :
    LocalBarrier I E H e h jDE jEH where
  angle := K.angle
  angle_mem := K.angle_mem
  Dpoint := K.Dpoint
  Tpoint := K.Tpoint
  Epoint := K.Epoint
  Etheta := K.Etheta
  E_frame := by
    right
    rcases K.E_frame with hh | hh
    · rw [hh]; exact ⟨le_rfl,neg_nonpos.mpr I.tilt_pos.le⟩
    · exact hh
  E_advance := he.trans K.E_advance
  D_sorted := K.D_sorted
  T_sorted := K.T_sorted
  E_sorted := K.E_sorted
  D_core := K.D_core
  T_core := K.T_core
  E_core := K.E_core
  D_circle_nonincrease := K.D_circle_nonincrease
  T_inside := K.T_inside
  E_contained := K.E_contained
  E_radial := K.E_radial
  E_circle_nonincrease := K.E_circle_nonincrease.trans hcircle
  D_negative := K.D_negative
  T_positive := K.T_positive
  E_nonpos := K.E_nonpos
  TD0 := K.TD0
  BT3 := K.BT3
  BT_unavailable := K.BT_unavailable
  DE := K.DE
  EH := K.EH
  bad_order := K.bad_order

def LocalEndpoint.prepend_contact {q t m e h : ℝ} {D T D' T' B E H : SignedPoint}
    (I : Source q t D T B) {J : Source q m D' T' B} {jDE jEH : Fin 4}
    (K : LocalEndpoint J E H e h jDE jEH)
    (hmt : m<t) (hcircle : D'.circle=D.circle) (htangent : |D'.y|≤|D.y|) :
    LocalEndpoint I E H e h jDE jEH where
  angle := K.angle
  angle_mem := ⟨K.angle_mem.1,K.angle_mem.2.trans hmt⟩
  Dpoint := K.Dpoint
  Tpoint := K.Tpoint
  Epoint := K.Epoint
  Etheta := K.Etheta
  E_frame := by
    rcases K.E_frame with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨by linarith [hh.1],hh.2⟩
  E_advance := K.E_advance
  D_sorted := K.D_sorted
  T_sorted := K.T_sorted
  E_sorted := K.E_sorted
  D_core := K.D_core
  T_core := K.T_core
  E_core := K.E_core
  D_circle_loss := K.D_circle_loss.trans_eq hcircle
  T_inside := K.T_inside
  E_contained := K.E_contained
  E_radial := K.E_radial
  E_circle_nonincrease := K.E_circle_nonincrease
  D_negative := K.D_negative
  T_positive := K.T_positive
  E_nonpos := K.E_nonpos
  D_nondiagonal := K.D_nondiagonal
  T_nondiagonal := K.T_nondiagonal
  D_tangent_decreases := K.D_tangent_decreases.trans_le htangent
  TD0 := K.TD0
  TD2 := K.TD2
  BT2 := K.BT2
  DE := K.DE
  EH := K.EH

def LocalBarrier.prepend_contact {q t m e h : ℝ} {D T D' T' B E H : SignedPoint}
    (I : Source q t D T B) {J : Source q m D' T' B} {jDE jEH : Fin 4}
    (K : LocalBarrier J E H e h jDE jEH)
    (hmt : m<t) (hcircle : D'.circle=D.circle) :
    LocalBarrier I E H e h jDE jEH where
  angle := K.angle
  angle_mem := ⟨K.angle_mem.1,K.angle_mem.2.trans hmt⟩
  Dpoint := K.Dpoint
  Tpoint := K.Tpoint
  Epoint := K.Epoint
  Etheta := K.Etheta
  E_frame := by
    rcases K.E_frame with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨by linarith [hh.1],hh.2⟩
  E_advance := K.E_advance
  D_sorted := K.D_sorted
  T_sorted := K.T_sorted
  E_sorted := K.E_sorted
  D_core := K.D_core
  T_core := K.T_core
  E_core := K.E_core
  D_circle_nonincrease := K.D_circle_nonincrease.trans_eq hcircle
  T_inside := K.T_inside
  E_contained := K.E_contained
  E_radial := K.E_radial
  E_circle_nonincrease := K.E_circle_nonincrease
  D_negative := K.D_negative
  T_positive := K.T_positive
  E_nonpos := K.E_nonpos
  TD0 := K.TD0
  BT3 := K.BT3
  BT_unavailable := K.BT_unavailable
  DE := K.DE
  EH := K.EH
  bad_order := K.bad_order

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
/-!
## Actual E-to-D alignment with an arbitrary contained H

The original positive H--D order keeps EH positive
until DE aligns. A compact minimum on E's full actual radial arc attains
that alignment while retaining both original weak mixed owners. No
near-diagonal bound or outer equality is assumed for H.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace FullE

theorem zero_tangent_impossible {q n : ℝ} {D : SignedPoint} {kind : ArcKind}
    (hDa : D.a<1) (hDs : D.Sorted) (hDy : D.y≤0)
    (ha : 0<kind.primary q 0) (hn : n∈Icc 0 (7/10 : ℝ))
    (j : Fin 4) (hj : j=2 ∨ j=3) :
    ¬quarterFeasible D (kind.point q 0) (-n) j := by
  intro hf
  have ht := transport_trig hn
  have hw := edgeWidth_ge_one (-n)
  rcases hj with rfl | rfl
  · have hcos := mul_le_mul_of_nonneg_left ht.2.1 hDs.1.le
    have hsin := mul_nonpos_of_nonpos_of_nonneg hDy ht.2.2.1
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_two,ArcKind.point,
      Real.sin_neg,Real.cos_neg,neg_zero,sub_zero,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
      Fin.succ_zero_eq_one,Matrix.cons_val_zero,Matrix.cons_val_one] at hf
    linarith
  · have hsin := mul_nonneg ha.le ht.2.2.1
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_three,ArcKind.point,
      Real.sin_neg,Real.cos_neg,neg_zero,zero_mul,sub_zero,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Matrix.cons_val_two,
      Matrix.cons_val_one,Matrix.cons_val_zero] at hf
    linarith


/-- The actual radial endpoint exists for either original EH owner and
either original negative DE owner, including curved-core E sources. -/
theorem alignment_endpoint_of_order {q n p : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q) (hHy : 0≤H.y)
    (hDy : 211/250< -D.y) (hDs : D.Sorted) (hDa : D.a<1)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hn : n∈Ioc 0 (7/10 : ℝ)) (hp : p∈Ioc 0 (7/10 : ℝ)) (hnp : n<p)
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E (-n) jDE) (hEH : quarterFeasible E H p jEH) :
    Nonempty (DirectNegativeE.AlignmentEndpoint q D E H n p jDE jEH) := by
  obtain ⟨kind,I⟩ := arcSource_of_boundary hEs hEy hEr
  let α := p-n
  let f := mixedSlack kind q H jEH
  let g := deSlack kind q α D jDE
  have hα : 0<α := by dsimp [α]; linarith
  have hαp : α<p := by dsimp [α]; linarith [hn.1]
  have hparams {x : ℝ} (hx : x∈Icc α p) :
      x∈Icc 0 (7/10 : ℝ) ∧ x-α∈Icc 0 (7/10 : ℝ) := by
    constructor
    · exact ⟨hα.le.trans hx.1,hx.2.trans hp.2⟩
    · constructor
      · linarith [hx.1]
      · dsimp [α]; linarith [hx.2,hn.2]
  have hprim := kind.continuous_primary q
  have hcf : Continuous (fun z : ℝ×ℝ => f z.1 z.2) := by
    dsimp [f,mixedSlack,DirectNegativeE.lowSlack,highSlack]
    split_ifs <;> fun_prop
  have hcg : Continuous (fun z : ℝ×ℝ => g z.1 z.2) := by
    dsimp [g,deSlack,OutsideE.de2Slack,de3Slack]
    split_ifs <;> fun_prop
  let S : Set (ℝ×ℝ) :=
    ((Icc α p ×ˢ Icc 0 (-E.y)) ∩ {z | 0≤f z.1 z.2}) ∩ {z | 0≤g z.1 z.2}
  have hcompact : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hcf)).inter_right
      (isClosed_le continuous_const hcg)
  have hstart : (p,-E.y)∈S := by
    refine ⟨⟨⟨⟨hαp.le,le_rfl⟩,⟨neg_nonneg.mpr hEy,le_rfl⟩⟩,?_⟩,?_⟩
    · dsimp [f]
      rw [mixedSlack_actual kind q H (-E.y) hjEH ⟨hp.1.le,hp.2⟩,I.initial]
      exact sub_nonneg.mpr hEH
    · dsimp [g]
      rw [deSlack_actual kind q α D (-E.y) hjDE
        (by dsimp [α]; simpa using ⟨hn.1.le,hn.2⟩),I.initial]
      simpa [α] using sub_nonneg.mpr hDE
  obtain ⟨z,hz,hmin⟩ := hcompact.exists_isMinOn ⟨(p,-E.y),hstart⟩
    continuous_fst.continuousOn
  let m := z.1
  let b := z.2
  have hm : m∈Icc α p := hz.1.1.1
  have hb : b∈Icc 0 (-E.y) := hz.1.1.2
  have hf : 0≤f m b := hz.1.2
  have hg : 0≤g m b := hz.2
  have hangles := hparams hm
  have hgeometry := I.geometry hqL hb
  have hEHfinal : quarterFeasible (kind.point q b) H m jEH := by
    have hh := hf
    dsimp [f] at hh
    rw [mixedSlack_actual kind q H b hjEH hangles.1] at hh
    exact sub_nonneg.mp hh
  have hDEfinal : quarterFeasible D (kind.point q b) (-(m-α)) jDE := by
    have hh := hg
    dsimp [g] at hh
    rw [deSlack_actual kind q α D b hjDE hangles.2] at hh
    exact sub_nonneg.mp hh
  have hbpos : 0<b := by
    apply lt_of_le_of_ne hb.1
    intro hzero
    have ha : 0<kind.primary q 0 := by
      have hh := hgeometry.2.2.2.2.2.1
      rw [← hzero] at hh
      linarith
    exact zero_tangent_impossible hDa hDs (by linarith) ha hangles.2 jDE hjDE
      (by simpa [← hzero] using hDEfinal)
  have hmα : m=α := by
    apply le_antisymm _ hm.1
    by_contra! hαm
    obtain ⟨β,hβ,hfder,hgder⟩ := I.improving_below_speed hqL hqU
      hHs hHcore hHc hHy hDs hDy hb hangles.1 hangles.2
      jDE jEH hjDE hjEH hEHfinal
    obtain ⟨z',hz'p,hz'b,hz'f,hz'g,hz'lt⟩ := OutsideE.feasible_shift_left
      (f := f) (g := g) ⟨hαm,hm.2⟩ hb hβ.le (Or.inr hbpos)
      (I.mixed_direction_derivative (H := H) (p := m) (β := β) jEH hqL hb)
      (I.de_direction_derivative (D := D) (α := α) (p := m) (β := β) jDE hqL hb)
      hf hg (Or.inr hfder) (Or.inr hgder)
    have hz'S : z'∈S := ⟨⟨⟨hz'p,hz'b⟩,hz'f⟩,hz'g⟩
    have hh : m≤z'.1 := hmin hz'S
    linarith
  exact ⟨{
    point := kind.point q b
    positive_span := hα
    sorted := hgeometry.1
    contained := hgeometry.2.1
    core := hgeometry.2.2.1
    radial := hgeometry.2.2.2.1
    nonpos := by dsimp [ArcKind.point]; linarith [hb.1]
    tangent_nonincrease := by
      simp only [ArcKind.point,abs_neg,abs_of_nonneg hb.1,abs_of_nonpos hEy]
      exact hb.2
    circle_nonincrease := hgeometry.2.2.2.2.1
    DE := by simpa [hmα] using hDEfinal
    EH := by simpa [hmα,α] using hEHfinal }⟩

end FullE
end SquaresInCircles.Eight
end
end
end

section
/-!
## Whole-domain positive DE continuation with the original E fixed

This is the positive-DE part of the complete one-negative
BT theorem. No H cut or H--D span is used. An actual outer DE3 contact has
error below .18; beyond .18 its actual margin has an explicit positive
reserve. Core E and DE2 have full-angle derivative bounds. The first actual
BT2 contact, or preceding DE alignment, therefore has strict original-DE
slack and can pay the already constructed D-circle contraction.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap

theorem outer_primary_plus_tangent {q : ℝ} {E : SignedPoint}
    (hqL : qLow≤q) (hEs : E.Sorted) (hEy : E.y≤0) (ho : E.Outer q) :
    axisCoordinate q≤E.a-E.y := by
  have hqroot : 0≤q-1/4 := by dsimp [qLow] at hqL; linarith
  have hroot := Real.sqrt_nonneg (q-1/4)
  have hroot2 := Real.sq_sqrt hqroot
  have hprod := mul_nonneg hEs.1.le (neg_nonneg.mpr hEy)
  have hcircle : (E.a+1/2)^2+(-E.y+1/2)^2=q := by
    simpa [SignedPoint.Outer,SignedPoint.circle,abs_of_nonpos hEy] using ho
  have hsum : 0≤E.a-E.y+1/2 := by linarith [hEs.1]
  unfold axisCoordinate
  by_contra! hbad
  nlinarith

private theorem outer_DE3_base {d : ℝ} (hd : d∈Icc (9/50 : ℝ) (7/10 : ℝ)) :
    (33/2500 : ℝ)<43/125+(9/10)*Real.sin d-(1/2)*Real.cos d := by
  let f : ℝ → ℝ := fun x => 43/125+(9/10)*Real.sin x-(1/2)*Real.cos x
  have hderiv (x : ℝ) : HasDerivAt f ((9/10)*Real.cos x+(1/2)*Real.sin x) x := by
    exact ((((Real.hasDerivAt_sin x).const_mul (9/10)).const_add (43/125)).sub
      ((Real.hasDerivAt_cos x).const_mul (1/2))).congr_deriv (by ring)
  have hmono : MonotoneOn f (Icc 0 (7/10 : ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg (by dsimp [f]; fun_prop) (fun x _ => hderiv x)
    intro x hx
    have ht := transport_trig (Ioo_subset_Icc_self hx)
    linarith [ht.1,ht.2.2.1]
  have hbase : (33/2500 : ℝ)<f (9/50) := by
    have hs := sin_lower_seven (show (0:ℝ)≤9/50 by norm_num)
    have hc := cos_upper_four (show (0:ℝ)≤9/50 by norm_num)
    dsimp [f]
    norm_num at hs hc
    linarith
  exact hbase.trans_le (hmono (by constructor <;> norm_num)
    ⟨by linarith [hd.1],hd.2⟩ hd.1)

/-- The actual outer-E margin, rather than a numerical contact search,
excludes the whole large-error interval. -/
theorem outer_DE3_margin {q d : ℝ} {D E : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hEs : E.Sorted) (hEy : E.y≤0) (ho : E.Outer q)
    (hDa : 211/250<D.a) (hd : d∈Icc (9/50 : ℝ) (7/10 : ℝ)) :
    33/2500<quarterProjection D E d 3-edgeWidth d := by
  have hd0 : d∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hd.1],hd.2⟩
  have ht := transport_trig hd0
  have haxis : (7/5 : ℝ)<axisCoordinate q := by
    have hh := (uniform_circle_reserves hqL hqU).2.2.1
    dsimp [axisCoordinate]
    linarith
  have hsum := outer_primary_plus_tangent hqL hEs hEy ho
  have hmul := mul_le_mul_of_nonneg_right hsum ht.2.2.1
  have hdiag := mul_nonneg (neg_nonneg.mpr hEy)
    (sub_nonneg.mpr ht.2.2.2.2.le)
  have hbound : axisCoordinate q*Real.sin d≤E.a*Real.sin d-E.y*Real.cos d := by
    nlinarith
  have haxisprod := mul_le_mul_of_nonneg_right
    (show (7/5 : ℝ)≤axisCoordinate q by linarith) ht.2.2.1
  have hbase := outer_DE3_base hd
  rw [edgeWidth_positive_formula hd0]
  simp only [quarterProjection,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  linarith


theorem core_original_e_rate {E : SignedPoint} {d : ℝ}
    (hEs : E.Sorted) (hEc : E.Core) (hEy : E.y≤0)
    (hd : d∈Icc 0 (7/10 : ℝ)) :
    (E.a-1/2)*Real.cos d+(1/2+E.y)*Real.sin d<203/500 := by
  have ha := SignedPoint.core_primary_le hEs hEc
  have ht := transport_trig hd
  have hcos0 : 0≤Real.cos d := by linarith [ht.1]
  have hprim := mul_le_mul_of_nonneg_right
    (show E.a-1/2≤(1/12:ℝ) by linarith) hcos0
  have hprim1 := mul_le_mul_of_nonneg_left ht.2.1 (by norm_num : (0:ℝ)≤1/12)
  have htan := mul_le_mul_of_nonneg_right
    (show 1/2+E.y≤(1/2:ℝ) by linarith) ht.2.2.1
  nlinarith [ht.2.2.2.1]

/-- A uniform derivative reserve on the actual small-slack set, on the
whole positive DE interval. E may be core corner, flat core, or outer. -/
theorem Source.positive_de_small_slack_derivative {q t e x : ℝ}
    {D T B E : SignedPoint} (I : Source q t D T B)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0)
    (he : e+x∈Icc 0 (7/10 : ℝ)) (j : Fin 4) (hj : j=2 ∨ j=3)
    (hsmall : positiveDESlack D.circle (B.a-1/2) e E j x≤1/1000) :
    positiveDEDerivative D.circle (B.a-1/2) e E j x< -(1/1250) := by
  rcases hj with rfl | rfl
  · have hh := I.lowMixedDerivative_negative hqU hx hnot he
    rw [SignedPoint.reflect_circle] at hh
    have h2 : lowMixedDerivative D.circle (B.a-1/2) e x< -(1/1250) :=
      hh.trans (by norm_num : -(3/50 : ℝ)< -(1/1250))
    simpa [positiveDEDerivative] using h2
  · have hgain := I.primary_gain hqU hx hnot
    have hrate : (E.a-1/2)*Real.cos (e+x)+(1/2+E.y)*Real.sin (e+x)<1249/1250 := by
      rcases hEr with ho | hc
      · have hDa : 211/250<(Dpath D.circle (B.a-1/2) x).a := by
          let J := I.atAngle hqU hx hnot
          have hh := J.H_sorted.2
          rw [abs_of_nonneg J.H_nonneg] at hh
          have hlow := (J.cuts hqU).2.2.2.1.trans_le hh
          rw [SignedPoint.reflect_circle] at hlow
          exact hlow
        have hshort : e+x<9/50 := by
          by_contra! hlarge
          have hm := outer_DE3_margin hqL hqU hEs hEy ho hDa ⟨hlarge,he.2⟩
          rw [← positiveDESlack_actual E 3 (Or.inr rfl) he] at hm
          linarith
        have ha := (SignedPoint.coordinate_bounds hEs hEcore hEc hqU).2.1
        have hh := short_original_e_rate ha (neg_nonneg.mpr hEy)
          (show e+x∈Icc 0 (21/100 : ℝ) from ⟨he.1,by linarith⟩)
        simpa using hh
      · exact (core_original_e_rate hEs hc hEy he).trans (by norm_num)
    simp only [positiveDEDerivative,show (3:Fin 4)≠2 by decide,ite_false,
      highMixedDerivative,SignedPoint.reflect]
    linarith


/-- With E fixed, actual BT2 or actual DE alignment is reached with strict
original-DE slack. The proof takes the first geometric hard contact and
uses the small-slack barrier, without assuming a feasible motion path. -/
theorem Source.positive_de_stop_full {q t e : ℝ} {D T B E : SignedPoint}
    (I : Source q t D T B) (hqL : qLow≤q) (hqU : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (he : e+t∈Ioc 0 (7/10 : ℝ)) (j : Fin 4) (hj : j=2 ∨ j=3)
    (hf : quarterFeasible D E (e+t) j) : Nonempty (PositiveDEStop I E e j) := by
  obtain ⟨O⟩ := I.first_hard hqU
  let P := B.a-1/2
  let r := max O.angle (-e)
  let L := positiveDESlack D.circle P e E j
  let F : ℝ → ℝ := fun x => L x-(t-x)/4000
  let dF : ℝ → ℝ := fun x => positiveDEDerivative D.circle P e E j x+1/4000
  have hrO : O.angle≤r := le_max_left _ _
  have hre : -e≤r := le_max_right _ _
  have hr0 : 0≤r := O.angle_mem.1.trans hrO
  have hrt : r<t := max_lt_iff.mpr ⟨O.angle_mem.2,by linarith [he.1]⟩
  have heR : e+r∈Icc 0 (7/10 : ℝ) := by constructor <;> linarith [he.2]
  have heX (x : ℝ) (hx : x∈Icc r t) : e+x∈Icc 0 (7/10 : ℝ) := by
    constructor <;> linarith [hx.1,hx.2,he.2]
  have hterminal : quarterFeasible (point P r) B.reflect (-r) 0 ∨ e+r=0 := by
    rcases le_total O.angle (-e) with hle | hle
    · right
      dsimp [r]
      rw [max_eq_right hle]
      ring
    · left
      have hr : r=O.angle := max_eq_left hle
      rw [hr]
      exact O.hard
  have hderiv (x : ℝ) (hx : x∈Icc r t) : HasDerivAt F (dF x) x := by
    have hx0 : 0≤x := hr0.trans hx.1
    have hc : Real.cos x≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hx0]; exact hx.2.trans I.tilt_cap)).ne'
    have hg := I.path_geometry hqU ⟨hx0,hx.2⟩
    have hL := positiveDESlack_hasDerivAt (qD := D.circle) (P := P) (e := e) E j hc
      (by have h6 := hg.2.2.2.2.2.2; rw [SignedPoint.reflect_circle] at h6; exact h6)
    exact (hL.sub (((hasDerivAt_id x).const_sub t).div_const 4000)).congr_deriv
      (by dsimp only [dF]; ring)
  have hcont : ContinuousOn F (Icc r t) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hFt : 0≤F t := by
    have hraw := (quarterFeasible_reflect D E (e+t) j).2 hf
    have hj' : reflectedOwner j=0 ∨ reflectedOwner j=1 := by
      rcases hj with rfl | rfl <;> norm_num [reflectedOwner]
    have hnormalized := (I.normalize hqU).retains_mixed hqU
      (by rw [abs_of_pos he.1]; exact he.2) hj' hraw
    rw [(I.normalize hqU).H_eq] at hnormalized
    have hback : quarterFeasible (Dpath D.circle P t) E (e+t) j := by
      apply (quarterFeasible_reflect (Dpath D.circle P t) E (e+t) j).1
      simp only [Dpath,SignedPoint.reflect_reflect]
      simp only [SignedPoint.reflect_circle] at hnormalized
      exact hnormalized
    have hLstart : 0≤L t := by
      dsimp [L]
      rw [positiveDESlack_actual E j hj ⟨he.1.le,he.2⟩]
      exact sub_nonneg.mpr hback
    simpa [F] using hLstart
  have hbarrier : 0≤F r := left_sublevel_barrier hrt hcont
    (fun x hx => hderiv x (Ioo_subset_Icc_self hx))
    (fun x hx hFx => by
      have hx0 : 0<x := hr0.trans_lt hx.1
      have hnot := O.later_unavailable ⟨hrO.trans_lt hx.1,hx.2.le⟩
      have hsmall : L x≤1/1000 := by
        dsimp [F] at hFx
        linarith [I.tilt_cap]
      have hh := I.positive_de_small_slack_derivative hqL hqU hEs hEc hEcore hEr hEy
        ⟨hx0,hx.2.le⟩ hnot (heX x (Ioo_subset_Icc_self hx)) j hj hsmall
      dsimp [dF,P]
      linarith) hFt
  have hstrict : 0<L r := by
    have hp : 0<(t-r)/4000 := div_pos (sub_pos.mpr hrt) (by norm_num)
    dsimp [F] at hbarrier
    linarith
  exact ⟨⟨r,⟨hr0,hrt⟩,heR,hstrict,hterminal⟩⟩


end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
/-!
## Exhaustive original-E positions in the one-negative BT construction

The original E may lie below, at or above D, and its EH error may have either sign. The same-q
construction returns either a hard endpoint with a strict loss on the original D or a negative-T
barrier state (`Source.full_aligned_endpoint_or_barrier`,
`Source.one_negative_endpoint_or_barrier`). H is arbitrary, and the true-core hypotheses are
kept through every stage.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap

theorem Source.full_aligned_endpoint_or_barrier {q t h : ℝ} {D T B E H : SignedPoint}
    (I : Source q t D T B) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q)
    (hEs : E.Sorted) (hEr : E.Boundary q) (hEy : E.y≤0)
    (hspan : h+t∈Ioc 0 (11/50 : ℝ))
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E 0 jDE) (hEH : quarterFeasible E H (h+t) jEH) :
    Nonempty (LocalEndpoint I E H (-t) h jDE jEH) ∨
      Nonempty (LocalBarrier I E H (-t) h jDE jEH) := by
  obtain ⟨kind,J⟩ := FullE.arcSource_of_boundary hEs hEy hEr
  obtain ⟨O⟩ := I.full_coupled_stop J hqL hqU hHs hHcore hHc hspan
    jDE jEH hjDE hjEH hDE hEH
  by_cases hhard : quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0
  · exact Or.inl (O.hard_endpoint J hqL hqU hjDE hjEH hDE hhard)
  · exact Or.inr ⟨O.local_barrier J hqL hqU hjDE hjEH hhard⟩

theorem Source.one_negative_endpoint_or_barrier {q t e h : ℝ} {D T B E H : SignedPoint}
    (I : Source q t D T B) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q) (hHy : 0≤H.y)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (hDEwidth : |e+t|≤7/10) (hEHwidth : |h-e|≤7/10)
    (hspan : h+t∈Ioc 0 (11/50 : ℝ))
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E (e+t) jDE) (hEH : quarterFeasible E H (h-e) jEH) :
    Nonempty (LocalEndpoint I E H e h jDE jEH) ∨
      Nonempty (LocalBarrier I E H e h jDE jEH) := by
  have hDs : D.Sorted := by simpa using I.H_sorted
  have hcuts := I.cuts hqU
  have hDy : 211/250< -D.y := hcuts.2.2.2.1
  have hDa : D.a<1 := hcuts.2.2.2.2.1
  rcases lt_trichotomy (e+t) 0 with hbelow | haligned | habove
  · let n := -(e+t)
    have hn : n∈Ioc 0 (7/10 : ℝ) := by
      dsimp [n]
      constructor <;> linarith [(abs_le.mp hDEwidth).1]
    have hp : h-e∈Ioc 0 (7/10 : ℝ) := by
      constructor <;> linarith [hspan.1,(abs_le.mp hEHwidth).2]
    have hnp : n<h-e := by dsimp [n]; linarith [hspan.1]
    obtain ⟨O⟩ := FullE.alignment_endpoint_of_order hqL hqU hHs hHcore hHc hHy
      hDy hDs hDa hEs hEy hEr hn hp hnp jDE jEH hjDE hjEH
      (by simpa [n] using hDE) hEH
    have hEHaligned : quarterFeasible O.point H (h+t) jEH := by
      have heq : (h-e)-n=h+t := by dsimp [n]; ring
      simpa only [heq] using O.EH
    rcases I.full_aligned_endpoint_or_barrier hqL hqU hHs hHcore hHc
      O.sorted O.radial O.nonpos hspan jDE jEH hjDE hjEH O.DE hEHaligned with hK | hK
    · obtain ⟨K⟩ := hK
      exact Or.inl ⟨K.prepend_E_motion (by linarith) O.circle_nonincrease⟩
    · obtain ⟨K⟩ := hK
      exact Or.inr ⟨K.prepend_E_motion (by linarith) O.circle_nonincrease⟩
  · have heq : e= -t := by linarith
    have hDEaligned : quarterFeasible D E 0 jDE := by simpa [haligned] using hDE
    have hEHaligned : quarterFeasible E H (h+t) jEH := by simpa [heq] using hEH
    simpa only [heq] using I.full_aligned_endpoint_or_barrier hqL hqU hHs hHcore hHc
      hEs hEr hEy hspan jDE jEH hjDE hjEH hDEaligned hEHaligned
  · have hd : e+t∈Ioc 0 (7/10 : ℝ) := ⟨habove,(abs_le.mp hDEwidth).2⟩
    obtain ⟨O⟩ := I.positive_de_stop_full hqL hqU hEs hEc hEcore hEr hEy hd jDE hjDE hDE
    by_cases hhard : quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0
    · exact Or.inl (O.hard_endpoint hqU hEs hEc hEcore hEr hEy hjDE hEH hhard)
    · by_cases hbad : h+O.angle≤0
      · exact Or.inr ⟨O.local_barrier hqU hEs hEc hEcore hEr hEy hjDE hEH hhard hbad⟩
      · have hal : e+O.angle=0 := O.terminal.resolve_left hhard
        have hmpos : 0<O.angle := by
          apply lt_of_le_of_ne O.angle_mem.1
          intro hzero
          have hprimary : quarterFeasible (point (B.a-1/2) 0) B.reflect 0 1 := by
            have h := (actual_primary_contact
              (show B.reflect.a=(B.a-1/2)+1/2 by dsimp [SignedPoint.reflect]; ring)
              (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).ge
            rw [neg_zero] at h
            exact h
          apply hhard
          rw [← hzero,neg_zero]
          exact (quarter_low_tie (point (B.a-1/2) 0) B.reflect).2 hprimary
        let D₁ := Dpath D.circle (B.a-1/2) O.angle
        let T₁ := Tpath (B.a-1/2) O.angle
        have hg := I.path_data hqU O.angle_mem
        have I₁ : Source q O.angle D₁ T₁ B := by
          have h := I.atAngle hqU ⟨hmpos,O.angle_mem.2.le⟩ hhard
          simp only [Source,D₁,T₁,Dpath,Tpath,SignedPoint.reflect_reflect]
          rw [SignedPoint.reflect_circle] at h
          exact h
        have hDEaligned : quarterFeasible D₁ E 0 jDE := by
          have hh := O.mixed_strict.le
          rw [positiveDESlack_actual E jDE hjDE
            ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩] at hh
          have h := sub_nonneg.mp hh
          rw [hal] at h
          exact h
        have heq : e= -O.angle := by linarith
        have hα : h+O.angle∈Ioc 0 (11/50 : ℝ) := by
          constructor <;> linarith [O.angle_mem.2,hspan.2]
        have hEHaligned : quarterFeasible E H (h+O.angle) jEH := by simpa [heq] using hEH
        rcases I₁.full_aligned_endpoint_or_barrier hqL hqU hHs hHcore hHc
          hEs hEr hEy hα jDE jEH hjDE hjEH hDEaligned hEHaligned with hK | hK
        · obtain ⟨K⟩ := hK
          have K' : LocalEndpoint I₁ E H e h jDE jEH := by rw [← heq] at K; exact K
          exact Or.inl ⟨LocalEndpoint.prepend_contact I K' O.angle_mem.2 hg.D_circle hg.D_tangent.le⟩
        · obtain ⟨K⟩ := hK
          have K' : LocalBarrier I₁ E H e h jDE jEH := by rw [← heq] at K; exact K
          exact Or.inr ⟨LocalBarrier.prepend_contact I K' O.angle_mem.2 hg.D_circle⟩

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
/-!
## Same-radius one-negative primary entry, with the exact remaining barrier

Every original E position is joined to an actual
necessary, ordered seven-cycle. The successful alternative has GA0 and
BT2 with strict original-D circle loss and H/G/A/B unchanged. The other
alternative is a complete original-witness negative-T state with H≤D,
ready for the separate anchor-order exclusion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace DirectNegativeT

structure HardTEntry (q : ℝ) (C : SignedCycle) (w : C.Witnesses) where
  input : SignedCycle.HardInput q
  ordered : input.cycle.Ordered
  TD_aligned : input.cycle.theta T=input.cycle.theta D
  D_advance : C.theta D< input.cycle.theta D
  D_below_B : input.cycle.theta D≤C.theta B
  original_TD : input.cycle.Feasible T (w.owner T)
  original_DE : input.cycle.Feasible D (w.owner D)
  original_EH : input.cycle.Feasible E (w.owner E)
  D_nondiagonal : |(input.cycle.point D).y|<(input.cycle.point D).a
  T_nondiagonal : |(input.cycle.point T).y|<(input.cycle.point T).a
  D_circle_loss : (input.cycle.point D).circle<(C.point D).circle
  anchor_nonincrease : AnchorNonincrease C input.cycle
  strict_anchor_loss : StrictAnchorLoss C input.cycle
  unchanged : ∀ i, i≠D → i≠T → i≠E →
    input.cycle.point i=C.point i ∧ input.cycle.theta i=C.theta i

def LocalEndpoint.hardTEntry {q : ℝ} {C : SignedCycle}
    {I : Source q (C.theta B-C.theta D) (C.point D) (C.point T) (C.point B)}
    (w : C.Witnesses)
    (O : LocalEndpoint I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (hz : C.ZeroSignImplications w) (hGA : C.Feasible G 0) : HardTEntry q C w where
  input := O.hardInput w hn ha hz hGA
  ordered := O.ordered w hn hq ha hz
  TD_aligned := by simp [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
  D_advance := by
    have hh : C.theta D<C.theta B-O.angle := by linarith [O.angle_mem.2]
    simpa [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E] using hh
  D_below_B := by
    have hh : C.theta B-O.angle≤C.theta B := by linarith [O.angle_mem.1]
    simpa [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E] using hh
  original_TD := (O.witnesses w).feasible T
  original_DE := (O.witnesses w).feasible D
  original_EH := (O.witnesses w).feasible E
  D_nondiagonal := by
    simpa [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
      using O.D_nondiagonal
  T_nondiagonal := by
    simpa [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
      using O.T_nondiagonal
  D_circle_loss := by
    simpa [LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
      using O.D_circle_loss
  anchor_nonincrease := O.anchor_nonincrease
  strict_anchor_loss := O.strict_anchor_loss
  unchanged := O.unchanged

/-- The only scalar span input is the original .22 upper bound. The
construction itself exposes any failure of positive H--D order as an
actual same-radius barrier, including a failure at the original state. -/
theorem one_negative_t_entry_of_span {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hqL : qLow≤q) (hqU : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0) (hrE : (C.point E).Boundary q)
    (hspan : C.theta H-C.theta D<11/50)
    (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3)
    (hnot : ¬C.Feasible B 2) (hGA : C.Feasible G 0) :
    Nonempty (HardTEntry q C w) ∨ Nonempty (NegativeTBarrier q) := by
  by_cases horder : C.theta D<C.theta H
  · let I := sourceOfCycle hn ha w halign ht hyT hBT hnot
    have hDEwidth : |(C.theta E-C.theta B)+(C.theta B-C.theta D)|≤7/10 := by
      rw [show (C.theta E-C.theta B)+(C.theta B-C.theta D)=C.theta E-C.theta D by ring]
      exact hn.spread E D
    have hEHwidth : |(C.theta H-C.theta B)-(C.theta E-C.theta B)|≤7/10 := by
      rw [show (C.theta H-C.theta B)-(C.theta E-C.theta B)=C.theta H-C.theta E by ring]
      exact hn.spread H E
    have hspan' : (C.theta H-C.theta B)+(C.theta B-C.theta D)∈Ioc 0 (11/50 : ℝ) := by
      constructor <;> linarith
    have hjDE : w.owner D=2 ∨ w.owner D=3 := by
      simpa [SignedCycle.normalOwners,D] using w.allowed D
    have hjEH : w.owner E=0 ∨ w.owner E=1 := by
      simpa [SignedCycle.normalOwners,E] using w.allowed E
    have hDE : quarterFeasible (C.point D) (C.point E)
        ((C.theta E-C.theta B)+(C.theta B-C.theta D)) (w.owner D) := by
      rw [show (C.theta E-C.theta B)+(C.theta B-C.theta D)=C.theta E-C.theta D by ring]
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        word,delta,next,D,E,quarterFeasible,sub_nonneg] using w.feasible D
    have hEH : quarterFeasible (C.point E) (C.point H)
        ((C.theta H-C.theta B)-(C.theta E-C.theta B)) (w.owner E) := by
      rw [show (C.theta H-C.theta B)-(C.theta E-C.theta B)=C.theta H-C.theta E by ring]
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
        word,delta,next,H,E,quarterFeasible,sub_nonneg] using w.feasible E
    rcases I.one_negative_endpoint_or_barrier hqL hqU
      (hn.sorted H) (hn.core H) (hn.contained H) ha.H_nonneg
      (hn.sorted E) (hn.contained E) (hn.core E) hrE hyE
      hDEwidth hEHwidth hspan' (w.owner D) (w.owner E) hjDE hjEH hDE hEH with hO | hO
    · obtain ⟨O⟩ := hO
      exact Or.inl ⟨O.hardTEntry w hn hqU ha hz hGA⟩
    · obtain ⟨O⟩ := hO
      exact Or.inr ⟨O.barrier w hn ha hz hGA⟩
  · exact Or.inr ⟨{
      cycle := C
      necessary := hn
      anchors_normal := ha
      E_nonpos := hyE
      witnesses := w
      zero_signs := hz
      GA_hard := hGA
      BT_secondary := hBT
      BT_unavailable := hnot
      TD_aligned := halign
      negative_BT := ht
      T_nonneg := hyT
      H_not_above := le_of_not_gt horder }⟩

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate

theorem NegativeTBarrier.false {q : ℝ} (I : NegativeTBarrier q) (hq : q≤qCap) : False := by
  have hh := SignedCycle.negative_BT_anchor_order hq I.necessary I.anchors_normal
    I.E_nonpos I.witnesses I.zero_signs I.TD_aligned I.negative_BT I.T_nonneg
    I.BT_secondary I.BT_unavailable I.GA_hard
  exact (not_lt_of_ge I.H_not_above) hh

namespace DirectNegativeT

/-- Fully constructive same-radius hard entry.  No span, H--D order,
near-H condition, mixed sign, or terminal exclusion is an input. -/
theorem one_negative_t_entry {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hqL : qLow≤q) (hqU : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0) (hrE : (C.point E).Boundary q)
    (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3)
    (hnot : ¬C.Feasible B 2) (hGA : C.Feasible G 0) :
    Nonempty (HardTEntry q C w) := by
  have hspan := AlignedNegative.opposite_aligned_negative_span hn hqU ha w
    halign ht hyT hBT hnot hGA
  rcases one_negative_t_entry_of_span hn hqL hqU ha w hz hyE hrE hspan
    halign ht hyT hBT hnot hGA with hentry | hI
  · exact hentry
  · obtain ⟨I⟩ := hI
    exact (I.false hqU).elim

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end
