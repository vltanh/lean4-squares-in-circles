module

public import SquaresInCircles.Eight.Words.One.NegativeAnchorCharge
public import SquaresInCircles.Eight.Owners.Stronger.EndpointBudget

/-!
# Eight squares: the sharper HG charge at the original signed source

Both weak HG owners are handled with the original endpoint circles, and the signed G tangent is
kept (`positive_zero`, `positive_HG_charge`). The short span uses the transverse corner floor and
the long span the full-circle support, which gives exactly the positive function
`OneNegativeAnchorCharge.f`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace OneNegativeHGCharge
open PositiveAngularEnvelope EndpointECharge EndpointBudgetScalars OneNegativeAnchorCharge

theorem point_remainder {P : SignedPoint} {v : ℝ}
    (hP : P.Sorted) (hc : P.circle≤qCap) (hv : v∈Icc 0 frameCap) :
    (P.a-1/2)*Real.sin v+(|P.y|+1/2)*(1-Real.cos v)≤p*v-OneNegativeAnchorCharge.f v := by
  by_cases hvh : v≤1/2
  · have hs := restricted_support
      (show 0≤P.a+1/2 by linarith [hP.1])
      (show 1/2≤|P.y|+1/2 by linarith [abs_nonneg P.y]) hc ⟨hv.1,hvh⟩
    rw [f_of_short hvh]
    dsimp only [short,positiveGain,OneNegativeAnchorCharge.k0] at hs ⊢
    linarith
  · have hs := circle_chord_support hc hv
    rw [f_of_long (lt_of_not_ge hvh)]
    dsimp only [long,OneNegativeAnchorCharge.R] at hs ⊢
    linarith

/-- A positive HG error yields the strict-excess charge for either original transverse owner,
for either sign of G. -/
theorem positive_zero {H G : SignedPoint} {v : ℝ}
    (hH : H.Sorted) (hG : G.Sorted)
    (hcH : H.circle≤qCap) (hcG : G.circle≤qCap)
    (hv : v∈Icc 0 frameCap)
    (hHG : zeroFeasible H G v 0 ∨ zeroFeasible H G v 2) :
    1+OneNegativeAnchorCharge.f v-p*v≤H.y-G.y := by
  have hw := edgeWidth_positive_formula hv
  have hcos : 0≤1-Real.cos v := by linarith [Real.cos_le_one v]
  rcases hHG with hHG | hHG
  · have hf : edgeWidth v≤H.y+G.a*Real.sin v-G.y*Real.cos v := by
      simpa [zeroFeasible,zeroProjection] using hHG
    have hsupport := point_remainder hG hcG hv
    have hsigned := mul_le_mul_of_nonneg_right (le_abs_self G.y) hcos
    rw [hw] at hf
    nlinarith
  · have hf : edgeWidth v≤H.a*Real.sin v+H.y*Real.cos v-G.y := by
      simpa [zeroFeasible,zeroProjection] using hHG
    have hsupport := point_remainder hH hcH hv
    have hsigned := mul_le_mul_of_nonneg_right (neg_le_abs H.y) hcos
    rw [hw] at hf
    nlinarith

end OneNegativeHGCharge

namespace SignedCycle
open Candidate EndpointBudgetScalars OneNegativeAnchorCharge

private theorem r60_feasible_zero {C : SignedCycle} {i : Vertex} (hw : Candidate.word i=0)
    (j : Fin 4) : C.Feasible i j ↔
      zeroFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,zeroFeasible,delta,sub_nonneg]

theorem positive_HG_charge {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (w : C.Witnesses)
    (hv : C.theta H≤C.theta G) :
    1+OneNegativeAnchorCharge.f (C.theta G-C.theta H)-p*(C.theta G-C.theta H)≤
      (C.point H).y-(C.point G).y := by
  have ho : w.owner H=0 ∨ w.owner H=2 := by
    simpa [normalOwners,H] using w.allowed H
  have hf : zeroFeasible (C.point H) (C.point G) (C.theta G-C.theta H) 0 ∨
      zeroFeasible (C.point H) (C.point G) (C.theta G-C.theta H) 2 := by
    have hw := (r60_feasible_zero (C := C) (i := H) (by decide) _).1 (w.feasible H)
    rw [show next H=G by decide] at hw
    rcases ho with ho | ho
    · left
      rwa [ho] at hw
    · right
      rwa [ho] at hw
  exact OneNegativeHGCharge.positive_zero (hC.sorted H) (hC.sorted G)
    ((hC.contained H).trans hq) ((hC.contained G).trans hq)
    ⟨sub_nonneg.mpr hv,(le_abs_self _).trans (hC.spread G H)⟩ hf

/-- The original H/D/E budget plus the original positive HG charge and aligned TD. The
nonnegative H--D deficit cancels exactly. -/
theorem positive_one_negative_excess {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (ha : C.NormalAnchors)
    (hyE : (C.point E).y≤0) (w : C.Witnesses)
    (halign : C.theta T=C.theta D) (hHG : C.theta H≤C.theta G) :
    S0+OneNegativeAnchorCharge.f (C.theta G-C.theta H)+(27/160000 : ℝ)<
      -(C.point G).y+(C.point T).y+p*(C.theta G-C.theta D) := by
  have hHGcharge := positive_HG_charge hq hC w hHG
  have hbudget := stronger_endpoint_budget hq hC ha hyE w
  have ho : w.owner T=0 ∨ w.owner T=2 := by
    simpa [normalOwners,T] using w.allowed T
  have hTD : 1≤(C.point T).y-(C.point D).y := by
    have hw := (r60_feasible_zero (C := C) (i := T) (by decide) _).1 (w.feasible T)
    rw [show next T=D by decide,halign,sub_self] at hw
    simp only [zeroFeasible,zeroProjection_aligned,edgeWidth_zero] at hw
    rcases ho with ho | ho <;> rw [ho] at hw <;> simpa using hw
  dsimp [StrongerEndpointScalars.charge,StrongerEndpointScalars.epsilon,p] at *
  linarith

end SignedCycle
end SquaresInCircles.Eight
