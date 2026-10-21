module

public import SquaresInCircles.Eight.TableFree.OneNegativeAnchorCharge
public import SquaresInCircles.Eight.TableFree.StrongerEndpointBudget
public import SquaresInCircles.Eight.TableFree.ZeroSignedCharge

/-!
# The sharper HG charge at the original signed source

Uncompiled source draft.  Both weak HG owners are handled using the
original endpoint circles.  The signed G tangent is retained.  The short
span uses the transverse corner floor and the long span uses full-circle
support, exactly matching the independently proved positive function f.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace OneNegativeHGCharge
open PositiveAngularEnvelope EndpointECharge EndpointBudgetScalars OneNegativeAnchorCharge

theorem point_remainder {P : SignedPoint} {v : ℝ}
    (hP : P.Sorted) (hc : P.circle≤qCap) (hv : v∈Icc 0 frameCap) :
    (P.a-1/2)*Real.sin v+(|P.y|+1/2)*(1-Real.cos v)≤p*v-f v := by
  by_cases hvh : v≤1/2
  · have hs := restricted_support
      (show 0≤P.a+1/2 by linarith [hP.1])
      (show 1/2≤|P.y|+1/2 by linarith [abs_nonneg P.y]) hc ⟨hv.1,hvh⟩
    rw [f_of_short hvh]
    dsimp [short,positiveGain]
    linarith
  · have hs := circle_chord_support hc hv
    rw [f_of_long (lt_of_not_ge hvh)]
    dsimp [long]
    linarith

/-- A positive HG error yields the strict-excess charge for either
original transverse owner, without any hypothesis on the sign of G. -/
theorem positive_zero {H G : SignedPoint} {v : ℝ}
    (hH : H.Sorted) (hG : G.Sorted)
    (hcH : H.circle≤qCap) (hcG : G.circle≤qCap)
    (hv : v∈Icc 0 frameCap)
    (hHG : zeroFeasible H G v 0 ∨ zeroFeasible H G v 2) :
    1+f v-p*v≤H.y-G.y := by
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

theorem positive_HG_charge {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (w : C.Witnesses)
    (hv : C.theta H≤C.theta G) :
    1+f (C.theta G-C.theta H)-p*(C.theta G-C.theta H)≤
      (C.point H).y-(C.point G).y := by
  have ho : w.owner H=0 ∨ w.owner H=2 := by
    simpa [normalOwners,H] using w.allowed H
  have hf : zeroFeasible (C.point H) (C.point G) (C.theta G-C.theta H) 0 ∨
      zeroFeasible (C.point H) (C.point G) (C.theta G-C.theta H) 2 := by
    have hw := w.feasible H
    rcases ho with ho | ho
    · left
      simpa [Feasible,slack,edge,delta,next,word,H,G,zeroFeasible,ho] using hw
    · right
      simpa [Feasible,slack,edge,delta,next,word,H,G,zeroFeasible,ho] using hw
  exact OneNegativeHGCharge.positive_zero (hC.sorted H) (hC.sorted G)
    ((hC.contained H).trans hq) ((hC.contained G).trans hq)
    ⟨sub_nonneg.mpr hv,(le_abs_self _).trans (hC.spread G H)⟩ hf

/-- Actual original H/D/E budget plus the original positive HG charge
and aligned TD.  The nonnegative H--D deficit cancels exactly. -/
theorem positive_one_negative_excess {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (ha : C.NormalAnchors)
    (hyE : (C.point E).y≤0) (w : C.Witnesses)
    (halign : C.theta T=C.theta D) (hHG : C.theta H≤C.theta G) :
    S0+f (C.theta G-C.theta H)+(27/160000 : ℝ)<
      -(C.point G).y+(C.point T).y+p*(C.theta G-C.theta D) := by
  have hHGcharge := positive_HG_charge hq hC w hHG
  have hbudget := stronger_endpoint_budget hq hC ha hyE w
  have ho : w.owner T=0 ∨ w.owner T=2 := by
    simpa [normalOwners,T] using w.allowed T
  have hTD : 1≤(C.point T).y-(C.point D).y := by
    have hw := w.feasible T
    have hδ : delta C.theta T=0 := by
      simp only [delta,next,T]
      change C.theta D-C.theta T=0
      rw [halign]
      ring
    rcases ho with ho | ho <;>
      simpa [Feasible,slack,edge,word,next,T,D,hδ,zeroProjection,edgeWidth,ho] using hw
  dsimp [StrongerEndpointScalars.charge,StrongerEndpointScalars.epsilon,p] at *
  linarith

end SignedCycle
end SquaresInCircles.Eight.TableFree
