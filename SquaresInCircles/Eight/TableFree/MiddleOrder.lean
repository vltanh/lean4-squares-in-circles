module

public import SquaresInCircles.Eight.TableFree.MiddleOrderScalar
public import SquaresInCircles.Eight.TableFree.MiddleOrderWidth
public import SquaresInCircles.Eight.TableFree.ZeroSignedCharge

/-!
# Strict intermediate frame order at the unchanged hard source

Uncompiled source draft.  A fixed positive sum of the three actual middle
contacts bounds the original signed quantity `-yG + yT`.  The two signed
outer charges and the strict all-mixed H/D/E budget then exclude every
frame order with T at or above G.  All source points and selected weak
owners are retained, including AB ties and either intermediate sign.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace MiddleOrder
open PositiveAngularEnvelope EndpointBudgetScalars

theorem angular_bound {x s : ℝ}
    (hx : |x|≤frameCap) (hs : |s|≤frameCap) (hr : 0≤x+s) :
    Real.sin x-psi x+Real.sin s-MiddleOrderWidth.width MiddleOrderScalar.weight s≤
      (3/4)*(x+s) := by
  have hl : MiddleOrderScalar.weight∈Icc (7/12 : ℝ) (3/5) :=
    ⟨MiddleOrderScalar.weight_bounds.1.le,MiddleOrderScalar.weight_bounds.2.le⟩
  by_cases hs0 : 0≤s
  · rw [MiddleOrderWidth.width,if_pos hs0]
    exact MiddleOrderScalar.positive_sector hl hx ⟨hs0,(le_abs_self s).trans hs⟩ hr
  · rw [MiddleOrderWidth.width,if_neg hs0]
    exact MiddleOrderScalar.negative_sector hx ⟨by linarith,(neg_le_abs s).trans hs⟩ hr

theorem actual_zero {G A B T : SignedPoint} {x d v : ℝ}
    (hA : A.circle≤qCap) (hB : B.circle≤qCap)
    (hyA : 0≤A.y) (hyB : B.y≤0)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hv : |v|≤frameCap)
    (hs : |d+v|≤frameCap) (hr : 0≤x+d+v)
    (hGA : quarterFeasible G A x 0) (hAB : zeroFeasible A B d 0)
    (hBT : quarterFeasible B T v 2) :
    -G.y+T.y≤S0+(3/4)*(x+d+v) := by
  have hraw := MiddleOrderScalar.raw_zero hA hB hyA hyB hx hd hv hs hGA hAB hBT
  have hl : MiddleOrderScalar.weight∈Icc (7/12 : ℝ) (3/5) :=
    ⟨MiddleOrderScalar.weight_bounds.1.le,MiddleOrderScalar.weight_bounds.2.le⟩
  have hwidth := MiddleOrderWidth.signed_width hl hd hv hs
  have hangle := angular_bound hx hs (show 0≤x+(d+v) by linarith)
  linarith

/-- Local reflected reversal changes AB2 to AB0 and keeps the signed
G/T sum and total G--T frame difference exactly unchanged. -/
theorem actual_middle {G A B T : SignedPoint} {x d v : ℝ}
    (hA : A.circle≤qCap) (hB : B.circle≤qCap)
    (hyA : 0≤A.y) (hyB : B.y≤0)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hv : |v|≤frameCap)
    (hs : |d+v|≤frameCap) (hs' : |x+d|≤frameCap) (hr : 0≤x+d+v)
    (hGA : quarterFeasible G A x 0)
    (hAB : zeroFeasible A B d 0 ∨ zeroFeasible A B d 2)
    (hBT : quarterFeasible B T v 2) :
    -G.y+T.y≤S0+(3/4)*(x+d+v) := by
  rcases hAB with hAB | hAB
  · exact actual_zero hA hB hyA hyB hx hd hv hs hr hGA hAB hBT
  · have hGA' : quarterFeasible T.reflect B.reflect v 0 := by
      simpa [reflectedOwner] using (quarterFeasible_reflect B T v 2).2 hBT
    have hAB' : zeroFeasible B.reflect A.reflect d 0 := by
      simpa [reflectedOwner] using (zeroFeasible_reflect A B d 2).2 hAB
    have hBT' : quarterFeasible A.reflect G.reflect x 2 := by
      simpa [reflectedOwner] using (quarterFeasible_reflect G A x 0).2 hGA
    have h := actual_zero
      (show B.reflect.circle≤qCap by simpa using hB)
      (show A.reflect.circle≤qCap by simpa using hA)
      (show 0≤B.reflect.y by simpa [SignedPoint.reflect] using neg_nonneg.mpr hyB)
      (show A.reflect.y≤0 by simpa [SignedPoint.reflect] using neg_nonpos.mpr hyA)
      hv hd hx (by simpa only [add_comm] using hs') (by linarith : 0≤v+d+x)
      hGA' hAB' hBT'
    simp only [SignedPoint.reflect,neg_neg] at h
    linarith

end MiddleOrder

namespace SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars

theorem middle_reverse_order_bound {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (w : C.Witnesses) (hGA : C.Feasible G 0) (hBT : C.Feasible B 2)
    (hGT : C.theta G≤C.theta T) :
    -(C.point G).y+(C.point T).y≤S0+(3/4)*(C.theta T-C.theta G) := by
  have howner : w.owner A=0 ∨ w.owner A=2 := by
    simpa [normalOwners,A] using w.allowed A
  have hga : quarterFeasible (C.point G) (C.point A) (C.theta A-C.theta G) 0 := by
    simpa [Feasible,slack,edge,delta,next,word,G,A,quarterFeasible] using hGA
  have hbt : quarterFeasible (C.point B) (C.point T) (C.theta T-C.theta B) 2 := by
    simpa [Feasible,slack,edge,delta,next,word,B,T,quarterFeasible] using hBT
  have hab : zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) 0 ∨
      zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) 2 := by
    have hw := w.feasible A
    rcases howner with ho | ho
    · left
      simpa [Feasible,slack,edge,delta,next,word,A,B,zeroFeasible,ho] using hw
    · right
      simpa [Feasible,slack,edge,delta,next,word,A,B,zeroFeasible,ho] using hw
  have hs : |(C.theta B-C.theta A)+(C.theta T-C.theta B)|≤frameCap := by
    convert hC.spread T A using 1 <;> congr 1 <;> ring
  have hs' : |(C.theta A-C.theta G)+(C.theta B-C.theta A)|≤frameCap := by
    convert hC.spread B G using 1 <;> congr 1 <;> ring
  have h := MiddleOrder.actual_middle ((hC.contained A).trans hq) ((hC.contained B).trans hq)
    hn.A_nonneg hn.B_nonpos (hC.spread A G) (hC.spread B A) (hC.spread T B) hs hs'
    (show 0≤(C.theta A-C.theta G)+(C.theta B-C.theta A)+(C.theta T-C.theta B) by linarith)
    hga hab hbt
  simpa only [show (C.theta A-C.theta G)+(C.theta B-C.theta A)+
    (C.theta T-C.theta B)=C.theta T-C.theta G by ring] using h

/-- Original necessary hard-owner geometry forces strict intermediate
order before either intermediate tangent sign has been corrected. -/
theorem intermediate_order {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hyE : (C.point E).y≤0) (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hGA : C.Feasible G 0) (hBT : C.Feasible B 2) :
    C.theta T<C.theta G := by
  by_contra! hGT
  obtain ⟨hHG,hTD⟩ := signed_outer_charges hq hC hn w hz
  have hmiddle := middle_reverse_order_bound hq hC hn w hGA hBT hGT
  have hbudget := endpoint_budget hq hC hn hyE w
  dsimp [charge,epsilon] at hHG hTD hbudget
  linarith

theorem HardInput.intermediate_order {q : ℝ} (I : HardInput q) (hq : q≤qCap) :
    I.cycle.theta T<I.cycle.theta G :=
  intermediate_order hq I.necessary I.anchors_normal I.E_nonpos I.witnesses
    I.zero_signs I.GA_hard I.BT_hard

end SignedCycle
end SquaresInCircles.Eight.TableFree
