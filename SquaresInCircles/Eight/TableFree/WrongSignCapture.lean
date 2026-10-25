module

public import SquaresInCircles.Eight.TableFree.WrongSignCaptureGeometry
public import SquaresInCircles.Eight.TableFree.MiddleOrder

/-!
# The global strict small-wrong-sign capture at the original hard source

Uncompiled source draft.  Either intermediate sign beyond one tenth is
inconsistent with the same original outer budget.  The proof chooses
one admissible positive stress at the actual three-frame hull width,
then applies the complete analytic hull comparison.  Both original AB
owners are covered by local reflected reversal of the three equations.

No original state, circle, E sign, or selected outer witness is changed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace WrongSignCapture
open PositiveAngularEnvelope EndpointRotationPenalty EndpointBudgetScalars
open WrongSignCaptureScalars WrongSignCaptureGeometry

private theorem compressed {G A B T : SignedPoint} {alpha a b c x d v : ℝ}
    (hA : A.circle≤qCap) (hB : B.circle≤qCap) (hyA : 0≤A.y) (hyB : B.y≤0)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hratio : b/c∈Icc (13/20 : ℝ) (23/25)) (hweights : a+c=alpha+1)
    (hcorrection : -G.y+T.y≤ -a*G.y+c*T.y-(1-alpha)/10)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hv : |v|≤frameCap)
    (hs : |d+v|≤frameCap)
    (hGA : quarterFeasible G A x 0) (hAB : zeroFeasible A B d 0)
    (hBT : quarterFeasible B T v 2) :
    -G.y+T.y-EndpointRotationPenalty.charge*(x+d+v)≤angular alpha a b c x (d+v) := by
  have hcA : A.Contained (R^2) := by
    show A.circle≤R^2
    rw [R_sq]
    exact hA
  have hcB : B.Contained (R^2) := by
    show B.circle≤R^2
    rw [R_sq]
    exact hB
  have hraw := MiddlePhysicalStress.signed_three_zero R_nonneg hcA hcB hyA hyB
    ha.le hb.le hc.le hx hd hv hGA hAB hBT
  have hwidth := scaled_width hc hratio hd hv hs
  dsimp [angular,offset]
  linarith

/-- The original AB0 equations rule out either large wrong sign using
the same analytically certified pair of weights. -/
theorem actual_wrong_zero {G A B T : SignedPoint} {x d v : ℝ}
    (hA : A.circle≤qCap) (hB : B.circle≤qCap) (hyA : 0≤A.y) (hyB : B.y≤0)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hv : |v|≤frameCap)
    (hs : |d+v|≤frameCap) (ht : |x+d+v|≤frameCap) (hr : x+d+v≤0)
    (hGA : quarterFeasible G A x 0) (hAB : zeroFeasible A B d 0)
    (hBT : quarterFeasible B T v 2)
    (hwrong : (1/10 : ℝ)≤G.y ∨ T.y≤ -(1/10 : ℝ)) :
    -G.y+T.y-EndpointRotationPenalty.charge*(x+d+v)<S0+(1/10000 : ℝ) := by
  have htotal : |x+(d+v)|≤frameCap := by simpa only [add_assoc] using ht
  obtain ⟨alpha,b,hadm,hleft,hright⟩ := angular_bounds hx hs htotal
    (show x+(d+v)≤0 by linarith)
  obtain ⟨ha,hb,_,_,hratio⟩ := admissible_domains hadm
  have halpha : 0≤1-alpha := by linarith [hadm.1.2]
  rcases hwrong with hG | hT
  · have hm := mul_le_mul_of_nonneg_left (show -G.y≤ -(1/10 : ℝ) by linarith) halpha
    have hcorrection : -G.y+T.y≤ -alpha*G.y+1*T.y-(1-alpha)/10 := by nlinarith
    have hstress := compressed hA hB hyA hyB ha hb (show (0:ℝ)<1 by norm_num)
      (by simpa using hadm.2.1) (by ring : alpha+1=alpha+1) hcorrection
      hx hd hv hs hGA hAB hBT
    exact hstress.trans_lt (hleft.trans radius_reserves.2.2)
  · have hm := mul_le_mul_of_nonneg_left hT halpha
    have hcorrection : -G.y+T.y≤ -1*G.y+alpha*T.y-(1-alpha)/10 := by nlinarith
    have hstress := compressed hA hB hyA hyB (show (0:ℝ)<1 by norm_num) hb ha
      hratio (by ring : 1+alpha=alpha+1) hcorrection
      hx hd hv hs hGA hAB hBT
    exact hstress.trans_lt (hright.trans radius_reserves.2.2)

/-- AB2 is a local reflected reversal of the original equations.  The
wrong-sign alternative is exchanged and the signed sum is unchanged. -/
theorem actual_wrong_middle {G A B T : SignedPoint} {x d v : ℝ}
    (hA : A.circle≤qCap) (hB : B.circle≤qCap) (hyA : 0≤A.y) (hyB : B.y≤0)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hv : |v|≤frameCap)
    (hs : |d+v|≤frameCap) (hs' : |x+d|≤frameCap)
    (ht : |x+d+v|≤frameCap) (hr : x+d+v≤0)
    (hGA : quarterFeasible G A x 0)
    (hAB : zeroFeasible A B d 0 ∨ zeroFeasible A B d 2)
    (hBT : quarterFeasible B T v 2)
    (hwrong : (1/10 : ℝ)≤G.y ∨ T.y≤ -(1/10 : ℝ)) :
    -G.y+T.y-EndpointRotationPenalty.charge*(x+d+v)<S0+(1/10000 : ℝ) := by
  rcases hAB with hAB | hAB
  · exact actual_wrong_zero hA hB hyA hyB hx hd hv hs ht hr hGA hAB hBT hwrong
  · have hGA' : quarterFeasible T.reflect B.reflect v 0 := by
      simpa [reflectedOwner] using (quarterFeasible_reflect B T v 2).2 hBT
    have hAB' : zeroFeasible B.reflect A.reflect d 0 := by
      simpa [reflectedOwner] using (zeroFeasible_reflect A B d 2).2 hAB
    have hBT' : quarterFeasible A.reflect G.reflect x 2 := by
      simpa [reflectedOwner] using (quarterFeasible_reflect G A x 0).2 hGA
    have hwrong' : (1/10 : ℝ)≤T.reflect.y ∨ G.reflect.y≤ -(1/10 : ℝ) := by
      rcases hwrong with h | h
      · right
        dsimp [SignedPoint.reflect]
        linarith
      · left
        dsimp [SignedPoint.reflect]
        linarith
    have htotal : |v+d+x|≤frameCap := by
      convert ht using 2
      ring
    have h := actual_wrong_zero
      (show B.reflect.circle≤qCap by simpa using hB)
      (show A.reflect.circle≤qCap by simpa using hA)
      (show 0≤B.reflect.y by simpa [SignedPoint.reflect] using neg_nonneg.mpr hyB)
      (show A.reflect.y≤0 by simpa [SignedPoint.reflect] using neg_nonpos.mpr hyA)
      hv hd hx (by simpa only [add_comm] using hs') htotal (by linarith : v+d+x≤0)
      hGA' hAB' hBT' hwrong'
    simp only [SignedPoint.reflect,neg_neg] at h
    linarith

end WrongSignCapture

namespace SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars

theorem wrong_middle_bound {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (w : C.Witnesses) (hGA : C.Feasible G 0) (hBT : C.Feasible B 2)
    (hGT : C.theta T≤C.theta G)
    (hwrong : (1/10 : ℝ)≤(C.point G).y ∨ (C.point T).y≤ -(1/10 : ℝ)) :
    -(C.point G).y+(C.point T).y+EndpointRotationPenalty.charge*(C.theta G-C.theta T)<S0+(1/10000 : ℝ) := by
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
      rw [ho] at hw
      simpa [Feasible,slack,edge,delta,next,word,A,B,zeroFeasible] using hw
    · right
      rw [ho] at hw
      simpa [Feasible,slack,edge,delta,next,word,A,B,zeroFeasible] using hw
  have hs : |(C.theta B-C.theta A)+(C.theta T-C.theta B)|≤frameCap := by
    convert hC.spread T A using 2
    ring
  have hs' : |(C.theta A-C.theta G)+(C.theta B-C.theta A)|≤frameCap := by
    convert hC.spread B G using 2
    ring
  have ht : |(C.theta A-C.theta G)+(C.theta B-C.theta A)+
      (C.theta T-C.theta B)|≤frameCap := by
    convert hC.spread T G using 2
    ring
  have h := WrongSignCapture.actual_wrong_middle ((hC.contained A).trans hq)
    ((hC.contained B).trans hq) hn.A_nonneg hn.B_nonpos
    (hC.spread A G) (hC.spread B A) (hC.spread T B) hs hs' ht
    (show (C.theta A-C.theta G)+(C.theta B-C.theta A)+
      (C.theta T-C.theta B)≤0 by linarith) hga hab hbt hwrong
  dsimp [EndpointRotationPenalty.charge] at h ⊢
  linarith

/-- Both strict one-tenth sign bounds hold at the original hard source,
before AB alignment or any anchor change. -/
theorem small_intermediate_signs {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hyE : (C.point E).y≤0) (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hGA : C.Feasible G 0) (hBT : C.Feasible B 2) :
    (C.point G).y<(1/10 : ℝ) ∧ -(1/10 : ℝ)<(C.point T).y := by
  have horder := intermediate_order hq hC hn hyE w hz hGA hBT
  obtain ⟨hHG,hTD⟩ := signed_outer_charges hq hC hn w hz
  have hend := endpoint_budget hq hC hn hyE w
  have hbudget : S0+epsilon< -(C.point G).y+(C.point T).y+
      EndpointRotationPenalty.charge*(C.theta G-C.theta T) := by
    dsimp [EndpointRotationPenalty.charge] at hHG hTD hend ⊢
    linarith
  have hfalse (hw : (1/10 : ℝ)≤(C.point G).y ∨ (C.point T).y≤ -(1/10 : ℝ)) : False := by
    have hsmall := wrong_middle_bound hq hC hn w hGA hBT horder.le hw
    dsimp [epsilon] at hbudget
    linarith
  constructor
  · by_contra! h
    exact hfalse (Or.inl h)
  · by_contra! h
    exact hfalse (Or.inr h)

theorem HardInput.small_intermediate_signs {q : ℝ} (I : HardInput q) (hq : q≤qCap) :
    (I.cycle.point G).y<(1/10 : ℝ) ∧ -(1/10 : ℝ)<(I.cycle.point T).y := by
  exact SignedCycle.small_intermediate_signs hq I.necessary I.anchors_normal I.E_nonpos I.witnesses
    I.zero_signs I.GA_hard I.BT_hard

end SignedCycle
end SquaresInCircles.Eight.TableFree
