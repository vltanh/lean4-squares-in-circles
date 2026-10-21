module

public import SquaresInCircles.Eight.TableFree.SmallCancelingConstruction
public import SquaresInCircles.Eight.TableFree.CrossedSmallGeometry
public import SquaresInCircles.Eight.TableFree.CrossedGACycle
public import SquaresInCircles.Eight.TableFree.SmallIntermediateSigns

/-!
# The small crossed HG2 branch on the actual hard source

Uncompiled source draft.  The opposite normal sign follows from its
larger tangent.  The two actual middle circles and hard axes prove the
full-angle capture, and the original-circle composite constructs the
new HG0/GA0 data.  Applying the already proved small HG0 capture to that
actual descendant yields the small common crossing at the source q.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars

theorem HardOuterGeometry.crossed_HG2_small_full_angle {q : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hHG : I.cycle.Feasible H 2) : I.cycle.theta G-I.cycle.theta H<1/5 := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  let v := I.cycle.theta A-I.cycle.theta T
  let Y := (I.cycle.point A).y+1/2
  have hr : 0≤r := (sub_pos.mpr hHA).le
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hv : v∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hTA,(le_abs_self v).trans (I.necessary.spread A T)⟩
  have hspan : z+r≤frameCap := by
    have hh := (le_abs_self (I.cycle.theta G-I.cycle.theta H)).trans (I.necessary.spread G H)
    dsimp [z,r]
    linarith
  have hhi : z+r∈Icc 0 frameCap := ⟨by linarith [hz.1],hspan⟩
  have hY : Y∈Icc (167/200 : ℝ) 1 := by
    dsimp [Y]
    constructor <;> linarith [hsmall.1,hsmall.2]
  have hTy := I.large_middle_T_positive hq hAB hnorm hTA hAG
    (by linarith [hsmall.2])
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  have hGA' := SignedOppositeHardEnvelope.negative_hard_contact hz hGA
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
    rw [show -v=I.cycle.theta T-I.cycle.theta B by dsimp [v]; rw [←hAB]; ring]
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg] using I.BT_hard
  have hBTref : quarterFeasible (I.cycle.point T).reflect (I.cycle.point B).reflect (-v) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ (-v) 2).2 hBT
  have hBT' := SignedOppositeHardEnvelope.negative_hard_contact hv hBTref
  simp only [SignedPoint.reflect,neg_neg] at hBT'
  have hyB : -(I.cycle.point B).y+1/2=2-Y := by dsimp [Y]; linarith
  rw [hyB] at hBT'
  have hAcircle : ((I.cycle.point A).a+1/2)^2+Y^2≤qCap := by
    simpa [Y,SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg I.anchors_normal.A_nonneg]
      using (I.necessary.contained A).trans hq
  have hBcircle : ((I.cycle.point B).a+1/2)^2+(2-Y)^2≤qCap := by
    have hb := (I.necessary.contained B).trans hq
    dsimp [SignedPoint.Contained,SignedPoint.circle] at hb
    rw [abs_of_nonpos I.anchors_normal.B_nonpos,hyB] at hb
    exact hb
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) (z+r) 2 := by
    convert hHG using 1 <;>
      simp [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,z,r] <;> ring
  have hHGscalar : 1/2≤ -(I.cycle.point G).y+
      CrossedCancelingScalar.S (I.cycle.point H) (z+r) := by
    rw [zeroFeasible,edgeWidth_positive_formula hhi] at hHG'
    simp [zeroProjection] at hHG'
    dsimp [CrossedCancelingScalar.S]
    linarith
  have hTD := (signed_outer_charges hq I.necessary I.anchors_normal I.witnesses I.zero_signs).2
  have hep := I.endpoint_bound hq
  have hbudget : (I.cycle.point H).y-(I.cycle.point T).y+charge*(r-v)<1-S0 := by
    dsimp [r,v,epsilon] at *
    linarith
  have hh := SmallCancelingScalar.full_error_short
    (I.necessary.sorted H) (I.necessary.core H) ((I.necessary.contained H).trans hq)
    I.anchors_normal.H_nonneg hY (I.necessary.sorted A).1.le (I.necessary.sorted B).1.le
    hAcircle hBcircle hr hz hv hspan hTy.le hHGscalar hGA' hBT' hbudget
  dsimp [z,r] at hh
  linarith

theorem HardOuterGeometry.crossed_HG2_small_data {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hGy : (I.cycle.point G).y≤0) (hHG : I.cycle.Feasible H 2) :
    Nonempty (CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  have hr : r∈Ioc 0 frameCap :=
    ⟨sub_pos.mpr hHA,(le_abs_self r).trans (I.necessary.spread A H)⟩
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hfull := I.crossed_HG2_small_full_angle hq hAB hnorm hTA hAG hHA hsmall hHG
  have hspan : z+r<1/5 := by dsimp [z,r]; linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) (z+r) 2 := by
    convert hHG using 1 <;>
      simp [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,z,r] <;> ring
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  exact SmallCancelingConstruction.actual_output hqL hq
    (I.necessary.sorted H) (I.necessary.sorted A) (I.necessary.core H) (I.necessary.core A)
    (I.necessary.contained H) (I.necessary.contained A) I.anchors_normal.H_nonneg
    hsmall hGy hr hz hspan hHG' hGA

theorem HardOuterGeometry.crossed_HG2_small_output {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hGy : (I.cycle.point G).y≤0) (hHG : I.cycle.Feasible H 2) :
    47/98<(I.cycle.point A).y ∧ I.cycle.theta A-I.cycle.theta H<1/100 ∧
      Nonempty (CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  obtain ⟨O⟩ := I.crossed_HG2_small_data hqL hq hAB hnorm hTA hAG hHA hsmall hGy hHG
  let J := I.fromCrossedGAData hAB O
  have hAB' : J.cycle.theta A=J.cycle.theta B := hAB
  have hsum' : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    change O.pointA.y-(I.cycle.point B).y=1
    rw [O.A_tangent]
    exact hnorm
  have hsmall' : (J.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) := by
    change O.pointA.y∈Icc (67/200 : ℝ) (1/2)
    rw [O.A_tangent]
    exact hsmall
  have hHG' : J.cycle.Feasible H 0 := by
    simpa [J,HardOuterGeometry.fromCrossedGAData,crossedGACycle,Feasible,slack,edge,word,
      delta,next,H,G,A,zeroFeasible,sub_nonneg] using O.HG_zero
  have hcap := J.crossed_HG0_small_reserve hqL hq hAB' hsum' hTA le_rfl hHA
    hsmall' O.G_nonpos hHG'
  refine ⟨?_,hcap.2.1,⟨O⟩⟩
  have hA := hcap.1
  change 47/98<O.pointA.y at hA
  simpa only [O.A_tangent] using hA

theorem HardInput.crossed_HG2_small_output {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hHG : I.cycle.Feasible H 2) :
    47/98<(I.cycle.point A).y ∧ I.cycle.theta A-I.cycle.theta H<1/100 ∧
      Nonempty (CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  have hG := I.small_middle_G_negative hqL hq hAB hnorm
    ⟨by linarith [hsmall.1],hsmall.2⟩ hTA hAG
  exact I.outerGeometry.crossed_HG2_small_output hqL hq hAB hnorm hTA hAG hHA hsmall hG.le hHG

end SquaresInCircles.Eight.TableFree.SignedCycle
