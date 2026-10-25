module

public import SquaresInCircles.Eight.TableFree.CrossedLargeCapture
public import SquaresInCircles.Eight.TableFree.SignedOppositeHardSigns

/-!
# The large crossed HG0 capture on the literal original hard cycle

Uncompiled source draft.  The middle circle lift is used only to bound
the original HG/GA contact pair.  The actual G support uses that same
q-circle, and the unchanged original TD witness supplies the opposite
charge.  The larger middle tangent already forces the original G sign;
the opposite T sign remains unrestricted.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate PositiveSmallScalar EndpointRotationPenalty EndpointBudgetScalars

namespace CrossedLargeGeometry

def capP (q : ℝ) (A : SignedPoint) : ℝ := Real.sqrt (q-(A.y+1/2)^2)-1
def capY (A : SignedPoint) : ℝ := A.y+1/2

theorem actual_hard_cap {q z : ℝ} {G A : SignedPoint}
    (hq : q≤qCap) (hAs : A.Sorted) (hAc : A.AvoidsCore)
    (hAq : A.Contained q) (hAy : 1/2≤A.y) (hGy : G.y≤0)
    (hz : z∈Icc 0 frameCap) (hGA : quarterFeasible G A (-z) 0) :
    CrossedLargeScalar.CapData q (capP q A) (capY A) ∧
      -G.y+1/2≤V (capP q A) (capY A) z := by
  have haa := SignedPoint.primary_gt_half hAs hAc
  have hsource : -G.y+1/2≤(A.a-1/2)*Real.cos z-(A.y+1/2)*Real.sin z :=
    SignedOppositeHardEnvelope.negative_hard_contact hz hGA
  have ht := transport_trig hz
  have hPcos := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤A.a-1/2 by linarith)
  have hYsin := mul_nonneg (show 0≤A.y+1/2 by linarith) ht.2.2.1
  have ha1 : 1≤A.a := by linarith
  have hcircle : (A.a+1/2)^2+(A.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg (show 0≤A.y by linarith)] using hAq
  have hr : 0≤q-(A.y+1/2)^2 := by linarith [sq_nonneg (A.a+1/2)]
  have hs := Real.sq_sqrt hr
  have hs0 := Real.sqrt_nonneg (q-(A.y+1/2)^2)
  have hprimary : A.a-1/2≤capP q A := by
    have h := le_of_pow_le_pow_left₀ two_ne_zero hs0
      (show (A.a+1/2)^2≤(Real.sqrt (q-(A.y+1/2)^2))^2 by rw [hs]; linarith)
    dsimp [capP]; linarith
  have hPl : 1/2≤capP q A := by linarith
  have hq' : q≤9789/2500 := hq
  have hy1 := pow_le_pow_left₀ (by norm_num) (show (1:ℝ)≤A.y+1/2 by linarith) 2
  have hPu : capP q A≤177/250 := by
    have h := le_of_pow_le_pow_left₀ two_ne_zero (by norm_num : (0:ℝ)≤427/250)
      (show (Real.sqrt (q-(A.y+1/2)^2))^2≤(427/250)^2 by rw [hs]; linarith)
    dsimp [capP]; linarith
  have hYu : capY A≤13/10 := by
    have ha2 := pow_le_pow_left₀ (by norm_num) (show (3/2:ℝ)≤A.a+1/2 by linarith) 2
    have h := le_of_pow_le_pow_left₀ two_ne_zero (by norm_num : (0:ℝ)≤13/10)
      (show (A.y+1/2)^2≤(13/10)^2 by linarith)
    dsimp [capY]; linarith
  have hcapcircle : (capP q A+1)^2+(capY A)^2=q := by
    dsimp [capP,capY]
    rw [sub_add_cancel,hs]
    ring
  have hcap := mul_le_mul_of_nonneg_right hprimary (show 0≤Real.cos z by linarith [ht.1])
  refine ⟨⟨⟨hPl,hPu⟩,⟨by dsimp [capY]; linarith,hYu⟩,hcapcircle,hq⟩,?_⟩
  dsimp [V,capY]
  linarith

theorem actual_pair_demand {q r z : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hGs : G.Sorted) (hGq : G.Contained q) (hGy : G.y≤0)
    (S : CrossedLargeScalar.CapData q (capP q A) (capY A))
    (hz : z∈Icc 0 frameCap) (hh : r+z∈Icc 0 frameCap)
    (hGA : -G.y+1/2≤V (capP q A) (capY A) z)
    (hHG : zeroFeasible H G (r+z) 0) :
    CrossedLargeScalar.demand q (capP q A) (capY A) r z≤H.y := by
  let Vz := V (capP q A) (capY A) z
  let R := SignedPoint.outerAt q (Vz-1/2)
  have hv : 1/2≤Vz := by dsimp [Vz]; linarith
  have hvU : Vz≤177/250 := (CrossedLargeScalar.V_upper S hz).trans S.P_mem.2
  have hy : 0≤Vz-1/2 := by linarith
  have hdiag : |Vz-1/2|≤diagonalCoordinate q := by
    rw [abs_of_nonneg hy]
    linarith [(uniform_circle_reserves hqL hq).1]
  obtain ⟨hRs,hRq,hRc⟩ := SignedPoint.outerAt_spec hqL hdiag
  have hsupport := PositiveCancelingOuter.sorted_support_mono
    (H := G.reflect) (J := R) (by simpa using hGs) hRs
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (show 0≤R.y from hy)
    (show G.reflect.circle≤R.circle by simpa [R] using hGq.trans_eq hRq.symm)
    (show G.reflect.y≤R.y by dsimp [SignedPoint.reflect,R,SignedPoint.outerAt]; linarith) hh
  have hRa : R.a=W q (capP q A) (capY A) z-1/2 := by
    change Real.sqrt (q-(|Vz-1/2|+1/2)^2)-1/2=_
    rw [abs_of_nonneg hy,sub_add_cancel]
    rfl
  change G.a*Real.sin (r+z)+(-G.y)*Real.cos (r+z)≤
    R.a*Real.sin (r+z)+(Vz-1/2)*Real.cos (r+z) at hsupport
  rw [hRa] at hsupport
  have hf := hHG
  rw [zeroFeasible,edgeWidth_positive_formula hh] at hf
  simp only [zeroProjection,Matrix.cons_val_zero] at hf
  dsimp [CrossedLargeScalar.demand]
  dsimp [Vz] at hsupport
  linarith

end CrossedLargeGeometry

namespace SignedCycle
open CrossedLargeGeometry

/-- The crossed large side is captured from the original points and
retained original axes.  The lifted cap is an explicit comparison, and
its strict alignment reserve remains at the same source q. -/
theorem HardOuterGeometry.crossed_HG0_large_reserve {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H≤I.cycle.theta A)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 0) :
    I.cycle.theta A-I.cycle.theta H<1/25 ∧
      CrossedLargeScalar.demand q (capP q (I.cycle.point A)) (capY (I.cycle.point A))
        (I.cycle.theta A-I.cycle.theta H) 0+
        (I.cycle.theta G-I.cycle.theta A)/150≤(I.cycle.point H).y := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  let v := I.cycle.theta A-I.cycle.theta T
  have hr : r∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hHA,(le_abs_self r).trans (I.necessary.spread A H)⟩
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hv : v∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hTA,(le_abs_self v).trans (I.necessary.spread A T)⟩
  have hh : r+z∈Icc 0 frameCap := by
    constructor
    · linarith [hr.1,hz.1]
    · have hspan := (le_abs_self (I.cycle.theta G-I.cycle.theta H)).trans
        (I.necessary.spread G H)
      dsimp [r,z]
      linarith
  have hGy := I.large_middle_G_negative hq hAB hnorm hTA hAG hlarge
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  obtain ⟨S,hcap⟩ := actual_hard_cap hq (I.necessary.sorted A) (I.necessary.core A)
    (I.necessary.contained A) hlarge hGy.le hz hGA
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) (r+z) 0 := by
    convert hHG using 1
    simp [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,r,z]
  have hpair := actual_pair_demand hqL hq (I.necessary.sorted G) (I.necessary.contained G)
    hGy.le S hz hh hcap hHG'
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
    rw [show -v=I.cycle.theta T-I.cycle.theta B by dsimp [v]; rw [←hAB]; ring]
    simpa [Feasible,slack,edge,word,delta,next,B,Candidate.T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  have hBTref : quarterFeasible (I.cycle.point T).reflect (I.cycle.point B).reflect (-v) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ (-v) 2).2 hBT
  have hBTscalar := SignedOppositeHardEnvelope.negative_hard_contact hv hBTref
  simp only [SignedPoint.reflect,neg_neg] at hBTscalar
  have hyB : -(I.cycle.point B).y+1/2=2-capY (I.cycle.point A) := by
    dsimp [capY]
    linarith
  rw [hyB] at hBTscalar
  have hBcircle : ((I.cycle.point B).a+1/2)^2+(2-capY (I.cycle.point A))^2≤qCap := by
    have hb := (I.necessary.contained B).trans hq
    dsimp [SignedPoint.Contained,SignedPoint.circle] at hb
    rw [abs_of_nonpos I.anchors_normal.B_nonpos,hyB] at hb
    exact hb
  have hTD := (signed_outer_charges hq I.necessary I.anchors_normal I.witnesses I.zero_signs).2
  have hep := I.endpoint_bound hq
  have hbudget : (I.cycle.point H).y-(I.cycle.point T).y+EndpointRotationPenalty.charge*(r-v)<1-S0 := by
    dsimp [r,v,epsilon] at *
    linarith
  exact CrossedLargeCapture.captured_alignment_gain S hr hz
    (by linarith) hv hBcircle hBTscalar hpair hbudget

theorem HardInput.crossed_HG0_large_reserve {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H≤I.cycle.theta A)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 0) :
    I.cycle.theta A-I.cycle.theta H<1/25 ∧
      CrossedLargeScalar.demand q (capP q (I.cycle.point A)) (capY (I.cycle.point A))
        (I.cycle.theta A-I.cycle.theta H) 0+
        (I.cycle.theta G-I.cycle.theta A)/150≤(I.cycle.point H).y :=
  I.outerGeometry.crossed_HG0_large_reserve hqL hq hAB hnorm hTA hAG hHA hlarge hHG

end SignedCycle
end SquaresInCircles.Eight.TableFree
