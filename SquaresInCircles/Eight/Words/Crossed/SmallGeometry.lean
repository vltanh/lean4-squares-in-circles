module

public import SquaresInCircles.Eight.Words.Crossed.SmallCapture
public import SquaresInCircles.Eight.Words.Crossed.LargeGeometry

/-!
# Eight squares: the original small crossed HG0 source has the strict alignment reserve

Every scalar comparison is formed at the q of the source. The original BT2 contact, the opposite
signed charge and the unchanged H/D/E budget prove the tangent and crossing captures. The support
of the source on the G circle (`actual_hard_cap`) then supplies the GA-alignment reserve
(`HardInput.crossed_HG0_small_reserve`); the lifted A point serves only as a comparison.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate PositiveSmallScalar CrossedLargeGeometry EndpointRotationPenalty EndpointBudgetScalars

namespace CrossedSmallGeometry

theorem actual_hard_cap {q z : ℝ} {G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap) (hAs : A.Sorted) (hAc : A.AvoidsCore)
    (hAq : A.Contained q) (hAy : A.y∈Icc (67/200 : ℝ) (1/2)) (hGy : G.y≤0)
    (hz : z∈Icc 0 frameCap) (hGA : quarterFeasible G A (-z) 0) :
    CrossedSmallScalar.CapData q (capP q A) (capY A) ∧
      -G.y+1/2≤V (capP q A) (capY A) z := by
  have haa := SignedPoint.primary_gt_half hAs hAc
  have hsource := SignedOppositeHardEnvelope.negative_hard_contact hz hGA
  have ht := transport_trig hz
  have hPcos := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤A.a-1/2 by linarith)
  have hYsin := mul_nonneg (show 0≤A.y+1/2 by linarith [hAy.1]) ht.2.2.1
  have ha1 : 1≤A.a := by linarith
  have hcircle : (A.a+1/2)^2+(A.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg (show 0≤A.y by linarith [hAy.1])] using hAq
  have hr : 0≤q-(A.y+1/2)^2 := by linarith [sq_nonneg (A.a+1/2)]
  have hs := Real.sq_sqrt hr
  have hs0 := Real.sqrt_nonneg (q-(A.y+1/2)^2)
  have hprimary : A.a-1/2≤capP q A := by
    have h := le_of_pow_le_pow_left₀ two_ne_zero hs0
      (show (A.a+1/2)^2≤(Real.sqrt (q-(A.y+1/2)^2))^2 by rw [hs]; linarith)
    dsimp [capP]; linarith
  have hPl : 1/2≤capP q A := by linarith
  have hPu : capP q A≤397/500 := by
    have hYsq := pow_le_pow_left₀ (show (0:ℝ)≤167/200 by norm_num)
      (show 167/200≤A.y+1/2 by linarith [hAy.1]) 2
    have hq' : q≤9789/2500 := hq
    have h := le_of_pow_le_pow_left₀ two_ne_zero (by norm_num : (0:ℝ)≤897/500)
      (show (Real.sqrt (q-(A.y+1/2)^2))^2≤(897/500)^2 by rw [hs]; linarith)
    dsimp [capP]; linarith
  have hY : capY A∈Icc (167/200 : ℝ) 1 := by
    dsimp [capY]
    constructor <;> linarith [hAy.1,hAy.2]
  have hcapcircle : (capP q A+1)^2+(capY A)^2=q := by
    dsimp [capP,capY]
    rw [sub_add_cancel,hs]
    ring
  have hcap := mul_le_mul_of_nonneg_right hprimary (show 0≤Real.cos z by linarith [ht.1])
  refine ⟨⟨⟨hPl,hPu⟩,hY,hcapcircle,hqL,hq⟩,?_⟩
  dsimp [V,capY]
  linarith

theorem actual_pair_demand {q r z : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hGs : G.Sorted) (hGq : G.Contained q) (hGy : G.y≤0)
    (S : CrossedSmallScalar.CapData q (capP q A) (capY A))
    (hz : z∈Icc 0 frameCap) (hh : r+z∈Icc 0 frameCap)
    (hGA : -G.y+1/2≤V (capP q A) (capY A) z)
    (hHG : zeroFeasible H G (r+z) 0) :
    CrossedLargeScalar.demand q (capP q A) (capY A) r z≤H.y := by
  let Vz := V (capP q A) (capY A) z
  let R := SignedPoint.outerAt q (Vz-1/2)
  have hv : 1/2≤Vz := by dsimp [Vz]; linarith
  have hvU : Vz≤397/500 := (PositiveSmallScalar.V_upper S.positive hz).trans S.P_mem.2
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

end CrossedSmallGeometry

namespace SignedCycle

theorem HardOuterGeometry.crossed_HG0_small_reserve {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hGy : (I.cycle.point G).y≤0) (hHG : I.cycle.Feasible H 0) :
    47/98<(I.cycle.point A).y ∧ I.cycle.theta A-I.cycle.theta H<1/100 ∧
      CrossedLargeScalar.demand q (capP q (I.cycle.point A)) (capY (I.cycle.point A))
        (I.cycle.theta A-I.cycle.theta H) 0+
        (I.cycle.theta G-I.cycle.theta A)/100≤(I.cycle.point H).y := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  let v := I.cycle.theta A-I.cycle.theta T
  have hr : r∈Ioc 0 frameCap :=
    ⟨sub_pos.mpr hHA,(le_abs_self r).trans (I.necessary.spread A H)⟩
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hv : v∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hTA,(le_abs_self v).trans (I.necessary.spread A T)⟩
  have hh : r+z∈Icc 0 frameCap := by
    constructor
    · linarith [hr.1,hz.1]
    · have hs := (le_abs_self _).trans (I.necessary.spread G H)
      dsimp [r,z]
      linarith
  have hTy := I.large_middle_T_positive hq hAB hnorm hTA hAG
    (by linarith [hsmall.2])
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [z,Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub] using I.GA_hard
  obtain ⟨S,hcap⟩ := CrossedSmallGeometry.actual_hard_cap hqL hq
    (I.necessary.sorted A) (I.necessary.core A) (I.necessary.contained A) hsmall hGy hz hGA
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) (r+z) 0 := by
    convert hHG using 1
    simp [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,r,z]
  have hpair := CrossedSmallGeometry.actual_pair_demand hqL hq (I.necessary.sorted G)
    (I.necessary.contained G) hGy S hz hh hcap hHG'
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
    rw [show -v=I.cycle.theta T-I.cycle.theta B by dsimp [v]; rw [←hAB]; ring]
    simpa [Feasible,slack,edge,word,delta,next,B,Candidate.T,quarterFeasible,sub_nonneg] using I.BT_hard
  have hBTref : quarterFeasible (I.cycle.point T).reflect (I.cycle.point B).reflect (-v) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ (-v) 2).2 hBT
  have hBTscalar := SignedOppositeHardEnvelope.negative_hard_contact hv hBTref
  simp only [SignedPoint.reflect,neg_neg] at hBTscalar
  have hyB : -(I.cycle.point B).y+1/2=2-capY (I.cycle.point A) := by dsimp [capY]; linarith
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
  obtain ⟨hY,hshort,hgain⟩ := CrossedSmallCapture.captured_alignment_gain S hr hz
    (by linarith) (I.necessary.sorted B).1.le hTy.le hv hBcircle hBTscalar hpair hbudget
  refine ⟨?_,hshort,hgain⟩
  dsimp [capY] at hY
  linarith

theorem HardInput.crossed_HG0_small_reserve {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hGy : (I.cycle.point G).y≤0) (hHG : I.cycle.Feasible H 0) :
    47/98<(I.cycle.point A).y ∧ I.cycle.theta A-I.cycle.theta H<1/100 ∧
      CrossedLargeScalar.demand q (capP q (I.cycle.point A)) (capY (I.cycle.point A))
        (I.cycle.theta A-I.cycle.theta H) 0+
        (I.cycle.theta G-I.cycle.theta A)/100≤(I.cycle.point H).y :=
  I.outerGeometry.crossed_HG0_small_reserve hqL hq hAB hnorm hTA hAG hHA hsmall hGy hHG

end SignedCycle
end SquaresInCircles.Eight
