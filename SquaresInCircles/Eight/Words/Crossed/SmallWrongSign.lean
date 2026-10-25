module

public import SquaresInCircles.Eight.Words.Crossed.WrongEndpointBound
public import SquaresInCircles.Eight.Frames.Signed.OppositeHardSigns
public import SquaresInCircles.Eight.Owners.Small.PositiveZeroEndpoint
public import SquaresInCircles.Eight.Owners.Wide.SmallHardEnvelope

/-!
# Eight squares: the original crossed small intermediate has its normal sign

The A primary is lifted only in a scalar comparison at the original q. The original H, D, E and
T points, their frames, the retained weak witnesses and the BT2 contact supply the signed
budget, and the two cap alternatives contradict it
(`HardOuterGeometry.crossed_small_wrong_G_impossible`). Reflection uses the invariant local
geometry, so either original E sign is allowed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate EndpointRotationPenalty EndpointBudgetScalars
namespace SignedCycle

theorem HardOuterGeometry.crossed_small_wrong_G_impossible {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hGy : 0≤(I.cycle.point G).y) (hGsmall : (I.cycle.point G).y<1/10) : False := by
  have hTy := I.large_middle_T_positive hq hAB hnorm hTA hAG
    (show 1/2≤ -(I.cycle.point B).y by linarith [hsmall.2])
  have hHG : I.cycle.Feasible H 0 := by
    have ho : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
      simpa [normalOwners,H] using I.witnesses.allowed H
    rcases ho with ho | ho
    · simpa [ho] using I.witnesses.feasible H
    · exact False.elim (not_lt_of_ge hGy (I.zero_signs.HG_canceling ho))
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  let v := I.cycle.theta A-I.cycle.theta T
  let h := r+z
  have hr : 0<r := sub_pos.mpr hHA
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hv : v∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hTA,(le_abs_self v).trans (I.necessary.spread A T)⟩
  have hh : h∈Icc 0 frameCap := by
    have hs := (le_abs_self _).trans (I.necessary.spread G H)
    dsimp [h,r,z]
    constructor <;> linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) h 0 := by
    have hd : h=I.cycle.theta G-I.cycle.theta H := by dsimp [h,r,z]; ring
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,hd] using hHG
  let A' := SignedPoint.outerAt q (I.cycle.point A).y
  obtain ⟨hAs,hAo,hAc⟩ := SignedPoint.outerAt_spec hqL
    (SignedPoint.contained_minor_le_diagonal (I.necessary.sorted A) (I.necessary.contained A))
  have hAy : A'.y=(I.cycle.point A).y := rfl
  have hAa : (I.cycle.point A).a≤A'.a := by
    have hsource := I.necessary.contained A
    have htarget := hAo
    change ((I.cycle.point A).a+1/2)^2+(|(I.cycle.point A).y|+1/2)^2≤q at hsource
    change (A'.a+1/2)^2+(|A'.y|+1/2)^2=q at htarget
    rw [hAy] at htarget
    have h2 : ((I.cycle.point A).a+1/2)^2≤(A'.a+1/2)^2 := by linarith only [hsource,htarget]
    have h3 := le_of_pow_le_pow_left₀ two_ne_zero (by linarith only [hAs.1]) h2
    linarith only [h3]
  let P := A'.a-1/2
  let Y := (I.cycle.point A).y+1/2
  have hY : Y∈Icc (39/50 : ℝ) 1 := by
    dsimp [Y]
    constructor <;> linarith only [hsmall.1,hsmall.2]
  have hcircle : (P+1)^2+Y^2=q := by
    have hc := hAo
    change (A'.a+1/2)^2+(|A'.y|+1/2)^2=q at hc
    rw [hAy,abs_of_nonneg I.anchors_normal.A_nonneg] at hc
    dsimp [P,Y]
    linarith only [hc]
  have hPpos : 0<P := by
    have hh := SignedPoint.primary_gt_half hAs hAc
    dsimp [P]
    linarith
  have hP : P∈Icc (1/2 : ℝ) (819/1000) := by
    have hqL' := hqL
    have hq' := hq
    dsimp [qLow,qCap] at hqL' hq'
    constructor
    · have hy2 := pow_le_pow_left₀ (show 0≤Y by linarith [hY.1]) hY.2 2
      by_contra! hlt
      have h3 := pow_lt_pow_left₀ (show P+1<3/2 by linarith) (by linarith) two_ne_zero
      linarith
    · have hy2 := pow_le_pow_left₀ (show (0:ℝ)≤39/50 by norm_num) hY.1 2
      by_contra! hlt
      have h3 := pow_lt_pow_left₀ (show (1819/1000:ℝ)<P+1 by linarith) (by norm_num) two_ne_zero
      linarith
  have S : CrossedSmallWrongScalar.CapData q P Y := {
    P_mem := hP
    Y_mem := hY
    circle := hcircle
    floor := hqL
    ceiling := hq }
  have hGA : -(I.cycle.point G).y+1/2≤PositiveSmallScalar.V P Y z := by
    have hf : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
      have hd : -z=I.cycle.theta A-I.cycle.theta G := by dsimp [z]; ring
      simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,hd] using I.GA_hard
    have hb := SignedOppositeHardEnvelope.negative_hard_contact hz hf
    have hm := mul_le_mul_of_nonneg_right hAa (show 0≤Real.cos z by
      linarith [(transport_trig hz).1])
    dsimp [PositiveSmallScalar.V,P,Y]
    linarith only [hb,hm]
  have hVlower : 2/5<PositiveSmallScalar.V P Y z := by linarith
  obtain ⟨Z,hZ,hZE⟩ := CrossedSmallWrongScalar.contact S
  have hZi := CrossedWrongEndpointBound.contact_mem hZ
  have hHreserve : 1+7/1000-27/6400≤
      (I.cycle.point H).y+EndpointRotationPenalty.charge*r+EndpointRotationPenalty.charge*Z := by
    by_cases hcap : 1/2≤PositiveSmallScalar.V P Y z
    · have hrad : 0≤q-1/4 := by have hqL' := hqL; dsimp [qLow] at hqL'; linarith
      have hw2 := Real.sq_sqrt hrad
      have hw0 := Real.sqrt_nonneg (q-1/4)
      have hGa : (I.cycle.point G).a≤Real.sqrt (q-1/4)-1/2 := by
        have hGc := I.necessary.contained G
        change ((I.cycle.point G).a+1/2)^2+(|(I.cycle.point G).y|+1/2)^2≤q at hGc
        rw [abs_of_nonneg hGy] at hGc
        have h2 : ((I.cycle.point G).a+1/2)^2≤(Real.sqrt (q-1/4))^2 := by
          rw [hw2]; linarith only [hGc,hGy,sq_nonneg (I.cycle.point G).y]
        have h3 := le_of_pow_le_pow_left₀ two_ne_zero hw0 h2
        linarith only [h3]
      have hsource : CrossedWrongEndpointCalculus.zeroDemand q h≤(I.cycle.point H).y := by
        have hf := hHG'
        rw [zeroFeasible,edgeWidth_positive_formula hh] at hf
        simp [zeroProjection] at hf
        have hm := mul_le_mul_of_nonneg_right hGa (transport_trig hh).2.2.1
        have hy := mul_nonneg hGy (show 0≤Real.cos h by linarith [(transport_trig hh).1])
        dsimp [CrossedWrongEndpointCalculus.zeroDemand]
        linarith only [hf,hm,hy]
      have hrsv := CrossedWrongEndpointBound.positive_cap_reserve S hZ hZE hz hcap
        hr.le (show r+z≤frameCap from hh.2)
      change 1+7/1000-27/6400≤
        CrossedWrongEndpointCalculus.zeroDemand q h+EndpointRotationPenalty.charge*r+
          EndpointRotationPenalty.charge*Z at hrsv
      linarith only [hsource,hrsv]
    · have hvwrong : PositiveSmallScalar.V P Y z∈Icc (2/5 : ℝ) (1/2) :=
        ⟨hVlower.le,(lt_of_not_ge hcap).le⟩
      have hb := CrossedSmallWrongScalar.root_bounds S hz hvwrong
      have hW2 : (SmallWrongScalar.W q P Y z)^2=
          q-(1-PositiveSmallScalar.V P Y z)^2 := Real.sq_sqrt hb.1.le
      have hGa : (I.cycle.point G).a≤SmallWrongScalar.W q P Y z-1/2 := by
        have hGc := I.necessary.contained G
        change ((I.cycle.point G).a+1/2)^2+(|(I.cycle.point G).y|+1/2)^2≤q at hGc
        rw [abs_of_nonneg hGy] at hGc
        have hy2 := pow_le_pow_left₀
          (show 0≤1-PositiveSmallScalar.V P Y z by linarith [hvwrong.2])
          (show 1-PositiveSmallScalar.V P Y z≤(I.cycle.point G).y+1/2 by linarith only [hGA]) 2
        have h2 : ((I.cycle.point G).a+1/2)^2≤(SmallWrongScalar.W q P Y z)^2 := by
          rw [hW2]; linarith only [hGc,hy2]
        have h3 := le_of_pow_le_pow_left₀ two_ne_zero
          (show 0≤SmallWrongScalar.W q P Y z from Real.sqrt_nonneg _) h2
        linarith only [h3]
      have hsource : CrossedWrongEndpointCalculus.chargedDemand q P Y z h≤
          (I.cycle.point H).y+EndpointRotationPenalty.charge*r := by
        have hf := hHG'
        rw [zeroFeasible,edgeWidth_positive_formula hh] at hf
        simp [zeroProjection] at hf
        have ha := mul_le_mul_of_nonneg_right hGa (transport_trig hh).2.2.1
        have hy := mul_le_mul_of_nonneg_right
          (show 1/2-PositiveSmallScalar.V P Y z≤(I.cycle.point G).y by linarith only [hGA])
          (show 0≤Real.cos h by linarith [(transport_trig hh).1])
        dsimp [CrossedWrongEndpointCalculus.chargedDemand]
        have hdiff : h-z=r := by dsimp [h]; ring
        rw [hdiff]
        linarith only [hf,ha,hy]
      have hrsv := CrossedWrongEndpointBound.wrong_cap_reserve S hZ hZE hz hvwrong
        (show h∈Icc z frameCap from ⟨by dsimp [h]; linarith only [hr],hh.2⟩)
      linarith only [hsource,hrsv]
  have hAq : (A'.a+1/2)^2+((I.cycle.point A).y+1/2)^2≤qCap := by
    have he : (A'.a+1/2)^2+((I.cycle.point A).y+1/2)^2=q := by
      dsimp [P,Y] at hcircle; linarith
    exact he.le.trans hq
  have hBq : ((I.cycle.point B).a+1/2)^2+(3/2-(I.cycle.point A).y)^2≤qCap := by
    have hc := (I.necessary.contained B).trans hq
    have hy : -(I.cycle.point B).y+1/2=3/2-(I.cycle.point A).y := by linarith
    change ((I.cycle.point B).a+1/2)^2+(|(I.cycle.point B).y|+1/2)^2≤qCap at hc
    rw [abs_of_nonpos I.anchors_normal.B_nonpos,hy] at hc
    exact hc
  have hGAzero : 1/2≤(A'.a-1/2)*Real.cos Z-
      ((I.cycle.point A).y+1/2)*Real.sin Z := by
    dsimp [PositiveSmallScalar.V,P,Y] at hZE
    exact hZE.ge
  have hBT : (I.cycle.point T).y+1/2≤
      ((I.cycle.point B).a-1/2)*Real.cos v-
        (3/2-(I.cycle.point A).y)*Real.sin v := by
    have hf : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-v) 2 := by
      have hd : I.cycle.theta 4-I.cycle.theta 3= -v := by
        change I.cycle.theta T-I.cycle.theta B= -v; dsimp [v]; rw [←hAB]; ring
      simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,hd] using I.BT_hard
    rw [quarterFeasible,edgeWidth_negative_formula hv] at hf
    simp [quarterProjection,Real.cos_neg,Real.sin_neg] at hf
    have hy : (I.cycle.point B).y=(I.cycle.point A).y-1 := by linarith only [hnorm]
    rw [hy] at hf
    linarith only [hf]
  have hmiddle := WideSmallHardEnvelope.actual_middle_bound hsmall
    (SignedPoint.primary_gt_half hAs hAc) hAq hBq hZi hv hTy.le hGAzero hBT
  have hTD := (signed_outer_charges hq I.necessary I.anchors_normal I.witnesses I.zero_signs).2
  have hbudget := I.endpoint_bound hq
  have hS := SmallPositiveZeroEndpoint.endpoint_constant_lower
  dsimp [r,v,EndpointRotationPenalty.charge,epsilon] at hHreserve hmiddle hTD hbudget
  linarith

end SignedCycle
end SquaresInCircles.Eight
