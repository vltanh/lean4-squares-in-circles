module

public import SquaresInCircles.Eight.Frames.Signed.OppositeHardSigns
public import SquaresInCircles.Eight.Owners.Small.PositiveZeroEndpoint
public import SquaresInCircles.Eight.Owners.Wide.SmallWrongSign
public import SquaresInCircles.Eight.Words.Crossed.ClampBudget
public import SquaresInCircles.Eight.Words.Crossed.WrongEndpointBound

/-!
# Eight squares: the original crossed small intermediate has its normal sign

The A primary is lifted only in a scalar comparison at the original q. The original H, D, E and
T points, their frames, the retained weak witnesses and the BT2 contact supply the signed
budget, and the two cap alternatives contradict it
(`HardOuterGeometry.crossed_small_wrong_G_impossible`). Reflection uses the invariant local
geometry, so either original E sign is allowed.
-/

section
/-!
## The remaining active-boundary angle capture

On `1 ≤ Y ≤ 1.04`, the normal hard contact first captures `u < .23`
(`BoundaryData.angle_medium_coarse`). The unchanged budget `F` is monotone on the whole rectangle
`.158 ≤ u < .23`: its `Y` derivative is negative (`F_y_negative`) and its `u` derivative is
positive (`F_u_positive`). One exact rational endpoint (`medium_endpoint`) contradicts that
budget, giving `u < .158` (`BoundaryData.angle_medium`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedClampBudget
open CrossedClampRates CrossedUpperRate EndpointRotationPenalty

theorem medium_radicals {Y : ℝ} (hY : Y∈Icc (1:ℝ) (26/25)) :
    0<qCap-Y^2 ∧ CrossedClampRates.radius qCap Y∈Ioo (42/25 : ℝ) (171/100) ∧
      (2-Y)∈Icc (24/25 : ℝ) 1 ∧
      0<qCap-(2-Y)^2 ∧ CrossedClampRates.radius qCap (2-Y)∈Ioo (683/400 : ℝ) (1731/1000) ∧
      (CrossedClampRates.radius qCap Y)^2+Y^2=qCap ∧
      (CrossedClampRates.radius qCap (2-Y))^2+(2-Y)^2=qCap := by
  have hY0 : 0≤Y := by linarith [hY.1]
  have hY2 := pow_le_pow_left₀ hY0 hY.2 2
  have hB : (2-Y)∈Icc (24/25 : ℝ) 1 := by constructor <;> linarith [hY.1,hY.2]
  have hB0 : 0≤2-Y := by linarith [hB.1]
  have hB2 := pow_le_pow_left₀ hB0 hB.2 2
  have hr : 0<qCap-Y^2 := by dsimp [qCap]; nlinarith
  have hz : 0<qCap-(2-Y)^2 := by dsimp [qCap]; nlinarith
  have hR0 : 0≤CrossedClampRates.radius qCap Y := Real.sqrt_nonneg _
  have hZ0 : 0≤CrossedClampRates.radius qCap (2-Y) := Real.sqrt_nonneg _
  have hR2 : (CrossedClampRates.radius qCap Y)^2=qCap-Y^2 := Real.sq_sqrt hr.le
  have hZ2 : (CrossedClampRates.radius qCap (2-Y))^2=qCap-(2-Y)^2 := Real.sq_sqrt hz.le
  have hR : CrossedClampRates.radius qCap Y∈Ioo (42/25 : ℝ) (171/100) := by
    dsimp [qCap] at hR2
    constructor <;> nlinarith [hY.1,sq_nonneg (Y-1)]
  have hZ : CrossedClampRates.radius qCap (2-Y)∈Ioo (683/400 : ℝ) (1731/1000) := by
    dsimp [qCap] at hZ2
    constructor <;> nlinarith [hB.1,sq_nonneg (2-Y-24/25)]
  exact ⟨hr,hR,hB,hz,hZ,by nlinarith,by nlinarith⟩

theorem BoundaryData.F_ceiling_lt {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) : F qCap Y u<1-EndpointBudgetScalars.S0 := by
  have hR : CrossedClampRates.radius q Y≤CrossedClampRates.radius qCap Y :=
    Real.sqrt_le_sqrt (sub_le_sub_right C.ceiling _)
  have hZ : CrossedClampRates.radius q (2-Y)≤CrossedClampRates.radius qCap (2-Y) :=
    Real.sqrt_le_sqrt (sub_le_sub_right C.ceiling _)
  have hc : 0≤Real.cos u := by linarith [(transport_trig C.u_mem).1]
  have hm := mul_le_mul_of_nonneg_right hZ hc
  have hf := C.F_lt
  dsimp [F] at *
  linarith

theorem BoundaryData.angle_medium_coarse {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) (hY : Y∈Icc (1:ℝ) (26/25)) :
    u<23/100 := by
  obtain ⟨_,_,hB,_,hZ,_,_⟩ := medium_radicals hY
  have hZq : CrossedClampRates.radius q (2-Y)≤CrossedClampRates.radius qCap (2-Y) :=
    Real.sqrt_le_sqrt (sub_le_sub_right C.ceiling _)
  have ht := transport_trig C.u_mem
  have hc0 : 0≤Real.cos u := by linarith [ht.1]
  have hs0 := ht.2.2.1
  have hm1 := mul_le_mul_of_nonneg_right
    (show CrossedClampRates.radius q (2-Y)-1≤731/1000 by linarith [hZ.2]) hc0
  have hm2 := mul_le_mul_of_nonneg_right hB.1 hs0
  have hcontact : 1/2≤(731/1000)*Real.cos u-(24/25)*Real.sin u := by
    linarith [C.BT,C.T_nonneg]
  by_contra hu
  have hcut : (23/100:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hs := CorrelatedSameBlock.sin_mono hcut C.u_mem (le_of_not_gt hu)
  have hc := CorrelatedSameBlock.cos_anti hcut C.u_mem (le_of_not_gt hu)
  have hsL := Real.sin_ge_sub_cube (show (0:ℝ)≤23/100 by norm_num)
  have hcU := cos_upper_four (show (0:ℝ)≤23/100 by norm_num)
  nlinarith

theorem F_y_hasDerivAt {q Y u : ℝ} (hY : 0<q-Y^2) (hB : 0<q-(2-Y)^2) :
    HasDerivAt (fun y => F q y u)
      (Y/CrossedClampRates.radius q Y-((2-Y)/CrossedClampRates.radius q (2-Y))*Real.cos u-Real.sin u) Y := by
  have hR : HasDerivAt (CrossedClampRates.radius q) (-Y/CrossedClampRates.radius q Y) Y := radius_hasDerivAt hY
  have h2 : HasDerivAt (fun y : ℝ => 2-y) (-1) Y := (hasDerivAt_id' Y).const_sub 2
  have hZ : HasDerivAt (fun y => CrossedClampRates.radius q (2-y)) (-(2-Y)/CrossedClampRates.radius q (2-Y)*(-1)) Y :=
    (radius_hasDerivAt hB).comp Y h2
  have hd : HasDerivAt
      (fun y => 3-CrossedClampRates.radius q y-(CrossedClampRates.radius q (2-y)-1)*Real.cos u+(2-y)*Real.sin u-charge*u)
      (0-(-Y/CrossedClampRates.radius q Y)-(-(2-Y)/CrossedClampRates.radius q (2-Y)*(-1))*Real.cos u+(-1)*Real.sin u-0) Y :=
    ((((hasDerivAt_const Y (3:ℝ)).fun_sub hR).fun_sub
      ((hZ.sub_const 1).mul_const (Real.cos u))).fun_add (h2.mul_const (Real.sin u))).fun_sub
      (hasDerivAt_const Y (charge*u))
  exact hd.congr_deriv (by ring)

theorem F_u_hasDerivAt (q Y u : ℝ) :
    HasDerivAt (F q Y) (U q (2-Y) u-charge) u := by
  have hd : HasDerivAt
      (fun x => 3-CrossedClampRates.radius q Y-(CrossedClampRates.radius q (2-Y)-1)*Real.cos x+(2-Y)*Real.sin x-charge*x)
      (-((CrossedClampRates.radius q (2-Y)-1)*(-Real.sin u))+(2-Y)*Real.cos u-charge*1) u :=
    ((((Real.hasDerivAt_cos u).const_mul (CrossedClampRates.radius q (2-Y)-1)).const_sub (3-CrossedClampRates.radius q Y)).fun_add
      ((Real.hasDerivAt_sin u).const_mul (2-Y))).fun_sub ((hasDerivAt_id' u).const_mul charge)
  exact hd.congr_deriv (by simp only [U]; ring)

theorem medium_trig {u : ℝ} (hu : u∈Icc (79/500 : ℝ) (23/100)) :
    1-(23/100 : ℝ)^2/2≤Real.cos u ∧
      (79/500 : ℝ)-(79/500 : ℝ)^3/6≤Real.sin u := by
  have hu0 : 0≤u := by linarith [hu.1]
  have hu2 := pow_le_pow_left₀ hu0 hu.2 2
  have hc := Real.one_sub_sq_div_two_le_cos (x := u)
  have hi : u∈Icc 0 frameCap := ⟨hu0,by dsimp [frameCap]; linarith [hu.2]⟩
  have hs := CorrelatedSameBlock.sin_mono
    (show (79/500:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hi hu.1
  have hsL := Real.sin_ge_sub_cube (show (0:ℝ)≤79/500 by norm_num)
  exact ⟨by linarith,by linarith⟩

theorem F_y_negative {Y u : ℝ} (hY : Y∈Icc (1:ℝ) (26/25))
    (hu : u∈Icc (79/500 : ℝ) (23/100)) :
    Y/CrossedClampRates.radius qCap Y-((2-Y)/CrossedClampRates.radius qCap (2-Y))*Real.cos u-Real.sin u<0 := by
  obtain ⟨_,hR,hB,_,hZ,_,_⟩ := medium_radicals hY
  obtain ⟨hc,hs⟩ := medium_trig hu
  have hR0 : 0<CrossedClampRates.radius qCap Y := by linarith [hR.1]
  have hZ0 : 0<CrossedClampRates.radius qCap (2-Y) := by linarith [hZ.1]
  have hratioA : Y/CrossedClampRates.radius qCap Y<(26/25)/(42/25) := by
    apply (div_lt_iff₀ hR0).2
    nlinarith [hY.2,hR.1]
  have hratioB : (24/25)/(1731/1000)<(2-Y)/CrossedClampRates.radius qCap (2-Y) := by
    apply (lt_div_iff₀ hZ0).2
    nlinarith [hB.1,hZ.2]
  have hc0 : 0<Real.cos u := by linarith
  have hm1 := mul_lt_mul_of_pos_right hratioB hc0
  have hm2 := mul_le_mul_of_nonneg_left hc
    (by norm_num : (0:ℝ)≤(24/25)/(1731/1000))
  nlinarith

theorem F_u_positive {Y u : ℝ} (hY : Y∈Icc (1:ℝ) (26/25))
    (hu : u∈Icc (79/500 : ℝ) (23/100)) : 0<U qCap (2-Y) u-charge := by
  obtain ⟨_,_,hB,_,hZ,_,_⟩ := medium_radicals hY
  obtain ⟨hc,hs⟩ := medium_trig hu
  have hP : 683/400-1≤CrossedClampRates.radius qCap (2-Y)-1 := by linarith [hZ.1]
  have hm1 := mul_le_mul hP hs
    (by norm_num : (0:ℝ)≤(79/500 : ℝ)-(79/500 : ℝ)^3/6)
    (by linarith [hZ.1] : 0≤CrossedClampRates.radius qCap (2-Y)-1)
  have hm2 := mul_le_mul hB.1 hc
    (by norm_num : (0:ℝ)≤1-(23/100 : ℝ)^2/2)
    (by linarith [hB.1] : 0≤2-Y)
  dsimp [U,charge]
  nlinarith

theorem medium_endpoint : 1-EndpointBudgetScalars.S0<F qCap (26/25) (79/500) := by
  obtain ⟨_,hR,_,_,hZ,hR2,hZ2⟩ := medium_radicals
    (show (26/25:ℝ)∈Icc 1 (26/25) by norm_num)
  have hRsharp : CrossedClampRates.radius qCap (26/25)<33669/20000 := by
    dsimp [qCap] at hR2
    nlinarith [hR.1]
  have hZsharp : CrossedClampRates.radius qCap (2-26/25)<21629/12500 := by
    dsimp [qCap] at hZ2
    nlinarith [hZ.1]
  have hroot : 683/400<Real.sqrt (qCap-1) := Real.lt_sqrt_of_sq_lt (by norm_num [qCap])
  have ht := transport_trig (show (79/500:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hc0 : 0<Real.cos (79/500) := by linarith [ht.1]
  have hc := cos_upper_four (show (0:ℝ)≤79/500 by norm_num)
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤79/500 by norm_num)
  have hm1 := mul_lt_mul_of_pos_right
    (show CrossedClampRates.radius qCap (2-26/25)-1<21629/12500-1 by linarith) hc0
  have hm2 := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤21629/12500-1)
  dsimp [F,EndpointBudgetScalars.S0,charge]
  nlinarith

theorem BoundaryData.angle_medium {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) (hY : Y∈Icc (1:ℝ) (26/25)) :
    u<79/500 := by
  have hu23 := C.angle_medium_coarse hY
  by_contra hu
  have hulo : 79/500≤u := le_of_not_gt hu
  have hui : u∈Icc (79/500:ℝ) (23/100) := ⟨hulo,hu23.le⟩
  have hmY : AntitoneOn (fun y => F qCap y u) (Icc (1:ℝ) (26/25)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro y hy
      obtain ⟨hr,_,_,hb,_,_,_⟩ := medium_radicals hy
      exact (F_y_hasDerivAt hr hb).continuousAt.continuousWithinAt
    · intro y hy
      obtain ⟨hr,_,_,hb,_,_,_⟩ := medium_radicals (Ioo_subset_Icc_self hy)
      exact F_y_hasDerivAt hr hb
    · intro y hy
      exact (F_y_negative (Ioo_subset_Icc_self hy) hui).le
  have hYcomp := hmY hY (show (26/25:ℝ)∈Icc 1 (26/25) by norm_num) hY.2
  have hmu : MonotoneOn (F qCap (26/25)) (Icc (79/500:ℝ) u) := by
    apply monoOn_of_hasDeriv_nonneg
    · unfold F; fun_prop
    · intro v hv
      exact F_u_hasDerivAt qCap (26/25) v
    · intro v hv
      exact (F_u_positive (show (26/25:ℝ)∈Icc 1 (26/25) by norm_num)
        ⟨hv.1.le,hv.2.le.trans hu23.le⟩).le
  have hucomp := hmu (show (79/500:ℝ)∈Icc (79/500) u from ⟨le_rfl,hulo⟩)
    (show u∈Icc (79/500:ℝ) u from ⟨hulo,le_rfl⟩) hulo
  have hbudget := C.F_ceiling_lt
  have hend := medium_endpoint
  linarith

end SquaresInCircles.Eight.CrossedClampBudget
end
end
end

section
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
end
end
end
