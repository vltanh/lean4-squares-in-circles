module

public import SquaresInCircles.Eight.Owners.Small.PositiveZeroEndpoint
public import SquaresInCircles.Eight.Owners.Wide.SmallWrongSign
public import SquaresInCircles.Eight.Words.Crossed.LargeGeometry
public import SquaresInCircles.Eight.Words.Crossed.SmallScalar
public import SquaresInCircles.Eight.Words.Crossed.WrongEndpointBound

/-!
# Eight squares: the original small crossed HG0 source has the strict alignment reserve

Every scalar comparison is formed at the q of the source. The original BT2 contact, the opposite
signed charge and the unchanged H/D/E budget prove the tangent and crossing captures. The support
of the source on the G circle (`actual_hard_cap`) then supplies the GA-alignment reserve
(`HardInput.crossed_HG0_small_reserve`); the lifted A point serves only as a comparison.
-/

section
/-!
## The small crossed source captures its tangent and crossing

The zero endpoint is excluded by the middle envelope on the whole interval. At the aligned
endpoint one Cauchy square bounds the sum of the two middle radii (`radius_pair`). The opposite
contact has a direct quadratic excess bound (`opposite_excess`), which gives `Y > 48/49` and
`r < .01` at the unchanged source radius (`capture`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedSmallCapture
open PositiveSmallScalar CrossedLargeScalar EndpointRotationPenalty EndpointBudgetScalars

def oppositeRadius (Y : ℝ) : ℝ := Real.sqrt (qCap-(2-Y)^2)

theorem opposite_radius {q P Y : ℝ} (S : CrossedSmallScalar.CapData q P Y) :
    (oppositeRadius Y)^2+(2-Y)^2=qCap ∧
      oppositeRadius Y∈Icc (1557/1000 : ℝ) (427/250) := by
  have hy : 2-Y∈Icc (1:ℝ) (233/200) := by constructor <;> linarith [S.Y_mem.1,S.Y_mem.2]
  have hysq := pow_le_pow_left₀ (show 0≤2-Y by linarith [hy.1]) hy.2 2
  have hr : 0≤qCap-(2-Y)^2 := by norm_num [qCap] at *; nlinarith
  have hw := Real.sq_sqrt hr
  have hw0 := Real.sqrt_nonneg (qCap-(2-Y)^2)
  refine ⟨by dsimp [oppositeRadius]; linarith,?_⟩
  dsimp [oppositeRadius]
  constructor
  · norm_num [qCap] at hw
    nlinarith
  · have hyl := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num) hy.1 2
    norm_num [qCap] at hw
    nlinarith

theorem opposite_quadratic {q P Y aB t v : ℝ} (S : CrossedSmallScalar.CapData q P Y)
    (_haB : 0≤aB) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v) :
    t+charge*v≤oppositeRadius Y-3/2+(charge-(2-Y))*v-v^2/5 := by
  obtain ⟨hRcircle,hR⟩ := opposite_radius S
  have hRa : aB-1/2≤oppositeRadius Y-1 := by
    have h := le_of_pow_le_pow_left₀ (by decide : (2:ℕ)≠0) (by linarith [hR.1] : 0≤oppositeRadius Y)
      (show (aB+1/2)^2≤(oppositeRadius Y)^2 by rw [←hRcircle] at hB; linarith)
    linarith
  have htr := transport_trig hv
  have hm := mul_le_mul_of_nonneg_right hRa (show 0≤Real.cos v by linarith [htr.1])
  have hcontact : 1/2≤(oppositeRadius Y-1)*Real.cos v-(2-Y)*Real.sin v := by linarith
  have hquad := WideSmallHardEnvelope.opposite_quadratic
    (show oppositeRadius Y-1∈Icc (557/1000 : ℝ) (177/250) by
      constructor <;> linarith [hR.1,hR.2])
    (show 2-Y∈Icc (1:ℝ) (61/50) by constructor <;> linarith [S.Y_mem.1,S.Y_mem.2])
    hv hcontact
  linarith

theorem opposite_flat {q P Y aB t v : ℝ} (S : CrossedSmallScalar.CapData q P Y)
    (haB : 0≤aB) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hY : charge≤2-Y) : t+charge*v≤oppositeRadius Y-3/2 := by
  have hh := opposite_quadratic S haB ht hv hB hBT
  have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hY) hv.1
  nlinarith [sq_nonneg v]

theorem opposite_excess {q P Y aB t v : ℝ} (S : CrossedSmallScalar.CapData q P Y)
    (haB : 0≤aB) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v) :
    t+charge*v≤oppositeRadius Y-3/2+5/9604 := by
  have hh := opposite_quadratic S haB ht hv hB hBT
  have hm := mul_le_mul_of_nonneg_right S.Y_mem.2 hv.1
  dsimp [charge] at *
  nlinarith [sq_nonneg (v-5/98)]

/-- The A radius and the opposite comparison radius obey one two-circle Cauchy bound, because
their transverse corners sum to 2. -/
theorem radius_pair {q P Y : ℝ} (S : CrossedSmallScalar.CapData q P Y) :
    1-S0≤3-P-oppositeRadius Y := by
  obtain ⟨hRcircle,hR⟩ := opposite_radius S
  have hs := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
  have hs0 := Real.sqrt_nonneg (qCap-1)
  have hsumSq : (P+1+oppositeRadius Y)^2≤4*(qCap-1) := by
    nlinarith [S.circle,S.ceiling,sq_nonneg (P+1-oppositeRadius Y),sq_nonneg (Y-1)]
  have hsum : P+1+oppositeRadius Y≤2*Real.sqrt (qCap-1) := by
    nlinarith [S.P_mem.1,hR.1]
  dsimp [S0]
  linarith

theorem zero_budget_lower {q P Y aB t r Z v : ℝ}
    (S : CrossedSmallScalar.CapData q P Y)
    (hr : r∈Icc 0 frameCap) (hZ : Z∈Ioo (39/200 : ℝ) (2/5))
    (hcontact : V P Y Z=1/2) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v) :
    117/200<demand q P Y r Z-t+charge*(r-v) := by
  have hZi := CrossedWrongEndpointBound.contact_mem hZ
  have hm := WideSmallHardEnvelope.actual_middle_bound
    (b := Y-1/2) (aA := P+1/2) (aB := aB) (t := t) (z := Z) (v := v)
    (show Y-1/2∈Icc (7/25 : ℝ) (1/2) by constructor <;> linarith [S.Y_mem.1,S.Y_mem.2])
    (by linarith [S.P_mem.1])
    (by convert S.circle.le.trans S.ceiling using 1; ring)
    (by convert hB using 1; ring) hZi hv ht
    (by dsimp [V] at hcontact; nlinarith)
    (by convert hBT using 1; ring)
  have hh : r+Z∈Icc (39/200 : ℝ) (11/10) := by
    dsimp [frameCap] at hr
    constructor <;> linarith [hr.1,hr.2,hZ.1,hZ.2]
  have hf := CrossedWrongEndpointCalculus.zeroDemand_reserve S.floor S.ceiling hh
  have heq : demand q P Y r Z=CrossedWrongEndpointCalculus.zeroDemand q (r+Z) := by
    norm_num [demand,W,CrossedWrongEndpointCalculus.zeroDemand,hcontact]
    ring
  rw [←heq] at hf
  linarith

theorem capture {q P Y aB t bH r z v : ℝ}
    (S : CrossedSmallScalar.CapData q P Y)
    (hr : r∈Ioc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hGA : 1/2≤V P Y z) (haB : 0≤aB) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hHG : demand q P Y r z≤bH)
    (hbudget : bH-t+charge*(r-v)<1-S0) :
    48/49<Y ∧ r<1/100 := by
  obtain ⟨Z,hzZ,hZ,hZE,hall⟩ := CrossedSmallScalar.contact_endpoint S hz hGA
  have hzero := zero_budget_lower S ⟨hr.1.le,hr.2⟩ hZ hZE ht hv hB hBT
  have hmin := CrossedSmallScalar.endpoint_minimum S ⟨hr.1.le,hr.2⟩
    ⟨by linarith [hZ.1],hZ.2.le⟩ hall ⟨hz.1,hzZ⟩
  have hconstant := SmallPositiveZeroEndpoint.endpoint_constant_lower
  have hzeroBad : bH<demand q P Y r Z := by linarith
  have hleft : demand q P Y r 0≤bH := by
    by_contra! hbad
    have hh := lt_min hbad hzeroBad
    linarith
  have hgrowth := CrossedSmallScalar.aligned_growth S ⟨hr.1.le,hr.2⟩
  have hradii := radius_pair S
  constructor
  · by_contra! hY
    have hopp := opposite_flat S haB ht hv hB hBT (by dsimp [charge]; linarith)
    have hpos : 0<(charge-9/10)*r := mul_pos (by norm_num [charge]) hr.1
    nlinarith
  · by_contra! hwide
    have hopp := opposite_excess S haB ht hv hB hBT
    dsimp [charge] at hgrowth hbudget hopp
    nlinarith

theorem captured_alignment_gain {q P Y aB t bH r z v : ℝ}
    (S : CrossedSmallScalar.CapData q P Y)
    (hr : r∈Ioc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hGA : 1/2≤V P Y z) (haB : 0≤aB) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hHG : demand q P Y r z≤bH)
    (hbudget : bH-t+charge*(r-v)<1-S0) :
    48/49<Y ∧ r<1/100 ∧ demand q P Y r 0+z/100≤bH := by
  obtain ⟨hY,hshort⟩ := capture S hr hz hGA haB ht hv hB hBT hHG hbudget
  obtain ⟨Z,hzZ,hZ,hZE,hall⟩ := CrossedSmallScalar.contact_endpoint S hz hGA
  have hZi := CrossedWrongEndpointBound.contact_mem hZ
  have hZtight := CrossedSmallScalar.tight_contact_angle S hY.le hZi hZE.ge
  have hgain := CrossedSmallScalar.alignment_gain S hY.le ⟨hr.1.le,hshort.le⟩
    ⟨hZi.1,hZtight.le⟩ hZE hall ⟨hz.1,hzZ⟩
  exact ⟨hY,hshort,by linarith⟩

end SquaresInCircles.Eight.CrossedSmallCapture
end
end
end

section
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
end
end
end
