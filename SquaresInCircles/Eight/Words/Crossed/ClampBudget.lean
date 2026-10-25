module

public import SquaresInCircles.Eight.Words.Crossed.AngleReserve
public import SquaresInCircles.Eight.Words.Crossed.ClampRates
public import SquaresInCircles.Eight.Owners.Endpoint.BudgetScalars

/-!
# Eight squares: the unchanged source budget at an active common-frame cap boundary

The hypotheses (`BoundaryData`) are weak necessary bounds for the HG0 and BT2 contacts at the
same q. The endpoint budget uses the original H and T tangents. A two-radius square identity
forces the active A transverse corner above `48/49` (`BoundaryData.Y_gt`). On the lower half,
the same budget captures the opposite error below `.06` (`BoundaryData.angle_small`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedClampBudget
open CrossedClampRates EndpointRotationPenalty

structure BoundaryData (q Y r u bH bT : ℝ) : Prop where
  floor : qLow≤q
  ceiling : q≤qCap
  Y_mem : Y∈Icc (23/25 : ℝ) (Real.sqrt (q-9/4))
  r_mem : r∈Icc (0 : ℝ) (1/25)
  u_mem : u∈Icc 0 frameCap
  T_nonneg : 0≤bT
  HG : 1/2+(1-transverse q Y)*Real.cos r-
    (adjacent q Y-1)*Real.sin r≤bH
  BT : bT+1/2≤(CrossedClampRates.radius q (2-Y)-1)*Real.cos u-(2-Y)*Real.sin u
  budget : bH-bT+charge*(r-u)<1-EndpointBudgetScalars.S0

def U (q B u : ℝ) : ℝ := (CrossedClampRates.radius q B-1)*Real.sin u+B*Real.cos u
def V (q B u : ℝ) : ℝ := (CrossedClampRates.radius q B-1)*Real.cos u-B*Real.sin u
def g (q B u : ℝ) : ℝ :=
  (CrossedClampRates.radius q B-1)*(Real.cos u-1)-B*Real.sin u+charge*u
def F (q Y u : ℝ) : ℝ :=
  3-CrossedClampRates.radius q Y-(CrossedClampRates.radius q (2-Y)-1)*Real.cos u+(2-Y)*Real.sin u-charge*u

theorem cap_radicals {q Y : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (23/25 : ℝ) (Real.sqrt (q-9/4))) :
    Y<1291/1000 ∧ (2-Y)∈Ioc (709/1000 : ℝ) (27/25) ∧
      0<q-Y^2 ∧ CrossedClampRates.radius q Y∈Ico (3/2 : ℝ) (219/125) ∧
      transverse q Y∈Ico (1/2 : ℝ) (94/125) ∧
      0<q-(transverse q Y)^2 ∧ adjacent q Y∈Ioo (183/100 : ℝ) (383/200) ∧
      0<q-(2-Y)^2 ∧ CrossedClampRates.radius q (2-Y)∈Ioo (33/20 : ℝ) (37/20) ∧
      (CrossedClampRates.radius q Y)^2+Y^2=q ∧
      (adjacent q Y)^2+(transverse q Y)^2=q ∧
      (CrossedClampRates.radius q (2-Y))^2+(2-Y)^2=q := by
  have hqL' : (19577/5000:ℝ)≤q := hqL
  have hq' : q≤9789/2500 := hq
  have hY0 : 0≤Y := by linarith [hY.1]
  have htop : 0≤q-9/4 := by linarith
  have htop2 := Real.sq_sqrt htop
  have hY2 : Y^2≤q-9/4 := by
    have h := pow_le_pow_left₀ hY0 hY.2 2
    rwa [htop2] at h
  have hYlow2 : (23/25:ℝ)^2≤Y^2 := pow_le_pow_left₀ (by norm_num) hY.1 2
  have hYmax : Y<1291/1000 := by
    have h : Real.sqrt (q-9/4)<1291/1000 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num; linarith)
    linarith [hY.2]
  have hB : (2-Y)∈Ioc (709/1000 : ℝ) (27/25) := ⟨by linarith,by linarith [hY.1]⟩
  have hr : 0<q-Y^2 := by linarith
  have hR2 : (CrossedClampRates.radius q Y)^2=q-Y^2 := Real.sq_sqrt hr.le
  have hR : CrossedClampRates.radius q Y∈Ico (3/2 : ℝ) (219/125) :=
    ⟨(Real.le_sqrt (by norm_num) hr.le).2 (by norm_num; linarith),
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num; linarith)⟩
  have hD : transverse q Y∈Ico (1/2 : ℝ) (94/125) := by
    dsimp [transverse]
    constructor <;> linarith [hR.1,hR.2]
  have hD0 : 0≤transverse q Y := by linarith [hD.1]
  have hD2 : (transverse q Y)^2≤(94/125)^2 := pow_le_pow_left₀ hD0 hD.2.le 2
  have hD2' : (1/2:ℝ)^2≤(transverse q Y)^2 := pow_le_pow_left₀ (by norm_num) hD.1 2
  have hx : 0<q-(transverse q Y)^2 := by norm_num at hD2; linarith
  have hX2 : (adjacent q Y)^2=q-(transverse q Y)^2 := Real.sq_sqrt hx.le
  have hX : adjacent q Y∈Ioo (183/100 : ℝ) (383/200) :=
    ⟨Real.lt_sqrt_of_sq_lt (by norm_num at hD2 ⊢; linarith),
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num at hD2' ⊢; linarith)⟩
  have hB0 : 0≤2-Y := by linarith [hB.1]
  have hB2 : (2-Y)^2≤(27/25)^2 := pow_le_pow_left₀ hB0 hB.2 2
  have hB2' : (709/1000:ℝ)^2≤(2-Y)^2 := pow_le_pow_left₀ (by norm_num) hB.1.le 2
  have hb : 0<q-(2-Y)^2 := by norm_num at hB2; linarith
  have hZ2 : (CrossedClampRates.radius q (2-Y))^2=q-(2-Y)^2 := Real.sq_sqrt hb.le
  have hZ : CrossedClampRates.radius q (2-Y)∈Ioo (33/20 : ℝ) (37/20) :=
    ⟨Real.lt_sqrt_of_sq_lt (by norm_num at hB2 ⊢; linarith),
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num at hB2' ⊢; linarith)⟩
  exact ⟨hYmax,hB,hr,hR,hD,hx,hX,hb,hZ,by linarith,by linarith,by linarith⟩

theorem radius_pair_upper {q Y : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (23/25 : ℝ) (Real.sqrt (q-9/4))) :
    CrossedClampRates.radius q Y+CrossedClampRates.radius q (2-Y)≤2*Real.sqrt (qCap-1) := by
  obtain ⟨_,_,_,hR,_,_,_,_,hZ,hR2,_,hZ2⟩ := cap_radicals hqL hq hY
  have hroot0 := Real.sqrt_nonneg (qCap-1)
  have hroot2 := Real.sq_sqrt (by norm_num [qCap] : 0≤qCap-1)
  have hsq : (CrossedClampRates.radius q Y+CrossedClampRates.radius q (2-Y))^2≤(2*Real.sqrt (qCap-1))^2 := by
    rw [mul_pow,hroot2]
    nlinarith only [hR2,hZ2,hq,sq_nonneg (Y-1),sq_nonneg (CrossedClampRates.radius q Y-CrossedClampRates.radius q (2-Y))]
  exact le_of_pow_le_pow_left₀ (by norm_num) (by linarith only [hroot0]) hsq

theorem BoundaryData.F_lt {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) : F q Y u<1-EndpointBudgetScalars.S0 := by
  obtain ⟨_,_,_,_,hD,_,hX,_,_,_,_,_⟩ := cap_radicals C.floor C.ceiling C.Y_mem
  have hreserve := CrossedAngleReserve.nonnegative
    (show 1-transverse q Y≤1/2 by linarith [hD.1])
    (show adjacent q Y-1≤183/200 by linarith [hX.2])
    (show r∈Icc (0:ℝ) (9/10) from ⟨C.r_mem.1,by linarith [C.r_mem.2]⟩)
  have hleft : 5/2-CrossedClampRates.radius q Y≤bH+charge*r := by
    have hh := C.HG
    dsimp [CrossedAngleReserve.curve,transverse] at hreserve hh
    nlinarith
  have hright := C.BT
  have hbudget := C.budget
  dsimp [F]
  nlinarith

theorem BoundaryData.g_pos {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) : 0<g q (2-Y) u := by
  have hf := C.F_lt
  have hj := radius_pair_upper C.floor C.ceiling C.Y_mem
  have hid : F q Y u+g q (2-Y) u=4-CrossedClampRates.radius q Y-CrossedClampRates.radius q (2-Y) := by
    dsimp [F,g]
    ring
  dsimp [EndpointBudgetScalars.S0] at hf
  linarith

theorem U_hasDerivAt (q B u : ℝ) : HasDerivAt (U q B) (V q B u) u := by
  have h1 : HasDerivAt (fun x => (CrossedClampRates.radius q B-1)*Real.sin x+B*Real.cos x)
      ((CrossedClampRates.radius q B-1)*Real.cos u+B*(-Real.sin u)) u :=
    ((Real.hasDerivAt_sin u).const_mul (CrossedClampRates.radius q B-1)).fun_add
      ((Real.hasDerivAt_cos u).const_mul B)
  have e : V q B u=(CrossedClampRates.radius q B-1)*Real.cos u+B*(-Real.sin u) := by simp only [V]; ring
  rw [e]
  exact h1

theorem g_hasDerivAt (q B u : ℝ) :
    HasDerivAt (g q B) (charge-U q B u) u := by
  have h1 : HasDerivAt (fun x => (CrossedClampRates.radius q B-1)*(Real.cos x-1)-B*Real.sin x+charge*x)
      ((CrossedClampRates.radius q B-1)*(-Real.sin u)-B*Real.cos u+charge*1) u :=
    ((((Real.hasDerivAt_cos u).sub_const 1).const_mul (CrossedClampRates.radius q B-1)).fun_sub
      ((Real.hasDerivAt_sin u).const_mul B)).fun_add ((hasDerivAt_id' u).const_mul charge)
  have e : charge-U q B u=(CrossedClampRates.radius q B-1)*(-Real.sin u)-B*Real.cos u+charge*1 := by
    simp only [U]; ring
  rw [e]
  exact h1

theorem V_left {q B u v : ℝ} (hP : 0≤CrossedClampRates.radius q B-1) (hB : 0≤B)
    (hu : u∈Icc 0 frameCap) (hv : v∈Icc 0 u) : V q B u≤V q B v := by
  have hv' : v∈Icc 0 frameCap := ⟨hv.1,hv.2.trans hu.2⟩
  have hc := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.cos_anti hv' hu hv.2) hP
  have hs := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.sin_mono hv' hu hv.2) hB
  dsimp [V]
  linarith

theorem U_lower_of_contact {q B u v : ℝ} (hP : 0≤CrossedClampRates.radius q B-1) (hB : 0≤B)
    (hu : u∈Icc 0 frameCap) (hV : 1/2≤V q B u) (hv : v∈Icc 0 u) :
    B+v/2≤U q B v := by
  have hc : ContinuousOn (U q B) (Icc 0 u) := by unfold U; fun_prop
  have hh := derivative_reserve hc
    (fun z hz => U_hasDerivAt q B z)
    (fun z hz => hV.trans (V_left hP hB hu (Ioo_subset_Icc_self hz)))
    (show (0:ℝ)∈Icc 0 u from ⟨le_rfl,hu.1⟩) hv hv.1
  simp only [U,Real.sin_zero,Real.cos_zero,mul_zero,mul_one,zero_add,sub_zero] at hh ⊢
  linarith

theorem BoundaryData.Y_gt {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) : 48/49<Y := by
  obtain ⟨_,hB,_,_,_,_,_,_,hZ,_,_,_⟩ := cap_radicals C.floor C.ceiling C.Y_mem
  have hB0 : 0≤2-Y := by linarith [hB.1]
  have hP : 0≤CrossedClampRates.radius q (2-Y)-1 := by linarith [hZ.1]
  have hV : 1/2≤V q (2-Y) u := by dsimp [V]; linarith [C.BT,C.T_nonneg]
  by_contra hY
  have hBcharge : charge≤2-Y := by dsimp [charge]; linarith
  have hm : AntitoneOn (g q (2-Y)) (Icc 0 u) := by
    apply antiOn_of_hasDeriv_nonpos
    · unfold g; fun_prop
    · intro v hv
      exact g_hasDerivAt q (2-Y) v
    · intro v hv
      have hh := U_lower_of_contact hP hB0 C.u_mem hV (Ioo_subset_Icc_self hv)
      linarith [hv.1]
  have hh := hm (show (0:ℝ)∈Icc 0 u from ⟨le_rfl,C.u_mem.1⟩)
    (show u∈Icc 0 u from ⟨C.u_mem.1,le_rfl⟩) C.u_mem.1
  have hp := C.g_pos
  have h0 : g q (2-Y) 0=0 := by simp [g]
  linarith

theorem g_le_at_one {q B u : ℝ} (hqL : qLow≤q) (_hq : q≤qCap)
    (hB : B∈Icc (1:ℝ) (27/25)) (hu : u∈Icc 0 frameCap) :
    g q B u≤g q 1 u := by
  have hqL' := hqL
  dsimp [qLow] at hqL'
  have hB2 := pow_le_pow_left₀ (show 0≤B by linarith [hB.1]) hB.2 2
  have hrad : 0≤q-B^2 := by nlinarith
  have hZ2 : (CrossedClampRates.radius q B)^2=q-B^2 := Real.sq_sqrt hrad
  have hZ0 : 0≤CrossedClampRates.radius q B := Real.sqrt_nonneg _
  have hZ : 1≤CrossedClampRates.radius q B := by nlinarith
  have hR2 : (CrossedClampRates.radius q 1)^2=q-1 := by
    dsimp [CrossedClampRates.radius]
    rw [one_pow,Real.sq_sqrt (by linarith : 0≤q-1)]
  have hR0 : 0≤CrossedClampRates.radius q 1 := Real.sqrt_nonneg _
  have hR1 : (27/25:ℝ)≤CrossedClampRates.radius q 1 := by nlinarith
  have hsum : B+1≤CrossedClampRates.radius q 1+CrossedClampRates.radius q B := by linarith [hB.2]
  have hdiff : CrossedClampRates.radius q 1-CrossedClampRates.radius q B≤B-1 := by
    refine le_of_not_gt fun hcon => ?_
    have h1 := mul_lt_mul_of_pos_right hcon (show 0<CrossedClampRates.radius q 1+CrossedClampRates.radius q B by linarith)
    have h2 := mul_le_mul_of_nonneg_left hsum (show 0≤B-1 by linarith [hB.1])
    nlinarith
  have ht := transport_trig hu
  have hcs : 1-Real.cos u≤Real.sin u := by
    nlinarith [Real.sin_sq_add_cos_sq u,
      mul_nonneg (show 0≤Real.cos u by linarith [ht.1]) ht.2.2.1]
  have hm1 := mul_le_mul_of_nonneg_right hdiff (sub_nonneg.mpr ht.2.1)
  have hm2 := mul_le_mul_of_nonneg_left hcs (show 0≤B-1 by linarith [hB.1])
  dsimp [g]
  linarith

theorem g_one_small_negative {q : ℝ} (hqL : qLow≤q) :
    g q 1 (3/50)<0 := by
  have hqL' := hqL
  dsimp [qLow] at hqL'
  have hR0 : 0≤CrossedClampRates.radius q 1 := Real.sqrt_nonneg _
  have hR2 : (CrossedClampRates.radius q 1)^2=q-1 := by
    dsimp [CrossedClampRates.radius]
    rw [one_pow,Real.sq_sqrt (by linarith : 0≤q-1)]
  have hR : 8537/5000<CrossedClampRates.radius q 1 := by nlinarith
  have hc := cos_upper_four (show (0:ℝ)≤3/50 by norm_num)
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤3/50 by norm_num)
  have hc0 : Real.cos (3/50)-1<0 := by norm_num at hc ⊢; linarith
  have hm := mul_lt_mul_of_neg_right
    (show 8537/5000-1<CrossedClampRates.radius q 1-1 by linarith) hc0
  have hm' := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤8537/5000-1)
  dsimp [g,charge]
  nlinarith

theorem BoundaryData.angle_small {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) (hY : Y≤1) : u<3/50 := by
  obtain ⟨_,hB,_,_,_,_,_,_,hZ,_,_,_⟩ := cap_radicals C.floor C.ceiling C.Y_mem
  have hB1 : 1≤2-Y := by linarith
  have hP : 0≤CrossedClampRates.radius q (2-Y)-1 := by linarith [hZ.1]
  have hV : 1/2≤V q (2-Y) u := by dsimp [V]; linarith [C.BT,C.T_nonneg]
  by_contra hu
  have hlu : 3/50≤u := le_of_not_gt hu
  have hm : AntitoneOn (g q (2-Y)) (Icc (3/50) u) := by
    apply antiOn_of_hasDeriv_nonpos
    · unfold g; fun_prop
    · intro v hv
      exact g_hasDerivAt q (2-Y) v
    · intro v hv
      have hvi : v∈Icc 0 u := ⟨by linarith [hv.1],hv.2.le⟩
      have hh := U_lower_of_contact hP (by linarith : 0≤2-Y) C.u_mem hV hvi
      dsimp [charge]
      linarith [hv.1]
  have hh := hm (show (3/50:ℝ)∈Icc (3/50) u from ⟨le_rfl,hlu⟩)
    (show u∈Icc (3/50:ℝ) u from ⟨hlu,le_rfl⟩) hlu
  have hcompare := g_le_at_one C.floor C.ceiling ⟨hB1,hB.2⟩
    (show (3/50:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hn := g_one_small_negative C.floor
  have hp := C.g_pos
  linarith

end SquaresInCircles.Eight.CrossedClampBudget
