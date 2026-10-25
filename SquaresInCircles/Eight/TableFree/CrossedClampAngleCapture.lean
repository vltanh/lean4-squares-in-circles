module

public import SquaresInCircles.Eight.TableFree.CrossedClampBudget

/-!
# The remaining active-boundary angle capture

Uncompiled source draft.  On 1 <= Y <= 1.04, the actual normal hard
contact first captures u below .23.  The unchanged budget is monotone
on the entire hypothetical rectangle .158 <= u < .23: its Y derivative
is negative and its u derivative is positive.  One exact rational
endpoint contradicts that budget, giving u < .158 without sampling.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CrossedClampBudget
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

end SquaresInCircles.Eight.TableFree.CrossedClampBudget
