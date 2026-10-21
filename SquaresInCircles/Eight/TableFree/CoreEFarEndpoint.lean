module

public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeEnvelope
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# The far negative endpoint on the full core-E coefficient rectangle

Uncompiled source draft of section 7 of
HAND_G5_POSITIVE_GA_CORE_E_ANGULAR_ENVELOPE.md and equations (30)--(31)
of its scalar companion.  At the one fixed far angle the negative norm
denominator is small enough to give separate concavity in both force
coefficients, including their ratios below one half.  Four intrinsic
coefficient corners then give the bound on the whole rectangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CoreEFarEndpoint
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison

def R : ℝ := Real.sqrt qCap
def Rlower : ℝ := 158303/80000
def F (p q : ℝ) : ℝ := V R p q frameCap-p+87/1250

theorem cap_mem : frameCap∈Icc 0 frameCap := by
  exact ⟨by norm_num [frameCap],le_rfl⟩

theorem radius_lower : Rlower<R := by
  have hs := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hn := Real.sqrt_nonneg qCap
  dsimp [R,Rlower,qCap] at *
  nlinarith

theorem rectangle_ratio {p q : ℝ}
    (hp : p∈Icc (1263/2500:ℝ) (4/5))
    (hq : q∈Icc (863/1000:ℝ) (26/25)) :
    0<p ∧ 0<q ∧ p/q∈Icc (12/25:ℝ) 1 := by
  have hp0 : 0<p := by linarith [hp.1]
  have hq0 : 0<q := by linarith [hq.1]
  refine ⟨hp0,hq0,?_,?_⟩
  · exact (le_div_iff₀ hq0).2 (by linarith [hp.1,hq.2])
  · exact (div_le_one hq0).2 (by linarith [hp.2,hq.1])

/-- The strict denominator comparison used by both coefficient Hessians.
The range begins at `.48`, so no half-ratio restriction is imported. -/
theorem far_fraction {r : ℝ} (hr : r∈Icc (12/25:ℝ) 1) :
    1/(shape r)^3<(Real.cos frameCap)^2/(root r (Real.sin frameCap))^3 := by
  have hr0 : 0<r := by linarith [hr.1]
  have hu := sin_mem cap_mem
  have hN := root_pos r hu
  have hS := shape_pos r
  have hN2 := root_sq r hu
  have hS2 := shape_sq r
  have hratio : (39/50)*(1+r^2)≤2*r := by
    have hh := mul_nonneg (show 0≤r-12/25 by linarith [hr.1])
      (show 0≤1-r by linarith [hr.2])
    nlinarith [hr.1]
  have hsin := mul_lt_mul_of_pos_left cap_sin_lower (by linarith : 0<2*r)
  have hhalf : (root r (Real.sin frameCap))^2<(shape r)^2/2 := by
    nlinarith [sq_nonneg r]
  have hNS : root r (Real.sin frameCap)<shape r := by
    nlinarith
  have hcos := (transport_trig cap_mem).1
  have hcos2 : (1/2:ℝ)<(Real.cos frameCap)^2 := by
    have hh : 0<(Real.cos frameCap-478/625)*(Real.cos frameCap+478/625) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hcube1 := mul_lt_mul_of_pos_right hhalf hN
  have hcube2 := mul_lt_mul_of_pos_left hNS
    (show 0<(shape r)^2/2 by positivity)
  have hcube3 := mul_lt_mul_of_pos_right hcos2 (pow_pos hS 3)
  have hcube : (root r (Real.sin frameCap))^3<
      (Real.cos frameCap)^2*(shape r)^3 := by
    nlinarith only [hcube1,hcube2,hcube3]
  exact (div_lt_div_iff₀ (pow_pos hS 3) (pow_pos hN 3)).2 (by simpa using hcube)

def smallerSecond (r : ℝ) : ℝ :=
  R*(1/(shape r)^3-(Real.cos frameCap)^2/(root r (Real.sin frameCap))^3)

theorem smallerD_deriv (r : ℝ) :
    HasDerivAt (fun a => smallerD R a frameCap) (smallerSecond r) r := by
  have hu := sin_mem cap_mem
  have hn := (root_pos r hu).ne'
  have hs := (shape_pos r).ne'
  have hpN := root_power_reduce r hu
  have hpS := shape_power_reduce r
  have hraw := (((hasDerivAt_id r).div (shape_hasDerivAt r) hs).sub
    (((hasDerivAt_id r).sub_const (Real.sin frameCap)).div
      (root_hasDerivAt_r hu) hn)).const_mul R
  have hc : (Real.cos frameCap)^2=1-(Real.sin frameCap)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq frameCap]
  convert hraw using 1
  · rfl
  · dsimp [smallerSecond]
    rw [hc]
    field_simp [hn,hs]
    ring_nf
    simp only [hpN 0,hpN 1,hpN 2,hpN 3,hpN 4,hpN 5,hpN 6,
      hpS 0,hpS 1,hpS 2,hpS 3,hpS 4,hpS 5,hpS 6,pow_zero,pow_one]
    ring

theorem smallerSecond_nonpos {r : ℝ} (hr : r∈Icc (12/25:ℝ) 1) :
    smallerSecond r≤0 := by
  dsimp [smallerSecond]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg qCap)
    (sub_nonpos.mpr (far_fraction hr).le)

theorem far_Dr_nonneg {r : ℝ} (hr : r∈Icc (12/25:ℝ) 1) :
    0≤Dr R r frameCap := by
  dsimp [Dr]
  exact mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg qCap) (by linarith [hr.1]))
    (sub_nonneg.mpr (far_fraction hr).le)

theorem F_concave_p {q : ℝ} (hq : q∈Icc (863/1000:ℝ) (26/25)) :
    ConcaveOn ℝ (Icc (1263/2500:ℝ) (4/5)) (fun p => F p q) := by
  have hq0 : 0<q := by linarith [hq.1]
  apply concave_of_deriv2
    (f' := fun p => smallerD R (p/q) frameCap-1)
    (f'' := fun p => smallerSecond (p/q)*(1/q))
  · intro p hp
    have hp0 := (rectangle_ratio hp hq).1
    simpa only [F] using
      (((V_hasDerivAt_p (R := R) hp0 hq0 cap_mem).sub (hasDerivAt_id p)).add_const
        (87/1250))
  · intro p hp
    have hh := (smallerD_deriv (p/q)).comp p ((hasDerivAt_id p).div_const q)
    simpa only [one_div] using hh.sub_const 1
  · intro p hp
    exact mul_nonpos_of_nonpos_of_nonneg
      (smallerSecond_nonpos (rectangle_ratio hp hq).2.2) (by positivity)

theorem F_concave_q {p : ℝ} (hp : p∈Icc (1263/2500:ℝ) (4/5)) :
    ConcaveOn ℝ (Icc (863/1000:ℝ) (26/25)) (F p) := by
  have hp0 : 0<p := by linarith [hp.1]
  apply concave_of_deriv2
    (f' := fun q => D R (p/q) frameCap)
    (f'' := fun q => Dr R (p/q) frameCap*(-p/q^2))
  · intro q hq
    have hq0 := (rectangle_ratio hp hq).2.1
    simpa only [F] using
      ((V_hasDerivAt_q (R := R) hp0 hq0 cap_mem).sub_const p).add_const (87/1250)
  · intro q hq
    exact D_quotient_hasDerivAt (rectangle_ratio hp hq).2.1 cap_mem
  · intro q hq
    exact mul_nonpos_of_nonneg_of_nonpos
      (far_Dr_nonneg (rectangle_ratio hp hq).2.2)
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp0.le) (sq_nonneg q))

/-- A lower zero-angle radical and upper negative-angle radical transfer
their exact rational reserve to the original norm expression. -/
theorem corner_lower {p q a b reserve : ℝ}
    (hp : 0<p) (hq : 0<q) (ha : 0≤a) (hb : 0<b) (hab : b<a)
    (haz : a^2<p^2+q^2)
    (hbn : p^2+q^2-2*p*q*HighOrderTaylor.S11 frameCap<b^2)
    (hreserve : reserve<q*(Arithmetic.cos10 frameCap-1)+
      Rlower*(a-b)-p+87/1250) : reserve<F p q := by
  have hzero : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hneg : |-frameCap|≤frameCap := by norm_num [frameCap]
  have hZ := pairNorm_pos hp hq hzero
  have hN := pairNorm_pos hp hq hneg
  have hZ2 := pairNorm_sq hp hq hzero
  have hN2 := pairNorm_sq hp hq hneg
  simp only [pairEnergy,pairProduct,Real.sin_zero,Real.sin_neg] at hZ2 hN2
  have hZlo : a<pairNorm p q 0 := by nlinarith
  have hS := HighOrderTaylor.S11_le_sin (show 0≤frameCap by norm_num [frameCap])
  have hSmul := mul_le_mul_of_nonneg_left hS (show 0≤2*p*q by positivity)
  have hNhi : pairNorm p q (-frameCap)<b := by nlinarith
  have hgap : a-b<pairNorm p q 0-pairNorm p q (-frameCap) := by linarith
  have hgap0 : 0<pairNorm p q 0-pairNorm p q (-frameCap) := by linarith
  have hR0 : 0<Rlower := by norm_num [Rlower]
  have hmul1 := mul_lt_mul_of_pos_left hgap hR0
  have hmul2 := mul_lt_mul_of_pos_right radius_lower hgap0
  have hC := Arithmetic.cos10_le_cos (show 0≤frameCap by norm_num [frameCap])
  have hCmul := mul_le_mul_of_nonneg_left hC hq.le
  dsimp [F,V]
  linarith

theorem corner_low_low : (1513/50000:ℝ)<F (1263/2500) (863/1000) := by
  apply corner_lower (a := 999998019/1000000000) (b := 662007699/1000000000)
  all_goals norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8,frameCap,Rlower]

theorem corner_low_high : (157/500000:ℝ)<F (1263/2500) (26/25) := by
  apply corner_lower (a := 1156212368/1000000000) (b := 812325543/1000000000)
  all_goals norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8,frameCap,Rlower]

theorem corner_high_low : (269/100000:ℝ)<F (4/5) (863/1000) := by
  apply corner_lower (a := 1176762083/1000000000) (b := 703728085/1000000000)
  all_goals norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8,frameCap,Rlower]

theorem corner_high_high : (2651/100000:ℝ)<F (4/5) (26/25) := by
  apply corner_lower (a := 1312097557/1000000000) (b := 805991172/1000000000)
  all_goals norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8,frameCap,Rlower]

theorem F_positive {p q : ℝ}
    (hp : p∈Icc (1263/2500:ℝ) (4/5))
    (hq : q∈Icc (863/1000:ℝ) (26/25)) : 0<F p q := by
  have hlo : 0<F (1263/2500) q :=
    concave_gt_of_endpoints (F_concave_q (by norm_num)) hq
      (by linarith [corner_low_low]) (by linarith [corner_low_high])
  have hhi : 0<F (4/5) q :=
    concave_gt_of_endpoints (F_concave_q (by norm_num)) hq
      (by linarith [corner_high_low]) (by linarith [corner_high_high])
  exact concave_gt_of_endpoints (F_concave_p hq) hp hlo hhi

theorem rectangle_lower {p q : ℝ}
    (hp : p∈Icc (1263/2500:ℝ) (4/5))
    (hq : q∈Icc (863/1000:ℝ) (26/25)) :
    p-87/1250<OrdinaryAngleConcavity.V (Real.sqrt qCap) p q frameCap := by
  have hh := F_positive hp hq
  dsimp [F,R] at hh
  linarith

end SquaresInCircles.Eight.TableFree.CoreEFarEndpoint
