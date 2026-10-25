module

public import SquaresInCircles.Eight.TableFree.GlobalGAClippedCircle
public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeSlope

/-!
# Variable D-support comparison on the whole negative-angle interval

Uncompiled source.  The reference coefficient satisfies `.5 ≤ k ≤ .85`
and the actual transverse coefficient satisfies `k ≤ c ≤ 2`.  The
diagonal derivative and the full-circle derivative both dominate the
same ordinary H increment.  Only their exact equality switch is needed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
open Secondary PositiveAngularEnvelope PairNormCalculus
open OrdinaryAngleConcavity OrdinaryNegativeSlope

theorem reference_slope_zero {k : ℝ} (hk : k∈Icc (1/2) (17/20)) :
    Vd R k 1 0<1283/1000 := by
  have hk0 : 0<k := by linarith [hk.1]
  have hN := pairNorm_pos (q:=1) (t:=0) hk0 (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (q:=1) (t:=0) hk0 (by norm_num) (by norm_num [frameCap])
  have hk2 := pow_le_pow_left₀ hk0.le hk.2 2
  have hRk : (R*k)^2=qCap*k^2 := by rw [mul_pow,radius_sq]
  have hreserve : qCap*(17/20:ℝ)^2<
      (1283/1000:ℝ)^2*(1+(17/20:ℝ)^2) := by norm_num [qCap]
  have hsq : (R*k)^2<(1283/1000:ℝ)^2*(pairNorm k 1 0)^2 := by
    norm_num [pairEnergy,pairProduct] at hN2
    rw [hRk]
    norm_num [qCap] at hreserve ⊢
    nlinarith
  have hcross : R*k<(1283/1000)*pairNorm k 1 0 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg qCap) hk0.le]
  have he : Vd R k 1 0=R*k/pairNorm k 1 0 := by
    simp [Vd,mixedNDerivative,normD1,pairProduct]
    ring
  rw [he]
  exact (div_lt_iff₀ hN).2 hcross

theorem reference_slope_upper {k s : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hs : s∈Icc 0 frameCap) :
    Vd R k 1 s<1283/1000 := by
  have hanti := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le
    (show 0<k by linarith [hk.1])
    (show k≤1 by linarith [hk.2]) (show 1≤2*k by linarith [hk.1])
  exact (hanti (by norm_num [frameCap]) hs hs.1).trans_lt (reference_slope_zero hk)

theorem diagonal_slope_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    (1327/1000:ℝ)<(GlobalGA.Secondary.diagonal-1/2)*Real.sin s+(GlobalGA.Secondary.diagonal+1/2)*Real.cos s := by
  have hsin : (6442/10000:ℝ)≤Real.sin frameCap := by
    have h := cap_trig.1
    norm_num [Arithmetic.sin7,frameCap] at h
    linarith
  have hcos := (transport_trig (x:=frameCap) (by norm_num [frameCap])).1
  have hm₁ := mul_le_mul
    (show (3992/10000:ℝ)≤GlobalGA.Secondary.diagonal-1/2 by linarith [diagonal_bounds.1])
    hsin (by norm_num : (0:ℝ)≤6442/10000) (by linarith [diagonal_bounds.1])
  have hm₂ := mul_le_mul
    (show (13992/10000:ℝ)≤GlobalGA.Secondary.diagonal+1/2 by linarith [diagonal_bounds.1])
    hcos.le (by norm_num : (0:ℝ)≤7648/10000) (by linarith [diagonal_bounds.1])
  have h := trig_concave_gt (α:=0) (A:=GlobalGA.Secondary.diagonal-1/2) (B:=GlobalGA.Secondary.diagonal+1/2)
    (m:=(1327/1000:ℝ)) (by linarith [diagonal_bounds.1])
    (by linarith [diagonal_bounds.1]) (by norm_num : (0:ℝ)≤0)
    (show frameCap≤Real.pi/2 by norm_num [frameCap]; linarith [Real.pi_gt_three]) hs
    (by norm_num; linarith [diagonal_bounds.1]) (by nlinarith)
  simpa using h

theorem negative_norm_fraction_mono {k c s : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hc : c∈Icc k 2)
    (hs : s∈Icc 0 frameCap) :
    k/pairNorm k 1 (-s)≤c/pairNorm c 1 (-s) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hc0 : 0<c := hk0.trans_le hc.1
  have habs : |-s|≤frameCap := by rw [abs_neg,abs_of_nonneg hs.1]; exact hs.2
  have hNk := pairNorm_pos hk0 (by norm_num : (0:ℝ)<1) habs
  have hNc := pairNorm_pos hc0 (by norm_num : (0:ℝ)<1) habs
  have hNk2 := pairNorm_sq hk0 (by norm_num : (0:ℝ)<1) habs
  have hNc2 := pairNorm_sq hc0 (by norm_num : (0:ℝ)<1) habs
  have hsU : Real.sin s≤7/10 := (Real.sin_le hs.1).trans (by simpa [frameCap] using hs.2)
  have hsin := mul_le_mul_of_nonneg_left hsU (mul_nonneg hc0.le hk0.le)
  have hkU := mul_nonneg (sub_nonneg.mpr hk.2) hc0.le
  have hcU := mul_nonneg (sub_nonneg.mpr hc.2) hk0.le
  have hfactor : 0≤c+k-2*c*k*Real.sin s := by nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hc.1) hfactor
  have hid : (c*pairNorm k 1 (-s))^2-(k*pairNorm c 1 (-s))^2=
      (c-k)*(c+k-2*c*k*Real.sin s) := by
    rw [mul_pow,mul_pow,hNk2,hNc2]
    simp only [pairEnergy,pairProduct,Real.sin_neg]
    ring
  have hcross : k*pairNorm c 1 (-s)≤c*pairNorm k 1 (-s) := by
    rw [← hid] at hprod
    nlinarith [mul_nonneg hk0.le hNc.le,mul_nonneg hc0.le hNk.le]
  exact (div_le_div_iff₀ hNk hNc).2 hcross

theorem negative_full_slope_nonneg {k c s : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hc : c∈Icc k 2)
    (hs : s∈Icc 0 frameCap) : 0≤Vd R c 1 s-Vd R k 1 s := by
  have hcos : 0≤Real.cos s := by linarith [(transport_trig hs).1]
  have h := mul_le_mul_of_nonneg_left (negative_norm_fraction_mono hk hc hs)
    (mul_nonneg (Real.sqrt_nonneg qCap) hcos)
  have he (p : ℝ) : Vd R p 1 s=
      -Real.sin s+(R*Real.cos s)*(p/pairNorm p 1 (-s)) := by
    simp [Vd,mixedNDerivative,normD1,pairProduct]
    ring
  rw [he,he]
  linarith

def negativeDiagonalResidual (k c s : ℝ) : ℝ :=
  (Real.cos s+Real.sin s-1)/2-GlobalGA.Secondary.diagonal*(Real.cos s+c-Real.sin s)+
    clippedSupport 1 c-V R k 1 s

def negativeFullResidual (k c s : ℝ) : ℝ :=
  V R c 1 s+clippedSupport 1 c-fullSupport 1 c-V R k 1 s

theorem negativeDiagonalResidual_hasDerivAt {k c s : ℝ}
    (hk : 0<k) (hs : s∈Icc 0 frameCap) :
    HasDerivAt (negativeDiagonalResidual k c)
      ((GlobalGA.Secondary.diagonal-1/2)*Real.sin s+(GlobalGA.Secondary.diagonal+1/2)*Real.cos s-Vd R k 1 s) s := by
  have hfirst := (((Real.hasDerivAt_cos s).fun_add (Real.hasDerivAt_sin s)).sub_const 1).div_const 2
  have hsecond := (((Real.hasDerivAt_cos s).add_const c).fun_sub
    (Real.hasDerivAt_sin s)).const_mul GlobalGA.Secondary.diagonal
  have h := ((hfirst.fun_sub hsecond).add_const (clippedSupport 1 c)).fun_sub
    (V_hasDerivAt (R:=R) (q:=1) hk (by norm_num) hs)
  exact h.congr_deriv (by ring)

theorem negativeFullResidual_hasDerivAt {k c s : ℝ}
    (hk : 0<k) (hc : 0<c) (hs : s∈Icc 0 frameCap) :
    HasDerivAt (negativeFullResidual k c) (Vd R c 1 s-Vd R k 1 s) s := by
  exact (((V_hasDerivAt hc (by norm_num) hs).add_const
    (clippedSupport 1 c)).sub_const (fullSupport 1 c)).sub
      (V_hasDerivAt hk (by norm_num) hs)

theorem negativeDiagonalResidual_monotone {k c : ℝ}
    (hk : k∈Icc (1/2) (17/20)) :
    MonotoneOn (negativeDiagonalResidual k c) (Icc 0 frameCap) := by
  have hk0 : 0<k := by linarith [hk.1]
  apply monoOn_of_hasDeriv_nonneg
  · intro s hs
    exact (negativeDiagonalResidual_hasDerivAt hk0 hs).continuousAt.continuousWithinAt
  · intro s hs
    exact negativeDiagonalResidual_hasDerivAt hk0 (Ioo_subset_Icc_self hs)
  · intro s hs
    have hsd := diagonal_slope_lower (Ioo_subset_Icc_self hs)
    have hsv := reference_slope_upper hk (Ioo_subset_Icc_self hs)
    linarith

theorem negativeFullResidual_monotone {k c : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hc : c∈Icc k 2) :
    MonotoneOn (negativeFullResidual k c) (Icc 0 frameCap) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hc0 : 0<c := hk0.trans_le hc.1
  apply monoOn_of_hasDeriv_nonneg
  · intro s hs
    exact (negativeFullResidual_hasDerivAt hk0 hc0 hs).continuousAt.continuousWithinAt
  · intro s hs
    exact negativeFullResidual_hasDerivAt hk0 hc0 (Ioo_subset_Icc_self hs)
  · intro s hs
    exact negative_full_slope_nonneg hk hc (Ioo_subset_Icc_self hs)

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
