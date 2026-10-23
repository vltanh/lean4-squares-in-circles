module

public import SquaresInCircles.Eight.TableFree.GlobalGAOneAngleFunctions

/-!
# Exact intrinsic support comparisons for the H/G one-angle terms

Uncompiled translation.  The short-arc values use positive square and
Taylor bounds.  The remaining whole arcs are controlled by the actual
axial-support test and its proved monotonicity.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity

abbrev cos6 (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720

theorem H_short_norm : pairNorm k 1 (-(3/5:ℝ))<8517214/10000000 := by
  have hN := pairNorm_sq (p:=k) (q:=1) (t:= -(3/5:ℝ))
    (by norm_num [k]) (by norm_num) (by norm_num [frameCap])
  have hs := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
  norm_num [pairEnergy,pairProduct,k,Real.sin_neg] at hN hs
  nlinarith [Real.sqrt_nonneg (k^2+1^2+2*k*1*Real.sin (-(3/5:ℝ)))]

theorem G_short_norm : pairNorm k l (-(3/10:ℝ))<15143111/10000000 := by
  have hN := pairNorm_sq (p:=k) (q:=l) (t:= -(3/10:ℝ))
    (by norm_num [k]) (by norm_num [l]) (by norm_num [frameCap])
  have hs := sin_lower_seven (show (0:ℝ)≤3/10 by norm_num)
  norm_num [pairEnergy,pairProduct,k,l,Real.sin_neg] at hN hs
  nlinarith [Real.sqrt_nonneg (k^2+l^2+2*k*l*Real.sin (-(3/10:ℝ)))]

theorem H_short_endpoint : (133/10000:ℝ)<negativeFull k 1 (3/5) := by
  have hN0 := radius_norm_lower (by norm_num : (0:ℝ)<12651580/10000000) H_zero_norm.1
  have hN1 := radius_norm_upper (by norm_num : (0:ℝ)<8517214/10000000) H_short_norm
  have hc := cos_lower_six (show (0:ℝ)≤3/5 by norm_num)
  norm_num [k] at hN0 hN1 hc
  dsimp [negativeFull,V]
  norm_num [k,charge]
  nlinarith

theorem G_short_endpoint : (483/10000:ℝ)<negativeFull k l (3/10) := by
  have hN0 := radius_norm_lower (by norm_num : (0:ℝ)<17329526/10000000) G_zero_norm.1
  have hN1 := radius_norm_upper (by norm_num : (0:ℝ)<15143111/10000000) G_short_norm
  have hc := cos_lower_six (show (0:ℝ)≤3/10 by norm_num)
  norm_num [k,l] at hN0 hN1 hc
  dsimp [negativeFull,V]
  norm_num [k,l,charge]
  nlinarith

theorem H_axial_start : 0<axialTest k 1 (3/5) := by
  have h := axial_test_endpoint_lower (p:=k) (q:=1) (w:=3/5)
    (S:=Arithmetic.sin7 (3/5)) (C:=cos6 (3/5)) (by norm_num)
    (sin_lower_seven (by norm_num)) (cos_lower_six (by norm_num))
    (by norm_num [k,Arithmetic.sin7])
  norm_num [k,Arithmetic.sin7,cos6] at h
  linarith

theorem G_axial_start : 0<axialTest k l (3/10) := by
  have h := axial_test_endpoint_lower (p:=k) (q:=l) (w:=3/10)
    (S:=Arithmetic.sin7 (3/10)) (C:=cos6 (3/10)) (by norm_num [l])
    (sin_lower_seven (by norm_num)) (cos_lower_six (by norm_num))
    (by norm_num [k,l,Arithmetic.sin7])
  norm_num [k,l,Arithmetic.sin7,cos6] at h
  linarith

theorem H_axial_derivative_cap : axialOneD 1 frameCap<0 := by
  have ht := transport_trig (x:=frameCap) (by norm_num [frameCap])
  have hc := cos_upper_four (show 0≤frameCap by norm_num [frameCap])
  have hprod := mul_le_mul
    (show axial-1/2≤14145757/10000000-1/2 by linarith [axial_bounds.2])
    ht.2.2.2.1.le ht.2.2.1 (by norm_num : (0:ℝ)≤14145757/10000000-1/2)
  norm_num [frameCap] at hc
  dsimp [axialOneD,charge]
  nlinarith

theorem G_axial_derivative_start : 0<axialOneD l (3/10) := by
  have hs := sin_lower_seven (show (0:ℝ)≤3/10 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤3/10 by norm_num)
  have hprod := mul_le_mul
    (show (14145756/10000000:ℝ)-1/2≤axial-1/2 by linarith [axial_bounds.1])
    hs (by norm_num : (0:ℝ)≤(3/10)-(3/10)^3/6+(3/10)^5/120-(3/10)^7/5040)
    (by linarith [axial_bounds.1] : 0≤axial-1/2)
  norm_num at hprod hc
  dsimp [axialOneD,l,charge]
  nlinarith

theorem H_axial_endpoint : (35/10000:ℝ)<axialOne k 1 frameCap := by
  have hN0 := radius_norm_lower (by norm_num : (0:ℝ)<12651580/10000000) H_zero_norm.1
  have hs := cap_trig.1
  have hc := cap_trig.2.2.2
  have hc0 : 0≤Real.cos frameCap := by
    linarith [(transport_trig (x:=frameCap) (by norm_num [frameCap])).1]
  have hprod := mul_le_mul
    (show axial-1/2≤14145757/10000000-1/2 by linarith [axial_bounds.2])
    hc hc0 (by norm_num : (0:ℝ)≤14145757/10000000-1/2)
  dsimp [axialOne]
  rw [fullSupport_pair k 1]
  norm_num [Arithmetic.sin7,Arithmetic.cos8,frameCap,k,charge] at hN0 hs hprod ⊢
  nlinarith

theorem G_axial_endpoint : 0<axialOne k l (3/10) := by
  have hN0 := radius_norm_lower (by norm_num : (0:ℝ)<17329526/10000000) G_zero_norm.1
  have hs := sin_lower_seven (show (0:ℝ)≤3/10 by norm_num)
  have hc := Arithmetic.cos_le_cos8 (show (0:ℝ)≤3/10 by norm_num)
  have hc0 : 0≤Real.cos (3/10:ℝ) := by
    linarith [(transport_trig (x:=(3/10:ℝ)) (by norm_num)).1]
  have hprod := mul_le_mul
    (show axial-1/2≤14145757/10000000-1/2 by linarith [axial_bounds.2])
    hc hc0 (by norm_num : (0:ℝ)≤14145757/10000000-1/2)
  dsimp [axialOne]
  rw [fullSupport_pair k l]
  norm_num [Arithmetic.cos8,k,l,charge] at hN0 hs hprod ⊢
  nlinarith

theorem H_axial_antitone : AntitoneOn (axialOne k 1) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro w hw
    exact (axialOne_hasDerivAt k 1 w).continuousAt.continuousWithinAt
  · intro w hw
    exact axialOne_hasDerivAt k 1 w
  · intro w hw
    have h := axialOneD_monotone (q:=1) (by norm_num)
      (Ioo_subset_Icc_self hw) (by norm_num [frameCap]) hw.2.le
    exact (h.trans_lt H_axial_derivative_cap).le

theorem G_axial_monotone : MonotoneOn (axialOne k l) (Icc (3/10) frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro w hw
    exact (axialOne_hasDerivAt k l w).continuousAt.continuousWithinAt
  · intro w hw
    exact axialOne_hasDerivAt k l w
  · intro w hw
    have h := axialOneD_monotone (q:=l) (by norm_num [l])
      (by norm_num [frameCap])
      (show w∈Icc 0 frameCap from ⟨by linarith [hw.1],hw.2.le⟩) hw.1.le
    exact (G_axial_derivative_start.trans_le h).le

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
