module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3LowPure

/-!
# The widened affected-GA saturation slope

Uncompiled Section 5. The ratio endpoint is 2/3. The exact upper
cosine Taylor value gives numerator coordinate below .766, while
the other coordinate exceeds .5704; the displayed square reserve
then bounds the normalized norm derivative by 1.6.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LowAffectedSlope
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open NegativeAPositiveTD.SecantCoordinate NegativeAPositiveTD.AffectedNorm

def firstR (r z x : ℝ) : ℝ :=
  (1-r*Real.sin z)*(Real.cos z+x*Real.sin z)/(norm r z x)^3
def charged (r z x : ℝ) : ℝ := (13/12+Real.sin frameCap)*x-R*norm r z x
def chargedFirst (r z x : ℝ) : ℝ := 13/12+Real.sin frameCap-R*first r z x

theorem normR_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (fun r => norm r z x) ((r+x*Real.cos z-Real.sin z)/norm r z x) r := by
  have hn := norm_pos (x:=x) hv
  have hne : (x+r*Real.cos z)^2+(1-r*Real.sin z)^2≠0 := by
    nlinarith [norm_sq r z x]
  have hd := (((((hasDerivAt_id r).mul_const (Real.cos z)).const_add x).pow 2).add
    ((((hasDerivAt_id r).mul_const (Real.sin z)).const_sub 1).pow 2)).sqrt hne
  have hs : Real.sqrt ((x+r*Real.cos z)^2+(1-r*Real.sin z)^2)=norm r z x := rfl
  convert hd using 1
  · rfl
  · simp only [id,Pi.add_apply,Pi.pow_apply,hs]
    field_simp
    linear_combination (-2*r)*(Real.sin_sq_add_cos_sq z)

theorem firstR_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (fun r => first r z x) (firstR r z x) r := by
  have hn := norm_pos (x:=x) hv
  have he : Real.cos z*(norm r z x)^2-
      (x+r*Real.cos z)*(r+x*Real.cos z-Real.sin z)=
      (1-r*Real.sin z)*(Real.cos z+x*Real.sin z) := by
    rw [norm_sq]
    linear_combination r*(x+r*Real.cos z)*(Real.sin_sq_add_cos_sq z)
  have hd := (((hasDerivAt_id r).mul_const (Real.cos z)).const_add x).div
    (normR_hasDerivAt hv) hn.ne'
  convert hd using 1
  · rfl
  · dsimp [first,firstR]
    field_simp [hn.ne']
    nlinarith only [he]

theorem first_x_monotone {r z : ℝ} (hr : r∈Icc (0:ℝ) (2/3:ℝ))
    (hz : z∈Icc 0 frameCap) : MonotoneOn (first r z) (Icc (0:ℝ) (32/125)) := by
  have hv := second_coordinate_pos ⟨hr.1,by linarith [hr.2]⟩ hz
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (first_hasDerivAt (x:=x) hv).continuousAt.continuousWithinAt)
    (fun x _ => first_hasDerivAt hv)
  intro x hx
  exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem first_r_monotone {z x : ℝ} (hx : 0≤x) (hz : z∈Icc 0 frameCap) :
    MonotoneOn (fun r => first r z x) (Icc (0:ℝ) (2/3)) := by
  have hv {r : ℝ} (hr : r∈Icc (0:ℝ) (2/3:ℝ)) :=
    second_coordinate_pos ⟨hr.1,by linarith [hr.2]⟩ hz
  apply monoOn_of_hasDeriv_nonneg
    (fun r hr => (firstR_hasDerivAt (x:=x) (hv hr)).continuousAt.continuousWithinAt)
    (fun r hr => firstR_hasDerivAt (hv (Ioo_subset_Icc_self hr)))
  intro r hr
  have htr := transport_trig hz
  exact div_nonneg
    (mul_nonneg (hv (Ioo_subset_Icc_self hr)).le
      (add_nonneg (by linarith [htr.1]) (mul_nonneg hx htr.2.2.1)))
    (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem first_z_monotone :
    MonotoneOn (fun z => first (2/3) z (32/125)) (Icc (0:ℝ) frameCap) := by
  have hv {z : ℝ} (hz : z∈Icc 0 frameCap) :=
    second_coordinate_pos (r:=(2/3:ℝ)) (by norm_num) hz
  apply monoOn_of_hasDeriv_nonneg
    (fun z hz => (firstZ_hasDerivAt (x:=(32/125:ℝ)) (hv hz)).continuousAt.continuousWithinAt)
    (fun z hz => firstZ_hasDerivAt (x:=(32/125:ℝ)) (hv (Ioo_subset_Icc_self hz)))
  intro z hz
  have ht := transport_trig (Ioo_subset_Icc_self hz)
  have hb : 0≤(2/3:ℝ)+(32/125)*Real.cos z-Real.sin z := by
    linarith [ht.1,ht.2.2.2.1]
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hv (Ioo_subset_Icc_self hz)).le) hb)
    (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem endpoint : R*first (2/3) frameCap (32/125)<8/5 := by
  have ht := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hc := HighOrderTaylor.cos_le_C12 (by norm_num [frameCap] : (0:ℝ)≤frameCap)
  norm_num [frameCap,HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hc
  have hu0 : 0≤(32/125:ℝ)+(2/3)*Real.cos frameCap := by linarith [ht.1]
  have hu : (32/125:ℝ)+(2/3)*Real.cos frameCap<383/500 := by linarith
  have hv : (713/1250:ℝ)<1-(2/3)*Real.sin frameCap := by linarith [ht.2.2.2.1]
  have hn := norm_pos (x:=(32/125:ℝ)) (show 0<1-(2/3)*Real.sin frameCap by linarith)
  have hn2 := norm_sq (2/3) frameCap (32/125)
  have hu2 := pow_le_pow_left₀ hu0 hu.le 2
  have hv2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤713/1250) hv.le 2
  have hQ : 0≤qCap-(8/5:ℝ)^2 := by norm_num [qCap]
  have hscale := mul_le_mul_of_nonneg_left hu2 hQ
  have htest : qCap*(383/500:ℝ)^2<(8/5:ℝ)^2*((383/500:ℝ)^2+(713/1250:ℝ)^2) := by
    norm_num [qCap]
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hprod : 0≤R*((32/125:ℝ)+(2/3)*Real.cos frameCap) := mul_nonneg hR0 hu0
  have hsquare : (R*((32/125:ℝ)+(2/3)*Real.cos frameCap))^2<
      ((8/5)*norm (2/3) frameCap (32/125))^2 := by
    rw [mul_pow,mul_pow,hR2,hn2]
    nlinarith only [hscale,hv2,htest]
  have hh : R*((32/125:ℝ)+(2/3)*Real.cos frameCap)<
      (8/5)*norm (2/3) frameCap (32/125) := by
    nlinarith
  dsimp [first]
  rw [←mul_div_assoc]
  exact (div_lt_iff₀ hn).2 hh

theorem normalized_norm_slope {r z x : ℝ} (hr : r∈Icc (0:ℝ) (2/3:ℝ))
    (hz : z∈Icc 0 frameCap) (hx : x∈Icc 0 (32/125:ℝ)) : R*first r z x<8/5 := by
  have h₁ := first_x_monotone hr hz hx (show (32/125:ℝ)∈Icc 0 (32/125:ℝ) by norm_num) hx.2
  have h₂ := first_r_monotone (x:=(32/125:ℝ)) (by norm_num) hz hr
    (show (2/3:ℝ)∈Icc 0 (2/3:ℝ) by norm_num) hr.2
  have h₃ := first_z_monotone hz
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hz.2
  exact (mul_le_mul_of_nonneg_left (h₁.trans (h₂.trans h₃)) (Real.sqrt_nonneg qCap)).trans_lt endpoint

theorem charged_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (charged r z) (chargedFirst r z x) x := by
  convert ((hasDerivAt_id x).const_mul (13/12+Real.sin frameCap)).sub
    ((norm_hasDerivAt hv).const_mul R) using 1
  · rfl
  · dsimp [chargedFirst]
    ring

theorem charged_slope {r z x : ℝ} (hr : r∈Icc (0:ℝ) (2/3:ℝ))
    (hz : z∈Icc 0 frameCap) (hx : x∈Icc 0 (32/125:ℝ)) :
    (127/1000:ℝ)<chargedFirst r z x := by
  have hh := normalized_norm_slope hr hz hx
  have hs := sin_lower_seven (by norm_num [frameCap] : (0:ℝ)≤frameCap)
  norm_num [frameCap] at hs
  dsimp [chargedFirst]
  linarith

theorem charged_monotone {r z : ℝ} (hr : r∈Icc (0:ℝ) (2/3:ℝ))
    (hz : z∈Icc 0 frameCap) : MonotoneOn (charged r z) (Icc (0:ℝ) (32/125)) := by
  have hv := second_coordinate_pos ⟨hr.1,by linarith [hr.2]⟩ hz
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (charged_hasDerivAt (x:=x) hv).continuousAt.continuousWithinAt)
    (fun x _ => charged_hasDerivAt hv)
  intro x hx
  exact (by norm_num : (0:ℝ)≤127/1000).trans (charged_slope hr hz (Ioo_subset_Icc_self hx)).le

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LowAffectedSlope
