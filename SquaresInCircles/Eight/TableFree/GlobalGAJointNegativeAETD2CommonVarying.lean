module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2CommonEnvelope

/-!
# The larger-coefficient derivative on the common-gain rectangle

Uncompiled transcription of (27)--(31). `VaryingBFunctions.D` is the
actual derivative of V with respect to its larger coefficient. The
slightly wider ratio interval contains k/sec r for every r≤.7.
The derivative in d is controlled before and after its intrinsic
zero-sign event sin d=k/q; no subdivision of the angle is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary OrdinaryCurvatureBounds OrdinaryAngleConcavity
open VaryingBFunctions VaryingBComparison

def varyingShape (ρ u : ℝ) : ℝ :=
  (2*ρ^2-1)+(u-ρ)*u*(ρ^2+2-ρ*u)-ρ^2*u^2

theorem varying_ratio_condition {ρ u : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000))
    (hu : u∈Icc (0:ℝ) (129/200)) : 0≤2*ρ-(1+ρ^2)*u := by
  have hfactor := mul_nonneg (show 0≤ρ-49/100 by linarith [hρ.1])
    (show 0≤2-(129/200)*(ρ+49/100) by linarith [hρ.2])
  have hh := mul_le_mul_of_nonneg_left hu.2 (show 0≤1+ρ^2 by positivity)
  nlinarith

theorem varying_Dr_nonnegative {ρ d : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000)) (hd : d∈Icc 0 frameCap) :
    0≤Dr R ρ d := by
  let u := Real.sin d
  have hu := sine_domain hd
  have hu' := sin_mem hd
  have hN := root_pos ρ hu'
  have hN2 := root_sq ρ hu'
  have hS := shape_pos ρ
  have hS2 := shape_sq ρ
  have hu2 : u^2≤(129/200:ℝ)^2 := by dsimp [u]; nlinarith [hu.1,hu.2]
  have hcondition := mul_nonneg (varying_ratio_condition hρ hu) hu.1
  have hbase : (root ρ u)^2≤(1+ρ^2)*(1-u^2) := by
    dsimp [u] at *
    nlinarith
  have hcube := pow_le_pow_left₀ (sq_nonneg (root ρ u)) hbase 3
  have h01 : 0≤1-u^2 ∧ 1-u^2≤1 := ⟨by linarith,by nlinarith [sq_nonneg u]⟩
  have hpow : (1-u^2)^3≤(1-u^2)^2 := by
    have hh := mul_le_mul_of_nonneg_left h01.2 (sq_nonneg (1-u^2))
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hpow (show 0≤(1+ρ^2)^3 by positivity)
  have hsquare : ((root ρ u)^3)^2≤((1-u^2)*(shape ρ)^3)^2 := by
    rw [show ((root ρ u)^3)^2=((root ρ u)^2)^3 by ring,
      show ((1-u^2)*(shape ρ)^3)^2=(1-u^2)^2*((shape ρ)^2)^3 by ring,hS2]
    nlinarith only [hcube,hprod]
  have hle : (root ρ u)^3≤(1-u^2)*(shape ρ)^3 := by
    nlinarith [pow_nonneg hN.le 3,mul_nonneg h01.1 (pow_nonneg hS.le 3)]
  have hfrac : 1/(shape ρ)^3≤(1-u^2)/(root ρ u)^3 :=
    (div_le_div_iff₀ (pow_pos hS 3) (pow_pos hN 3)).2 (by simpa using hle)
  dsimp [Dr]
  rw [cos_square]
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) (by linarith [hρ.1]))
    (sub_nonneg.mpr hfrac)

theorem varying_Dtt_identity {ρ d : ℝ} (hd : d∈Icc 0 frameCap) :
    Dtt R ρ d= -Real.cos d+R*ρ^2*varyingShape ρ (Real.sin d)/(root ρ (Real.sin d))^5 := by
  have hn := (root_pos ρ (sin_mem hd)).ne'
  have hN2 := root_sq ρ (sin_mem hd)
  have h3 : ρ^2*(ρ-Real.sin d)/(root ρ (Real.sin d))^3=
      ρ^2*(ρ-Real.sin d)*(1+ρ^2-2*ρ*Real.sin d)/(root ρ (Real.sin d))^5 := by
    rw [← hN2]; field_simp
  dsimp [Dtt,integrand,integrandD,varyingShape]
  rw [h3,cos_square]
  ring

theorem varying_shape_upper {ρ u : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000))
    (hu : u∈Icc (0:ℝ) (129/200)) (hur : u≤ρ) : varyingShape ρ u≤129/1000 := by
  have hρ0 : 0≤ρ := by linarith [hρ.1]
  have hρ2 : ρ^2≤(751/1000:ℝ)^2 := pow_le_pow_left₀ hρ0 hρ.2 2
  have hprod := mul_le_mul_of_nonneg_left hur hρ0
  have hb : 0≤ρ^2+2-ρ*u := by linarith
  have hbad := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hur) hu.1) hb
  have hsquare := mul_nonneg (sq_nonneg ρ) (sq_nonneg u)
  dsimp [varyingShape]
  nlinarith

theorem varying_Dtt_negative {ρ d : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000)) (hd : d∈Icc 0 frameCap)
    (hsin : Real.sin d≤ρ) : Dtt R ρ d<0 := by
  have hy := sine_domain hd
  have hN := root_pos ρ (sin_mem hd)
  have hN2 := root_sq ρ (sin_mem hd)
  have hNlow : (191/250:ℝ)<root ρ (Real.sin d) := by
    nlinarith [sq_nonneg (ρ-Real.sin d),hy.1,hy.2]
  have hc : (191/250:ℝ)<Real.cos d := by linarith [(transport_trig hd).1]
  have hshape := varying_shape_upper hρ hy hsin
  rw [varying_Dtt_identity hd]
  by_cases hs : varyingShape ρ (Real.sin d)≤0
  · have hh := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (Real.sqrt_nonneg qCap) (sq_nonneg ρ)) hs)
      (pow_nonneg hN.le 5)
    linarith
  · have hs0 : 0≤varyingShape ρ (Real.sin d) := le_of_lt (lt_of_not_ge hs)
    have hr : R≤2 := by linarith [Secondary.radius_bounds.2]
    have hρ2 : ρ^2≤(751/1000:ℝ)^2 :=
      pow_le_pow_left₀ (by linarith [hρ.1]) hρ.2 2
    have hprod := mul_le_mul (mul_le_mul hr hρ2 (sq_nonneg ρ) (by norm_num))
      hshape hs0 (by norm_num : (0:ℝ)≤2*(751/1000)^2)
    have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤191/250) hNlow.le 5
    have hfrac : R*ρ^2*varyingShape ρ (Real.sin d)/(root ρ (Real.sin d))^5<191/250 := by
      apply (div_lt_iff₀ (pow_pos hN 5)).2
      nlinarith
    linarith

theorem varying_Dt_upper {ρ d : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000)) (hd : d∈Icc 0 frameCap) :
    Dt R ρ d≤R*ρ^3/(shape ρ)^3 := by
  have hρ0 : 0≤ρ := by linarith [hρ.1]
  by_cases hsin : Real.sin d≤ρ
  · have hmono : AntitoneOn (Dt R ρ) (Icc 0 d) := by
      apply antiOn_of_hasDeriv_nonpos
      · intro x hx
        exact (Dt_hasDerivAt (R:=R) (r:=ρ) ⟨hx.1,hx.2.trans hd.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        exact Dt_hasDerivAt ⟨hx.1.le,hx.2.le.trans hd.2⟩
      · intro x hx
        have hx' : x∈Icc 0 frameCap := ⟨hx.1.le,hx.2.le.trans hd.2⟩
        have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [hx.1,Real.pi_pos])
          (by norm_num [frameCap] at hd; linarith [hd.2,Real.pi_gt_three]) hx.2.le
        exact (varying_Dtt_negative hρ hx' (hs.trans hsin)).le
    have hh := hmono ⟨le_rfl,hd.1⟩ ⟨hd.1,le_rfl⟩ hd.1
    simpa [Dt,integrand,pow_succ,mul_div_assoc] using hh
  · have hsign : integrand ρ (Real.sin d)≤0 := by
      dsimp [integrand]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ρ) (by linarith))
        (pow_nonneg (root_pos ρ (sin_mem hd)).le 3)
    have hprod := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.sqrt_nonneg qCap) (show 0≤Real.cos d by linarith [(transport_trig hd).1])) hsign
    have hright : 0≤R*ρ^3/(shape ρ)^3 :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) (pow_nonneg hρ0 3)) (pow_nonneg (shape_pos ρ).le 3)
    dsimp [Dt]
    linarith [(sine_domain hd).1]

theorem varying_D_upper {ρ d : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000)) (hd : d∈Icc 0 frameCap) :
    VaryingBFunctions.D R ρ d≤R*ρ^3/(shape ρ)^3*d := by
  have hh := derivative_reserve
    (f:=fun x => -VaryingBFunctions.D R ρ x) (df:=fun x => -Dt R ρ x)
    (k:=-(R*ρ^3/(shape ρ)^3)) (l:=0) (u:=frameCap)
    (fun x hx => (D_hasDerivAt_t (R:=R) (r:=ρ) hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (D_hasDerivAt_t (R:=R) (r:=ρ) (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (varying_Dt_upper hρ (Ioo_subset_Icc_self hx)))
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hd hd.1
  simp only [D_zero,neg_zero,sub_zero] at hh
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain
