module

public import SquaresInCircles.Eight.Frames.Core.HighPrimaryContinuation
public import SquaresInCircles.Eight.Frames.Core.HighSecondaryNorm

/-!
# Eight squares: whole-interval circle supports for a core-source transverse witness

The negative high tangent has a concave support up to angle `6/5`.
The positive high tangent has concave supports on both sides of the
quarter turn, meeting at the exact previously established quarter value.
All radical bounds are consequences of the actual rotating norms.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighSecondaryScalars
open FramePair FrameCircleArc FrameHighArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreMidScalars (ap cp)
open FrameCoreHighSecondaryNorm

def Cminus : ℝ := ap+(u-v)/2+k
def Cplus : ℝ := ap-(u-v)/2-k
def Fminus (x : ℝ) : ℝ :=
  x+Cminus+(g-9/100)*(Real.sin x+Real.cos x)-R*N false x
def FminusD (x : ℝ) : ℝ :=
  1+(g-9/100)*(Real.cos x-Real.sin x)-R*Nd false x
def FminusDD (x : ℝ) : ℝ :=
  -(g-9/100)*(Real.sin x+Real.cos x)-R*Ndd false x
def FplusFirst (x : ℝ) : ℝ :=
  x+Cplus+(g-9/100)*Real.sin x-(9/100)*Real.cos x-R*N true x
def FplusFirstD (x : ℝ) : ℝ :=
  1+(g-9/100)*Real.cos x+(9/100)*Real.sin x-R*Nd true x
def FplusFirstDD (x : ℝ) : ℝ :=
  -(g-9/100)*Real.sin x+(9/100)*Real.cos x-R*Ndd true x
def FplusSecond (x : ℝ) : ℝ :=
  x+Cplus+(g-9/100)*(Real.sin x-Real.cos x)-R*N true x
def FplusSecondD (x : ℝ) : ℝ :=
  1+(g-9/100)*(Real.cos x+Real.sin x)-R*Nd true x
def FplusSecondDD (x : ℝ) : ℝ :=
  (g-9/100)*(Real.cos x-Real.sin x)-R*Ndd true x

theorem Fminus_deriv (x : ℝ) : HasDerivAt Fminus (FminusD x) x := by
  have h := (((hasDerivAt_id' x).add_const Cminus).fun_add
    (((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).const_mul (g-9/100))).fun_sub
      ((N_deriv false x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FminusD]; ring

theorem FminusD_deriv (x : ℝ) : HasDerivAt FminusD (FminusDD x) x := by
  have h := ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul
    (g-9/100)).const_add 1).fun_sub ((Nd_deriv false x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FminusDD]; ring

theorem FplusFirst_deriv (x : ℝ) : HasDerivAt FplusFirst (FplusFirstD x) x := by
  have h := ((((hasDerivAt_id' x).add_const Cplus).fun_add
    ((Real.hasDerivAt_sin x).const_mul (g-9/100))).fun_sub
      ((Real.hasDerivAt_cos x).const_mul (9/100))).fun_sub
        ((N_deriv true x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FplusFirstD]; ring

theorem FplusFirstD_deriv (x : ℝ) : HasDerivAt FplusFirstD (FplusFirstDD x) x := by
  have h := ((((Real.hasDerivAt_cos x).const_mul (g-9/100)).const_add 1).fun_add
    ((Real.hasDerivAt_sin x).const_mul (9/100))).fun_sub
      ((Nd_deriv true x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FplusFirstDD]; ring

theorem FplusSecond_deriv (x : ℝ) : HasDerivAt FplusSecond (FplusSecondD x) x := by
  have h := (((hasDerivAt_id' x).add_const Cplus).fun_add
    (((Real.hasDerivAt_sin x).fun_sub (Real.hasDerivAt_cos x)).const_mul (g-9/100))).fun_sub
      ((N_deriv true x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FplusSecondD]; ring

theorem FplusSecondD_deriv (x : ℝ) : HasDerivAt FplusSecondD (FplusSecondDD x) x := by
  have h := ((((Real.hasDerivAt_cos x).fun_add (Real.hasDerivAt_sin x)).const_mul
    (g-9/100)).const_add 1).fun_sub ((Nd_deriv true x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FplusSecondDD]; ring

theorem Fminus_concave : ConcaveOn ℝ (Icc (0:ℝ) (6/5)) Fminus := by
  apply concave_of_deriv2 (fun x _ => Fminus_deriv x) (fun x _ => FminusD_deriv x)
  intro x hx
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width hxq).1] at hw
  have hh := curvature_work false x
  dsimp [FminusDD,g] at *
  linarith

theorem FplusFirst_concave :
    ConcaveOn ℝ (Icc (7/5:ℝ) (Real.pi/2)) FplusFirst := by
  apply concave_of_deriv2 (fun x _ => FplusFirst_deriv x)
    (fun x _ => FplusFirstD_deriv x)
  intro x hx
  have ht := positive_first_trig hx
  have hh := mul_pos R_pos (positive_norm_curvature hx)
  dsimp [FplusFirstDD,g] at *
  linarith

theorem FplusSecond_concave :
    ConcaveOn ℝ (Icc (Real.pi/2) (5/2:ℝ)) FplusSecond := by
  apply concave_of_deriv2 (fun x _ => FplusSecond_deriv x)
    (fun x _ => FplusSecondD_deriv x)
  intro x hx
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hw := FrameCoreArc.width_one_le x
  rw [(second_width hxq).1] at hw
  have hh := curvature_work true x
  dsimp [FplusSecondDD,g] at *
  linarith

theorem minus_endpoints :
    (221/250:ℝ)<Fminus 0 ∧ (51/50:ℝ)<Fminus (6/5) := by
  have hR0 : R*N false 0<radiusUpper*(223/250) :=
    mul_lt_mul'' radius_bound norm_endpoints.1 R_pos.le (N_pos false 0).le
  have hR1 : R*N false (6/5)<radiusUpper*(63/40) :=
    mul_lt_mul'' radius_bound norm_endpoints.2.1 R_pos.le (N_pos false (6/5)).le
  have hk := k_bounds.1
  have ht := FrameCoreMidScalars.trig_six_fifths
  constructor
  · dsimp [Fminus,Cminus,ap,g,u,v,radiusUpper] at hR0 hk ⊢
    simp only [Real.sin_zero,Real.cos_zero]
    linarith
  · dsimp [Fminus,Cminus,ap,g,u,v,radiusUpper] at hR1 hk ⊢
    linarith [ht.1,ht.2.2.1]

theorem positive_start : (221/250:ℝ)<FplusFirst (7/5) := by
  have hR : R*N true (7/5)<radiusUpper*(67/125) :=
    mul_lt_mul'' radius_bound norm_endpoints.2.2.1 R_pos.le (N_pos true (7/5)).le
  have ht := trig_seven_fifths
  have hk := k_bounds.2.1
  dsimp [FplusFirst,Cplus,ap,g,u,v,radiusUpper] at hR hk ⊢
  linarith [ht.1,ht.2.2.2]

theorem quarter_first :
    FplusFirst (Real.pi/2)=FrameCoreHighPrimaryContinuation.quarterValue := by
  dsimp [FplusFirst,Cplus,ap,FrameCoreHighPrimaryContinuation.quarterValue,k]
  rw [positive_quarter_norm]
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero,sub_zero]
  ring

theorem quarter_second :
    FplusSecond (Real.pi/2)=FrameCoreHighPrimaryContinuation.quarterValue := by
  dsimp [FplusSecond,Cplus,ap,FrameCoreHighPrimaryContinuation.quarterValue,k]
  rw [positive_quarter_norm]
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,sub_zero]
  ring

theorem positive_end : (97/100:ℝ)<FplusSecond (5/2) := by
  have hR : R*N true (5/2)<radiusUpper*(63/50) :=
    mul_lt_mul'' radius_bound norm_endpoints.2.2.2 R_pos.le (N_pos true (5/2)).le
  have hs := FrameCoreHighCorePrimary.trig_endpoints.2.2.2.1
  have hc := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤5/2 by norm_num)
  norm_num [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hc
  have hk := k_bounds.2.1
  dsimp [FplusSecond,Cplus,ap,g,u,v,radiusUpper] at hR hk ⊢
  linarith

theorem minus_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) :
    (8833/10000:ℝ)<Fminus x :=
  concave_gt_of_endpoints Fminus_concave hx
    (by linarith [minus_endpoints.1]) (by linarith [minus_endpoints.2])

theorem positive_first_lower {x : ℝ} (hx : x∈Icc (7/5:ℝ) (Real.pi/2)) :
    (8833/10000:ℝ)<FplusFirst x := by
  apply concave_gt_of_endpoints FplusFirst_concave hx
  · linarith [positive_start]
  · rw [quarter_first]
    linarith [FrameCoreHighPrimaryContinuation.quarter_lower]

theorem positive_second_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (5/2:ℝ)) :
    (8833/10000:ℝ)<FplusSecond x := by
  apply concave_gt_of_endpoints FplusSecond_concave hx
  · rw [quarter_second]
    linarith [FrameCoreHighPrimaryContinuation.quarter_lower]
  · linarith [positive_end]

end SquaresInCircles.Eight.FrameCoreHighSecondaryScalars
