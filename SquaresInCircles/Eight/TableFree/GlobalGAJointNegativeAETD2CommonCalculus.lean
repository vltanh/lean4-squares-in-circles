module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2CommonInverse

/-!
# Exact derivatives of the common secant gain

Uncompiled transcription of (8), (10), and (11). The square-root
identities are used before clearing denominators, so each derivative
reduces to the displayed polynomial identity in sine and cosine.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary

theorem D_positive (k x : ℝ) : 0<D k x := Real.sqrt_pos.mpr (by positivity)
theorem D_square (k x : ℝ) : (D k x)^2=1+k^2*Real.cos x^2 :=
  Real.sq_sqrt (by positivity)
theorem cos_square (x : ℝ) : Real.cos x^2=1-Real.sin x^2 := by
  linarith [Real.sin_sq_add_cos_sq x]
theorem D_shape (k x : ℝ) : (D k x)^2=shapeA k (Real.sin x) := by
  rw [D_square,cos_square]
  dsimp [shapeA]
  ring

theorem D_angle_derivative (k x : ℝ) :
    HasDerivAt (D k) (-k^2*Real.sin x*Real.cos x/D k x) x := by
  have hd := ((((Real.hasDerivAt_cos x).pow 2).const_mul (k^2)).const_add 1).sqrt
    (show 1+k^2*Real.cos x^2≠0 by positivity)
  convert hd using 1
  · rfl
  · dsimp [D]
    ring
theorem D_parameter_derivative (k x : ℝ) :
    HasDerivAt (fun k => D k x) (k*Real.cos x^2/D k x) k := by
  have hd := ((((hasDerivAt_id k).pow 2).mul_const (Real.cos x^2)).const_add 1).sqrt
    (show 1+k^2*Real.cos x^2≠0 by positivity)
  convert hd using 1
  · rfl
  · dsimp [D]
    ring

theorem B_angle_derivative (k x : ℝ) :
    HasDerivAt (fun x => shapeB k (Real.sin x))
      ((2*(1+k^2)*Real.sin x-8*k^2*Real.sin x^3)*Real.cos x) x := by
  have hd := ((((Real.hasDerivAt_sin x).pow 2).const_add 1).const_mul (1+k^2)).sub
    (((Real.hasDerivAt_sin x).pow 4).const_mul (2*k^2))
  convert hd using 1 <;> dsimp [shapeB] <;> ring
theorem B_parameter_derivative (k y : ℝ) :
    HasDerivAt (fun k => shapeB k y) (2*k*(1+y^2)-4*k*y^4) k := by
  have hd := ((((hasDerivAt_id k).pow 2).const_add 1).mul_const (1+y^2)).sub
    (((hasDerivAt_id k).pow 2).mul_const (2*y^4))
  convert hd using 1 <;> dsimp [shapeB] <;> ring
theorem C_parameter_derivative (k y : ℝ) :
    HasDerivAt (fun k => shapeC k y)
      (2*k*(13+16*k^2)+2*k*(-11-24*k^2)*y^2-4*k*y^4+16*k^3*y^6) k := by
  have hp := (hasDerivAt_id k).pow 2
  have hd := ((((hp.const_add 1).mul ((hp.const_mul 8).const_add 5)).add
    (((hp.const_add 1).mul ((hp.const_mul 12).const_sub 1)).mul_const (y^2))).sub
      (hp.mul_const (2*y^4))).add (((hasDerivAt_id k).pow 4).mul_const (4*y^6))
  convert hd using 1 <;> dsimp [shapeC] <;> ring

theorem F_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (F k) (F1 k x) x := by
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  have hh := SecantNormCurvature.normalized_hasDerivAt (R:=R) (a:=k) hc
  have he := NegativeAPositiveTD.SecantBaseline.angleSlope_eq (l:=1) (r:=k) hc
  have he' : SecantNormCurvature.gainFirst R k x=F1 k x := by
    simpa [F1,D,K,NegativeAPositiveTD.SecantBaseline.angleSlope,
      NegativeAPositiveTD.SecantBaseline.denominator] using he
  rw [he'] at hh
  exact hh

theorem F1_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (F1 k) (F2 k x) x := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by linarith [(transport_trig hx).1]).ne'
  have hD := (D_positive k x).ne'
  have hB : shapeB k (Real.sin x)=
      (Real.cos x^2+2*Real.sin x^2)*(D k x)^2+
        k^2*Real.sin x^2*Real.cos x^2 := by
    rw [D_square,cos_square]
    dsimp [shapeB]
    ring
  have h1 : 1+Real.sin x^2=Real.cos x^2+2*Real.sin x^2 := by rw [cos_square]; ring
  have hd := (((Real.hasDerivAt_sin x).const_add K).sub
    (((Real.hasDerivAt_sin x).const_mul R).div (D_angle_derivative k x) hD)).div
      ((Real.hasDerivAt_cos x).pow 2) (pow_ne_zero _ hc)
  convert hd using 1
  · rfl
  · dsimp [F2]
    rw [hB,h1]
    field_simp [hc,hD]
    ring

theorem F2_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (F2 k) (F3 k x) x := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by linarith [(transport_trig hx).1]).ne'
  have hD := (D_positive k x).ne'
  have hC : Real.sin x*shapeC k (Real.sin x)=
      Real.cos x^2*((2*(1+k^2)*Real.sin x-8*k^2*Real.sin x^3)*(D k x)^2+
        3*k^2*Real.sin x*shapeB k (Real.sin x))+
      3*Real.sin x*shapeB k (Real.sin x)*(D k x)^2 := by
    rw [D_square,cos_square]
    dsimp [shapeB,shapeC]
    ring
  have hK : 2*K+5*Real.sin x+4*K*Real.sin x^2+Real.sin x^3=
      (2*K+2*Real.sin x)*Real.cos x^2+
        3*Real.sin x*(2*K*Real.sin x+1+Real.sin x^2) := by
    rw [cos_square]
    ring
  have hd := (((((Real.hasDerivAt_sin x).const_mul (2*K)).add_const 1).add
    ((Real.hasDerivAt_sin x).pow 2)).sub
      (((B_angle_derivative k x).const_mul R).div ((D_angle_derivative k x).pow 3)
        (pow_ne_zero _ hD))).div ((Real.hasDerivAt_cos x).pow 3) (pow_ne_zero _ hc)
  convert hd using 1
  · rfl
  · dsimp [F3]
    rw [show R*Real.sin x*shapeC k (Real.sin x)=R*(Real.sin x*shapeC k (Real.sin x)) by ring,hC,hK]
    field_simp [hc,hD]
    ring

theorem F1_parameter_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (fun k => F1 k x) (R*k*Real.sin x/(D k x)^3) k := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by linarith [(transport_trig hx).1]).ne'
  have hD := (D_positive k x).ne'
  have hd := (((hasDerivAt_const k (R*Real.sin x)).div
    (D_parameter_derivative k x) hD).const_sub (K+Real.sin x)).div_const (Real.cos x^2)
  convert hd using 1
  · rfl
  · field_simp [hc,hD]
    ring

theorem F2_parameter_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (fun k => F2 k x) (F2k k x) k := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by linarith [(transport_trig hx).1]).ne'
  have hD := (D_positive k x).ne'
  have hid : -(2*k*(1+Real.sin x^2)-4*k*Real.sin x^4)*(D k x)^2+
      3*shapeB k (Real.sin x)*k*Real.cos x^2=
        k*Real.cos x^4*(1+k^2*(1+2*Real.sin x^2)) := by
    rw [D_square,show Real.cos x^4=(Real.cos x^2)^2 by ring,cos_square]
    dsimp [shapeB]
    ring
  have hout : F2k k x=R*(-(2*k*(1+Real.sin x^2)-4*k*Real.sin x^4)*(D k x)^2+
      3*shapeB k (Real.sin x)*k*Real.cos x^2)/((D k x)^5*Real.cos x^3) := by
    rw [hid]
    dsimp [F2k]
    field_simp [hc,hD]
    ring
  have hd := ((((B_parameter_derivative k (Real.sin x)).const_mul R).div
    ((D_parameter_derivative k x).pow 3) (pow_ne_zero _ hD)).const_sub
      (2*K*Real.sin x+1+Real.sin x^2)).div_const (Real.cos x^3)
  convert hd using 1
  · rfl
  · rw [hout]
    field_simp [hc,hD]
    ring

theorem F3_parameter_derivative {k x : ℝ} (hx : x∈Icc 0 frameCap) :
    HasDerivAt (fun k => F3 k x) (F3k k x) k := by
  have hc : Real.cos x≠0 := (show 0<Real.cos x by linarith [(transport_trig hx).1]).ne'
  have hD := (D_positive k x).ne'
  have hid : -(2*k*(13+16*k^2)+2*k*(-11-24*k^2)*Real.sin x^2-
      4*k*Real.sin x^4+16*k^3*Real.sin x^6)*(D k x)^2+
      5*shapeC k (Real.sin x)*k*Real.cos x^2=
        k*Real.cos x^4*signPolynomial (k^2) (Real.sin x^2) := by
    rw [D_square,show Real.cos x^4=(Real.cos x^2)^2 by ring,cos_square]
    dsimp [shapeC,signPolynomial]
    ring
  have hout : F3k k x=R*Real.sin x*
      (-(2*k*(13+16*k^2)+2*k*(-11-24*k^2)*Real.sin x^2-
        4*k*Real.sin x^4+16*k^3*Real.sin x^6)*(D k x)^2+
        5*shapeC k (Real.sin x)*k*Real.cos x^2)/((D k x)^7*Real.cos x^4) := by
    rw [hid]
    dsimp [F3k]
    field_simp [hc,hD]
    ring
  have hd := ((((C_parameter_derivative k (Real.sin x)).const_mul (R*Real.sin x)).div
    ((D_parameter_derivative k x).pow 5) (pow_ne_zero _ hD)).const_sub
      (2*K+5*Real.sin x+4*K*Real.sin x^2+Real.sin x^3)).div_const (Real.cos x^4)
  convert hd using 1
  · dsimp [F3]
    congr 1
    ring
  · rw [hout]
    field_simp [hc,hD]
    ring

@[simp] theorem F_zero (k : ℝ) : F k 0=0 := by
  simp [F,SecantNormCurvature.normalized,SecantNormCurvature.secant,SecantNormCurvature.supportNorm]

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain
