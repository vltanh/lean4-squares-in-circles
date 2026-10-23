module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowSeparatedSlope

/-!
# The two polynomial reserves in the low separated-block argument

Uncompiled transcription of Section 7, equations (39)--(46), of the
negative-DE TD2 angle companion. The degree-fourteen polynomial retains
its centered quadratic on the whole short interval. The interior-D
quartic retains its positive coefficients at y = .27. No sample points
or interval mesh enter either bound.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope

namespace Certificate
open PositiveTD.Certificate (S5 C4)

def AP : ℚ[X] := C (13753/50000)-C (13607/12500)*X-C (1/6)*X^2+C (1/6)*X^3
def BP : ℚ[X] := C (32033/25000)-C (2729/4000)*X-C (5/24)*X^2+C (5/24)*X^3
def shortPolynomial : ℚ[X] := C (13/12)-C (2/5)*S5.comp (C (7/10)-X)-
  (C4.comp (C (7/10)-X))^2*(BP+C (500/389)*AP^2)
def shortTranslated : ℚ[X] := DirectedPowerBounds.shift (3/25) shortPolynomial

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem short_certificate :
    shortTranslated=C (shortTranslated.coeff 0)+C (shortTranslated.coeff 1)*X+
      C (shortTranslated.coeff 2)*X^2+PowerTailBounds.tail shortTranslated 3 12 ∧
    (21067/2500000:ℚ)<shortTranslated.coeff 0 ∧
    |shortTranslated.coeff 1|<(77231/10000000:ℚ) ∧
    (6217/10000:ℚ)<shortTranslated.coeff 2 ∧
    (4307/20000:ℚ)<shortTranslated.coeff 2-
      PowerTailBounds.norm shortTranslated 3 12 (6/25) := by decide

theorem short_positive {d : ℝ} (hd : d∈Icc (0:ℝ) (9/25)) :
    (167/20000:ℝ)<aeval d shortPolynomial := by
  let x : ℝ := d-3/25
  have hx : |x|≤6/25 := by
    rw [abs_le]
    dsimp [x]
    exact ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have ht := PowerTailBounds.quadratic_lower short_certificate.1 (by norm_num) hx
  have h0 : (21067/2500000:ℝ)<(shortTranslated.coeff 0:ℝ) := by
    exact_mod_cast short_certificate.2.1
  have h1 : |(shortTranslated.coeff 1:ℝ)|<(77231/10000000:ℝ) := by
    exact_mod_cast short_certificate.2.2.1
  have h2 : (4307/20000:ℝ)<(shortTranslated.coeff 2:ℝ)-
      (PowerTailBounds.norm shortTranslated 3 12 (6/25):ℝ) := by
    exact_mod_cast short_certificate.2.2.2.2
  have hlin : -(77231/10000000)*|x|≤(shortTranslated.coeff 1:ℝ)*x := by
    have hh := mul_le_mul_of_nonneg_right h1.le (abs_nonneg x)
    rw [←abs_mul] at hh
    exact (abs_le.mp hh).1
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg x)
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(21067/2500000:ℝ)) (b:=-(77231/10000000:ℝ)) (x:=|x|)
    (show (0:ℝ)<4307/20000 by norm_num)
  have hreserve : (167/20000:ℝ)<21067/2500000-
      (77231/10000000:ℝ)^2/(4*(4307/20000)) := by norm_num
  have he : aeval x shortTranslated=aeval d shortPolynomial := by
    simp only [shortTranslated,DirectedPowerBounds.shift_eval]
    congr 1
    dsimp [x]
    ring
  rw [he] at ht
  rw [sq_abs] at hmin
  nlinarith

@[simp] theorem AP_eval (d : ℝ) : aeval d AP=A d := by simp [AP,A]
@[simp] theorem BP_eval (d : ℝ) : aeval d BP=B d := by simp [BP,B]

theorem short_model_reserve {d : ℝ} (hd : d∈Icc (0:ℝ) (9/25)) :
    0<13/12-(2/5)*aeval (frameCap-d) S5-
      (aeval (frameCap-d) C4)^2*model d := by
  have hp := short_positive hd
  have he : aeval d shortPolynomial=13/12-(2/5)*aeval (frameCap-d) S5-
      (aeval (frameCap-d) C4)^2*model d := by
    simp [shortPolynomial,aeval_comp,frameCap,model,AP_eval,BP_eval]
  rw [he] at hp
  linarith

def interiorPolynomial : ℚ[X] := C (1/1200)-C (9/184)*X+C (79057/211600)*X^2-
  C (881/1150)*X^3+C (375/529)*X^4
def interiorTranslated : ℚ[X] := DirectedPowerBounds.shift (27/100) interiorPolynomial

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem interior_certificate :
    interiorTranslated=C (interiorTranslated.coeff 0)+C (interiorTranslated.coeff 1)*X+
      C (interiorTranslated.coeff 2)*X^2+C (interiorTranslated.coeff 3)*X^3+
      C (interiorTranslated.coeff 4)*X^4 ∧
    (71/20000:ℚ)<interiorTranslated.coeff 0 ∧
    (411/10000:ℚ)<interiorTranslated.coeff 1 ∧
    (1263/20000:ℚ)<interiorTranslated.coeff 2 ∧
    -(123/250000:ℚ)<interiorTranslated.coeff 3 ∧
    (0:ℚ)<interiorTranslated.coeff 4 := by decide

theorem interior_positive {y : ℝ} (hy : y∈Icc (27/100:ℝ) (129/200)) :
    0<aeval y interiorPolynomial := by
  let v : ℝ := y-27/100
  have hv : v∈Icc (0:ℝ) (3/8) := by
    dsimp [v]
    exact ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have h0 : (71/20000:ℝ)<(interiorTranslated.coeff 0:ℝ) := by
    exact_mod_cast interior_certificate.2.1
  have h1 : (411/10000:ℝ)<(interiorTranslated.coeff 1:ℝ) := by
    exact_mod_cast interior_certificate.2.2.1
  have h2 : (1263/20000:ℝ)<(interiorTranslated.coeff 2:ℝ) := by
    exact_mod_cast interior_certificate.2.2.2.1
  have h3 : -(123/250000:ℝ)<(interiorTranslated.coeff 3:ℝ) := by
    exact_mod_cast interior_certificate.2.2.2.2.1
  have h4 : (0:ℝ)<(interiorTranslated.coeff 4:ℝ) := by
    exact_mod_cast interior_certificate.2.2.2.2.2
  have hm1 := mul_le_mul_of_nonneg_right h1.le hv.1
  have hm2 := mul_le_mul_of_nonneg_right h2.le (sq_nonneg v)
  have hm3 := mul_le_mul_of_nonneg_right h3.le (pow_nonneg hv.1 3)
  have hm4 := mul_nonneg h4.le (pow_nonneg hv.1 4)
  have hcube : v^3≤(3/8)*v^2 := by
    nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv.2)]
  have hi := congrArg (fun p : ℚ[X] => aeval v p) interior_certificate.1
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at hi
  have he : aeval v interiorTranslated=aeval y interiorPolynomial := by
    simp only [interiorTranslated,DirectedPowerBounds.shift_eval]
    congr 1
    dsimp [v]
    ring
  rw [he] at hi
  nlinarith [sq_nonneg v]

end Certificate

def AFirst (d : ℝ) : ℝ := -(13607/12500)-d/3+d^2/2
def lateCubic (d : ℝ) : ℝ := 960319/800000-(41011/100000)*d-d^2/6+d^3/6

theorem A_derivative (d : ℝ) : HasDerivAt A (AFirst d) d := by
  have hd : Differentiable ℝ A := by dsimp [A]; fun_prop
  convert (hd d).hasDerivAt using 1
  simp (disch := fun_prop) [A,AFirst]
  ring

theorem A_late_upper {d : ℝ} (hd : d∈Icc (9/25:ℝ) frameCap) : A d<-(389/4000:ℝ) := by
  have hm : AntitoneOn A (Icc (9/25:ℝ) frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun d _ => (A_derivative d).continuousAt.continuousWithinAt)
      (fun d _ => A_derivative d)
    intro d hd
    have hd2 := pow_le_pow_left₀ (show 0≤d by linarith [hd.1]) hd.2.le 2
    dsimp [AFirst,frameCap] at *
    nlinarith [hd.1]
  have hh := hm (by norm_num [frameCap]) hd hd.1
  norm_num [A] at hh
  linarith

theorem lateCubic_derivative (d : ℝ) : HasDerivAt lateCubic
    (-(41011/100000)-d/3+d^2/2) d := by
  have hd : Differentiable ℝ lateCubic := by dsimp [lateCubic]; fun_prop
  convert (hd d).hasDerivAt using 1
  simp (disch := fun_prop) [lateCubic]
  ring

theorem lateCubic_upper {d : ℝ} (hd : d∈Icc (9/25:ℝ) frameCap) : lateCubic d<1039/1000 := by
  have hm : AntitoneOn lateCubic (Icc (9/25:ℝ) frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun d _ => (lateCubic_derivative d).continuousAt.continuousWithinAt)
      (fun d _ => lateCubic_derivative d)
    intro d hd
    have hd2 := pow_le_pow_left₀ (show 0≤d by linarith [hd.1]) hd.2.le 2
    norm_num [frameCap] at hd2
    nlinarith [hd.1]
  have hh := hm (by norm_num [frameCap]) hd hd.1
  norm_num [lateCubic] at hh
  linarith

theorem late_slope_upper {p q d : ℝ}
    (hp : 0<p) (hp0 : p≤p0) (hq : q∈Icc 1 qMax)
    (hd : d∈Icc (9/25:ℝ) frameCap) : OrdinaryNegativeSlope.Vd Secondary.R p q d<1039/1000 := by
  have hmodel := quadratic_model hp hp0 hq ⟨by linarith [hd.1],hd.2⟩
  have hA := A_late_upper hd
  have hproduct := mul_nonpos_of_nonpos_of_nonneg
    (show A d+389/4000≤0 by linarith) (sub_nonneg.mpr hq.1)
  have he : B d+A d*(q-q0)-(389/2000)*(q-q0)^2=
      lateCubic d+(A d+389/4000)*(q-1)-(389/2000)*(q-1)^2 := by
    dsimp [A,B,lateCubic,q0]
    ring
  rw [he] at hmodel
  have hh : OrdinaryNegativeSlope.Vd Secondary.R p q d<lateCubic d := by
    nlinarith [sq_nonneg (q-1)]
  exact hh.trans (lateCubic_upper hd)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowSeparated
