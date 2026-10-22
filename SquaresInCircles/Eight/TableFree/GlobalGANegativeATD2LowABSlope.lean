module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2LowPure

/-!
# The low AB angular baseline slope

Uncompiled transcription of (45)--(46). The positive-square comparison
is the displayed concave cubic in the sine square. The final cubic
uses the prescribed shift by `.2` and its exact completed-square reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.LowABSlope
open Candidate Secondary SecantBaseline

def squarePolynomial (t : ℝ) : ℝ := (7/5+(19/50)*t)^2*(2-t)-qCap
def squareFirst (t : ℝ) : ℝ := 21/125-(969/625)*t-(1083/2500)*t^2
def squareSecond (t : ℝ) : ℝ := -(969/625)-(1083/1250)*t

theorem square_hasDerivAt (t : ℝ) :
    HasDerivAt squarePolynomial (squareFirst t) t := by
  have hd : Differentiable ℝ squarePolynomial := by dsimp [squarePolynomial]; fun_prop
  convert (hd t).hasDerivAt using 1
  simp (disch := fun_prop) [squarePolynomial,squareFirst]
  ring

theorem squareFirst_hasDerivAt (t : ℝ) :
    HasDerivAt squareFirst (squareSecond t) t := by
  have hd : Differentiable ℝ squareFirst := by dsimp [squareFirst]; fun_prop
  convert (hd t).hasDerivAt using 1
  simp (disch := fun_prop) [squareFirst,squareSecond]
  ring

theorem square_positive {t : ℝ} (ht : t∈Icc 0 ((371/1000:ℝ)^2)) :
    0<squarePolynomial t := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) ((371/1000:ℝ)^2)) squarePolynomial := by
    apply concave_of_deriv2 (fun x _ => square_hasDerivAt x)
      (fun x _ => squareFirst_hasDerivAt x)
    intro x hx
    dsimp [squareSecond]
    nlinarith [hx.1]
  exact concave_gt_of_endpoints hc ht
    (by norm_num [squarePolynomial,qCap]) (by norm_num [squarePolynomial,qCap])

theorem cubic_positive {y : ℝ} (hy : y∈Icc 0 (371/1000:ℝ)) :
    0<(13/12:ℝ)-26/25-(2/5)*y+(26/25)*y^2-(19/50)*y^3 := by
  let v : ℝ := y-1/5
  have hv : v≤171/1000 := by dsimp [v]; linarith [hy.2]
  have htail := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv)
  have hsq := sq_nonneg (v-740/37351)
  have hid : (13/12:ℝ)-26/25-(2/5)*y+(26/25)*y^2-(19/50)*y^3=
      71/37500-(37/1250)*v+(203/250)*v^2-(19/50)*v^3 := by dsimp [v]; ring
  have hcomplete : (71/37500:ℝ)-(37/1250)*v+(37351/50000)*v^2=
      (37351/50000)*(v-740/37351)^2+2241221/1400662500 := by ring
  rw [hid]
  nlinarith only [htail,hsq,hcomplete]

theorem sine_bound {s : ℝ} (hs : s∈Icc 0 (19/50:ℝ)) :
    Real.sin s∈Icc 0 (371/1000:ℝ) := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := trig_bracket (l:=0) (u:=(19/50:ℝ)) (x:=s)
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  exact ⟨(transport_trig hsf).2.2.1,by norm_num at hb; linarith [hb.2.1]⟩

theorem coefficient {r s : ℝ} (hr : 1≤r) (hs : s∈Icc 0 (19/50:ℝ)) :
    R/denominator r s<7/5+(19/50)*(Real.sin s)^2 := by
  have hy := sine_bound hs
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hp := square_positive ⟨sq_nonneg (Real.sin s),hy2⟩
  have hden := denominator_sq r s
  have hr2 : 1≤r^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hr2 (sq_nonneg (Real.cos s))
  have hd : 2-(Real.sin s)^2≤(denominator r s)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq s]
  have hD : 0<7/5+(19/50)*(Real.sin s)^2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hd (sq_nonneg (7/5+(19/50)*(Real.sin s)^2))
  apply OrdinaryCurvatureBounds.quotient_lt_of_square (denominator_pos r s) hD
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  dsimp [squarePolynomial] at hp
  nlinarith only [hp,hscaled,hR2]

theorem lower {l r s : ℝ} (hl : 0<l) (hr : 1≤r)
    (hs : s∈Icc 0 (19/50:ℝ)) : (26/25)*l<angleSlope l r s := by
  have hy := sine_bound hs
  have hcoef := coefficient hr hs
  have hpoly := cubic_positive hy
  have hc : 0<Real.cos s := by linarith [Explicit.AB_cut_cosine hs]
  have hp := mul_le_mul_of_nonneg_right hcoef.le hy.1
  have hnum : (26/25)*(Real.cos s)^2<
      13/12+Real.sin s-R*Real.sin s/denominator r s := by
    have he : R*Real.sin s/denominator r s=(R/denominator r s)*Real.sin s := by ring
    rw [he]
    nlinarith [Real.sin_sq_add_cos_sq s]
  unfold angleSlope
  apply (lt_div_iff₀ (sq_pos_of_pos hc)).2
  nlinarith only [mul_lt_mul_of_pos_left hnum hl]

theorem original {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 (19/50:ℝ)) :
    (26/25)*Explicit.l .low z<angleSlope (Explicit.l .low z)
      (Explicit.m .low z/Explicit.l .low z) s := by
  have hl := (Explicit.family_positive .low hz).2.1
  exact lower hl ((one_le_div hl).2 (Explicit.low_tilted hz).1.le) hs

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.LowABSlope
