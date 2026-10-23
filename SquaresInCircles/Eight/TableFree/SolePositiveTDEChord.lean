module

public import SquaresInCircles.Eight.TableFree.SolePositiveTGrowth
public import SquaresInCircles.Eight.TableFree.PositiveScalarPolynomials

/-!
# The remaining DE low-family terminal chord

Uncompiled source. The original two-positive-square argument is proved
on the entire interval [0,.35]. The radius is the rational lower radius,
so the resulting chord transfers to every original working radius.
-/

@[expose] public section
namespace SquaresInCircles.Eight.TableFree.SolePositiveTDEChord
open Polynomial WholeIntervalPolynomial
open SolePositiveTGrowth

def sineUpper : ℚ[X] := PositiveScalarPolynomials.sine+C (1/1307674368000)*X^15
def cosineUpper : ℚ[X] := PositiveScalarPolynomials.cosine
def capSine : ℚ := PositiveScalarPolynomials.sine.eval (7/10)
def capCosine : ℚ :=
  (PositiveScalarPolynomials.cosine-C (1/20922789888000)*X^16).eval (7/10)
def a : ℚ[X] := C (903/1000)*(C (5/8)+C (27/100)*X)
def b : ℚ := 903/1000
def capSquare : ℚ[X] := a^2+C (b^2)-C (2*b*capSine)*a
def squareDifference : ℚ[X] := C (2*b)*a*(C capSine-sineUpper)
def A : ℚ[X] := C (7/10)*(C (7/10)-X)+C b*(cosineUpper-C capCosine)
def B : ℚ[X] := C (lowerRadius^2)*squareDifference-A^2
def P : ℚ[X] := B^2-C (4*lowerRadius^2)*A^2*capSquare

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem identities :
    centered 0 (7/20) A=expansion 16 (centered 0 (7/20) A) ∧
    centered 0 (7/20) B=expansion 32 (centered 0 (7/20) B) ∧
    centered 0 (7/20) P=expansion 64 (centered 0 (7/20) P) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem reserves :
    (2/5:ℚ)<lowerOn 16 0 (7/20) A ∧
    (6/5:ℚ)<lowerOn 32 0 (7/20) B ∧
    (1/4:ℚ)<lowerOn 64 0 (7/20) P := by decide

noncomputable section
open Set PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope SingleAngleConcavity VaryingBFunctions

theorem polynomial_values (t : ℝ) :
    aeval t sineUpper=HighOrderTaylor.S13 t ∧
    aeval t cosineUpper=HighOrderTaylor.C16 t ∧
    (capSine:ℝ)=HighOrderTaylor.S15 frameCap ∧
    (capCosine:ℝ)=HighOrderTaylor.C14 frameCap := by
  norm_num [sineUpper,cosineUpper,capSine,capCosine,
    PositiveScalarPolynomials.sine,PositiveScalarPolynomials.cosine,
    HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,frameCap]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem positive_values {t : ℝ} (ht : t∈Icc 0 (7/20:ℝ)) :
    0<aeval t A ∧ 0<aeval t B ∧ 0<aeval t P := by
  have hA := positive_on_interval (by norm_num : (0:ℚ)<7/20) identities.1 reserves.1 ht
  have hB := positive_on_interval (by norm_num : (0:ℚ)<7/20) identities.2.1 reserves.2.1 ht
  have hP := positive_on_interval (by norm_num : (0:ℚ)<7/20) identities.2.2 reserves.2.2 ht
  exact ⟨by linarith,by linarith,by linarith⟩

theorem chord {t : ℝ} (ht : t∈Icc 0 (7/20:ℝ)) :
    (7/10)*(frameCap-t)<(903/1000)*
      (V (lowerRadius:ℝ) (5/8+27/100*t) 1 frameCap-
        V (lowerRadius:ℝ) (5/8+27/100*t) 1 t) := by
  let α : ℝ := (903/1000)*(5/8+27/100*t)
  let β : ℝ := 903/1000
  have hα : 0<α := by dsimp [α]; nlinarith [ht.1]
  have hβ : 0<β := by norm_num [β]
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  let N := pairNorm α β (-t)
  let H := pairNorm α β (-frameCap)
  have hN : 0<N := pairNorm_pos hα hβ (by rw [abs_neg,abs_of_nonneg ht.1]; exact ht'.2)
  have hH : 0<H := pairNorm_pos hα hβ (by simp [frameCap])
  have hN2 : N^2=α^2+β^2-2*α*β*Real.sin t := by
    simpa [N,pairEnergy,pairProduct,Real.sin_neg] using
      pairNorm_sq hα.le hβ.le (by rw [abs_neg,abs_of_nonneg ht.1]; exact ht'.2)
  have hH2 : H^2=α^2+β^2-2*α*β*Real.sin frameCap := by
    simpa [H,pairEnergy,pairProduct,Real.sin_neg] using
      pairNorm_sq hα.le hβ.le (show |-frameCap|≤frameCap by simp [frameCap])
  have hS0 := HighOrderTaylor.S15_le_sin (show 0≤frameCap by norm_num [frameCap])
  have hS1 := HighOrderTaylor.sin_le_S13 ht.1
  have hC0 := HighOrderTaylor.C14_le_cos (show 0≤frameCap by norm_num [frameCap])
  have hC1 := HighOrderTaylor.cos_le_C16 ht.1
  have hvalues := polynomial_values t
  have hcap : H^2≤aeval t capSquare := by
    have hm := mul_le_mul_of_nonneg_left hS0 (show 0≤2*α*β by positivity)
    simp [capSquare,a,b,hvalues.2.2.1,α,β] at hm ⊢
    nlinarith [hH2]
  have hdiff : aeval t squareDifference≤N^2-H^2 := by
    have hsd : HighOrderTaylor.S15 frameCap-HighOrderTaylor.S13 t≤
        Real.sin frameCap-Real.sin t := by linarith
    have hm := mul_le_mul_of_nonneg_left hsd (show 0≤2*α*β by positivity)
    simp only [squareDifference,map_mul,map_sub,aeval_C,hvalues.1,hvalues.2.2.1]
    have ha : aeval t a=α := by simp [a,α]
    rw [ha]
    dsimp [b,β] at *
    nlinarith
  have hAupper : (7/10)*(frameCap-t)+β*(Real.cos t-Real.cos frameCap)≤aeval t A := by
    have hm := mul_le_mul_of_nonneg_left
      (show Real.cos t-Real.cos frameCap≤HighOrderTaylor.C16 t-HighOrderTaylor.C14 frameCap by linarith)
      hβ.le
    simp only [A,map_add,map_mul,map_sub,aeval_C,aeval_X,hvalues.2.1,hvalues.2.2.2]
    dsimp [b,β,frameCap] at *
    linarith
  rcases positive_values ht with ⟨hA,hB,hP⟩
  have hBid : aeval t B=(lowerRadius:ℝ)^2*aeval t squareDifference-(aeval t A)^2 := by
    simp [B]
  have hPid : aeval t P=(aeval t B)^2-
      4*(lowerRadius:ℝ)^2*(aeval t A)^2*aeval t capSquare := by simp [P]
  have hcapmul := mul_le_mul_of_nonneg_left hcap
    (show 0≤4*(lowerRadius:ℝ)^2*(aeval t A)^2 by positivity)
  have hcross : 2*(lowerRadius:ℝ)*aeval t A*H<aeval t B := by
    have hn : 0≤2*(lowerRadius:ℝ)*aeval t A*H := by
      exact mul_nonneg (mul_nonneg (by norm_num [lowerRadius]) hA.le) hH.le
    nlinarith
  have hdiffmul := mul_le_mul_of_nonneg_left hdiff (sq_nonneg (lowerRadius:ℝ))
  have hrootcross : (lowerRadius:ℝ)*H+aeval t A<(lowerRadius:ℝ)*N := by
    have hn : 0≤(lowerRadius:ℝ)*N := mul_nonneg (by norm_num [lowerRadius]) hN.le
    nlinarith [hBid]
  have hraw : (7/10)*(frameCap-t)<V (lowerRadius:ℝ) α β frameCap-V (lowerRadius:ℝ) α β t := by
    dsimp [V]
    change (7/10)*(frameCap-t)<
      β*(Real.cos frameCap-1)-(lowerRadius:ℝ)*(H-pairNorm α β 0)-
        (β*(Real.cos t-1)-(lowerRadius:ℝ)*(N-pairNorm α β 0))
    linarith
  have hhom (u : ℝ) : V (lowerRadius:ℝ) α β u=
      (903/1000)*V (lowerRadius:ℝ) (5/8+27/100*t) 1 u := by
    simpa only [α,β,mul_one] using
      V_homogeneous (by norm_num : (0:ℝ)≤903/1000) (lowerRadius:ℝ) (5/8+27/100*t) 1 u
  rw [hhom,hhom] at hraw
  nlinarith

theorem growth {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hp : 0<p) (hpq : p≤q)
    (hratio : (5/8+27/100*t)*q≤p) (hq : 903/1000≤q) (hnu : nu≤q)
    (ht : t∈Icc 0 (7/20:ℝ)) :
    (7/10)*(frameCap-t)≤Vnu R p q nu frameCap-Vnu R p q nu t := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  have hch := chord ht
  have hlen : 0≤frameCap-t := by linarith [ht'.2]
  have hv : 0≤V (lowerRadius:ℝ) (5/8+27/100*t) 1 frameCap-
      V (lowerRadius:ℝ) (5/8+27/100*t) 1 t := by
    nlinarith [mul_nonneg (by norm_num : (0:ℝ)≤7/10) hlen]
  have hscale := mul_le_mul_of_nonneg_right hq hv
  have htransfer := normalized_growth (radius_le hR hQL) hp hpq
    (show 0<5/8+27/100*t by linarith [ht.1]) hratio hnu ht'
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht'.2
  linarith

end SquaresInCircles.Eight.TableFree.SolePositiveTDEChord
