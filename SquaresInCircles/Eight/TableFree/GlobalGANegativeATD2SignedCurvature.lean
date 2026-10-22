module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2IntrinsicSource

/-!
# Ordinary-norm curvature on the full signed interval

Uncompiled transcription of equations (16)--(19) of the negative-A angle
companion. The fourth-derivative sign is extended to negative arguments
with the displayed polynomial T and its positive derivative in a.
Both tangent inequalities consequently hold on the whole signed interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Curvature
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds

def fourthPolynomial (a y : ℝ) : ℝ :=
  4*a^2-15+a*(a^2-2)*y+(10-a^2)*y^2+2*a*y^3+y^4
def fourthDerivative (a y : ℝ) : ℝ :=
  8*a+(3*a^2-2)*y-2*a*y^2+2*y^3

theorem fourthPolynomial_hasDerivAt (a y : ℝ) :
    HasDerivAt (fun a => fourthPolynomial a y) (fourthDerivative a y) a := by
  have hd : Differentiable ℝ (fun a => fourthPolynomial a y) := by
    dsimp [fourthPolynomial]
    fun_prop
  convert (hd a).hasDerivAt using 1
  simp (disch := fun_prop) [fourthPolynomial,fourthDerivative]
  ring

theorem fourthDerivative_lower {a y : ℝ}
    (ha : a∈Icc (2:ℝ) (5/2:ℝ)) (hy : y∈Icc (-(129/200):ℝ) 0) :
    (10317811/4000000:ℝ)≤fourthDerivative a y := by
  have ha0 : 0≤a := by linarith [ha.1]
  have ha2 := pow_le_pow_left₀ ha0 ha.2 2
  have hy0 : 0≤-y := by linarith [hy.2]
  have hyn : -y≤129/200 := by linarith [hy.1]
  have hy2 := pow_le_pow_left₀ hy0 hyn 2
  have hy3 := pow_le_pow_left₀ hy0 hyn 3
  have hcoef : 3*a^2-2≤(67/4:ℝ) := by nlinarith
  have h₁ := mul_le_mul_of_nonpos_right hcoef hy.2
  have h₂ := mul_le_mul_of_nonneg_left hy.1 (by norm_num : (0:ℝ)≤67/4)
  have h₃ := mul_le_mul ha.2
    (show y^2≤(129/200:ℝ)^2 by nlinarith only [hy2]) (sq_nonneg y)
    (by norm_num : (0:ℝ)≤5/2)
  dsimp [fourthDerivative]
  nlinarith

theorem fourthPolynomial_positive {a y : ℝ}
    (ha : a∈Icc (2:ℝ) (5/2:ℝ)) (hy : y∈Icc (-(129/200):ℝ) 0) :
    0<fourthPolynomial a y := by
  have hmono : MonotoneOn (fun a => fourthPolynomial a y) (Icc (2:ℝ) (5/2:ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (fourthPolynomial_hasDerivAt a y).continuousAt.continuousWithinAt)
      (fun a _ => fourthPolynomial_hasDerivAt a y)
    intro a ha
    have hh := fourthDerivative_lower (Ioo_subset_Icc_self ha) hy
    linarith
  have hh := hmono (show (2:ℝ)∈Icc (2:ℝ) (5/2:ℝ) by norm_num) ha ha.1
  have hid : fourthPolynomial 2 y=(1+y)^4 := by dsimp [fourthPolynomial]; ring
  rw [hid] at hh
  exact (pow_pos (show 0<1+y by linarith [hy.1]) 4).trans_le hh

theorem normD4_nonnegative_signed {p q t : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (ht : |t|≤frameCap) :
    0≤normD4 p q t := by
  by_cases ht0 : 0≤t
  · exact normD4_nonneg hp hpq hqp ⟨ht0,by simpa [abs_of_nonneg ht0] using ht⟩
  have hq := hp.trans_le hpq
  have hB : 0<pairProduct p q := mul_pos hp hq
  have hAlo := pairEnergy_ge_twice p q
  have hAhi := pairEnergy_le_five_halves hp hpq hqp
  have ha : pairEnergy p q/pairProduct p q∈Icc (2:ℝ) (5/2:ℝ) := by
    constructor
    · exact (le_div_iff₀ hB).2 (by linarith)
    · exact (div_le_iff₀ hB).2 (by linarith)
  have htneg : -t∈Icc 0 frameCap := by
    constructor
    · linarith
    · linarith [(abs_le.mp ht).1]
  have hsin := transport_trig htneg
  have hy : Real.sin t∈Icc (-(129/200):ℝ) 0 := by
    simp only [Real.sin_neg] at hsin
    exact ⟨by linarith [hsin.2.2.2.1],by linarith [hsin.2.2.1]⟩
  have hpoly := fourthPolynomial_positive ha hy
  have he : normD4 p q t=
      (pairProduct p q)^4*fourthPolynomial (pairEnergy p q/pairProduct p q) (Real.sin t)/
        (pairNorm p q t)^7 := by
    dsimp [normD4,fourthPolynomial]
    field_simp [hB.ne']
    ring
  rw [he]
  exact div_nonneg (mul_nonneg (pow_nonneg hB.le 4) hpoly.le)
    (pow_nonneg (Real.sqrt_nonneg _) 7)

theorem curvatureD_antitone_signed {p q : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    AntitoneOn (curvatureD R p q) (Icc (-frameCap) frameCap) := by
  have hq := hp.trans_le hpq
  apply antiOn_of_hasDeriv_nonpos
  · intro t ht
    exact (curvatureD_hasDerivAt hp hq (abs_le.mpr ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact curvatureD_hasDerivAt hp hq (abs_le.mpr ⟨ht.1.le,ht.2.le⟩)
  · intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg qCap))
      (normD4_nonnegative_signed hp hpq hqp (abs_le.mpr ⟨ht.1.le,ht.2.le⟩))

theorem curvature_signed_tangent {p q t : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (ht : |t|≤frameCap) :
    curvature R p q t≤curvatureZero R p q+curvatureSlope R p q*t := by
  by_cases ht0 : 0≤t
  · exact curvature_positive_upper (Real.sqrt_nonneg qCap) hp hpq hqp
      ⟨ht0,by simpa [abs_of_nonneg ht0] using ht⟩
  have hq := hp.trans_le hpq
  have hz : (0:ℝ)∈Icc (-frameCap) 0 := by norm_num [frameCap]
  have hzero : (0:ℝ)∈Icc (-frameCap) frameCap := by norm_num [frameCap]
  have htc : t∈Icc (-frameCap) 0 := ⟨(abs_le.mp ht).1,by linarith⟩
  have hdc (x : ℝ) (hx : x∈Icc (-frameCap) 0) :=
    curvature_hasDerivAt (R:=R) hp hq
      (abs_le.mpr ⟨hx.1,hx.2.trans hzero.2⟩)
  have hbound (x : ℝ) (hx : x∈Icc (-frameCap) 0) :
      curvatureSlope R p q≤curvatureD R p q x := by
    simpa using curvatureD_antitone_signed hp hpq hqp
      ⟨hx.1,hx.2.trans hzero.2⟩ hzero hx.2
  have hh := derivative_reserve
    (f:=curvature R p q) (df:=curvatureD R p q) (k:=curvatureSlope R p q)
    (fun x hx => (hdc x hx).continuousAt.continuousWithinAt)
    (fun x hx => hdc x (Ioo_subset_Icc_self hx))
    (fun x hx => hbound x (Ioo_subset_Icc_self hx)) htc hz htc.2
  rw [curvature_zero] at hh
  linarith

def slopeZero (p q : ℝ) : ℝ := R*pairProduct p q/pairNorm p q 0

theorem norm_slope_signed_tangent {p q t : ℝ}
    (hp : 0<p) (hq : 0<q) (ht : |t|≤frameCap) :
    R*normD1 p q t≤slopeZero p q-curvatureZero R p q*t := by
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hzero : (0:ℝ)∈Icc (-frameCap) frameCap := by norm_num [frameCap]
  have hzeroVal : R*normD1 p q 0=slopeZero p q := by simp [normD1,slopeZero]
  by_cases ht0 : 0≤t
  · have ht' : t∈Icc 0 frameCap := ⟨ht0,by simpa [abs_of_nonneg ht0] using ht⟩
    have hd (x : ℝ) (hx : x∈Icc 0 frameCap) :=
      (normD1_hasDerivAt hp hq (by rw [abs_of_nonneg hx.1]; exact hx.2)).const_mul (-R)
    have hb (x : ℝ) (hx : x∈Icc 0 frameCap) :
        curvatureZero R p q≤-R*normD2 p q x := by
      have hh := curvature_monotone hR hp hq hzero
        ⟨by linarith [hzero.1,hx.1],hx.2⟩ hx.1
      simpa [curvature] using hh
    have hh := derivative_reserve
      (f:=fun x => -R*normD1 p q x) (df:=fun x => -R*normD2 p q x)
      (k:=curvatureZero R p q)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
      (fun x hx => hb x (Ioo_subset_Icc_self hx))
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht' ht0
    linarith
  · have ht' : t∈Icc (-frameCap) 0 := ⟨(abs_le.mp ht).1,by linarith⟩
    have hd (x : ℝ) (hx : x∈Icc (-frameCap) 0) :=
      (normD1_hasDerivAt hp hq (abs_le.mpr ⟨hx.1,hx.2.trans hzero.2⟩)).const_mul R
    have hb (x : ℝ) (hx : x∈Icc (-frameCap) 0) :
        -curvatureZero R p q≤R*normD2 p q x := by
      have hh := curvature_negative_upper hR hp hq hx
      dsimp [curvature] at hh
      linarith
    have hh := derivative_reserve
      (f:=fun x => R*normD1 p q x) (df:=fun x => R*normD2 p q x)
      (k:=-curvatureZero R p q)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
      (fun x hx => hb x (Ioo_subset_Icc_self hx)) ht'
      (show (0:ℝ)∈Icc (-frameCap) 0 by norm_num [frameCap]) ht'.2
    rw [hzeroVal] at hh
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Curvature
