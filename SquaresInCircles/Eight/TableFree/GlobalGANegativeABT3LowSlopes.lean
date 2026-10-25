module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3LowAffectedSlope

/-!
# The widened low AB and fixed-pair slope bounds

Uncompiled Section 5, (24). The positive-square comparison is concave
in sin(s)^2. Its final cubic uses the prescribed shift by 1/4 and an
exact completed square. The new G constants use ratio 2/3 directly.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LowSlopes
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryNegativeSlope OrdinaryAngleConcavity
open NegativeAPositiveTD.SecantBaseline

def squarePolynomial (t : ℝ) : ℝ :=
  (721/500+(2/5)*t)^2*(1+(47/50:ℝ)^2*(1-t))-qCap
def squareFirst (t : ℝ) : ℝ :=
  2*(2/5)*(721/500+(2/5)*t)*(1+(47/50:ℝ)^2*(1-t))-
    (47/50:ℝ)^2*(721/500+(2/5)*t)^2
def squareSecond (t : ℝ) : ℝ :=
  2*(2/5:ℝ)^2*(1+(47/50:ℝ)^2*(1-t))-
    4*(2/5)*(47/50:ℝ)^2*(721/500+(2/5)*t)

theorem square_hasDerivAt (t : ℝ) : HasDerivAt squarePolynomial (squareFirst t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 721/500+(2/5)*t) (2/5) t := by
    simpa using ((hasDerivAt_id t).const_mul (2/5:ℝ)).const_add (721/500:ℝ)
  have h2 : HasDerivAt (fun t : ℝ => 1+(47/50:ℝ)^2*(1-t)) ((47/50:ℝ)^2*(-1)) t := by
    simpa using (((hasDerivAt_id t).const_sub (1:ℝ)).const_mul ((47/50:ℝ)^2)).const_add (1:ℝ)
  have h := ((h1.pow 2).mul h2).sub_const qCap
  unfold squarePolynomial
  convert h using 1
  simp only [squareFirst]
  norm_num
  ring
theorem squareFirst_hasDerivAt (t : ℝ) : HasDerivAt squareFirst (squareSecond t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 721/500+(2/5)*t) (2/5) t := by
    simpa using ((hasDerivAt_id t).const_mul (2/5:ℝ)).const_add (721/500:ℝ)
  have h2 : HasDerivAt (fun t : ℝ => 1+(47/50:ℝ)^2*(1-t)) ((47/50:ℝ)^2*(-1)) t := by
    simpa using (((hasDerivAt_id t).const_sub (1:ℝ)).const_mul ((47/50:ℝ)^2)).const_add (1:ℝ)
  have h := (((h1.const_mul (2*(2/5:ℝ))).mul h2).sub ((h1.pow 2).const_mul ((47/50:ℝ)^2)))
  unfold squareFirst
  convert h using 1
  simp only [squareSecond]
  norm_num
  ring
theorem square_positive {t : ℝ} (ht : t∈Icc 0 ((371/1000:ℝ)^2)) : 0<squarePolynomial t := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) ((371/1000:ℝ)^2)) squarePolynomial := by
    apply concave_of_deriv2 (fun x _ => square_hasDerivAt x) (fun x _ => squareFirst_hasDerivAt x)
    intro x hx
    dsimp [squareSecond]
    nlinarith [hx.1]
  exact concave_gt_of_endpoints hc ht
    (by norm_num [squarePolynomial,qCap]) (by norm_num [squarePolynomial,qCap])

theorem cubic_positive {y : ℝ} (hy : y∈Icc 0 (371/1000:ℝ)) :
    0<(13/12:ℝ)-103/100-(221/500)*y+(103/100)*y^2-(2/5)*y^3 := by
  let v := y-1/4
  have hv : v≤121/1000 := by dsimp [v]; linarith [hy.2]
  have htail := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv)
  have hid : (13/12:ℝ)-103/100-(221/500)*y+(103/100)*y^2-(2/5)*y^3=
      23/24000-v/500+(73/100)*v^2-(2/5)*v^3 := by dsimp [v]; ring
  rw [hid]
  nlinarith only [htail,sq_nonneg (v-5/3408)]

theorem AB_coefficient {r s : ℝ} (hr : (47/50:ℝ)≤r) (hs : s∈Icc 0 (19/50:ℝ)) :
    R/denominator r s<721/500+(2/5)*(Real.sin s)^2 := by
  have hy := NegativeAPositiveTD.LowABSlope.sine_bound hs
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hp := square_positive ⟨sq_nonneg (Real.sin s),hy2⟩
  have hden := denominator_sq r s
  have hr2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤47/50) hr 2
  have hprod := mul_le_mul_of_nonneg_right hr2 (sq_nonneg (Real.cos s))
  have hd : 1+(47/50:ℝ)^2*(1-(Real.sin s)^2)≤(denominator r s)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq s]
  have hD : 0<721/500+(2/5)*(Real.sin s)^2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hd (sq_nonneg (721/500+(2/5)*(Real.sin s)^2))
  apply quotient_lt_of_square (denominator_pos r s) hD
  have hR2 : R^2=qCap := radius_sq
  dsimp [squarePolynomial] at hp
  rw [hR2]
  linarith only [hp,hscaled]

theorem AB_lower {l r s : ℝ} (hl : 0<l) (hr : (47/50:ℝ)≤r)
    (hs : s∈Icc 0 (19/50:ℝ)) : (103/100)*l<angleSlope l r s := by
  have hy := NegativeAPositiveTD.LowABSlope.sine_bound hs
  have hcoef := AB_coefficient hr hs
  have hpoly := cubic_positive hy
  have hc : 0<Real.cos s := by linarith [Explicit.AB_cut_cosine hs]
  have hp := mul_le_mul_of_nonneg_right hcoef.le hy.1
  have hnum : (103/100)*(Real.cos s)^2<13/12+Real.sin s-R*Real.sin s/denominator r s := by
    have he : R*Real.sin s/denominator r s=(R/denominator r s)*Real.sin s := by ring
    rw [he]
    nlinarith [Real.sin_sq_add_cos_sq s]
  unfold angleSlope
  exact (lt_div_iff₀ (sq_pos_of_pos hc)).2 (by nlinarith only [mul_lt_mul_of_pos_left hnum hl])
theorem AB_original {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) :
    (103/100)*Explicit.l .low z<angleSlope (Explicit.l .low z) (Explicit.m .low z/Explicit.l .low z) s := by
  have hl : 0<Explicit.l .low z := by
    linarith [(Explicit.positive .low (by
      norm_num [Certificate.left,Certificate.right,Certificate.split]; exact hz)).2.1]
  exact AB_lower hl ((le_div_iff₀ hl).2 (Explicit.low_ratios hz).2.2.1.le) hs
theorem GA_original {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) :
    (249/250:ℝ)<angleSlope (Explicit.l .low z) (Explicit.k .low z/Explicit.l .low z) s := by
  have hb := Explicit.low_ranges hz
  have hh := (NegativeAPositiveTD.LowGASlope.fixed_lower hs).trans_le
    (NegativeAPositiveTD.LowGASlope.coefficient_comparison (k:=Explicit.k .low z)
      (l:=Explicit.l .low z) hb.1.1 (by linarith [hb.2.1.1]) hs)
  rwa [NegativeAPositiveTD.LowGASlope.slope_eq (by linarith [hb.2.1.1] : 0<Explicit.l .low z)] at hh

theorem narrow_endpoints : shapeC0q R (2/3)<51/100 ∧ NegativeAPositiveTD.Curvature.shapeD0q (2/3)<11/10 := by
  have hR2 := radius_sq
  constructor
  · unfold shapeC0q
    apply quotient_lt_of_square (pow_pos (shape_pos _) 3) (by norm_num)
    rw [show ((shape (2/3:ℝ))^3)^2=((shape (2/3:ℝ))^2)^3 by ring,shape_sq,mul_pow,hR2]
    norm_num [qCap]
  · unfold NegativeAPositiveTD.Curvature.shapeD0q
    apply quotient_lt_of_square (shape_pos _) (by norm_num)
    rw [shape_sq,mul_pow,hR2]
    norm_num [qCap]

theorem narrow_constants {p q : ℝ} (hp : 0<p) (hpq : p≤q) (hr : p≤(2/3)*q) :
    curvatureZero R p q<(51/100)*q ∧ NegativeAPositiveTD.Curvature.slopeZero p q<(11/10)*q := by
  have hq := hp.trans_le hpq
  have hr0 := div_nonneg hp.le hq.le
  have hr1 := (div_le_one hq).2 hpq
  have hre := (div_le_iff₀ hq).2 hr
  obtain ⟨_,_,hC,_⟩ := curvature_constants_normalize (R:=R) hp hq
  obtain ⟨_,hD⟩ := NegativeAPositiveTD.Curvature.constants_normalize hp hq
  constructor
  · rw [hC]
    have hh := (NegativeAPositiveTD.Curvature.shapeC0q_monotone ⟨hr0,hr1⟩ (by norm_num : (2/3:ℝ)∈Icc 0 1) hre).trans_lt
      narrow_endpoints.1
    simpa [mul_comm] using mul_lt_mul_of_pos_left hh hq
  · rw [hD]
    have hh := (NegativeAPositiveTD.Curvature.shapeD0q_monotone ⟨hr0,hr1⟩ (by norm_num : (2/3:ℝ)∈Icc 0 1) hre).trans_lt
      narrow_endpoints.2
    simpa [mul_comm] using mul_lt_mul_of_pos_left hh hq

theorem G_endpoint : Vd R (2/3) 1 (8/25)<93/100 := by
  have ht : (8/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  obtain ⟨hsl,hsh,hcl,hch⟩ := NegativeAPositiveTD.NegativeSlope.rational_taylor (t:=8/25)
    (by norm_num [frameCap])
  have h825 : ((8/25:ℚ):ℝ)=8/25 := by norm_num
  rw [h825] at hsl hsh hcl hch
  have hN0 := pairNorm_pos (by norm_num : (0:ℝ)<2/3) (by norm_num : (0:ℝ)<1)
    (show |-(8/25:ℝ)|≤frameCap by norm_num [frameCap])
  have hN2 := pairNorm_sq (by norm_num : (0:ℝ)<2/3) (by norm_num : (0:ℝ)<1)
    (show |-(8/25:ℝ)|≤frameCap by norm_num [frameCap])
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one,Real.sin_neg] at hN2
  have hreserve : (253/250:ℚ)^2<1+(2/3:ℚ)^2-(4/3)*NegativeAPositiveTD.NegativeSlope.sinHi (8/25) ∧
      (494697/250000:ℚ)*(2/3)*NegativeAPositiveTD.NegativeSlope.cosHi (8/25)<
        (93/100+NegativeAPositiveTD.NegativeSlope.sinLo (8/25))*(253/250) := by
    norm_num [NegativeAPositiveTD.NegativeSlope.sinHi,NegativeAPositiveTD.NegativeSlope.cosHi,NegativeAPositiveTD.NegativeSlope.sinLo,
      PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.S11,
      PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4]
  have hres₁ : (253/250:ℝ)^2<1+(2/3:ℝ)^2-(4/3)*(NegativeAPositiveTD.NegativeSlope.sinHi (8/25):ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr hreserve.1
    push_cast at h
    exact h
  have hres₂ : (494697/250000:ℝ)*(2/3)*(NegativeAPositiveTD.NegativeSlope.cosHi (8/25):ℝ)<
      (93/100+(NegativeAPositiveTD.NegativeSlope.sinLo (8/25):ℝ))*(253/250) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr hreserve.2
    push_cast at h
    exact h
  have hn : (253/250:ℝ)<pairNorm (2/3) 1 (-(8/25)) := by nlinarith
  have hnum := mul_le_mul (mul_le_mul_of_nonneg_right NegativeAPositiveTD.NegativeSlope.radius_tight.2.le
    (by norm_num : (0:ℝ)≤2/3)) hch (show 0≤Real.cos (8/25:ℝ) by linarith [(transport_trig ht).1])
    (by norm_num : (0:ℝ)≤(494697/250000)*(2/3))
  have h₁ := mul_le_mul_of_nonneg_right hsl (by norm_num : (0:ℝ)≤253/250)
  have h₂ := mul_lt_mul_of_pos_left hn (show 0<(93/100:ℝ)+Real.sin (8/25:ℝ) by
    linarith [(transport_trig ht).2.2.1])
  have hh := (div_lt_iff₀ hN0).2
    (show R*(2/3)*Real.cos (8/25)<(93/100+Real.sin (8/25))*pairNorm (2/3) 1 (-(8/25)) by nlinarith)
  have he : Vd R (2/3) 1 (8/25)= -Real.sin (8/25)+R*(2/3)*Real.cos (8/25)/pairNorm (2/3) 1 (-(8/25)) := by
    simp only [Vd,mixedNDerivative,normD1,pairProduct,zero_sub,Real.cos_neg,mul_one,one_mul]
    ring
  rw [he]
  linarith

theorem G_upper {p q t : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hr : p≤(2/3)*q) (ht : t∈Icc (8/25:ℝ) frameCap) : Vd R p q t<(93/100)*q := by
  have hq := hp.trans_le hpq
  have ha : (8/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hant := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hp hpq hqp ha
    ⟨by linarith [ht.1],ht.2⟩ ht.1
  have hm := NegativeAPositiveTD.NegativeSlope.normalized_slope_mono (div_nonneg hp.le hq.le)
    ((div_le_iff₀ hq).2 hr) (by norm_num : (2/3:ℝ)≤1) ha
  have he : Vd R p q (8/25)=q*Vd R (p/q) 1 (8/25) := by
    rw [Vd_normalized hq,Vd_normalized (by norm_num : (0:ℝ)<1)]
    norm_num
  have hh := mul_lt_mul_of_pos_left (hm.trans_lt G_endpoint) hq
  rw [←he] at hh
  exact hant.trans_lt (by simpa [mul_comm] using hh)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LowSlopes
