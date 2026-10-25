module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Angular
public import SquaresInCircles.Eight.Owners.GA.Negative.ELowAStress
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3Endpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3High
public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESourceData
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2HighAffected
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowABSlope
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2NegativeSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData

/-!
# Eight squares: all low saturated alternatives and the complete reference scalar theorem

The same-block H/B comparisons retain their
exact surplus. The positive allowance .68125(h-z) includes the widened
D cost. The final finite-sum theorem uses both original signed budgets.
-/

section
/-!
## All pure alternatives on the low quarter interval

The GA equal-angle endpoint pays for AB through
the exact decreasing norm increment in the other coefficient. The
negative H curve is concave in tan(s) on the complete interval [0,z].
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowPure
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.SecantCoordinate NegativeAPositiveTD.SecantBounds

private theorem r69_low_dom {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]; exact hz

theorem baseline_comparison {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 frameCap) :
    baseline true (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z≤
      baseline false (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hb := Explicit.positive .low (r69_low_dom hz)
  have hl : 0<Explicit.l .low z := by linarith [hb.2.1]
  have hkm := (Explicit.low_ratios hz).2.2.2.2
  have hh := NegativeAPositiveTD.LowEqual.charge_comparison hb.1 hkm.le hl hs
  rw [Angular.baseline_eq_extension true _ _ _ _ hs,Angular.baseline_eq_extension false _ _ _ _ hs]
  simp only [Angular.extension,Angular.affected,↓reduceIte,Bool.false_eq_true,baseline_zero]
  linarith [hh]

theorem equal_positive (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z z := by
  have hh := (low_endpoints hz).2.2.2.2
  cases atG
  · exact hh.trans_le (baseline_comparison hz (Explicit.frame_domain .low (r69_low_dom hz)))
  · exact hh

def scalar (atG : Bool) (z x : ℝ) : ℝ :=
  NegativeAPositiveTD.SecantCoordinate.pure
    (baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z)
    (Explicit.l .low z)
    (Angular.ratio atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z))
    (Explicit.k .low z) 1 z x

theorem ratio_domain (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    Angular.ratio atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z)∈Icc 0 (113/100:ℝ) := by
  have hb := Explicit.positive .low (r69_low_dom hz)
  have hl : 0<Explicit.l .low z := by linarith [hb.2.1]
  have hr := Explicit.low_ratios hz
  cases atG
  · exact ⟨div_nonneg hb.2.2.le hl.le,(div_le_iff₀ hl).2 hr.2.2.2.1.le⟩
  · exact ⟨div_nonneg hb.1.le hl.le,(div_le_iff₀ hl).2 (by
      simp only [Angular.affected,↓reduceIte]; linarith [hr.2.1,hl])⟩

theorem scalar_concave (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    ConcaveOn ℝ (Icc 0 (Real.tan z)) (scalar atG z) := by
  have hb := Explicit.low_ranges hz
  have hzf := Explicit.frame_domain .low (r69_low_dom hz)
  apply pure_concave (by linarith [hb.1.1] : 0<Explicit.k .low z) (by norm_num : (0:ℝ)<1)
    hzf le_rfl hzf.2
  intro x hx
  have hs := arctan_interval hzf hx
  have hxhi : x≤32/125 := by
    have ht := tan_monotone hzf (show (1/4:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.2
    linarith [hx.2,tan_GA_cut]
  exact (LowNegative.pure_curvature hb.2.1.1 (ratio_domain atG hz)
    ⟨hb.1.1,by linarith [hb.1.2]⟩ ⟨hx.1,hxhi⟩
    ⟨by linarith [hs.2],by linarith [hs.1,hz.2]⟩).le.trans (by norm_num)

theorem scalar_zero (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) : 0<scalar atG z 0 := by
  simpa [scalar,NegativeAPositiveTD.SecantCoordinate.pure,baseline_zero] using (low_endpoints hz).1
theorem scalar_equal (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) : 0<scalar atG z (Real.tan z) := by
  have hl : 0<Explicit.l .low z := by linarith [(Explicit.positive .low (r69_low_dom hz)).2.1]
  have hh := Angular.pure_at_original (k:=Explicit.k .low z) (m:=Explicit.m .low z) (z:=z)
    (p:=Explicit.k .low z) (q:=1) atG hl (Explicit.frame_domain .low (r69_low_dom hz))
  simpa only [scalar,hh,sub_self,V_zero,add_zero] using equal_positive atG hz

theorem H_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 z) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      V R (Explicit.k .low z) 1 (z-s) := by
  have hzf := Explicit.frame_domain .low (r69_low_dom hz)
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hzf.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan z) := ⟨tan_nonnegative hsf,tan_monotone hsf hzf hs.2⟩
  have hh := concave_gt_of_endpoints (scalar_concave atG hz) hx (scalar_zero atG hz) (scalar_equal atG hz)
  have hl : 0<Explicit.l .low z := by linarith [(Explicit.positive .low (r69_low_dom hz)).2.1]
  simpa only [scalar,Angular.pure_at_original atG hl hsf] using hh

theorem negative_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (hsz : s≤z) (i : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      V R (Explicit.p .low atG z s i) (Explicit.q .low atG z s i) (z-s) := by
  have hh := H_positive atG hz ⟨hs.1,hsz⟩
  have hc := LowNegative.comparison (t:=z-s) atG hz hs ⟨by linarith,by linarith [hz.2,hs.1]⟩ i
  linarith

theorem original (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.pure .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i j s z := by
  by_cases hsz : s≤z
  · simpa only [Concentration.pure,ite_eq_left hsz] using negative_positive atG hz hs hsz j
  · have hp := Positive.reduces_to_equal .low atG (r69_low_dom hz) hs (le_of_not_ge hsz) i
    have he := equal_positive atG hz
    simp only [Concentration.pure,ite_eq_right hsz]
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowPure
end
end
end

section
/-!
## The widened low AB and fixed-pair slope bounds

The positive-square comparison is concave
in sin(s)^2. Its final cubic uses the prescribed shift by 1/4 and an
exact completed square. The new G constants use ratio 2/3 directly.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowSlopes
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
    simp only [Vd,mixedNDerivative,normD1,pairProduct,zero_sub,Real.cos_neg,mul_one]
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

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowSlopes
end
end
end

section
/-!
## The low BT3 saturated G curves

The affected GA norm uses ratio at most 2/3
and its 1.6 derivative bound. The unaffected AB same-block derivative
uses the widened .94 baseline ratio and the exact .117l reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowSaturatedG
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeAPositiveTD.SecantCoordinate Angular LowAffectedSlope

private theorem r69_low_dom {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]; exact hz

def same (atG : Bool) (k l c s z : ℝ) : ℝ :=
  baseline atG k l c s z+mixedBlock R k (lambdaG atG l s) (frameCap-z) (frameCap-s)
def negative (k l c s z : ℝ) : ℝ :=
  baseline true k l c s z+V R k (NegativeAPositiveTD.secant l s) (frameCap-s)
def ABextension (k l c s z : ℝ) : ℝ :=
  extension false k l c s z+mixedBlock R k l (frameCap-z) (frameCap-s)
def ABfirst (k l c s z : ℝ) : ℝ :=
  angleSlope l (c/l) s-
    mixedNDerivative R k l (frameCap-z) (frameCap-s)

theorem cap_cosine {s : ℝ} (hs : s∈Icc 0 frameCap) :
    Real.cos (frameCap-s)/Real.cos s=Real.cos frameCap+Real.tan s*Real.sin frameCap := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [Real.cos_sub,Real.tan_eq_sin_div_cos]
  field_simp [hc.ne']

theorem GA_same_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    same true k l c s z=baseline true k l c 0 z+k*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
      l*(Real.cos frameCap-1)+
      l*(charged (k/l) z (Real.tan s)+R*OrdinaryCurvatureBounds.shape (k/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hcos := cap_cosine hs
  rw [same,baseline_eq_extension true k l c z hs]
  simp only [extension,affected,lambdaG,NegativeAPositiveTD.lambdaG,↓reduceIte,FlatTStress.secantCharge,mixedBlock]
  rw [show frameCap-z-(frameCap-s)=s-z by ring,
    NegativeAPositiveTD.AffectedPositive.rotation_norm hl hc k z,NegativeAPositiveTD.AffectedPositive.zero_norm hl k]
  dsimp [LowAffectedSlope.charged,NegativeAPositiveTD.secant]
  have hh := congrArg (fun a : ℝ => l*a) hcos
  field_simp [hl.ne',hc.ne'] at hh ⊢
  linear_combination (12*l)*hh

theorem GA_negative_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    negative k l c s z=baseline true k l c 0 z+l*(Real.cos frameCap-1)+
      l*(charged (k/l) frameCap (Real.tan s)+R*OrdinaryCurvatureBounds.shape (k/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hcos := cap_cosine hs
  rw [negative,baseline_eq_extension true k l c z hs]
  simp only [extension,affected,↓reduceIte,FlatTStress.secantCharge,V]
  rw [show -(frameCap-s)=s-frameCap by ring,
    NegativeAPositiveTD.AffectedPositive.rotation_norm hl hc k frameCap,NegativeAPositiveTD.AffectedPositive.zero_norm hl k]
  dsimp [LowAffectedSlope.charged,NegativeAPositiveTD.secant]
  have hh := congrArg (fun a : ℝ => l*a) hcos
  field_simp [hl.ne',hc.ne'] at hh ⊢
  linear_combination (12*l)*hh

theorem original_ratio {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    Explicit.k .low z/Explicit.l .low z∈Icc (0:ℝ) (2/3:ℝ) := by
  have hp := Explicit.family_positive .low (r69_low_dom hz)
  exact ⟨div_nonneg hp.1.le hp.2.1.le,(div_le_iff₀ hp.2.1).2 (Explicit.low_ratio hz).2.le⟩

theorem tan_original {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    Real.tan s∈Icc 0 (32/125:ℝ) := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hh := tan_monotone hsf (show (1/4:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hs.2
  exact ⟨tan_nonnegative hsf,hh.trans NegativeAPositiveTD.SecantBounds.tan_GA_cut.le⟩

theorem GA_same_zero_le {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) :
    same true (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z≤
      same true (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hl := (Explicit.family_positive .low (r69_low_dom hz)).2.1
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hh := charged_monotone (original_ratio hz) hzframe
    (show (0:ℝ)∈Icc 0 (32/125:ℝ) by norm_num) (tan_original hs) (tan_original hs).1
  rw [GA_same_identity hl (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]),
    GA_same_identity hl hsf,Real.tan_zero]
  nlinarith [mul_le_mul_of_nonneg_left hh hl.le]

theorem GA_negative_zero_le {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) :
    negative (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z≤
      negative (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hl := (Explicit.family_positive .low (r69_low_dom hz)).2.1
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hh := charged_monotone (original_ratio hz)
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
    (show (0:ℝ)∈Icc 0 (32/125:ℝ) by norm_num) (tan_original hs) (tan_original hs).1
  rw [GA_negative_identity hl (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]),
    GA_negative_identity hl hsf,Real.tan_zero]
  nlinarith [mul_le_mul_of_nonneg_left hh hl.le]

theorem ABextension_eq {k l c s z : ℝ} (hs : s∈Icc 0 frameCap) :
    ABextension k l c s z=same false k l c s z := by
  rw [same,baseline_eq_extension false k l c z hs]
  rfl

theorem ABextension_hasDerivAt {k l c s z : ℝ}
    (hk : 0<k) (hl : 0<l) (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) :
    HasDerivAt (fun s => ABextension k l c s z) (ABfirst k l c s z) s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hP : frameCap-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hd := (extension_hasDerivAt (k:=k) (m:=c) (z:=z) false hl hc).add
    ((mixedN_hasDerivAt (R:=R) hk hl hP hN).comp s ((hasDerivAt_id s).const_sub frameCap))
  convert hd using 1
  · rfl
  · dsimp [ABfirst,ratio,affected]
    ring

theorem ABfirst_lower {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) :
    (117/1000)*Explicit.l .low z<ABfirst (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hp := Explicit.family_positive .low (r69_low_dom hz)
  have hratio := Explicit.low_ratio hz
  have hbasic := Explicit.family_basic_domain .low (r69_low_dom hz)
  have habs : |s-z|≤frameCap := by
    rw [abs_le]
    dsimp [frameCap]
    constructor <;> linarith [hs.1,hs.2,hz.1,hz.2]
  have ht := NegativeAPositiveTD.Curvature.norm_slope_signed_tangent hp.1 hp.2.1 habs
  obtain ⟨hC,hD⟩ := LowSlopes.narrow_constants hp.1 hbasic.2.2.2.1.le hratio.2.le
  have hC0 : 0≤curvatureZero R (Explicit.k .low z) (Explicit.l .low z) := by
    dsimp [curvatureZero]
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
      (pow_nonneg (by rw [pairNorm_zero]; positivity) 3)
  have hshift := mul_le_mul_of_nonneg_left
    (show -(s-z)≤1/4 by linarith [hs.1,hz.2]) hC0
  have hnorm : R*normD1 (Explicit.k .low z) (Explicit.l .low z) (s-z)<
      ((11/10:ℝ)+(51/100)*(1/4))*Explicit.l .low z := by
    linarith
  have hN : frameCap-s∈Icc (8/25:ℝ) (7/10:ℝ) := by
    dsimp [frameCap]
    constructor <;> linarith [hs.1,hs.2]
  have hsin := trig_bracket (l:=(8/25:ℝ)) (u:=(7/10:ℝ)) (x:=frameCap-s)
    (by norm_num) (by linarith [Real.pi_gt_three]) hN
  have hsine : (629/2000:ℝ)<Real.sin (frameCap-s) := by
    norm_num at hsin
    linarith [hsin.1]
  have hsine' := mul_lt_mul_of_pos_left hsine hp.2.1
  have hb := LowSlopes.AB_original hz hs
  dsimp [ABfirst,mixedNDerivative] at hb ⊢
  rw [show frameCap-z-(frameCap-s)=s-z by ring]
  linarith

theorem AB_same_zero_le {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) :
    same false (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z≤
      same false (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hp := Explicit.family_positive .low (r69_low_dom hz)
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hdom {s : ℝ} (hs : s∈Icc 0 (19/50:ℝ)) : s∈Icc 0 frameCap :=
    ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hm : MonotoneOn (fun s => ABextension (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z)
      (Icc (0:ℝ) (19/50)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun s hs => (ABextension_hasDerivAt hp.1 hp.2.1 (hdom hs) hzframe).continuousAt.continuousWithinAt)
      (fun s hs => ABextension_hasDerivAt hp.1 hp.2.1 (hdom (Ioo_subset_Icc_self hs)) hzframe)
    intro s hs
    exact (mul_nonneg (by norm_num) hp.2.1.le).trans (ABfirst_lower hz (Ioo_subset_Icc_self hs)).le
  have hh := hm (show (0:ℝ)∈Icc 0 (19/50:ℝ) by norm_num) hs hs.1
  simp only at hh
  rwa [ABextension_eq (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]),ABextension_eq (hdom hs)] at hh

theorem same_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<same atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hzero : 0<same atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z := by
    have he : frameCap-z-(frameCap-0)=-z := by ring
    simpa [same,lambdaG,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.secant,baseline_zero,
      mixedBlock,mixedG,NegativeAPositiveTD.mixedG,he] using (low_endpoints hz).2.1
  cases atG
  · exact hzero.trans_le (AB_same_zero_le hz hs)
  · exact hzero.trans_le (GA_same_zero_le hz hs)

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowSaturatedG
end
end
end

section
/-!
## The low separated H and G reference curves

Their positive allowance is the fixed .68125(h-z).
The widened AB baseline slope is greater than 1.03l; the fixed-G slope
is less than .93l, and the two H comparisons retain their original
1.032 and .964 upper slopes. Each combined curve minimizes at s=0.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open Angular NegativeAPositiveTD.NegativeSlope

private theorem r69_low_dom {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]; exact hz

inductive Case where
  | abG | abH | gaH
  deriving DecidableEq
def atG : Case→Bool | .gaH=>true | _=>false
def larger (e : Case) (l : ℝ) : ℝ := if e=.abG then l else 1
def upperValue : Case→ℝ | .abG=>93/100 | .abH=>129/125 | .gaH=>241/250
def curve (e : Case) (k l c z s : ℝ) : ℝ :=
  extension (atG e) k l c s z+V R k (larger e l) (frameCap-s)
def first (e : Case) (k l c _z s : ℝ) : ℝ :=
  angleSlope l (ratio (atG e) k l c) s-Vd R k (larger e l) (frameCap-s)
def allowance (z : ℝ) : ℝ := (109/160)*(frameCap-z)

theorem curve_hasDerivAt (e : Case) {k l c z s : ℝ}
    (hk : 0<k) (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    HasDerivAt (curve e k l c z) (first e k l c z s) s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hq : 0<larger e l := by cases e <;> simp [larger]; positivity
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hd := (extension_hasDerivAt (k:=k) (m:=c) (z:=z) (atG e) hl hc).add
    ((V_hasDerivAt (R:=R) hk hq hN).comp s ((hasDerivAt_id s).const_sub frameCap))
  convert hd using 1
  · rfl
  · dsimp [first]
    ring

theorem upper_original (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    Vd R (Explicit.k .low z) (larger e (Explicit.l .low z)) (frameCap-s)<
      upperValue e*larger e (Explicit.l .low z) := by
  have hb := Explicit.low_ranges hz
  have hp := Explicit.family_positive .low (r69_low_dom hz)
  have hkl := (Explicit.family_basic_domain .low (r69_low_dom hz)).2.2.2.1
  have hratio := Explicit.low_ratio hz
  cases e
  · apply LowSlopes.G_upper hp.1 hkl.le (by linarith [hratio.1]) hratio.2.le
    dsimp [atG,Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut,frameCap] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  · simp only [larger,upperValue,reduceCtorEq,↓reduceIte]
    have ht : frameCap-s∈Icc ((NegativeAPositiveTD.NegativeSlope.upperAngle .H32:ℚ):ℝ) frameCap := by
      simp only [atG,Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut,Bool.false_eq_true,
        ↓reduceIte] at hs
      rw [Set.mem_Icc]
      constructor <;> norm_num [NegativeAPositiveTD.NegativeSlope.upperAngle,frameCap] <;>
        linarith [hs.1,hs.2]
    have h := NegativeAPositiveTD.NegativeSlope.upper_bound .H32 (q:=1) hp.1
      (by linarith [hb.1.2]) (by linarith [hb.1.1])
      (by norm_num [NegativeAPositiveTD.NegativeSlope.upperRatio]; linarith [hb.1.2]) ht
    simp only [NegativeAPositiveTD.NegativeSlope.upperValue] at h
    push_cast at h
    linarith
  · simp only [larger,upperValue,reduceCtorEq,↓reduceIte]
    have ht : frameCap-s∈Icc ((NegativeAPositiveTD.NegativeSlope.upperAngle .H45:ℚ):ℝ) frameCap := by
      simp only [atG,Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut,
        ↓reduceIte] at hs
      rw [Set.mem_Icc]
      constructor <;> norm_num [NegativeAPositiveTD.NegativeSlope.upperAngle,frameCap] <;>
        linarith [hs.1,hs.2]
    have h := NegativeAPositiveTD.NegativeSlope.upper_bound .H45 (q:=1) hp.1
      (by linarith [hb.1.2]) (by linarith [hb.1.1])
      (by norm_num [NegativeAPositiveTD.NegativeSlope.upperRatio]; linarith [hb.1.2]) ht
    simp only [NegativeAPositiveTD.NegativeSlope.upperValue] at h
    push_cast at h
    linarith

theorem first_positive (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    0<first e (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z s := by
  have hV := upper_original e hz hs
  have hl := (Explicit.low_ranges hz).2.1.1
  cases e
  · have hB := LowSlopes.AB_original hz hs
    dsimp [first,atG,larger,upperValue,ratio,affected] at hV ⊢
    linarith
  · have hB := LowSlopes.AB_original hz hs
    dsimp [first,atG,larger,upperValue,ratio,affected] at hV ⊢
    linarith
  · have hB := LowSlopes.GA_original hz hs
    dsimp [first,atG,larger,upperValue,ratio,affected] at hV ⊢
    linarith

theorem fixed_zero_le (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    baseline (atG e) (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z+
        V R (Explicit.k .low z) (larger e (Explicit.l .low z)) frameCap≤
      baseline (atG e) (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
        V R (Explicit.k .low z) (larger e (Explicit.l .low z)) (frameCap-s) := by
  have hp := Explicit.family_positive .low (r69_low_dom hz)
  have hzero : (0:ℝ)∈Icc 0 (Explicit.angleCut (atG e)) := by
    cases e <;> norm_num [atG,Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut]
  have hm : MonotoneOn (curve e (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z)
      (Icc (0:ℝ) (Explicit.angleCut (atG e))) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun s hs => (curve_hasDerivAt e hp.1 hp.2.1 (Explicit.angle_domain _ hs).2).continuousAt.continuousWithinAt)
      (fun s hs => curve_hasDerivAt e hp.1 hp.2.1 (Explicit.angle_domain _ (Ioo_subset_Icc_self hs)).2)
    intro s hs
    exact (first_positive e hz (Ioo_subset_Icc_self hs)).le
  have hh := hm hzero hs hs.1
  dsimp [curve] at hh
  rw [←baseline_eq_extension (atG e) _ _ _ _ (Explicit.angle_domain _ hzero).2,
    ←baseline_eq_extension (atG e) _ _ _ _ (Explicit.angle_domain _ hs).2,sub_zero] at hh
  exact hh

theorem H_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z-
      allowance z+V R (Explicit.k .low z) 1 (frameCap-s) := by
  have hzero := (low_endpoints hz).2.2.1
  cases atG
  · have hh := fixed_zero_le .abH hz hs
    simp only [atG,larger,reduceCtorEq,↓reduceIte,baseline_zero] at hh
    dsimp [allowance]
    linarith
  · have hh := fixed_zero_le .gaH hz hs
    simp only [atG,larger,reduceCtorEq,↓reduceIte,baseline_zero] at hh
    dsimp [allowance]
    linarith

theorem G_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z-
      allowance z+V R (Explicit.k .low z) (lambdaG atG (Explicit.l .low z) s) (frameCap-s) := by
  have hzero := (low_endpoints hz).2.2.2.1
  cases atG
  · have hh := fixed_zero_le .abG hz hs
    simp only [atG,larger,↓reduceIte,baseline_zero] at hh
    dsimp [allowance,lambdaG,NegativeAPositiveTD.lambdaG]
    linarith
  · have hh := LowSaturatedG.GA_negative_zero_le hz hs
    simp only [LowSaturatedG.negative,NegativeAPositiveTD.secant,Real.cos_zero,div_one,
      sub_zero,baseline_zero] at hh
    dsimp [allowance,lambdaG,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.secant]
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowSeparated
end
end
end

section
/-!
## The five actual low negative-DE scalar endpoints

The mixed endpoint retains the
original G same-block correction, the separated endpoints retain the
largest tilted B coefficient, and the equal-angle endpoint uses the
actual diagonal D support with its secant cancelled by cosine.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (C10 C12 S9 S11 C4 ch Ch sh h cbar num3
  taylor_bounds pairNorm_nonneg num3_transfer ch_cast Ch_cast sh_cast)

private theorem r74_low {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    θ∈Icc ((left .low:ℚ):ℝ) ((right .low:ℚ):ℝ) := by
  simpa [left,right,PositiveTD.Certificate.L] using hθ

theorem low_mixed_charge {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ ZG≤Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+
      Explicit.l .low θ*(Real.cos frameCap-Real.cos θ) := by
  obtain ⟨hk,hl,_,_⟩ := split_positive .low .atT (r74_low hθ)
  have hθ' := family_frame_domain .low (r74_low hθ)
  have ht := taylor_bounds hθ'
  have hcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have htcap := taylor_bounds hcap
  have hs : 0≤Real.sin θ := (transport_trig hθ').2.2.1
  have hsum : (ch:ℝ)+(sh:ℝ)≤Real.cos frameCap+Real.sin frameCap := by
    rw [ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.1]
  have hsum0 : 0≤Real.cos frameCap+Real.sin frameCap := by
    linarith [(transport_trig hcap).1,(transport_trig hcap).2.2.1]
  have hprod := mul_le_mul hsum ht.2.2.2.2.1
    (show 0≤aeval θ C10 by linarith [ht.2.2.2.1]) hsum0
  have hdiff : Real.cos frameCap-Real.sin frameCap≤(Ch:ℝ)-(sh:ℝ) := by
    rw [Ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.2]
  have hdiff0 : 0≤(Ch:ℝ)-(sh:ℝ) := by
    linarith [(transport_trig hcap).2.2.2.2]
  have hprod' := mul_le_mul hdiff ht.2.2.1 hs hdiff0
  have hphi : PositiveAngularEnvelope.phi (frameCap-θ)=
      (Real.cos frameCap+Real.sin frameCap)*Real.cos θ-
        (Real.cos frameCap-Real.sin frameCap)*Real.sin θ := by
    simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
    ring
  have hphiLower : ((ch:ℝ)+(sh:ℝ))*aeval θ C10-
      ((Ch:ℝ)-(sh:ℝ))*aeval θ S9≤PositiveAngularEnvelope.phi (frameCap-θ) := by
    rw [hphi]
    linarith
  have hK := mul_le_mul_of_nonneg_left (sub_le_sub_right hphiLower 1) hk.le
  have hcos : (ch:ℝ)-aeval θ C12≤Real.cos frameCap-Real.cos θ := by
    rw [ch_cast]
    linarith [htcap.2.2.2.2.1,ht.2.2.2.2.2]
  have hL := mul_le_mul_of_nonneg_left hcos hl.le
  simp only [ZG,map_add,map_sub,map_mul,map_one,aeval_C,k_eval,l_eval,eq_ratCast]
  linarith only [hK,hL]

theorem mixed_num3 (e : Split) : NM e=num3 (lowB e+C10-1+ZG)
    (PHminus .low) (PG .low) (PB .low e) (RHminus .low) (RG .low) (RB .low e) := by
  dsimp [NM,NH,lowDen,num3]
  ring

theorem low_H_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<lowBase e θ 0+V R (Explicit.k .low θ) 1 θ := by
  have hn := ordinary_norm_bounds .low e (r74_low hθ)
  have ht := taylor_bounds (family_frame_domain .low (r74_low hθ))
  have hA : aeval θ (lowB e+C10-1)≤lowNonradical e θ+Real.cos θ-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [low_nonradical_lower e hθ,ht.2.2.2.2.1]
  have hp := num3_transfer
    (show 0<aeval θ (RHminus .low) from low_auxiliary_positive e 3 hθ)
    (show 0<aeval θ (RG .low) from low_auxiliary_positive e 1 hθ)
    (show 0<aeval θ (RB .low e) from low_auxiliary_positive e 2 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.2.2.2.1 hn.2.1 hn.2.2.1 hA
    (by simpa [NH] using (low_numerators_positive e hθ).1)
  rw [low_H_identity e hθ θ]
  exact hp

theorem low_M_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<lowBase e θ 0+V R (Explicit.k .low θ) 1 θ+
      Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+
      Explicit.l .low θ*(Real.cos frameCap-Real.cos θ) := by
  have hn := ordinary_norm_bounds .low e (r74_low hθ)
  have ht := taylor_bounds (family_frame_domain .low (r74_low hθ))
  have hA : aeval θ (lowB e+C10-1+ZG)≤lowNonradical e θ+Real.cos θ-1+
      (Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+
        Explicit.l .low θ*(Real.cos frameCap-Real.cos θ)) := by
    simp only [map_add,map_sub,map_one]
    linarith [low_nonradical_lower e hθ,ht.2.2.2.2.1,low_mixed_charge hθ]
  have hP : 0<aeval θ (num3 (lowB e+C10-1+ZG) (PHminus .low) (PG .low)
      (PB .low e) (RHminus .low) (RG .low) (RB .low e)) := by
    rw [←mixed_num3]
    exact (low_numerators_positive e hθ).2.1
  have hp := num3_transfer
    (show 0<aeval θ (RHminus .low) from low_auxiliary_positive e 3 hθ)
    (show 0<aeval θ (RG .low) from low_auxiliary_positive e 1 hθ)
    (show 0<aeval θ (RB .low e) from low_auxiliary_positive e 2 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.2.2.2.1 hn.2.1 hn.2.2.1 hA hP
  rw [low_H_identity e hθ θ]
  linarith only [hp]

theorem low_separated_nonradical (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (lowB e-C (109/200)*mHi .low e*(C PositiveTD.Certificate.h-X))≤
      lowNonradical e θ-(109/200)*Explicit.splitM .low e θ*(frameCap-θ) := by
  have ht := (tilted_bounds .low e (r74_low hθ)).2.2
  have hp := mul_le_mul_of_nonneg_right ht
    (sub_nonneg.mpr (family_frame_domain .low (r74_low hθ)).2)
  have hh : ((PositiveTD.Certificate.h:ℚ):ℝ)=frameCap := by
    norm_num [PositiveTD.Certificate.h,frameCap]
  have hl := low_nonradical_lower e hθ
  simp only [map_sub,map_mul,aeval_C,aeval_X,eq_ratCast,hh]
  push_cast
  generalize frameCap = F at hp ⊢
  linarith

theorem low_SH_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<lowBase e θ 0-(109/200)*Explicit.splitM .low e θ*(frameCap-θ)+
      V R (Explicit.k .low θ) 1 frameCap := by
  have hn := ordinary_norm_bounds .low e (r74_low hθ)
  have hcap := cap_norm_bounds hθ
  have ht := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hA : aeval θ (lowB e-C (109/200)*mHi .low e*(C PositiveTD.Certificate.h-X)+C (ch-1))≤
      lowNonradical e θ-(109/200)*Explicit.splitM .low e θ*(frameCap-θ)+Real.cos frameCap-1 := by
    simp only [map_add,aeval_C,eq_ratCast,Rat.cast_sub,Rat.cast_one,ch_cast]
    linarith [low_separated_nonradical e hθ,ht.2.2.2.2.1]
  have hp := num3_transfer
    (show 0<aeval θ (RHcap) from low_auxiliary_positive e 4 hθ)
    (show 0<aeval θ (RG .low) from low_auxiliary_positive e 1 hθ)
    (show 0<aeval θ (RB .low e) from low_auxiliary_positive e 2 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hcap.1 hn.2.1 hn.2.2.1 hA (low_numerators_positive e hθ).2.2.1
  have he := low_H_identity e hθ frameCap
  linarith only [hp,he]

theorem low_SG_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<lowBase e θ 0-(109/200)*Explicit.splitM .low e θ*(frameCap-θ)+
      V R (Explicit.k .low θ) (Explicit.l .low θ) frameCap := by
  have hn := ordinary_norm_bounds .low e (r74_low hθ)
  have hcap := cap_norm_bounds hθ
  have ht := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hl := (split_positive .low e (r74_low hθ)).2.1
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 hl.le
  have hA : aeval θ (lowB e-C (109/200)*mHi .low e*(C PositiveTD.Certificate.h-X)+l .low*C (ch-1))≤
      lowNonradical e θ-(109/200)*Explicit.splitM .low e θ*(frameCap-θ)+
        Explicit.l .low θ*(Real.cos frameCap-1) := by
    simp only [map_add,map_mul,aeval_C,eq_ratCast,Rat.cast_sub,Rat.cast_one,l_eval,ch_cast]
    linarith [low_separated_nonradical e hθ]
  have hp := num3_transfer
    (show 0<aeval θ (RH .low) from low_auxiliary_positive e 0 hθ)
    (show 0<aeval θ (RGcap) from low_auxiliary_positive e 5 hθ)
    (show 0<aeval θ (RB .low e) from low_auxiliary_positive e 2 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hcap.2 hn.2.2.1 hA (low_numerators_positive e hθ).2.2.2.1
  have he := low_G_identity e hθ frameCap
  linarith only [hp,he]

theorem low_equal_nonradical (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (C10*(lowB e+C dbar)+C K*S11-C dbar)≤
      Real.cos θ*(lowNonradical e θ+(GlobalGA.Secondary.diagonal-1/2))+Explicit.K*Real.sin θ-(GlobalGA.Secondary.diagonal-1/2) := by
  have ht := taylor_bounds (family_frame_domain .low (r74_low hθ))
  have hB : 0<aeval θ (lowB e+C dbar) := by
    simpa only [↓reduceIte] using multiplied_baseline_positive .low e (r74_low hθ)
  have h₁ := mul_le_mul_of_nonneg_right ht.2.2.2.2.1 hB.le
  have hc : 0≤Real.cos θ := by linarith [(transport_trig (family_frame_domain .low (r74_low hθ))).1]
  have h₂ := mul_le_mul_of_nonneg_left (low_nonradical_lower e hθ) hc
  have h₃ := mul_nonneg (sub_nonneg.mpr PositiveTD.Certificate.diagonal_le_cbar)
    (sub_nonneg.mpr (Real.cos_le_one θ))
  have hK : ((K:ℚ):ℝ)=Explicit.K := by norm_num [K,Explicit.K]
  have hhalf : ((1/2:ℚ):ℝ)=1/2 := by norm_num
  simp only [map_sub,map_add,map_mul,aeval_C,eq_ratCast,hhalf,hK] at h₁ ⊢
  have hK0 : 0≤Explicit.K := by norm_num [Explicit.K]
  have h₄ := mul_le_mul_of_nonneg_left ht.2.1 hK0
  generalize ((cbar:ℚ):ℝ) = cb at h₁ h₃ ⊢
  linarith only [h₁,h₂,h₃,h₄]

theorem low_Z_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<lowBase e θ θ := by
  have hn := ordinary_norm_bounds .low e (r74_low hθ)
  have hθ' := family_frame_domain .low (r74_low hθ)
  have hc : 0<Real.cos θ := by linarith [(transport_trig hθ').1]
  have hp := num3_transfer
    (show 0<aeval θ (C4*RH .low) from low_auxiliary_positive e 6 hθ)
    (show 0<aeval θ (C4*RG .low) from low_auxiliary_positive e 7 hθ)
    (show 0<aeval θ (C4*RB .low e) from low_auxiliary_positive e 8 hθ)
    (mul_nonneg hc.le (pairNorm_nonneg _ _ _))
    (mul_nonneg hc.le (pairNorm_nonneg _ _ _))
    (mul_nonneg hc.le (pairNorm_nonneg _ _ _))
    (scaled_norm_bound hθ' hn.1) (scaled_norm_bound hθ' hn.2.1)
    (scaled_norm_bound hθ' hn.2.2.1) (low_equal_nonradical e hθ)
    (by simpa only [NZ,↓reduceIte] using (low_numerators_positive e hθ).2.2.2.2)
  rw [←low_equal_identity e hθ] at hp
  exact (mul_pos_iff_of_pos_left hc).mp hp

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Certificate
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryPositiveEnvelope
namespace Low

private theorem r69_low_dom {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]; exact hz

theorem positive_allowance (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (i : Fin 4) :
    -LowSeparated.allowance z≤Concentration.positive .low
      (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z) := by
  have hP : frameCap-z∈Icc 0 frameCap := ⟨by dsimp [frameCap]; linarith [hz.2],by linarith [hz.1]⟩
  by_cases hi : i=3
  · subst i
    simp only [Concentration.positive,PositiveTD.Hybrid.positive,↓reduceIte,LowSeparated.allowance]
    simp only [frameCap] at hP ⊢
    linarith [hP.1]
  · have hc := Explicit.ordered_pair_domain .low atG (r69_low_dom hz) hs i
    have hq := Explicit.low_q_upper atG hz hs i
    have hu := U_lower (Real.sqrt_nonneg _) radius_sq.le hc.1 hc.2.1 hc.2.2 hP
    have hh := mul_le_mul_of_nonneg_right hq.le hP.1
    simp only [Concentration.positive,PositiveTD.Hybrid.positive,↓reduceIte,ite_eq_right hi,
      LowSeparated.allowance]
    nlinarith only [hu,hh]

theorem separated_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.positive .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z)+
        V R (Explicit.p .low atG z s j) (Explicit.q .low atG z s j) (frameCap-s) := by
  have hu := positive_allowance atG hz hs i
  have hH := LowSeparated.H_positive atG hz hs
  have hG := LowSeparated.G_positive atG hz hs
  have hsf := (Explicit.angle_domain atG hs).2
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  fin_cases j
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.positive .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z)+
        V R (Explicit.k .low z) 1 (frameCap-s)
    linarith
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.positive .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z)+
        V R (Explicit.k .low z) (lambdaG atG (Explicit.l .low z) s) (frameCap-s)
    linarith
  · have hB := LowNegative.B_dominates_H atG hz hs hN
    change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.positive .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z)+
        V R (Explicit.p .low atG z s 2) (Explicit.q .low atG z s 2) (frameCap-s)
    linarith
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.positive .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z)+
        V R (Explicit.k .low z) 1 (frameCap-s)
    linarith

theorem HB_pure_le_same (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i : Fin 4) (hi : i=0∨i=2) :
    Concentration.pure .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i i s z≤
      mixedBlock R (Explicit.p .low atG z s i) (Explicit.q .low atG z s i) (frameCap-z) (frameCap-s) := by
  have hc := Explicit.ordered_pair_domain .low atG (r69_low_dom hz) hs i
  have hr := Explicit.low_HB_ratio atG hz hs i hi
  have hsf := (Explicit.angle_domain atG hs).2
  have hP : frameCap-z∈Icc 0 frameCap := ⟨by dsimp [frameCap]; linarith [hz.2],by linarith [hz.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  have hiD : i≠3 := by rcases hi with rfl|rfl <;> decide
  by_cases hsz : s≤z
  · have ht := transport_trig hN
    have hp := mul_le_mul hr ht.2.2.2.1.le ht.2.2.1
      (show 0≤(3/2)*Explicit.p .low atG z s i by linarith [hc.1])
    have hpay : Explicit.q .low atG z s i*Real.sin (frameCap-s)≤Explicit.p .low atG z s i := by
      nlinarith only [hp,hc.1]
    have hh := NegativeAPositiveTD.SameBlock.negative_surplus hc.1.le
      (show frameCap-z∈Icc 0 (frameCap-s) from ⟨hP.1,by linarith⟩) hN hpay
    simpa only [Concentration.pure,ite_eq_left hsz,show frameCap-s-(frameCap-z)=z-s by ring] using hh
  · have hh := NegativeAPositiveTD.SameBlock.positive_surplus hc.1.le
      (show Explicit.q .low atG z s i≤(17/10)*Explicit.p .low atG z s i by nlinarith only [hr,hc.1]) hP
      (show frameCap-s∈Icc 0 (frameCap-z) from ⟨hN.1,by linarith⟩)
    simpa only [Concentration.pure,ite_eq_right hsz,Concentration.positive,PositiveTD.Hybrid.positive,
      ↓reduceIte,ite_eq_right hiD,show frameCap-z-(frameCap-s)=s-z by ring] using hh

theorem saturated_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.saturated .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i j s z := by
  by_cases hij : i=j
  · subst j
    by_cases hiD : i=3
    · subst i
      simpa only [Concentration.saturated,Concentration.block,Concentration.positive,
        PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive,↓reduceIte,add_assoc] using
        separated_positive atG hz hs 3 3
    by_cases hiG : i=1
    · subst i
      simpa [Concentration.saturated,Concentration.block,PositiveTD.Hybrid.block,
        Explicit.p,Explicit.q,pWeights,qWeights,LowSaturatedG.same] using LowSaturatedG.same_positive atG hz hs
    have hi : i=0∨i=2 := by fin_cases i <;> simp_all
    have hc := HB_pure_le_same atG hz hs i hi
    have hp := LowPure.original atG hz hs i i
    simp only [Concentration.saturated,Concentration.block,PositiveTD.Hybrid.block,↓reduceIte,ite_eq_right hiD]
    linarith
  · simpa only [Concentration.saturated,ite_eq_right hij,add_assoc] using separated_positive atG hz hs i j

theorem intrinsic_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      min (Concentration.pure .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i j s z)
        (Concentration.saturated .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i j s z) := by
  rw [add_min]
  exact lt_min (LowPure.original atG hz hs i j) (saturated_positive atG hz hs i j)

end Low

theorem reference_scalar_positive (f : Certificate.Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (P N : Fin 4→ℝ)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPbudget : (∑i,P i)≤frameCap-z) (hNbudget : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=z-s) :
    0<baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s z+
      ∑i,Concentration.block f (Explicit.p f atG z s) (Explicit.q f atG z s) i (P i) (N i) := by
  have hp := Explicit.ordered_pair_domain f atG hz hs
  obtain ⟨i,j,hh⟩ := Concentration.concentrate f (Explicit.p f atG z s) (Explicit.q f atG z s) P N
    (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2) hP hN
    (Explicit.angle_domain atG hs).2 (Explicit.frame_domain f hz) hPbudget hNbudget hbalance
  have hpos : 0<baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s z+
      min (Concentration.pure f (Explicit.p f atG z s) (Explicit.q f atG z s) i j s z)
        (Concentration.saturated f (Explicit.p f atG z s) (Explicit.q f atG z s) i j s z) := by
    cases f
    · exact Low.intrinsic_positive atG (by
        have h := hz; norm_num [Certificate.left,Certificate.right,Certificate.split] at h; exact h) hs i j
    · exact High.intrinsic_positive atG (by
        have h := hz; norm_num [Certificate.left,Certificate.right,Certificate.split] at h; exact h) hs i j
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeABT3
end
end
end
