module

public import SquaresInCircles.Eight.Words.One.NegativeAnchorPolynomial

/-!
# Eight squares: exterior slopes for the original one-negative middle stress

The two coefficient families (`Weights`) are continuous stresses on their whole domains. All
exterior slope comparisons are proved at the common angle `7/10`, after derivative monotonicity
on the whole angle interval (`negativeSlope_mono`, `positiveSlope_mono`). The varying-weight
reciprocal norm comparison uses one quartic identity on the whole coefficient interval, with
positive Bernstein coefficients. The resulting caps are `lower_exterior_cap` and
`upper_exterior_cap`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OneNegativeAnchorConcentration
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope

abbrev R : ℝ := EndpointRotationPenalty.R
abbrev negativeSupport := OneNegativeAnchorPolynomial.negativeSupport

/-- The exact two stresses used in the anchor-order argument. -/
def Weights (l mu L : ℝ) : Prop :=
  (L∈Icc 0 (1/25 : ℝ) ∧ l=121/200 ∧ mu=47/50) ∨
  (L∈Icc (1/25 : ℝ) frameCap ∧ l=59/100+L/2 ∧ mu=1)

theorem Weights.bounds {l mu L : ℝ} (hw : Weights l mu L) :
    L∈Icc 0 frameCap ∧ (121/200 : ℝ)≤l ∧ l≤ mu ∧
      mu≤1 ∧ (47/50 : ℝ)≤ mu ∧ l/mu∈Icc (61/100 : ℝ) (47/50) ∧
      PositiveStressCoefficients.ratio L≤l := by
  rcases hw with ⟨hL,rfl,rfl⟩ | ⟨hL,rfl,rfl⟩
  · exact ⟨⟨hL.1,by dsimp [frameCap]; linarith [hL.2]⟩,
      by norm_num,by norm_num,by norm_num,le_rfl,by norm_num,
      by dsimp [PositiveStressCoefficients.ratio]; linarith [hL.2]⟩
  · simp only [div_one]
    dsimp [PositiveStressCoefficients.ratio]
    dsimp [frameCap] at hL ⊢
    exact ⟨⟨by linarith [hL.1],hL.2⟩,by linarith [hL.1],
      by linarith [hL.2],le_rfl,by norm_num,
      ⟨by linarith [hL.1],by linarith [hL.2]⟩,by linarith [hL.1]⟩

def positiveSupport (a b c t : ℝ) : ℝ := R*pairNorm a b t-c*PositiveAngularEnvelope.phi t
def negativeSlope (a b c t : ℝ) : ℝ := -R*normD1 a b (-t)+c*Real.sin t
def positiveSlope (a b c t : ℝ) : ℝ :=
  R*normD1 a b t-c*(Real.cos t-Real.sin t)

theorem negativeSupport_hasDerivAt {a b c t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (negativeSupport a b c) (negativeSlope a b c t) t := by
  have hn := (pairNorm_hasDerivAt ha hb
    (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)).comp t
      (hasDerivAt_id t).neg
  convert (hn.const_mul R).sub ((Real.hasDerivAt_cos t).const_mul c) using 1
  · rfl
  · dsimp [negativeSlope]
    ring

theorem positiveSupport_hasDerivAt {a b c t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (positiveSupport a b c) (positiveSlope a b c t) t := by
  have hn := pairNorm_hasDerivAt ha hb
    (show |t|≤frameCap by rw [abs_of_nonneg ht.1]; exact ht.2)
  convert (hn.const_mul R).sub
    (((Real.hasDerivAt_cos t).add (Real.hasDerivAt_sin t)).const_mul c) using 1
  · rfl
  · dsimp [positiveSlope]
    ring

theorem negativeSlope_hasDerivAt {a b c t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (negativeSlope a b c)
      (R*normD2 a b (-t)+c*Real.cos t) t := by
  have hn := (normD1_hasDerivAt ha hb
    (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)).comp t
      (hasDerivAt_id t).neg
  convert (hn.const_mul (-R)).add ((Real.hasDerivAt_sin t).const_mul c) using 1
  · rfl
  · ring

theorem positiveSlope_hasDerivAt {a b c t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (positiveSlope a b c)
      (R*normD2 a b t+c*PositiveAngularEnvelope.phi t) t := by
  have hn := normD1_hasDerivAt ha hb
    (show |t|≤frameCap by rw [abs_of_nonneg ht.1]; exact ht.2)
  convert (hn.const_mul R).sub
    (((Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t)).const_mul c) using 1
  · rfl
  · dsimp [PositiveAngularEnvelope.phi]
    ring

private theorem r47_abs_cap : |frameCap|≤frameCap := by
  rw [abs_of_nonneg (by norm_num [frameCap])]

private theorem r47_abs_neg_cap : |-frameCap|≤frameCap := by
  rw [abs_neg]; exact r47_abs_cap

theorem negativeSlope_mono {a b c : ℝ} (ha : 0<a) (hb : 0<b) (hbc : b≤c) :
    MonotoneOn (negativeSlope a b c) (Icc 0 frameCap) := by
  have hswap : curvatureZero R a b=curvatureZero R b a := by
    dsimp [curvatureZero,pairProduct]
    rw [pairNorm_symm a b 0]
    ring
  have hzero : curvatureZero R a b<(381/500)*b := by
    rw [hswap,(curvature_constants_normalize (R := R) hb ha).1]
    rw [mul_comm (381/500 : ℝ) b]
    exact mul_lt_mul_of_pos_left
      (shapeC0p_lt EndpointRotationPenalty.R_sq.le) hb
  apply monoOn_of_hasDeriv_nonneg
  · exact fun t ht => (negativeSlope_hasDerivAt ha hb ht).continuousAt.continuousWithinAt
  · exact fun t ht => negativeSlope_hasDerivAt ha hb (Ioo_subset_Icc_self ht)
  · intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have hcurv := curvature_negative_upper EndpointRotationPenalty.R_nonneg ha hb
      (show -t∈Icc (-frameCap) 0 by constructor <;> linarith [ht'.1,ht'.2])
    have hc := (transport_trig ht').1
    have hcos := mul_lt_mul_of_pos_left hc hb
    have hmore := mul_le_mul_of_nonneg_right hbc (show 0≤Real.cos t by linarith)
    dsimp [curvature] at hcurv
    nlinarith


theorem positiveSlope_mono {a b c : ℝ}
    (hb : 0<b) (hba : b≤a) (hab : a≤2*b) (hbc : b≤c) :
    MonotoneOn (positiveSlope a b c) (Icc 0 frameCap) := by
  have ha : 0<a := hb.trans_le hba
  have hswap (t : ℝ) : curvature R a b t=curvature R b a t := by
    dsimp [curvature,normD2,pairProduct,pairEnergy]
    rw [pairNorm_symm a b t]
    ring
  apply monoOn_of_hasDeriv_nonneg
  · exact fun t ht => (positiveSlope_hasDerivAt ha hb ht).continuousAt.continuousWithinAt
  · exact fun t ht => positiveSlope_hasDerivAt ha hb (Ioo_subset_Icc_self ht)
  · intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have hc := mixedP_second_lt EndpointRotationPenalty.R_nonneg
      EndpointRotationPenalty.R_sq.le hb hba hab ht'
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    simp only [sub_zero] at hc
    rw [← hswap] at hc
    have hphi : 0≤PositiveAngularEnvelope.phi t := (by norm_num : (0:ℝ)≤1).trans
      (CorrelatedSameBlock.one_le_phi ht')
    have hmore := mul_le_mul_of_nonneg_right hbc hphi
    dsimp [curvature] at hc
    nlinarith

theorem cap_reserves :
    (3221/5000 : ℝ)<Real.sin frameCap ∧ Real.sin frameCap<(6443/10000 : ℝ) ∧
    (478/625 : ℝ)<Real.cos frameCap ∧ Real.cos frameCap<(153001/200000 : ℝ) ∧
    (241/2000 : ℝ)<Real.cos frameCap-Real.sin frameCap ∧
    (19787/10000 : ℝ)<R ∧ R<(4947/2500 : ℝ) := by
  have hslo := sin_lower_seven (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hshi := sin_upper_five (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hclo := cos_lower_six (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hchi := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hRlo := sqrt_cap_lower
  have hRhi := OneNegativeAnchorPolynomial.radius_reserves.1
  norm_num [frameCap] at hslo hshi hclo hchi
  dsimp [OneNegativeAnchorPolynomial.Rplus] at hRhi
  refine ⟨by linarith,by linarith,by linarith,by linarith,
    by linarith,hRlo,?_⟩
  norm_num at hRhi
  linarith

theorem radius_cos_reserves :
    (19787/10000 : ℝ)*(478/625)<R*Real.cos frameCap ∧
      R*Real.cos frameCap<(4947/2500 : ℝ)*(153001/200000) := by
  obtain ⟨_,_,hc,hc',_,hR,hR'⟩ := cap_reserves
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hR) (sub_pos.mpr hc)]
  · have hp := mul_pos (sub_pos.mpr hR') (show 0<Real.cos frameCap by linarith)
    linarith

theorem pairNorm_normalize {a : ℝ} (ha : 0<a) (b t : ℝ) :
    pairNorm a b t=a*pairNorm 1 (b/a) t := by
  have he : a*(b/a)=b := by field_simp [ha.ne']
  calc
    pairNorm a b t=pairNorm (a*1) (a*(b/a)) t := by rw [he,mul_one]
    _=a*pairNorm 1 (b/a) t := pairNorm_homogeneous ha.le 1 (b/a) t

/-- The positive exterior A term has slope below `.72` on its whole
domain; the only endpoint comparison is by positive squaring. -/
theorem positive_one_cap {l : ℝ} (hl : 0<l) (hl1 : l≤1) :
    positiveSlope 1 l 1 frameCap<(18/25 : ℝ) := by
  have hh : |frameCap|≤frameCap := by rw [abs_of_nonneg]; norm_num [frameCap]
  have hN := pairNorm_pos (show (0:ℝ)<1 by norm_num) hl hh
  have hN2 := pairNorm_sq (show (0:ℝ)<1 by norm_num) hl hh
  obtain ⟨hs,_,_,_,hd,_,_⟩ := cap_reserves
  have hp := mul_nonneg (show 0≤1-l by linarith)
    (show 0≤1+l+2*l*Real.sin frameCap by positivity)
  have hNsq : ((1813/1000)*l)^2<(pairNorm 1 l frameCap)^2 := by
    have hs' := mul_lt_mul_of_pos_left hs (show 0<2*l^2 by positivity)
    dsimp [pairEnergy,pairProduct] at hN2
    nlinarith [sq_pos_of_pos hl]
  have hNl : (1813/1000)*l<pairNorm 1 l frameCap := by
    nlinarith [mul_pos (show (0:ℝ)<1813/1000 by norm_num) hl]
  have hupper := radius_cos_reserves.2
  have hnum : R*l*Real.cos frameCap<(21/25)*pairNorm 1 l frameCap := by
    have hm := mul_lt_mul_of_pos_right hupper hl
    nlinarith
  have hdiv : R*normD1 1 l frameCap<(21/25 : ℝ) := by
    calc
      R*normD1 1 l frameCap=(R*l*Real.cos frameCap)/pairNorm 1 l frameCap := by
        dsimp [normD1,pairProduct]
        ring
      _<(21/25 : ℝ) := (div_lt_iff₀ hN).2 hnum
  dsimp [positiveSlope]
  nlinarith

theorem negative_norm_cap {r : ℝ} (hr : r∈Icc (61/100 : ℝ) (47/50)) :
    pairNorm 1 r (-frameCap)<(4101/5000 : ℝ) := by
  have hr0 : 0<r := by linarith [hr.1]
  have hh : |-frameCap|≤frameCap := r47_abs_neg_cap
  have hN := pairNorm_sq (show (0:ℝ)<1 by norm_num) hr0 hh
  have hs := mul_lt_mul_of_pos_left cap_reserves.1 (show 0<2*r by positivity)
  have hp := mul_nonpos_of_nonneg_of_nonpos (show 0≤r-61/100 by linarith [hr.1])
    (show r-47/50≤0 by linarith [hr.2])
  dsimp [pairEnergy,pairProduct] at hN
  simp only [Real.sin_neg,one_pow,one_mul] at hN
  have hN0 := Real.sqrt_nonneg (1^2+r^2+2*1*r*Real.sin (-frameCap))
  change 0≤pairNorm 1 r (-frameCap) at hN0
  have hsq : (pairNorm 1 r (-frameCap))^2<(4101/5000)^2 := by
    have hr2 := hr.2
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq


theorem negative_mu_cap {l mu : ℝ} (hmu : 0< mu) (hl : 0<l)
    (hr : l/mu∈Icc (61/100 : ℝ) (47/50)) :
    negativeSlope mu l l frameCap< -(6/5)*l := by
  have hr0 : 0<l/mu := div_pos hl hmu
  have hh : |-frameCap|≤frameCap := r47_abs_neg_cap
  have hN := pairNorm_pos (show (0:ℝ)<1 by norm_num) hr0 hh
  have hNu := negative_norm_cap hr
  have hlow := radius_cos_reserves.1
  have hdiv : (18443/10000 : ℝ)<R*Real.cos frameCap/pairNorm 1 (l/mu) (-frameCap) := by
    apply (lt_div_iff₀ hN).2
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hdiv hl
  have hsin := mul_lt_mul_of_pos_left cap_reserves.2.1 hl
  have he : negativeSlope mu l l frameCap=
      l*(Real.sin frameCap-R*Real.cos frameCap/pairNorm 1 (l/mu) (-frameCap)) := by
    dsimp [negativeSlope,normD1,pairProduct]
    rw [pairNorm_normalize hmu,Real.cos_neg]
    field_simp [hmu.ne',hN.ne']
    ring
  rw [he]
  nlinarith


def exteriorC (r : ℝ) : ℝ :=
  R*Real.cos frameCap/pairNorm 1 r frameCap-Real.cos frameCap+Real.sin frameCap
def exteriorG (l : ℝ) : ℝ :=
  R*Real.cos frameCap/pairNorm 1 l (-frameCap)-Real.sin frameCap/l

theorem positive_norm_lower {r : ℝ} (hr : (61/100 : ℝ)≤r) :
    (1469/1000 : ℝ)<pairNorm 1 r frameCap := by
  have hr0 : 0<r := by linarith
  have hN := pairNorm_sq (show (0:ℝ)<1 by norm_num) hr0
    r47_abs_cap
  have hsq := mul_nonneg (show 0≤r-61/100 by linarith)
    (show 0≤r+61/100 by linarith)
  have hs := mul_lt_mul_of_pos_left cap_reserves.1 (show 0<2*r by positivity)
  have hN0 := pairNorm_pos (show (0:ℝ)<1 by norm_num) hr0
    r47_abs_cap
  dsimp [pairEnergy,pairProduct] at hN
  nlinarith


theorem positive_norm_lower_small {r : ℝ} (hr : (16/25 : ℝ)≤r) :
    (747/500 : ℝ)<pairNorm 1 r frameCap := by
  have hr0 : 0<r := by linarith
  have hN := pairNorm_sq (show (0:ℝ)<1 by norm_num) hr0
    r47_abs_cap
  have hsq := mul_nonneg (show 0≤r-16/25 by linarith)
    (show 0≤r+16/25 by linarith)
  have hs := mul_lt_mul_of_pos_left cap_reserves.1 (show 0<2*r by positivity)
  have hN0 := pairNorm_pos (show (0:ℝ)<1 by norm_num) hr0
    r47_abs_cap
  dsimp [pairEnergy,pairProduct] at hN
  nlinarith


theorem exteriorC_large {r : ℝ} (hr : (61/100 : ℝ)≤r) :
    exteriorC r<(91/100 : ℝ) := by
  have hN := positive_norm_lower hr
  have hdiv : R*Real.cos frameCap/pairNorm 1 r frameCap<(2061/2000 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0<pairNorm 1 r frameCap)).2
    nlinarith [radius_cos_reserves.2]
  dsimp [exteriorC]
  linarith [cap_reserves.2.2.2.2.1]

theorem exteriorC_small {r : ℝ} (hr : (16/25 : ℝ)≤r) :
    exteriorC r<(893/1000 : ℝ) := by
  have hN := positive_norm_lower_small hr
  have hdiv : R*Real.cos frameCap/pairNorm 1 r frameCap<(2027/2000 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0<pairNorm 1 r frameCap)).2
    nlinarith [radius_cos_reserves.2]
  dsimp [exteriorC]
  linarith [cap_reserves.2.2.2.2.1]

private def lowerProduct : ℝ := (19787/10000)*(478/625)
private def quartic (l : ℝ) : ℝ :=
  (lowerProduct*l)^2-((23/25)*l+6443/10000)^2*(1+l^2-2*(3221/5000)*l)

/-- A single positive-coefficient identity on the whole interval `.61≤l≤1`. -/
private theorem quartic_positive {l : ℝ} (hl : l∈Icc (61/100 : ℝ) 1) :
    0<quartic l := by
  let z : ℝ := (l-61/100)/(39/100)
  have hz : z∈Icc 0 1 := by dsimp [z]; constructor <;> linarith [hl.1,hl.2]
  have he : l=61/100+(39/100)*z := by dsimp [z]; ring
  let b0 : ℝ := 29287839019429/97656250000000000
  let b1 : ℝ := 243170797943379757/1562500000000000000
  let b2 : ℝ := 126344718400862311/390625000000000000
  let b3 : ℝ := 29481487353515773/62500000000000000
  let b4 : ℝ := 85749482285509/156250000000000
  have hid : quartic l=1/5000+
      (b0-1/5000)*(1-z)^4+4*(b1-1/5000)*z*(1-z)^3+
      6*(b2-1/5000)*z^2*(1-z)^2+4*(b3-1/5000)*z^3*(1-z)+
      (b4-1/5000)*z^4 := by
    rw [he]
    dsimp [quartic,lowerProduct,b0,b1,b2,b3,b4]
    ring
  have h0 : 0≤(b0-1/5000)*(1-z)^4 := mul_nonneg (by norm_num [b0]) (by positivity)
  have h1 : 0≤4*(b1-1/5000)*z*(1-z)^3 := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num [b1]) hz.1
    · exact pow_nonneg (by linarith [hz.2]) _
  have h2 : 0≤6*(b2-1/5000)*z^2*(1-z)^2 :=
    mul_nonneg (mul_nonneg (by norm_num [b2]) (sq_nonneg z)) (sq_nonneg (1-z))
  have h3 : 0≤4*(b3-1/5000)*z^3*(1-z) := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num [b3]) (pow_nonneg hz.1 _)
    · linarith [hz.2]
  have h4 : 0≤(b4-1/5000)*z^4 := mul_nonneg (by norm_num [b4]) (by positivity)
  linarith

theorem exteriorG_large {l : ℝ} (hl : l∈Icc (61/100 : ℝ) 1) :
    (23/25 : ℝ)<exteriorG l := by
  have hl0 : 0<l := by linarith [hl.1]
  have hh : |-frameCap|≤frameCap := r47_abs_neg_cap
  have hN := pairNorm_pos (show (0:ℝ)<1 by norm_num) hl0 hh
  have hN2 := pairNorm_sq (show (0:ℝ)<1 by norm_num) hl0 hh
  dsimp [pairEnergy,pairProduct] at hN2
  simp only [one_pow,one_mul,Real.sin_neg] at hN2
  have hslo := mul_lt_mul_of_pos_left cap_reserves.1 (show 0<2*l by positivity)
  have hNup : (pairNorm 1 l (-frameCap))^2≤1+l^2-2*(3221/5000)*l := by
    nlinarith
  have hw := mul_le_mul_of_nonneg_left hNup
    (sq_nonneg ((23/25)*l+6443/10000))
  have hpoly := quartic_positive hl
  have hprod : ((23/25)*l+6443/10000)*pairNorm 1 l (-frameCap)<lowerProduct*l := by
    have hright : 0<lowerProduct*l := by dsimp [lowerProduct]; positivity
    have hleft : 0≤((23/25)*l+6443/10000)*pairNorm 1 l (-frameCap) := by positivity
    dsimp [quartic] at hpoly
    nlinarith
  have hR := mul_lt_mul_of_pos_right radius_cos_reserves.1 hl0
  change lowerProduct*l<R*Real.cos frameCap*l at hR
  have hsin := mul_lt_mul_of_pos_right cap_reserves.2.1 hN
  have hactual : ((23/25)*l+Real.sin frameCap)*pairNorm 1 l (-frameCap)<
      R*Real.cos frameCap*l := by nlinarith
  have he : ((23/25)+Real.sin frameCap/l)*pairNorm 1 l (-frameCap)*l=
      ((23/25)*l+Real.sin frameCap)*pairNorm 1 l (-frameCap) := by
    field_simp [hl0.ne']
  have hdiv : (23/25)+Real.sin frameCap/l<
      R*Real.cos frameCap/pairNorm 1 l (-frameCap) := by
    apply (lt_div_iff₀ hN).2
    refine lt_of_mul_lt_mul_right ?_ hl0.le
    rw [he]
    exact hactual
  dsimp [exteriorG]
  linarith


theorem exteriorG_small : (9/10 : ℝ)<exteriorG (121/200) := by
  suffices h : ∀ l : ℝ, l=121/200 → (9/10 : ℝ)<exteriorG l from h _ rfl
  intro l hl
  have hl0 : 0<l := by rw [hl]; norm_num
  have hh : |-frameCap|≤frameCap := r47_abs_neg_cap
  have hN := pairNorm_pos (show (0:ℝ)<1 by norm_num) hl0 hh
  have hN2 := pairNorm_sq (show (0:ℝ)<1 by norm_num) hl0 hh
  dsimp [pairEnergy,pairProduct] at hN2
  simp only [one_pow,one_mul,Real.sin_neg] at hN2
  have hslo := mul_lt_mul_of_pos_left cap_reserves.1 (show 0<2*l by positivity)
  have hNup : (pairNorm 1 l (-frameCap))^2≤1+l^2-2*(3221/5000)*l := by nlinarith
  have hw := mul_le_mul_of_nonneg_left hNup (sq_nonneg ((9/10)*l+6443/10000))
  have hpoly : 0<(lowerProduct*l)^2-
      ((9/10)*l+6443/10000)^2*(1+l^2-2*(3221/5000)*l) := by
    rw [hl]; norm_num [lowerProduct]
  have hprod : ((9/10)*l+6443/10000)*pairNorm 1 l (-frameCap)<lowerProduct*l := by
    have hright : 0<lowerProduct*l := by dsimp [lowerProduct]; positivity
    have hleft : 0≤((9/10)*l+6443/10000)*pairNorm 1 l (-frameCap) := by positivity
    nlinarith
  have hR := mul_lt_mul_of_pos_right radius_cos_reserves.1 hl0
  change lowerProduct*l<R*Real.cos frameCap*l at hR
  have hsin := mul_lt_mul_of_pos_right cap_reserves.2.1 hN
  have hactual : ((9/10)*l+Real.sin frameCap)*pairNorm 1 l (-frameCap)<
      R*Real.cos frameCap*l := by nlinarith
  have he : ((9/10)+Real.sin frameCap/l)*pairNorm 1 l (-frameCap)*l=
      ((9/10)*l+Real.sin frameCap)*pairNorm 1 l (-frameCap) := by
    field_simp [hl0.ne']
  have hdiv : (9/10)+Real.sin frameCap/l<
      R*Real.cos frameCap/pairNorm 1 l (-frameCap) := by
    apply (lt_div_iff₀ hN).2
    refine lt_of_mul_lt_mul_right ?_ hl0.le
    rw [he]
    exact hactual
  dsimp [exteriorG]
  linarith


theorem lower_exterior_cap {l mu L : ℝ} (hw : Weights l mu L) :
    negativeSlope 1 l 1 frameCap+positiveSlope mu l l frameCap<0 := by
  obtain ⟨hL,hl,hlu,hmu1,hmu,hr,_⟩ := hw.bounds
  have hl0 : 0<l := by linarith
  have hmu0 : 0< mu := by linarith
  have hN := pairNorm_pos (show (0:ℝ)<1 by norm_num) (div_pos hl0 hmu0)
    r47_abs_cap
  have hNm := pairNorm_pos (show (0:ℝ)<1 by norm_num) hl0
    r47_abs_neg_cap
  have he : negativeSlope 1 l 1 frameCap+positiveSlope mu l l frameCap=
      l*(exteriorC (l/mu)-exteriorG l) := by
    dsimp [negativeSlope,positiveSlope,exteriorC,exteriorG,normD1,pairProduct]
    rw [pairNorm_normalize hmu0,Real.cos_neg]
    field_simp [hmu0.ne',hl0.ne',hN.ne',hNm.ne']
    ring
  have hCG : exteriorC (l/mu)<exteriorG l := by
    rcases hw with ⟨_,rfl,rfl⟩ | ⟨hL,rfl,rfl⟩
    · have hc := exteriorC_small (r := (121/200)/(47/50)) (by norm_num)
      linarith [exteriorG_small]
    · have hc := exteriorC_large (r := 59/100+L/2)
        (by linarith [hL.1])
      have hg := exteriorG_large (l := 59/100+L/2)
        ⟨by linarith [hL.1],by dsimp [frameCap] at hL; linarith [hL.2]⟩
      simp only [div_one]
      linarith
  rw [he]
  exact mul_neg_of_pos_of_neg hl0 (sub_neg.mpr hCG)


theorem upper_exterior_cap {l mu L : ℝ} (hw : Weights l mu L) :
    positiveSlope 1 l 1 frameCap+negativeSlope mu l l frameCap<0 := by
  obtain ⟨_,hl,hlu,hmu1,hmu,hr,_⟩ := hw.bounds
  have hl0 : 0<l := by linarith
  have hp := positive_one_cap hl0 (hlu.trans hmu1)
  have hn := negative_mu_cap (by linarith : 0< mu) hl0 hr
  linarith

end SquaresInCircles.Eight.OneNegativeAnchorConcentration
