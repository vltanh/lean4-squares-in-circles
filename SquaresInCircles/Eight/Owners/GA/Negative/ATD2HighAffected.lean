module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic
public import SquaresInCircles.Eight.Owners.GA.Negative.ELowAStress
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedPositive
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowNegativeComparison
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CurvatureConstants
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2SecantBounds
public import SquaresInCircles.Eight.Owners.SplitConcavityTools

/-!
# Eight squares: every high affected negative endpoint with its original secant pair

The GA curve is affine minus
its rotated norm. The AB curve retains its intrinsic coefficient switch
and downward derivative jump. Both reduce on the full algebraic
interval to the already certified zero and equal-angle scalar values.
-/

section
/-!
## The unaffected negative-angle curvature estimates

The ordinary signed tangents give a convex expression `bracket` in the remaining angle, and its
two endpoints are compared (`bracket_endpoint_upper`). The final AB combination uses the
degree-six polynomial `combination` on its whole interval (`combination_upper`), followed by the
separate late-ratio estimate (`AB_late_total_curvature`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.UnaffectedCurvature
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope PairNormCalculus OrdinaryCurvatureBounds
open SecantCoordinate SecantBounds

def bracket (C D E x θ : ℝ) : ℝ :=
  -Real.cos θ-2*x*Real.sin θ+C+2*D*x+(2*C*x-E)*θ
def bracketFirst (C E x θ : ℝ) : ℝ :=
  Real.sin θ-2*x*Real.cos θ+2*C*x-E

theorem bracket_hasDerivAt (C D E x θ : ℝ) :
    HasDerivAt (bracket C D E x) (bracketFirst C E x θ) θ := by
  have hd := (((((Real.hasDerivAt_cos θ).neg).sub
    ((Real.hasDerivAt_sin θ).const_mul (2*x))).add_const C).add_const (2*D*x)).add
    ((hasDerivAt_id θ).const_mul (2*C*x-E))
  convert hd using 1
  · rfl
  · dsimp [bracketFirst]
    ring

theorem bracketFirst_hasDerivAt (C E x θ : ℝ) :
    HasDerivAt (bracketFirst C E x) (Real.cos θ+2*x*Real.sin θ) θ := by
  have hd := (((Real.hasDerivAt_sin θ).sub
    ((Real.hasDerivAt_cos θ).const_mul (2*x))).add_const (2*C*x)).sub_const E
  convert hd using 1
  · rfl
  · ring

theorem bracket_neg_concave (C D E : ℝ) {x : ℝ} (hx : 0≤x) :
    ConcaveOn ℝ (Icc (0:ℝ) frameCap) (fun θ => -bracket C D E x θ) := by
  apply concave_of_deriv2 (fun θ _ => (bracket_hasDerivAt C D E x θ).neg)
    (fun θ _ => (bracketFirst_hasDerivAt C E x θ).neg)
  intro θ hθ
  have ht := transport_trig hθ
  have hp := mul_nonneg (show 0≤2*x by linarith) ht.2.2.1
  linarith [ht.1]

theorem bracket_endpoint_upper {C D E x θ b : ℝ} (hx : 0≤x)
    (hθ : θ∈Icc 0 frameCap)
    (h0 : bracket C D E x 0≤b) (hh : bracket C D E x frameCap≤b) :
    bracket C D E x θ≤b := by
  have hm := (bracket_neg_concave C D E hx).min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hθ
  have hl : -b≤ min (-bracket C D E x 0) (-bracket C D E x frameCap) :=
    le_min (by linarith) (by linarith)
  linarith

theorem bracket_difference (C D E x : ℝ) :
    bracket C D E x frameCap-bracket C D E x 0=
      1-Real.cos frameCap-E*frameCap+
        2*x*(C*frameCap-Real.sin frameCap) := by
  simp only [bracket,Real.sin_zero,Real.cos_zero,mul_zero,add_zero,sub_zero]
  ring

theorem cap_sine : (49/100:ℝ)<Real.sin frameCap := by
  have hh := sin_lower_seven (by norm_num [frameCap] : (0:ℝ)≤frameCap)
  norm_num [frameCap] at hh ⊢
  linarith

theorem GA_bracket_upper {x θ : ℝ} (hx : 0≤x) (hθ : θ∈Icc 0 frameCap) :
    bracket (7/10) (7/5) (1/3) x θ≤-(3/10:ℝ)+(14/5)*x+1867/1000000 := by
  have hc := (transport_trig
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1
  have hsmall : (7/10:ℝ)*frameCap-Real.sin frameCap<0 := by
    dsimp [frameCap]
    linarith [cap_sine]
  have hm := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*x by linarith) hsmall.le
  have hd := bracket_difference (7/10) (7/5) (1/3) x
  have h0 : bracket (7/10) (7/5) (1/3) x 0=-(3/10:ℝ)+(14/5)*x := by
    simp [bracket]
    ring
  apply bracket_endpoint_upper hx hθ
  · rw [h0]
    linarith
  · rw [h0] at hd
    dsimp [frameCap] at hd
    linarith

theorem AB_bracket_upper {x θ : ℝ} (hx : 0≤x) (hθ : θ∈Icc 0 frameCap) :
    bracket (627/1000) (1273/1000) (173/500) x θ≤-(373/1000:ℝ)+(1273/500)*x := by
  have hc := (transport_trig
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1
  have hsmall : (627/1000:ℝ)*frameCap-Real.sin frameCap<0 := by
    dsimp [frameCap]
    linarith [cap_sine]
  have hm := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*x by linarith) hsmall.le
  have hd := bracket_difference (627/1000) (1273/1000) (173/500) x
  have h0 : bracket (627/1000) (1273/1000) (173/500) x 0=
      -(373/1000:ℝ)+(1273/500)*x := by
    simp [bracket]
    ring
  apply bracket_endpoint_upper hx hθ
  · exact h0.le
  · rw [h0] at hd
    dsimp [frameCap] at hd
    linarith

theorem numerator_upper {p q x θ C D E : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hx : 0≤x) (hθ : θ∈Icc 0 frameCap)
    (hC : curvatureZero R p q≤C*q)
    (hD : Curvature.slopeZero p q≤D*q)
    (hE : E*q≤curvatureSlope R p q) :
    curvature R p q (-θ)-q*Real.cos θ+2*x*Vd R p q θ≤q*bracket C D E x θ := by
  have hq := hp.trans_le hpq
  have habs : |-θ|≤frameCap := by rw [abs_neg,abs_of_nonneg hθ.1]; exact hθ.2
  have hc := Curvature.curvature_signed_tangent hp hpq hqp habs
  have hd := Curvature.norm_slope_signed_tangent hp hq habs
  have hEθ := mul_le_mul_of_nonneg_right hE hθ.1
  have hCθ := mul_le_mul_of_nonneg_right hC hθ.1
  have hv : Vd R p q θ≤-q*Real.sin θ+D*q+C*q*θ := by
    dsimp [Vd,mixedNDerivative]
    simp only [zero_sub]
    nlinarith only [hd,hD,hCθ]
  have hscaled := mul_le_mul_of_nonneg_left hv (show 0≤2*x by linarith)
  dsimp [bracket]
  nlinarith only [hc,hC,hEθ,hscaled]

def rational (a b x : ℝ) : ℝ := (a+b*x)/(1+x^2)^2
def rationalFirst (a b x : ℝ) : ℝ := (b-4*a*x-3*b*x^2)/(1+x^2)^3

theorem rational_hasDerivAt (a b x : ℝ) :
    HasDerivAt (rational a b) (rationalFirst a b x) x := by
  have hn := ((hasDerivAt_id x).const_mul b).const_add a
  have hd := ((((hasDerivAt_id x).pow 2).const_add 1).pow 2)
  convert hn.div hd (by positivity : (1+x^2)^2≠0) using 1
  · rfl
  · dsimp [rationalFirst]
    field_simp [show 1+x^2≠0 by positivity]
    ring

theorem rational_monotone {a b : ℝ} (ha : a≤0) (hb : 0≤b) :
    MonotoneOn (rational a b) (Icc (0:ℝ) (2/5)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (rational_hasDerivAt a b x).continuousAt.continuousWithinAt)
    (fun x _ => rational_hasDerivAt a b x)
  intro x hx
  have hx2 := pow_le_pow_left₀ hx.1.le hx.2.le 2
  have hax := mul_nonpos_of_nonpos_of_nonneg ha hx.1.le
  have hbx := mul_nonneg hb (show 0≤1-3*x^2 by nlinarith)
  exact div_nonneg (by nlinarith only [hax,hbx]) (by positivity)

theorem GA_rational_upper {x : ℝ} (hx : x∈Icc 0 (32/125:ℝ)) :
    rational (-(3/10)+1867/1000000) (14/5) x<419/1000 := by
  have hm := rational_monotone
    (by norm_num : -(3/10:ℝ)+1867/1000000≤0) (by norm_num : (0:ℝ)≤14/5)
      ⟨hx.1,by linarith [hx.2]⟩ (show (32/125:ℝ)∈Icc 0 (2/5) by norm_num) hx.2
  have he : rational (-(3/10)+1867/1000000) (14/5) (32/125)<(419/1000:ℝ) := by
    norm_num [rational]
  exact hm.trans_lt he

theorem AB_rational_upper {x : ℝ} (hx : x∈Icc 0 (2/5:ℝ)) :
    rational (-(373/1000)) (1273/500) x<12/25 := by
  have hm := rational_monotone (by norm_num : -(373/1000:ℝ)≤0)
    (by norm_num : (0:ℝ)≤1273/500) hx
    (show (2/5:ℝ)∈Icc 0 (2/5) by norm_num) hx.2
  have he : rational (-(373/1000)) (1273/500) (2/5)<(12/25:ℝ) := by
    norm_num [rational]
  exact hm.trans_lt he

theorem GA_negative_curvature {p q z x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hx : x∈Icc 0 (32/125:ℝ)) (hθ : z-Real.arctan x∈Icc 0 frameCap) :
    negativeSecond p q z x<(419/1000)*q := by
  have hq := hp.trans_le hpq
  obtain ⟨hC,hE,hD⟩ := Curvature.universal_constants hp hpq hqp
  have hn := numerator_upper hp hpq hqp hx.1 hθ hC.le hD.le hE.le
  have hb := mul_le_mul_of_nonneg_left (GA_bracket_upper hx.1 hθ) hq.le
  have hnum := hn.trans hb
  have hd : 0<(1+x^2)^2 := by positivity
  have hdiv := div_le_div_of_nonneg_right hnum hd.le
  have hr := mul_lt_mul_of_pos_left (GA_rational_upper hx) hq
  dsimp [negativeSecond,rational] at ⊢ hr
  have e : q*(-(3/10)+14/5*x+1867/1000000)/(1+x^2)^2=
      q*((-(3/10)+1867/1000000+14/5*x)/(1+x^2)^2) := by ring
  rw [e] at hdiv
  linarith only [hdiv,hr]

theorem AB_negative_curvature {p q z x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hratio : p≤(21/25)*q)
    (hx : 0≤x) (hθ : z-Real.arctan x∈Icc 0 frameCap) :
    negativeSecond p q z x≤q*rational (-(373/1000)) (1273/500) x := by
  have hq := hp.trans_le hpq
  obtain ⟨hC,hD⟩ := Curvature.restricted_constants .wide hp hpq
    (show p≤(Curvature.ratioEnd .wide:ℝ)*q by
      rw [show ((Curvature.ratioEnd .wide:ℚ):ℝ)=21/25 by norm_num [Curvature.ratioEnd]]
      exact hratio)
  have hE := Curvature.restricted_C1 hp hpq hqp hratio
  rw [show ((Curvature.C0End .wide:ℚ):ℝ)=627/1000 by norm_num [Curvature.C0End]] at hC
  rw [show ((Curvature.D0End .wide:ℚ):ℝ)=1273/1000 by norm_num [Curvature.D0End]] at hD
  have hn := numerator_upper hp hpq hqp hx hθ hC.le hD.le hE.le
  have hb := mul_le_mul_of_nonneg_left (AB_bracket_upper hx hθ) hq.le
  have hdiv := div_le_div_of_nonneg_right (hn.trans hb)
    (show 0≤(1+x^2)^2 by positivity)
  simpa only [negativeSecond,rational,mul_div_assoc] using hdiv

def combination (x : ℝ) : ℝ :=
  -(749/1000)+(1273/500)*x-(551/500)*x^2-(269/250)*x^4-(7/20)*x^6
def combinationFirst (x : ℝ) : ℝ :=
  1273/500-(551/250)*x-(538/125)*x^3-(21/10)*x^5

theorem combination_hasDerivAt (x : ℝ) :
    HasDerivAt combination (combinationFirst x) x := by
  have h1 : HasDerivAt (fun x:ℝ => (1273/500)*x) (1273/500) x := by
    simpa using (hasDerivAt_id x).const_mul (1273/500:ℝ)
  have h2 : HasDerivAt (fun x:ℝ => (551/500)*x^2) ((551/500)*(2*x)) x := by
    simpa using ((hasDerivAt_id x).fun_pow 2).const_mul (551/500:ℝ)
  have h4 : HasDerivAt (fun x:ℝ => (269/250)*x^4) ((269/250)*(4*x^3)) x := by
    simpa using ((hasDerivAt_id x).fun_pow 4).const_mul (269/250:ℝ)
  have h6 : HasDerivAt (fun x:ℝ => (7/20)*x^6) ((7/20)*(6*x^5)) x := by
    simpa using ((hasDerivAt_id x).fun_pow 6).const_mul (7/20:ℝ)
  exact ((((h1.const_add (-(749/1000:ℝ))).fun_sub h2).fun_sub h4).fun_sub h6).congr_deriv
    (by simp only [combinationFirst]; ring)

theorem combination_upper {x : ℝ} (hx : x∈Icc 0 (7/20:ℝ)) :
    combination x< -(6/625:ℝ) := by
  have hm : MonotoneOn combination (Icc (0:ℝ) (7/20)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (combination_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => combination_hasDerivAt x)
    intro x hx
    have h3 := pow_le_pow_left₀ hx.1.le hx.2.le 3
    have h5 := pow_le_pow_left₀ hx.1.le hx.2.le 5
    dsimp [combinationFirst]
    nlinarith [hx.2]
  have hh := hm hx (show (7/20:ℝ)∈Icc 0 (7/20) by norm_num) hx.2
  have he : combination (7/20:ℝ)< -(6/625:ℝ) := by norm_num [combination]
  exact hh.trans_lt he

theorem combination_identity (x : ℝ) :
    -(47/125)-(7/20)*x^2+rational (-(373/1000)) (1273/500) x=
      combination x/(1+x^2)^2 := by
  dsimp [rational,combination]
  field_simp [show 1+x^2≠0 by positivity]
  ring

theorem GA_total_curvature {l r p q z x : ℝ}
    (hl : 0<l) (hr : r∈Icc 0 (17/20:ℝ))
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hql : q≤(11/10)*l)
    (hx : x∈Icc 0 (32/125:ℝ)) (hθ : z-Real.arctan x∈Icc 0 frameCap) :
    pureSecond l r p q z x< -(461/10000)*l := by
  have hb := mul_lt_mul_of_pos_left (GA_base_curvature hr hx) hl
  have hv := GA_negative_curvature hp hpq hqp hx hθ
  dsimp [pureSecond]
  nlinarith

theorem AB_early_total_curvature {l r p q z x : ℝ}
    (hl : 0<l) (hr : r∈Icc 0 (129/125:ℝ))
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hratio : p≤(21/25)*q) (hql : q≤l)
    (hx : x∈Icc 0 (7/20:ℝ)) (hθ : z-Real.arctan x∈Icc 0 frameCap) :
    pureSecond l r p q z x<0 := by
  have hq := hp.trans_le hpq
  have hb := mul_lt_mul_of_pos_left (AB_early_base_curvature hr hx) hl
  have hv := AB_negative_curvature hp hpq hqp hratio hx.1 hθ
  by_cases hn : -(373/1000:ℝ)+(1273/500)*x≤0
  · have hr0 : rational (-(373/1000)) (1273/500) x≤0 :=
      div_nonpos_of_nonpos_of_nonneg hn (by positivity)
    have hp0 := mul_nonpos_of_nonneg_of_nonpos hq.le hr0
    have hsq := mul_nonneg hl.le (sq_nonneg x)
    dsimp [pureSecond]
    nlinarith
  · have hr0 : 0≤rational (-(373/1000)) (1273/500) x :=
      div_nonneg (by linarith) (by positivity)
    have hmul := mul_le_mul_of_nonneg_right hql hr0
    have hsum : -(47/125)-(7/20)*x^2+
        rational (-(373/1000)) (1273/500) x<0 := by
      rw [combination_identity]
      exact div_neg_of_neg_of_pos (by linarith [combination_upper hx]) (by positivity)
    have hscaled := mul_neg_of_pos_of_neg hl hsum
    dsimp [pureSecond]
    nlinarith

theorem AB_late_total_curvature {l r p q z x : ℝ}
    (hl : 0<l) (hr : r∈Icc 0 (23/25:ℝ))
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hratio : p≤(21/25)*q) (hql : q≤l)
    (hx : x∈Icc (7/20:ℝ) (2/5:ℝ)) (hθ : z-Real.arctan x∈Icc 0 frameCap) :
    pureSecond l r p q z x< -(1/1000)*l := by
  have hq := hp.trans_le hpq
  have hx0 : 0≤x := by linarith [hx.1]
  have hb := mul_lt_mul_of_pos_left (AB_late_base_curvature hr hx) hl
  have hv := AB_negative_curvature hp hpq hqp hratio hx0 hθ
  have hrb := mul_lt_mul_of_pos_left (AB_rational_upper ⟨hx0,hx.2⟩) hq
  dsimp [pureSecond]
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.UnaffectedCurvature
end
end
end

section
/-!
## The widened quarter-angle negative comparison and curvature

The larger-coefficient comparison (`larger_coefficient`) uses `q/k ≤ 5/3` and `t ≤ 1/4`. The
denominator `√34` is weakened to `6`, which leaves a rational reserve `.0255`. The resulting H
comparison has curvature below `-.037` in the secant coordinate (`H_curvature`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowNegative
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope OrdinaryNegativeEnvelope PairNormCalculus OrdinaryCurvatureBounds
open VaryingBFunctions
open NegativeAPositiveTD.SecantCoordinate NegativeAPositiveTD.SecantBounds

theorem integrand_lower {r u : ℝ} (hr : r∈Icc (3/5:ℝ) 1)
    (hu : u∈Icc 0 (1/4:ℝ)) : (21/272:ℝ)≤ integrand r u := by
  have hr0 : 0<r := by linarith [hr.1]
  have huf : u∈Icc 0 frameCap := ⟨hu.1,by dsimp [frameCap]; linarith [hu.2]⟩
  have hn := root_pos r huf
  have hn2 := root_sq r huf
  have hr2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/5) hr.1 2
  have hsq : (root r u)^2≤(34/9)*r^2 := by nlinarith [mul_nonneg hr0.le hu.1]
  have hnU : root r u≤2*r := by nlinarith
  have hn3 : (root r u)^3≤(68/9)*r^3 := by
    have hh := mul_le_mul hsq hnU hn.le (show 0≤(34/9)*r^2 by positivity)
    nlinarith only [hh]
  have hnum : (7/12)*r^3≤r^2*(r-u) := by
    have hh : u≤(5/12)*r := by linarith [hu.2,hr.1]
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hh)]
  exact (le_div_iff₀ (pow_pos hn 3)).2 (by nlinarith only [hn3,hnum])

theorem gain_lower {r u : ℝ} (hr : r∈Icc (3/5:ℝ) 1)
    (hu : u∈Icc 0 (1/4:ℝ)) : (21/272)*u≤gain r u := by
  have hdom {x : ℝ} (hx : x∈Icc 0 (1/4:ℝ)) : x∈Icc 0 frameCap :=
    ⟨hx.1,by dsimp [frameCap]; linarith [hx.2]⟩
  have hh := derivative_reserve (f:=gain r) (df:=integrand r) (k:=(21/272:ℝ))
    (fun x hx => (gain_hasDerivAt_u r (hdom hx)).continuousAt.continuousWithinAt)
    (fun x hx => gain_hasDerivAt_u r (hdom (Ioo_subset_Icc_self hx)))
    (fun x hx => integrand_lower hr (Ioo_subset_Icc_self hx))
    (show (0:ℝ)∈Icc 0 (1/4:ℝ) by norm_num) hu hu.1
  simpa only [gain_zero,sub_zero] using hh

theorem small_trig {t : ℝ} (ht : t∈Icc 0 (1/4:ℝ)) :
    (95/96)*t≤Real.sin t ∧ 1-t^2/2≤Real.cos t ∧ Real.sin t∈Icc 0 (1/4:ℝ) := by
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  have hs := Real.sin_ge_sub_cube ht.1
  have hc := cos_lower_six ht.1
  have htail : 0≤t^4/24-t^6/720 := by
    have hh := mul_nonneg (pow_nonneg ht.1 4) (show 0≤30-t^2 by nlinarith)
    nlinarith only [hh]
  have hcube := mul_le_mul_of_nonneg_right ht2 ht.1
  have htf : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  exact ⟨by nlinarith,by linarith,
    ⟨(transport_trig htf).2.2.1,(Real.sin_le ht.1).trans ht.2⟩⟩

theorem D_lower {r t : ℝ} (hr : r∈Icc (3/5:ℝ) 1) (ht : t∈Icc 0 (1/4:ℝ)) :
    (51/2000)*t≤VaryingBFunctions.D R r t := by
  obtain ⟨hs,hc,hsdom⟩ := small_trig ht
  have hg := gain_lower hr hsdom
  have hgs := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤21/272)
  have hR := NegativeAPositiveTD.Curvature.radius_bounds.1
  have hp := mul_le_mul_of_nonneg_left hg (show 0≤R by linarith)
  have hRp := mul_le_mul_of_nonneg_right hR.le (mul_nonneg (by norm_num : (0:ℝ)≤21/272) hsdom.1)
  have ht2 : t^2/2≤t/8 := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  dsimp [VaryingBFunctions.D]
  nlinarith only [hp,hRp,hgs,hc,ht2,ht.1]

theorem larger_coefficient {p a b t : ℝ}
    (hp : 0<p) (hpa : p≤a) (hab : a≤b) (hbp : b≤(5/3)*p) (ht : t∈Icc 0 (1/4:ℝ)) :
    V R p a t≤V R p b t := by
  have htf : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  have hc {q : ℝ} (hq : q∈Icc a b) : 0<q ∧ p/q∈Icc (3/5:ℝ) 1 := by
    have hq0 := hp.trans_le (hpa.trans hq.1)
    exact ⟨hq0,⟨(le_div_iff₀ hq0).2 (by linarith [hq.2]),(div_le_one hq0).2 (hpa.trans hq.1)⟩⟩
  have hm : MonotoneOn (fun q => V R p q t) (Icc a b) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun q hq => (VaryingBComparison.V_hasDerivAt_q hp (hc hq).1 htf).continuousAt.continuousWithinAt)
      (fun q hq => VaryingBComparison.V_hasDerivAt_q hp (hc (Ioo_subset_Icc_self hq)).1 htf)
    intro q hq
    exact (mul_nonneg (by norm_num) ht.1).trans (D_lower (hc (Ioo_subset_Icc_self hq)).2 ht)
  exact hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab

theorem B_dominates_H (atG : Bool) {s z t : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ht : t∈Icc 0 frameCap) :
    V R (Explicit.k .low z) 1 t≤V R (Explicit.p .low atG z s 2) (Explicit.q .low atG z s 2) t := by
  have hb := Explicit.low_ranges hz
  have hz' : z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
    norm_num [Certificate.left,Certificate.right,Certificate.split]; exact hz
  have hw := (Explicit.secant_bounds .low atG hz' hs).1
  have hpmin : (241/250:ℝ)≤Explicit.p .low atG z s 2 := by
    cases atG <;> simp only [Explicit.p,pWeights,lambdaB,NegativeAPositiveTD.lambdaB,
      Bool.false_eq_true,↓reduceIte] at hw ⊢
    all_goals apply le_min <;> linarith [hb.2.1.1,hb.2.2.1]
  have hp := Explicit.ordered_pair_domain .low atG hz' hs 2
  have hh := NegativeAPositiveTD.LowNegativeComparison.H_tangent
    ⟨hb.1.1,by linarith [hb.1.2]⟩ ht
  have hv := V_chord_lower hp.1 hp.2.1 hp.2.2 ht
  have hscale := mul_le_mul_of_nonneg_right hpmin ht.1
  nlinarith only [hh,hv,hscale,ht.1]

theorem comparison (atG : Bool) {s z t : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ht : t∈Icc 0 (1/4:ℝ)) (i : Fin 4) :
    V R (Explicit.k .low z) 1 t≤V R (Explicit.p .low atG z s i) (Explicit.q .low atG z s i) t := by
  have hb := Explicit.low_ranges hz
  have hw := (Explicit.secant_bounds .low atG (by
    norm_num [Certificate.left,Certificate.right,Certificate.split]; exact hz) hs).1
  have hq : 1≤lambdaG atG (Explicit.l .low z) s := by
    cases atG <;> simp only [lambdaG,NegativeAPositiveTD.lambdaG,Bool.false_eq_true,
      ↓reduceIte] <;> linarith [hb.2.1.1,hw]
  fin_cases i
  · simp [Explicit.p,Explicit.q,pWeights,qWeights]
  · simpa [Explicit.p,Explicit.q,pWeights,qWeights] using larger_coefficient
      (by linarith [hb.1.1] : 0<Explicit.k .low z) (by linarith [hb.1.2]) hq
      (Explicit.low_G_ratio atG hz hs).le ht
  · exact B_dominates_H atG hz hs ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  · simp [Explicit.p,Explicit.q,pWeights,qWeights]

theorem base_at_zero : baseSecond (113/100) 0< -(31/100:ℝ) := by
  have hh := normalized_radius_bounds (A:=1+(113/100:ℝ)^2) (L:=131/100) (U:=164/125)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [qCap]) (by norm_num [qCap])
  have hS := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<1+(113/100:ℝ)^2)
  have hS2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤1+(113/100:ℝ)^2)
  have he : baseSecond (113/100) 0=1-R/Real.sqrt (1+(113/100:ℝ)^2) := by
    have h0 : (1:ℝ)+(113/100)^2+0^2=1+(113/100)^2 := by norm_num
    have h1 : Real.sqrt (1+(0:ℝ)^2)=1 := by norm_num
    simp only [baseSecond,radical,h0,h1]
    generalize Real.sqrt (1+(113/100:ℝ)^2)=S at hS hS2 ⊢
    rw [← hS2]
    field_simp
  rw [he]
  linarith [hh.1]
theorem base_antitone : AntitoneOn (baseSecond (113/100)) (Icc (0:ℝ) (32/125)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (baseSecond_hasDerivAt (113/100) x).continuousAt.continuousWithinAt)
    (fun x _ => baseSecond_hasDerivAt (113/100) x)
  intro x hx
  apply baseThird_nonpos_of_endpoint (u:=(32/125:ℝ)) (by norm_num) (Ioo_subset_Icc_self hx)
  norm_num [qCap]
theorem base_curvature {r x : ℝ} (hr : r∈Icc 0 (113/100:ℝ)) (hx : x∈Icc 0 (32/125:ℝ)) :
    baseSecond r x< -(31/100:ℝ) := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  exact (baseSecond_ratio_mono hr.1 hr.2 (by nlinarith)).trans_lt
    ((base_antitone (show (0:ℝ)∈Icc 0 (32/125:ℝ) by norm_num) hx hx.1).trans_lt base_at_zero)

theorem H_curvature {k z x : ℝ} (hk : k∈Icc (2/3:ℝ) (187/250:ℝ))
    (hx : x∈Icc 0 (32/125:ℝ)) (hθ : z-Real.arctan x∈Icc 0 (1/4:ℝ)) :
    negativeSecond k 1 z x<(281/1000:ℝ) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hk1 : k≤1 := by linarith [hk.2]
  obtain ⟨hC,hD⟩ := NegativeAPositiveTD.Curvature.restricted_constants .middle hk0 hk1
    (show k≤(NegativeAPositiveTD.Curvature.ratioEnd .middle:ℝ)*1 by simpa [NegativeAPositiveTD.Curvature.ratioEnd] using hk.2)
  norm_num only [NegativeAPositiveTD.Curvature.C0End,NegativeAPositiveTD.Curvature.D0End] at hC hD
  have hE := curvatureSlope_nonneg (Real.sqrt_nonneg qCap) hk0 (by norm_num : (0:ℝ)<1)
  have hθf : z-Real.arctan x∈Icc 0 frameCap := ⟨hθ.1,by dsimp [frameCap]; linarith [hθ.2]⟩
  have hn := NegativeAPositiveTD.UnaffectedCurvature.numerator_upper hk0 hk1 (show (1:ℝ)≤2*k by linarith [hk.1]) hx.1 hθf
    (show curvatureZero R k 1≤(569/1000)*1 by linarith)
    (show NegativeAPositiveTD.Curvature.slopeZero k 1≤(593/500)*1 by linarith)
    (show (0:ℝ)*1≤curvatureSlope R k 1 by simpa using hE)
  have htr := small_trig hθ
  have hθ2 := pow_le_pow_left₀ hθ.1 hθ.2 2
  have hc : (31/32:ℝ)≤Real.cos (z-Real.arctan x) := by linarith [htr.2.1]
  have hsin := mul_nonneg (show 0≤2*x by linarith [hx.1]) htr.2.2.1
  have hxt := mul_le_mul hx.2 hθ.2 hθ.1 (by norm_num : (0:ℝ)≤32/125)
  have hb : NegativeAPositiveTD.UnaffectedCurvature.bracket (569/1000) (593/500) 0 x (z-Real.arctan x)<281/1000 := by
    dsimp [NegativeAPositiveTD.UnaffectedCurvature.bracket]
    nlinarith only [hc,hsin,hxt,hx.2]
  have hnum : curvature R k 1 (-(z-Real.arctan x))-1*Real.cos (z-Real.arctan x)+
      2*x*Vd R k 1 (z-Real.arctan x)<281/1000 := by linarith only [hn,hb]
  have hden : 1≤(1+x^2)^2 := by nlinarith [sq_nonneg x,sq_nonneg (x^2)]
  unfold negativeSecond
  exact (div_lt_iff₀ (by positivity : 0<(1+x^2)^2)).2 (by nlinarith only [hnum,hden])

theorem pure_curvature {l r k z x : ℝ} (hl : (513/500:ℝ)≤l)
    (hr : r∈Icc 0 (113/100:ℝ)) (hk : k∈Icc (2/3:ℝ) (187/250:ℝ))
    (hx : x∈Icc 0 (32/125:ℝ)) (hθ : z-Real.arctan x∈Icc 0 (1/4:ℝ)) :
    pureSecond l r k 1 z x< -(37/1000:ℝ) := by
  have hb := mul_lt_mul_of_pos_left (base_curvature hr hx) (show 0<l by linarith)
  have hh := H_curvature hk hx hθ
  dsimp [pureSecond]
  nlinarith only [hb,hh,hl]

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LowNegative
end
end
end

section
/-!
## Joining the affected AB curve at its intrinsic coefficient equality

The
two tangent estimates join at the common value; the right derivative
may be smaller than the left derivative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedJoin
open SplitConcavityTools

theorem downward {f g : ℝ→ℝ} {l c u dL dR : ℝ}
    (hc : c∈Icc l u) (hf : ConcaveOn ℝ (Icc l c) f)
    (hg : ConcaveOn ℝ (Icc c u) g) (he : f c=g c)
    (hdf : HasDerivAt f dL c) (hdg : HasDerivAt g dR c) (hdown : dR≤dL) :
    ConcaveOn ℝ (Icc l u) (fun x => if x≤c then f x else g x) := by
  let F : ℝ→ℝ := fun x => if x≤c then f x else g x
  have hFleft {x : ℝ} (hx : x≤c) : F x=f x := ite_eq_left hx
  have hFright {x : ℝ} (hx : c≤x) : F x=g x := by
    by_cases hxc : x≤c
    · have heq : x=c := le_antisymm hxc hx
      subst x
      simpa [F] using he
    · exact ite_eq_right hxc
  apply concave_of_chords
  intro x hx y hy hxy z hz
  change (y-z)*F x+(z-x)*F y≤(y-x)*F z
  by_cases hyc : y≤c
  · rw [hFleft (hxy.le.trans hyc),hFleft hyc,hFleft (hz.2.trans hyc)]
    exact chord hf ⟨hx.1,hxy.le.trans hyc⟩ ⟨hy.1,hyc⟩ hxy hz
  by_cases hcx : c≤x
  · rw [hFright hcx,hFright (hcx.trans hxy.le),hFright (hcx.trans hz.1)]
    exact chord hg ⟨hcx,hx.2⟩ ⟨hcx.trans hxy.le,hy.2⟩ hxy hz
  have hxc : x<c := lt_of_not_ge hcx
  have hcy : c<y := lt_of_not_ge hyc
  have hfx := tangent_upper hf (show c∈Icc l c from ⟨hc.1,le_rfl⟩) ⟨hx.1,hxc.le⟩ hdf
  have hgy := tangent_upper hg (show c∈Icc c u from ⟨le_rfl,hc.2⟩) ⟨hcy.le,hy.2⟩ hdg
  rw [← he] at hgy
  have hfx' := mul_le_mul_of_nonneg_left hfx (sub_nonneg.mpr hcy.le)
  have hgy' := mul_le_mul_of_nonneg_left hgy (sub_nonneg.mpr hxc.le)
  have hjump := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdown)
    (mul_nonneg (sub_nonneg.mpr hxc.le) (sub_nonneg.mpr hcy.le))
  have hbridge : (y-c)*f x+(c-x)*g y≤(y-x)*f c := by
    nlinarith only [hfx',hgy',hjump]
  rw [hFleft hxc.le,hFright hcy.le]
  by_cases hzc : z≤c
  · rw [hFleft hzc]
    have hlocal := chord hf ⟨hx.1,hxc.le⟩ ⟨hc.1,le_rfl⟩ hxc ⟨hz.1,hzc⟩
    have hp := mul_le_mul_of_nonneg_left hlocal (sub_nonneg.mpr hxy.le)
    have hq := mul_le_mul_of_nonneg_left hbridge (sub_nonneg.mpr hz.1)
    have hh : (c-x)*((y-z)*f x+(z-x)*g y)≤(c-x)*((y-x)*f z) := by
      nlinarith only [hp,hq]
    exact le_of_mul_le_mul_left hh (sub_pos.mpr hxc)
  · rw [hFright (lt_of_not_ge hzc).le]
    have hlocal := chord hg ⟨le_rfl,hc.2⟩ ⟨hcy.le,hy.2⟩ hcy ⟨(lt_of_not_ge hzc).le,hz.2⟩
    rw [← he] at hlocal
    have hp := mul_le_mul_of_nonneg_left hlocal (sub_nonneg.mpr hxy.le)
    have hq := mul_le_mul_of_nonneg_left hbridge (sub_nonneg.mpr hz.2)
    have hh : (y-c)*((y-z)*f x+(z-x)*g y)≤(y-c)*((y-x)*g z) := by
      nlinarith only [hp,hq]
    exact le_of_mul_le_mul_left hh (sub_pos.mpr hcy)

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedJoin
end
end
end

section
/-!
## Curvature through the affected AB coefficient transition

On the lower-secant branch the non-norm curvature is below `.225` and the norm curvature exceeds
`.348` (`nonnorm_upper`, `norm_lower`). The equality of the coefficients at `switch r` is the only
split, and the jump of the derivative there keeps the minimum concave (`minimum_concave`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedNegativeCurvature
open Candidate Secondary SecantCoordinate SecantBounds AffectedNegativeCurves

theorem small_z_trig {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    (31/32:ℝ)≤Real.cos z ∧ Real.sin z∈Icc 0 (1/4:ℝ) := by
  have hz2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hc := cos_lower_six hz.1
  have ht : 0≤z^4/24-z^6/720 := by
    have hh := mul_nonneg (pow_nonneg hz.1 4) (show 0≤30-z^2 by nlinarith)
    nlinarith only [hh]
  have hframe : z∈Icc 0 frameCap := ⟨hz.1,by simp only [frameCap]; linarith [hz.2]⟩
  exact ⟨by linarith,⟨(transport_trig hframe).2.2.1,(Real.sin_le hz.1).trans hz.2⟩⟩

theorem nonnorm_upper {r z x : ℝ} (hr : 1≤r)
    (hz : z∈Icc 0 (1/4:ℝ)) (hx : x∈Icc 0 (32/125:ℝ)) :
    1/(radical 1 x)^3+
      r*(-Real.cos z*(1-2*x^2)-3*x*Real.sin z)/(radical 1 x)^5<(9/40:ℝ) := by
  have ht := small_z_trig hz
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hW1 : 1≤radical 1 x := by nlinarith [sq_nonneg x]
  have hW5 : 1≤(radical 1 x)^5 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hW1 5
  have hfactor : 0≤1-2*x^2 := by nlinarith
  have hcos := mul_le_mul_of_nonneg_right ht.1 hfactor
  have hsin := mul_nonneg (show 0≤3*x by linarith [hx.1]) ht.2.1
  have hbr : -Real.cos z*(1-2*x^2)-3*x*Real.sin z≤-(31/32)*(1-2*x^2) := by
    linarith
  have hbr0 : -Real.cos z*(1-2*x^2)-3*x*Real.sin z≤0 := by
    nlinarith only [hbr,hfactor]
  have hscale := mul_le_mul_of_nonpos_right hr hbr0
  have hn : (radical 1 x)^2+
      r*(-Real.cos z*(1-2*x^2)-3*x*Real.sin z)<(9/40)*(radical 1 x)^5 := by
    nlinarith only [hW2,hx2,hbr,hscale,hW5]
  have he : 1/(radical 1 x)^3+
      r*(-Real.cos z*(1-2*x^2)-3*x*Real.sin z)/(radical 1 x)^5=
      ((radical 1 x)^2+r*(-Real.cos z*(1-2*x^2)-3*x*Real.sin z))/(radical 1 x)^5 := by
    field_simp [hW.ne']
  rw [he]
  exact (div_lt_iff₀ (pow_pos hW 5)).2 hn

theorem norm_lower {r z x : ℝ} (hr : r∈Icc 1 (129/125:ℝ))
    (hz : z∈Icc 0 (1/4:ℝ)) (hx : x∈Icc 0 (Real.tan z))
    (hw : radical 1 x≤r) : (87/250:ℝ)<R*AffectedNorm.second r z x := by
  have ht := small_z_trig hz
  have hc : 0<Real.cos z := by linarith [ht.1]
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  have hv : (371/500:ℝ)≤1-r*Real.sin z := by
    have hp := mul_le_mul hr.2 ht.2.2 ht.2.1 (by norm_num : (0:ℝ)≤129/125)
    linarith
  have hn := AffectedNorm.norm_pos (x:=x) (show 0<1-r*Real.sin z by linarith)
  have hnx := AffectedNorm.norm_sq_expanded r z x
  have hxc : x*Real.cos z≤Real.sin z := by
    have hh := mul_le_mul_of_nonneg_right hx.2 hc.le
    have he := (AffectedNorm.tan_identity hc).1
    linarith
  have hterm := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤2*r by linarith [hr.1]) (sub_nonpos.mpr hxc)
  have hw2 := pow_le_pow_left₀ hW.le hw 2
  have hr2 := pow_le_pow_left₀ (by linarith [hr.1] : 0≤r) hr.2 2
  have hn2 : (AffectedNorm.norm r z x)^2≤2*(129/125:ℝ)^2 := by
    nlinarith only [hnx,hterm,hw2,hW2,hr2]
  have hn6 := pow_le_pow_left₀ (sq_nonneg (AffectedNorm.norm r z x)) hn2 3
  have hn3 : (AffectedNorm.norm r z x)^3<(311/100:ℝ) := by
    have he : ((AffectedNorm.norm r z x)^2)^3=((AffectedNorm.norm r z x)^3)^2 := by ring
    rw [he] at hn6
    norm_num at hn6
    nlinarith [pow_nonneg hn.le 3]
  have hv2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤371/500) hv 2
  have hR := Curvature.radius_bounds.1
  have hprod := mul_lt_mul_of_pos_right hR (sq_pos_of_pos (show 0<1-r*Real.sin z by linarith))
  have hscale := mul_le_mul_of_nonneg_left hv2 (by norm_num : (0:ℝ)≤197/100)
  dsimp [AffectedNorm.second]
  rw [←mul_div_assoc]
  apply (lt_div_iff₀ (pow_pos hn 3)).2
  nlinarith only [hn3,hprod,hscale]

theorem lower_curvature {r z x : ℝ} (hr : r∈Icc 1 (129/125:ℝ))
    (hz : z∈Icc 0 (1/4:ℝ)) (hx : x∈Icc 0 (Real.tan z))
    (hw : radical 1 x≤r) : lowerSecond r z x< -(123/1000:ℝ) := by
  have ht := tan_monotone
    (show z∈Icc 0 frameCap from ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩)
    (show (1/4:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.2
  have hx' : x∈Icc 0 (32/125:ℝ) := ⟨hx.1,by linarith [hx.2,tan_GA_cut]⟩
  have hnon := nonnorm_upper hr.1 hz hx'
  have hnorm := norm_lower hr hz hx hw
  dsimp [lowerSecond]
  linarith

def switch (r : ℝ) : ℝ := Real.sqrt (r^2-1)

theorem switch_data {r : ℝ} (hr : 1≤r) :
    0≤ switch r ∧ (switch r)^2=r^2-1 ∧ radical 1 (switch r)=r := by
  have hr0 : 0≤r := by linarith
  have hh : 0≤r^2-1 := by nlinarith
  have hs : (switch r)^2=r^2-1 := Real.sq_sqrt hh
  have hW := radical_positive (A:=1) (x:=switch r) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=switch r) (by norm_num)
  have hsq : (radical 1 (switch r))^2=r^2 := by rw [hW2,hs]; ring
  exact ⟨Real.sqrt_nonneg _,hs,(pow_left_inj₀ hW.le hr0 two_ne_zero).mp hsq⟩

theorem switch_order {r x : ℝ} (hr : 1≤r) (hx : 0≤x) :
    x≤ switch r ↔ radical 1 x≤r := by
  obtain ⟨hs,hs2,he⟩ := switch_data hr
  have hW := radical_positive (A:=1) (x:=x) (by norm_num)
  have hW2 := radical_square (A:=1) (x:=x) (by norm_num)
  constructor <;> intro hh <;> nlinarith

theorem lower_concave {r z a : ℝ} (hr : r∈Icc 1 (129/125:ℝ))
    (hz : z∈Icc 0 (1/4:ℝ)) (ha : a∈Icc 0 (Real.tan z)) (has : a≤ switch r) :
    ConcaveOn ℝ (Icc 0 a) (lower r z) := by
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hv := AffectedNorm.second_coordinate_pos
    (show r∈Icc (0:ℝ) (71/50:ℝ) from ⟨by linarith [hr.1],by linarith [hr.2]⟩) hzframe
  apply concave_of_deriv2 (fun x _ => lower_hasDerivAt hv)
    (fun x _ => lowerFirst_hasDerivAt hv)
  intro x hx
  have hx' : x∈Icc 0 (Real.tan z) := ⟨hx.1,hx.2.trans ha.2⟩
  exact (lower_curvature hr hz hx' ((switch_order hr.1 hx.1).1 (hx.2.trans has))).le.trans
    (by norm_num)

theorem minimum_concave {r z : ℝ} (hr : r∈Icc 0 (129/125:ℝ))
    (hz : z∈Icc 0 frameCap) (hlarge : 1<r→z≤1/4) :
    ConcaveOn ℝ (Icc 0 (Real.tan z))
      (fun x => min (upper r z x) (lower r z x)) := by
  have hv := AffectedNorm.second_coordinate_pos
    (show r∈Icc (0:ℝ) (71/50:ℝ) from ⟨hr.1,by linarith [hr.2]⟩) hz
  have hu := upper_concave (a:=0) (b:=Real.tan z) hv
  have htan := tan_nonnegative hz
  by_cases hr1 : r≤1
  · have he (x : ℝ) (hx : x∈Icc 0 (Real.tan z)) :
        min (upper r z x) (lower r z x)=upper r z x := by
      have hw := radical_positive (A:=1) (x:=x) (by norm_num)
      have hw2 := radical_square (A:=1) (x:=x) (by norm_num)
      have hwr : r≤radical 1 x := by nlinarith [sq_nonneg x]
      have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hwr)
        (sub_nonpos.mpr (cosine_le_one z x))
      rw [←branch_difference] at hh
      exact min_eq_left (by linarith)
    refine ⟨convex_Icc _ _,?_⟩
    intro x hx y hy a b ha hb hab
    dsimp only
    rw [he x hx,he y hy,he _ (hu.1 hx hy ha hb hab)]
    exact hu.2 hx hy ha hb hab
  have hr' : r∈Icc 1 (129/125:ℝ) := ⟨(lt_of_not_ge hr1).le,hr.2⟩
  have hz' : z∈Icc 0 (1/4:ℝ) := ⟨hz.1,hlarge (lt_of_not_ge hr1)⟩
  have hc := switch_data hr'.1
  have he (x : ℝ) (hx : x∈Icc 0 (Real.tan z)) :
      min (upper r z x) (lower r z x)=
        if x≤ switch r then lower r z x else upper r z x := by
    by_cases hxc : x≤ switch r
    · rw [ite_eq_left hxc]
      have hw := (switch_order hr'.1 hx.1).1 hxc
      have hh := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hw)
        (sub_nonpos.mpr (cosine_le_one z x))
      rw [←branch_difference] at hh
      exact min_eq_right (by linarith)
    · rw [ite_eq_right hxc]
      have hw : r≤radical 1 x := by
        have hn : ¬radical 1 x≤r := by
          intro hh
          exact hxc ((switch_order hr'.1 hx.1).2 hh)
        exact (lt_of_not_ge hn).le
      have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hw)
        (sub_nonpos.mpr (cosine_le_one z x))
      rw [←branch_difference] at hh
      exact min_eq_left (by linarith)
  have hconc : ConcaveOn ℝ (Icc 0 (Real.tan z))
      (fun x => if x≤ switch r then lower r z x else upper r z x) := by
    by_cases hcut : switch r≤Real.tan z
    · apply AffectedJoin.downward ⟨hc.1,hcut⟩
        (lower_concave hr' hz' ⟨hc.1,hcut⟩ le_rfl)
        (upper_concave hv)
      · have hd := branch_difference r z (switch r)
        rw [hc.2.2,sub_self,zero_mul] at hd
        linarith
      · exact lower_hasDerivAt hv
      · exact upper_hasDerivAt hv
      · exact downward_derivative hc.1 hc.2.2
    · have hl := lower_concave hr' hz' ⟨htan,le_rfl⟩ (le_of_not_ge hcut)
      refine ⟨convex_Icc _ _,?_⟩
      intro x hx y hy a b ha hb hab
      have hxy := hl.1 hx hy ha hb hab
      simp only [ite_eq_left (hx.2.trans (le_of_not_ge hcut)),
        ite_eq_left (hy.2.trans (le_of_not_ge hcut)),
        ite_eq_left (hxy.2.trans (le_of_not_ge hcut))]
      exact hl.2 hx hy ha hb hab
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  dsimp only
  rw [he x hx,he y hy,he _ (hconc.1 hx hy ha hb hab)]
  exact hconc.2 hx hy ha hb hab

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedNegativeCurvature
end
end
end

section
/-!
## The high unaffected negative curves, with their original coefficients

The GA H/B and AB H/G curves are concave on their actual cuts. Their
two endpoints are discharged by the scalar companion, including the
equal-angle alternative and every actual-cut function. D uses the
identical H negative charge. No endpoint positivity is an input.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.HighUnaffected
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SecantCoordinate SecantBounds UnaffectedCurvature

def Unaffected : Bool→Fin 4→Prop
  | true,i => i=0∨i=2∨i=3
  | false,i => i=0∨i=1∨i=3
def p (atG : Bool) (z : ℝ) (i : Fin 4) : ℝ :=
  Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) 0 i
def q (atG : Bool) (z : ℝ) (i : Fin 4) : ℝ :=
  Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) 0 i
def ratio (atG : Bool) (z : ℝ) : ℝ :=
  SecantBaseline.basicRatio atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z
def angleEnd (atG : Bool) (z : ℝ) : ℝ := min z (Explicit.angleCut atG)
def scalar (atG : Bool) (z : ℝ) (i : Fin 4) (x : ℝ) : ℝ :=
  pure (baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) 0 z)
    (Explicit.l .high z) (ratio atG z) (p atG z i) (q atG z i) z x

private lemma r71_high_dom {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
  exact hz

theorem cut_domain (atG : Bool) : Explicit.angleCut atG∈Icc (0:ℝ) frameCap := by
  cases atG <;> norm_num [Explicit.angleCut,frameCap]

theorem angleEnd_domain (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    angleEnd atG z∈Icc 0 frameCap ∧ angleEnd atG z≤z ∧
      angleEnd atG z≤Explicit.angleCut atG := by
  have hc := cut_domain atG
  exact ⟨⟨le_min (by linarith [hz.1]) hc.1,(min_le_right _ _).trans hc.2⟩,
    min_le_left _ _,min_le_right _ _⟩

theorem weights_fixed (atG : Bool) (z s : ℝ) (i : Fin 4) (hi : Unaffected atG i) :
    Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i=p atG z i ∧
    Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i=q atG z i := by
  cases atG <;> fin_cases i <;>
    simp [Unaffected,p,q,Source.pWeights,Source.qWeights,lambdaG,lambdaB,secant] at hi ⊢

theorem ordered (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) :
    0<p atG z i ∧ p atG z i≤q atG z i ∧ q atG z i≤2*p atG z i := by
  exact Explicit.ordered_pair_domain .high atG (r71_high_dom hz)
    (show (0:ℝ)∈Icc 0 (Explicit.angleCut atG) from ⟨le_rfl,(cut_domain atG).1⟩) i

theorem GA_pair_upper {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) :
    q true z i≤(11/10)*Explicit.l .high z := by
  have hq := (Explicit.high_GA_pair_bounds hz
    (show (0:ℝ)∈Icc 0 (1/4:ℝ) by norm_num) i).2.2
  have hl := (Explicit.high_ranges hz).2.2.1
  dsimp [q]
  linarith

theorem AB_pair_upper {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ))
    (i : Fin 4) (hi : Unaffected false i) :
    p false z i≤(21/25)*q false z i ∧ q false z i≤Explicit.l .high z := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi,hkc,hkl⟩ := Explicit.high_ranges hz
  have hkr := (Explicit.high_tilted hz).2.2
  rcases hi with rfl|rfl|rfl <;>
    norm_num [p,q,Source.pWeights,Source.qWeights,lambdaG,lambdaB,secant] <;>
    (try constructor) <;> linarith

theorem GA_ratio {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    ratio true z∈Icc 0 (17/20:ℝ) := by
  obtain ⟨hk,hl,hc,hm⟩ := Explicit.family_positive .high (r71_high_dom hz)
  have hkr := (Explicit.high_tilted hz).2.2
  dsimp [ratio,SecantBaseline.basicRatio,SecantBaseline.affected]
  constructor
  · exact div_nonneg hk.le hl.le
  · apply (div_le_iff₀ hl).2
    linarith

theorem AB_ratio {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    ratio false z∈Icc 0 (129/125:ℝ) := by
  obtain ⟨hk,hl,hc,hm⟩ := Explicit.family_positive .high (r71_high_dom hz)
  have hmr := (Explicit.high_tilted hz).2.1
  change Explicit.m .high z/Explicit.l .high z∈Icc 0 (129/125:ℝ)
  exact ⟨div_nonneg hm.le hl.le,(div_le_iff₀ hl).2 hmr.le⟩

theorem AB_ratio_late {z x : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ))
    (hx : x∈Icc 0 (Real.tan (angleEnd false z))) (hlate : (7/20:ℝ)<x) :
    ratio false z∈Icc 0 (23/25:ℝ) := by
  have ha := angleEnd_domain false hz
  have hs := arctan_interval ha.1 hx
  have hsframe : Real.arctan x∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ha.1.2⟩
  have hthird : (1/3:ℝ)<Real.arctan x := by
    by_contra hh
    have hle : Real.arctan x≤1/3 := le_of_not_gt hh
    have ht := tan_monotone hsframe
      (show (1/3:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hle
    rw [Real.tan_arctan] at ht
    linarith [tan_third]
  have hzthird : z∈Icc (1/3:ℝ) (7/10:ℝ) :=
    ⟨by linarith [hs.2,ha.2.1],hz.2⟩
  have hmr := Explicit.high_tilted_third hzthird
  have hl := (Explicit.family_positive .high (r71_high_dom hz)).2.1
  have hbase := AB_ratio hz
  change Explicit.m .high z/Explicit.l .high z∈Icc 0 (23/25:ℝ)
  exact ⟨hbase.1,(div_le_iff₀ hl).2 hmr.le⟩

theorem scalar_at_original (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 frameCap)
    (i : Fin 4) (hi : Unaffected atG i) :
    scalar atG z i (Real.tan s)=
      baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z+
        V R (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i)
          (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i) (z-s) := by
  obtain ⟨hp,hq⟩ := weights_fixed atG z s i hi
  rw [hp,hq]
  exact pure_at_original atG (Explicit.family_positive .high (r71_high_dom hz)).2.1 hs

private lemma r71_scalar_zero_eq (atG : Bool) (z : ℝ) (i : Fin 4) :
    scalar atG z i 0=PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z)
      (Explicit.c .high z) z+V R (p atG z i) (q atG z i) z := by
  simp only [scalar,SecantCoordinate.pure,sub_self,mul_zero,Real.arctan_zero,sub_zero,add_zero,
    baseline_zero]

theorem scalar_zero (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    0<scalar atG z i 0 := by
  rw [r71_scalar_zero_eq]
  obtain ⟨hH,hG,hB,hGA,hAB⟩ := Certificate.high_endpoints hz
  cases atG
  · rcases hi with rfl|rfl|rfl
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val] using hH
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val,lambdaG,
        Bool.false_eq_true,↓reduceIte] using hG
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val] using hH
  · rcases hi with rfl|rfl|rfl
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val] using hH
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val,lambdaB,
        ↓reduceIte] using hB
    · simpa only [p,q,Source.pWeights,Source.qWeights,Matrix.cons_val] using hH

theorem scalar_equal (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    0<scalar atG z i (Real.tan z) := by
  have hzframe : z∈Icc 0 frameCap := ⟨by linarith [hz.1],hz.2⟩
  rw [scalar_at_original atG hz hzframe i hi]
  simp only [sub_self,V_zero,add_zero]
  cases atG
  · exact (Certificate.high_endpoints hz).2.2.2.2
  · exact (Certificate.high_endpoints hz).2.2.2.1

theorem scalar_cut (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hcut : Explicit.angleCut atG≤z)
    (i : Fin 4) (hi : Unaffected atG i) :
    0<scalar atG z i (Real.tan (Explicit.angleCut atG)) := by
  rw [scalar_at_original atG hz (cut_domain atG) i hi]
  cases atG
  · have hz' : z∈Icc (19/50:ℝ) (7/10:ℝ) := ⟨hcut,hz.2⟩
    obtain ⟨hG,hH⟩ := Certificate.AB_cut_endpoints hz'
    rcases hi with rfl|rfl|rfl
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB] using hH
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB] using hG
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB] using hH
  · have hz' : z∈Icc (1/4:ℝ) (7/10:ℝ) := ⟨hcut,hz.2⟩
    obtain ⟨hH,hB⟩ := Certificate.GA_cut_endpoints hz'
    have hml := Explicit.high_tilted_quarter hz'
    rcases hi with rfl|rfl|rfl
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB] using hH
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB,
        min_eq_right hml.le,max_eq_left hml.le] using hB
    · simpa [Explicit.angleCut,Source.pWeights,Source.qWeights,lambdaG,lambdaB] using hH

theorem scalar_right (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    0<scalar atG z i (Real.tan (angleEnd atG z)) := by
  by_cases hh : z≤Explicit.angleCut atG
  · rw [angleEnd,min_eq_left hh]
    exact scalar_equal atG hz i hi
  · rw [angleEnd,min_eq_right (le_of_not_ge hh)]
    exact scalar_cut atG hz (le_of_not_ge hh) i hi

theorem scalar_concave (atG : Bool) {z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (i : Fin 4) (hi : Unaffected atG i) :
    ConcaveOn ℝ (Icc 0 (Real.tan (angleEnd atG z))) (scalar atG z i) := by
  have ha := angleEnd_domain atG hz
  obtain ⟨hp,hpq,hqp⟩ := ordered atG hz i
  have hq := hp.trans_le hpq
  have hl := (Explicit.family_positive .high (r71_high_dom hz)).2.1
  apply pure_concave hp hq ha.1 ha.2.1 hz.2
  intro x hx
  have hs := arctan_interval ha.1 hx
  have hθ : z-Real.arctan x∈Icc 0 frameCap :=
    ⟨by linarith [hs.2,ha.2.1],by simp only [frameCap]; linarith [hz.2,hs.1]⟩
  have htan := tan_monotone ha.1 (cut_domain atG) ha.2.2
  cases atG
  · have hxcut : x∈Icc 0 (2/5:ℝ) :=
      ⟨hx.1,by simpa [Explicit.angleCut] using (hx.2.trans htan).trans tan_AB_cut.le⟩
    have hpair := AB_pair_upper hz i hi
    by_cases hearly : x≤7/20
    · exact (AB_early_total_curvature hl (AB_ratio hz) hp hpq hqp hpair.1 hpair.2
        ⟨hx.1,hearly⟩ hθ).le
    · have hlate : (7/20:ℝ)<x := lt_of_not_ge hearly
      have hh := AB_late_total_curvature hl (AB_ratio_late hz hx hlate)
        hp hpq hqp hpair.1 hpair.2 ⟨hlate.le,hxcut.2⟩ hθ
      linarith
  · have hxcut : x∈Icc 0 (32/125:ℝ) :=
      ⟨hx.1,by simpa [Explicit.angleCut] using (hx.2.trans htan).trans tan_GA_cut.le⟩
    have hh := GA_total_curvature hl (GA_ratio hz) hp hpq hqp (GA_pair_upper hz i) hxcut hθ
    linarith

/-- The actual high unaffected H/G/B/D alternative is strictly positive. -/
theorem original (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (hsz : s≤z)
    (i : Fin 4) (hi : Unaffected atG i) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z+
      V R (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i)
        (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i) (z-s) := by
  have hsframe := (Explicit.angle_domain atG hs).2
  have ha := angleEnd_domain atG hz
  have hsa : s≤angleEnd atG z := le_min hsz hs.2
  have hx : Real.tan s∈Icc 0 (Real.tan (angleEnd atG z)) :=
    ⟨tan_nonnegative hsframe,tan_monotone hsframe ha.1 hsa⟩
  have hh := concave_gt_of_endpoints (scalar_concave atG hz i hi) hx
    (scalar_zero atG hz i hi) (scalar_right atG hz i hi)
  rwa [scalar_at_original atG hz hsframe i hi] at hh

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.HighUnaffected
end
end
end

section
/-!
## The low pure-negative secant curvature

The baseline is enlarged to
the exact ratio `1.42`; its third derivative has the prescribed single
positive-square endpoint test. The H contribution has upper bound
`.117`, leaving the stated `.022` reserve in the total curvature.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowNegativeCurvature
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope PairNormCalculus OrdinaryCurvatureBounds
open SecantCoordinate SecantBounds

theorem tan_low_cut : Real.tan (1/5:ℝ)<203/1000 := by
  have hb := trig_bracket (l:=(1/5:ℝ)) (u:=(1/5:ℝ)) (x:=(1/5:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  have hc : 0<Real.cos (1/5:ℝ) := by norm_num at hb; linarith [hb.2.2.1]
  rw [Real.tan_eq_sin_div_cos,div_lt_iff₀ hc]
  norm_num at hb
  linarith [hb.2.1,hb.2.2.1]

theorem base_at_zero : baseSecond (71/50) 0< -(139/1000:ℝ) := by
  have hh := normalized_radius_bounds (A:=1+(71/50:ℝ)^2)
    (L:=1139/1000) (U:=57/50) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [qCap]) (by norm_num [qCap])
  have hS := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<1+(71/50:ℝ)^2)
  have hS2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤1+(71/50:ℝ)^2)
  have h1 : radical 1 0=1 := by rw [radical]; norm_num
  have h2 : radical (1+(71/50:ℝ)^2) 0=Real.sqrt (1+(71/50:ℝ)^2) := by
    rw [radical]; congr 1; ring
  have h3 : Real.sqrt (1+(71/50:ℝ)^2)^3=(1+(71/50:ℝ)^2)*Real.sqrt (1+(71/50:ℝ)^2) := by
    rw [pow_succ,hS2]
  have he : baseSecond (71/50) 0=1-R/Real.sqrt (1+(71/50:ℝ)^2) := by
    simp only [baseSecond]
    rw [h1,h2,h3]
    field_simp
  rw [he]
  linarith [hh.1]

theorem base_antitone :
    AntitoneOn (baseSecond (71/50)) (Icc (0:ℝ) (203/1000)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (baseSecond_hasDerivAt (71/50) x).continuousAt.continuousWithinAt)
    (fun x _ => baseSecond_hasDerivAt (71/50) x)
  intro x hx
  apply baseThird_nonpos_of_endpoint (u:=(203/1000:ℝ)) (by norm_num) (Ioo_subset_Icc_self hx)
  norm_num [qCap]

theorem base_curvature {r x : ℝ} (hr : r∈Icc 0 (71/50:ℝ))
    (hx : x∈Icc 0 (203/1000:ℝ)) : baseSecond r x< -(139/1000:ℝ) := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  exact (baseSecond_ratio_mono hr.1 hr.2 (by nlinarith)).trans_lt
    ((base_antitone (show (0:ℝ)∈Icc 0 (203/1000:ℝ) by norm_num) hx hx.1).trans_lt base_at_zero)

theorem H_curvature {k z x : ℝ} (hk : k∈Icc (2/3:ℝ) (187/250:ℝ))
    (hx : x∈Icc 0 (203/1000:ℝ))
    (hθ : z-Real.arctan x∈Icc 0 (1/5:ℝ)) :
    negativeSecond k 1 z x<(117/1000:ℝ) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hk1 : k≤1 := by linarith [hk.2]
  obtain ⟨hC,hD⟩ := Curvature.restricted_constants .middle hk0 hk1
    (show k≤(Curvature.ratioEnd .middle:ℝ)*1 by
      rw [show ((Curvature.ratioEnd .middle:ℚ):ℝ)=187/250 by norm_num [Curvature.ratioEnd]]
      linarith [hk.2])
  rw [show ((Curvature.C0End .middle:ℚ):ℝ)=569/1000 by norm_num [Curvature.C0End]] at hC
  rw [show ((Curvature.D0End .middle:ℚ):ℝ)=593/500 by norm_num [Curvature.D0End]] at hD
  have hE := curvatureSlope_nonneg (Real.sqrt_nonneg qCap) hk0 (by norm_num : (0:ℝ)<1)
  have hθframe : z-Real.arctan x∈Icc 0 frameCap :=
    ⟨hθ.1,by dsimp [frameCap]; linarith [hθ.2]⟩
  have hn := UnaffectedCurvature.numerator_upper hk0 hk1
    (show (1:ℝ)≤2*k by linarith [hk.1]) hx.1 hθframe
    (show curvatureZero R k 1≤(569/1000)*1 by linarith)
    (show Curvature.slopeZero k 1≤(593/500)*1 by linarith)
    (show (0:ℝ)*1≤curvatureSlope R k 1 by simpa using hE)
  have htr := LowNegativeComparison.small_trig hθ
  have hθ2 := pow_le_pow_left₀ hθ.1 hθ.2 2
  have hc : (49/50:ℝ)≤Real.cos (z-Real.arctan x) := by
    linarith [htr.2.1]
  have hsin := mul_nonneg (show 0≤2*x by linarith [hx.1]) htr.2.2.1
  have hxt := mul_le_mul hx.2 hθ.2 hθ.1 (by norm_num : (0:ℝ)≤203/1000)
  have hb : UnaffectedCurvature.bracket (569/1000) (593/500) 0 x (z-Real.arctan x)<117/1000 := by
    dsimp [UnaffectedCurvature.bracket]
    nlinarith only [hc,hsin,hxt,hx.2]
  have hnum : curvature R k 1 (-(z-Real.arctan x))-1*Real.cos (z-Real.arctan x)+
      2*x*Vd R k 1 (z-Real.arctan x)<117/1000 := by
    linarith only [hn,hb]
  have hden : 1≤(1+x^2)^2 := by nlinarith [sq_nonneg x,sq_nonneg (x^2)]
  unfold negativeSecond
  apply (div_lt_iff₀ (by positivity : 0<(1+x^2)^2)).2
  nlinarith only [hnum,hden]

theorem pure_curvature {l r k z x : ℝ} (hl : 1≤l)
    (hr : r∈Icc 0 (71/50:ℝ)) (hk : k∈Icc (2/3:ℝ) (187/250:ℝ))
    (hx : x∈Icc 0 (203/1000:ℝ))
    (hθ : z-Real.arctan x∈Icc 0 (1/5:ℝ)) :
    pureSecond l r k 1 z x< -(11/500:ℝ) := by
  have hb := base_curvature hr hx
  have hH := H_curvature hk hx hθ
  have hm := mul_lt_mul_of_pos_left hb (by linarith : 0<l)
  dsimp [pureSecond]
  nlinarith only [hm,hH,hl]

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowNegativeCurvature
end
end
end

section
/-!
## The absolute low GA angular baseline slope

The physical slope is increased
in its original coefficients k and l. The l derivative uses the exact
maximum of `(1+2u)/(1+u)^(3/2)`. The resulting fixed-coefficient rational
function is decreased to the prescribed sine endpoint `.248`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowGASlope
open Candidate Secondary SecantBaseline SecantCoordinate

def factor (u : ℝ) : ℝ := (1+2*u)/(Real.sqrt (1+u))^3
def factorFirst (u : ℝ) : ℝ := (1/2-u)/(Real.sqrt (1+u))^5
def norm (k l s : ℝ) : ℝ := Real.sqrt (l^2+k^2*(Real.cos s)^2)
def slope (k l s : ℝ) : ℝ :=
  (l*(13/12+Real.sin s)-R*l^2*Real.sin s/norm k l s)/(Real.cos s)^2
def slopeK (k l s : ℝ) : ℝ := R*l^2*Real.sin s*k/(norm k l s)^3
def slopeL (k l s : ℝ) : ℝ :=
  (13/12+Real.sin s-R*Real.sin s*l*(l^2+2*k^2*(Real.cos s)^2)/(norm k l s)^3)/(Real.cos s)^2
def rational (y : ℝ) : ℝ := (13/12-(169/250)*y)/(1-y^2)
def rationalFirst (y : ℝ) : ℝ :=
  (-(169/250)+(13/6)*y-(169/250)*y^2)/(1-y^2)^2

theorem factor_hasDerivAt {u : ℝ} (hu : 0≤u) :
    HasDerivAt factor (factorFirst u) u := by
  have hp : 0<1+u := by linarith
  have hs := Real.sqrt_pos.mpr hp
  have hs2 := Real.sq_sqrt hp.le
  have hroot := ((hasDerivAt_id u).const_add 1).sqrt hp.ne'
  have hd := (((hasDerivAt_id u).const_mul (2:ℝ)).const_add 1).div
    (hroot.pow 3) (pow_ne_zero 3 hs.ne')
  convert hd using 1
  · rfl
  · dsimp [factorFirst]
    field_simp [hs.ne']
    nlinarith

theorem factor_maximum {u : ℝ} (hu : 0≤u) : factor u≤factor (1/2) := by
  by_cases hh : u≤1/2
  · have hm : MonotoneOn factor (Icc (0:ℝ) (1/2)) := by
      apply monoOn_of_hasDeriv_nonneg
        (fun v hv => (factor_hasDerivAt hv.1).continuousAt.continuousWithinAt)
        (fun v hv => factor_hasDerivAt hv.1.le)
      intro v hv
      exact div_nonneg (by linarith [hv.2]) (pow_nonneg (Real.sqrt_nonneg _) 5)
    exact hm ⟨hu,hh⟩ (by norm_num) hh
  · have hm : AntitoneOn factor (Icc (1/2:ℝ) u) := by
      apply antiOn_of_hasDeriv_nonpos
        (fun v hv => (factor_hasDerivAt (by linarith [hv.1])).continuousAt.continuousWithinAt)
        (fun v hv => factor_hasDerivAt (by linarith [hv.1]))
      intro v hv
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hv.1]) (pow_nonneg (Real.sqrt_nonneg _) 5)
    exact hm ⟨le_rfl,(lt_of_not_ge hh).le⟩ ⟨(lt_of_not_ge hh).le,le_rfl⟩ (lt_of_not_ge hh).le

theorem factor_upper {u : ℝ} (hu : 0≤u) : factor u<109/100 := by
  have hp : 0<Real.sqrt (1+(1/2:ℝ)) := by positivity
  have hs : (Real.sqrt (1+(1/2:ℝ)))^2=3/2 := by
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hh : factor (1/2)<(109/100:ℝ) := by
    unfold factor
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    have hc : (Real.sqrt (1+(1/2:ℝ)))^3=(3/2)*Real.sqrt (1+(1/2:ℝ)) := by
      rw [pow_succ,hs]
    rw [hc]
    nlinarith
  exact (factor_maximum hu).trans_lt hh

theorem norm_positive {k l s : ℝ} (hl : 0<l) : 0<norm k l s :=
  Real.sqrt_pos.mpr (by nlinarith [sq_nonneg (k*Real.cos s)])

theorem norm_square (k l s : ℝ) : (norm k l s)^2=l^2+k^2*(Real.cos s)^2 :=
  Real.sq_sqrt (by positivity)

theorem norm_scale {k l s : ℝ} (hl : 0<l) :
    norm k l s=l*denominator (k/l) s := by
  have hn := norm_positive (k:=k) (s:=s) hl
  have hd := denominator_pos (k/l) s
  have hsq : (l*denominator (k/l) s)^2=(norm k l s)^2 := by
    rw [mul_pow,denominator_sq,norm_square]
    field_simp [hl.ne']
  nlinarith [mul_pos hl hd]

theorem slope_eq {k l s : ℝ} (hl : 0<l) :
    slope k l s=angleSlope l (k/l) s := by
  rw [slope,norm_scale hl]
  dsimp [angleSlope]
  field_simp [hl.ne',(denominator_pos (k/l) s).ne']

theorem norm_hasDerivAt_k {k l s : ℝ} (hl : 0<l) :
    HasDerivAt (fun k => norm k l s) (k*(Real.cos s)^2/norm k l s) k := by
  have hp := norm_positive (k:=k) (s:=s) hl
  have hd := (((((hasDerivAt_id k).pow 2).mul_const ((Real.cos s)^2)).const_add (l^2))).sqrt
    (show l^2+k^2*(Real.cos s)^2≠0 by nlinarith [norm_square k l s])
  convert hd using 1
  · rfl
  · dsimp [norm]
    ring

theorem norm_hasDerivAt_l {k l s : ℝ} (hl : 0<l) :
    HasDerivAt (fun l => norm k l s) (l/norm k l s) l := by
  have hp := norm_positive (k:=k) (s:=s) hl
  have hd := ((((hasDerivAt_id l).pow 2).add_const (k^2*(Real.cos s)^2))).sqrt
    (show l^2+k^2*(Real.cos s)^2≠0 by nlinarith [norm_square k l s])
  convert hd using 1
  · rfl
  · dsimp [norm]
    ring

theorem slope_hasDerivAt_k {k l s : ℝ} (hl : 0<l) (hc : Real.cos s≠0) :
    HasDerivAt (fun k => slope k l s) (slopeK k l s) k := by
  have hn := norm_positive (k:=k) (s:=s) hl
  have hd := (((hasDerivAt_const k (R*l^2*Real.sin s)).div
    (norm_hasDerivAt_k hl) hn.ne').const_sub (l*(13/12+Real.sin s))).div_const ((Real.cos s)^2)
  convert hd using 1
  · rfl
  · dsimp [slopeK]
    field_simp [hn.ne',hc]
    ring

theorem slope_hasDerivAt_l {k l s : ℝ} (hl : 0<l) :
    HasDerivAt (fun l => slope k l s) (slopeL k l s) l := by
  have hn := norm_positive (k:=k) (s:=s) hl
  have hn2 := norm_square k l s
  have h1 : HasDerivAt (fun l:ℝ => l*(13/12+Real.sin s)) (13/12+Real.sin s) l := by
    simpa using (hasDerivAt_id l).mul_const (13/12+Real.sin s)
  have h2 : HasDerivAt (fun l:ℝ => R*l^2*Real.sin s) (R*(2*l)*Real.sin s) l :=
    ((((hasDerivAt_id l).fun_pow 2).const_mul R).mul_const (Real.sin s)).congr_deriv (by simp)
  have hd := (h1.fun_sub (h2.fun_div (norm_hasDerivAt_l hl) hn.ne')).div_const ((Real.cos s)^2)
  refine hd.congr_deriv ?_
  have e1 : (R*(2*l)*Real.sin s*norm k l s-R*l^2*Real.sin s*(l/norm k l s))/norm k l s^2=
      R*Real.sin s*l*(l^2+2*k^2*(Real.cos s)^2)/(norm k l s)^3 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    linear_combination (2*Real.sin s)*hn2
  rw [e1]
  rfl

theorem normalized_factor {k l s : ℝ} (hl : 0<l) :
    l*(l^2+2*k^2*(Real.cos s)^2)/(norm k l s)^3=
      factor ((k*Real.cos s/l)^2) := by
  have hN := norm_positive (k:=k) (s:=s) hl
  have hS : 0<Real.sqrt (1+(k*Real.cos s/l)^2) := by positivity
  have hS2 := Real.sq_sqrt (by positivity : 0≤1+(k*Real.cos s/l)^2)
  have he : norm k l s=l*Real.sqrt (1+(k*Real.cos s/l)^2) := by
    have hsq : (l*Real.sqrt (1+(k*Real.cos s/l)^2))^2=(norm k l s)^2 := by
      rw [mul_pow,hS2,norm_square]
      field_simp [hl.ne']
    nlinarith [mul_pos hl hS]
  rw [he]
  dsimp [factor]
  field_simp [hl.ne',hS.ne']

theorem sine_GA {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    Real.sin s∈Icc 0 (31/125:ℝ) := by
  have hb := trig_bracket (l:=0) (u:=(1/4:ℝ)) (x:=s)
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  exact ⟨(transport_trig hsf).2.2.1,by norm_num at hb; linarith [hb.2.1]⟩

theorem slopeL_positive {k l s : ℝ} (hl : 0<l) (hs : s∈Icc 0 (1/4:ℝ)) :
    0<slopeL k l s := by
  have hy := sine_GA hs
  have hf := factor_upper (sq_nonneg (k*Real.cos s/l))
  have hf0 : 0≤factor ((k*Real.cos s/l)^2) := by dsimp [factor]; positivity
  have hR := Curvature.radius_bounds.2
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hp := mul_le_mul (show R≤(99/50:ℝ) by linarith) hf.le hf0 (by norm_num : (0:ℝ)≤99/50)
  have hpy := mul_le_mul_of_nonneg_right hp hy.1
  have hy' := mul_le_mul_of_nonneg_left hy.2
    (by norm_num : (0:ℝ)≤(99/50)*(109/100)-1)
  have hnum : 0<13/12+Real.sin s-R*Real.sin s*factor ((k*Real.cos s/l)^2) := by
    nlinarith only [hpy,hy']
  have hc : 0<Real.cos s := by linarith [Explicit.GA_cut_cosine hs]
  have he : R*Real.sin s*l*(l^2+2*k^2*(Real.cos s)^2)/(norm k l s)^3=
      R*Real.sin s*factor ((k*Real.cos s/l)^2) := by
    rw [←normalized_factor hl]
    ring
  rw [slopeL,he]
  exact div_pos hnum (sq_pos_of_pos hc)

theorem coefficient_comparison {k l s : ℝ}
    (hk : (2/3:ℝ)≤k) (hl : (1023/1000:ℝ)≤l) (hs : s∈Icc 0 (1/4:ℝ)) :
    slope (2/3) (1023/1000) s≤ slope k l s := by
  have hl0 : 0<l := by linarith
  have hc : Real.cos s≠0 := ne_of_gt (by linarith [Explicit.GA_cut_cosine hs])
  have hy := sine_GA hs
  have hmK : MonotoneOn (fun k => slope k l s) (Icc (2/3:ℝ) k) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun a _ => (slope_hasDerivAt_k (k:=a) hl0 hc).continuousAt.continuousWithinAt)
      (fun a _ => slope_hasDerivAt_k hl0 hc)
    intro a ha
    dsimp [slopeK]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) (sq_nonneg l)) hy.1)
        (by linarith [ha.1])) (pow_nonneg (norm_positive (k:=a) (s:=s) hl0).le 3)
  have hmL : MonotoneOn (fun l => slope (2/3) l s) (Icc (1023/1000:ℝ) l) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun b hb => (slope_hasDerivAt_l (k:=(2/3:ℝ)) (s:=s) (by linarith [hb.1])).continuousAt.continuousWithinAt)
      (fun b hb => slope_hasDerivAt_l (k:=(2/3:ℝ)) (s:=s) (by linarith [hb.1]))
    intro b hb
    exact (slopeL_positive (k:=(2/3:ℝ)) (by linarith [hb.1]) hs).le
  exact (hmL ⟨le_rfl,hl⟩ ⟨hl,le_rfl⟩ hl).trans
    (hmK ⟨le_rfl,hk⟩ ⟨hk,le_rfl⟩ hk)

theorem rational_hasDerivAt {y : ℝ} (hy : y∈Icc 0 (31/125:ℝ)) :
    HasDerivAt rational (rationalFirst y) y := by
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hn : 1-y^2≠0 := by nlinarith
  have hd := (((hasDerivAt_id y).const_mul (169/250:ℝ)).const_sub (13/12:ℝ)).div
    (((hasDerivAt_id y).pow 2).const_sub 1) hn
  convert hd using 1
  · rfl
  · dsimp [rationalFirst]
    field_simp [hn]
    ring

theorem rational_antitone : AntitoneOn rational (Icc (0:ℝ) (31/125)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun y hy => (rational_hasDerivAt hy).continuousAt.continuousWithinAt)
    (fun y hy => rational_hasDerivAt (Ioo_subset_Icc_self hy))
  intro y hy
  exact div_nonpos_of_nonpos_of_nonneg
    (by nlinarith [hy.2,sq_nonneg y]) (sq_nonneg _)

theorem fixed_lower {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    (249/250:ℝ)<slope (2/3) (1023/1000) s := by
  have hy := sine_GA hs
  have hc : 0<Real.cos s := by linarith [Explicit.GA_cut_cosine hs]
  have hcoef := coefficient_upper (r₀:=((2/3:ℝ)/(1023/1000))) (c₀:=(121/125:ℝ)) (D:=(419/250:ℝ))
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (show (121/125:ℝ)≤Real.cos s by linarith [Explicit.GA_cut_cosine hs])
    (by norm_num [qCap])
  have hp := mul_le_mul_of_nonneg_right hcoef.le hy.1
  have hcos2 : (Real.cos s)^2=1-(Real.sin s)^2 := by nlinarith [Real.sin_sq_add_cos_sq s]
  have hrational := rational_antitone hy (show (31/125:ℝ)∈Icc 0 (31/125:ℝ) by norm_num) hy.2
  have hrlower := mul_le_mul_of_nonneg_left hrational (by norm_num : (0:ℝ)≤1023/1000)
  have hendpoint : (249/250:ℝ)<(1023/1000)*rational (31/125) := by norm_num [rational]
  have he : R*Real.sin s/denominator ((2/3:ℝ)/(1023/1000)) s=
      R/denominator ((2/3:ℝ)/(1023/1000)) s*Real.sin s := by ring
  have hbound : (1023/1000)*rational (Real.sin s)≤angleSlope (1023/1000) ((2/3)/(1023/1000)) s := by
    dsimp only [rational,angleSlope]
    rw [←hcos2,←mul_div_assoc]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hc)).2
    rw [he]
    nlinarith only [hp]
  rw [slope_eq (by norm_num : (0:ℝ)<1023/1000)]
  exact (hendpoint.trans_le hrlower).trans_le hbound

theorem original {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) :
    (249/250:ℝ)<angleSlope (Explicit.l .low z) (Explicit.k .low z/Explicit.l .low z) s := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  have hh := (fixed_lower hs).trans_le (coefficient_comparison hklo.le hllo.le hs)
  rwa [slope_eq (by linarith : 0<Explicit.l .low z)] at hh

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowGASlope
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.HighAffected
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SecantCoordinate SecantBaseline AffectedNegativeCurves

def value (atG : Bool) (k l c s z : ℝ) : ℝ :=
  baseline atG k l c s z+
    if atG then V R k (NegativeAPositiveTD.secant l s) (z-s)
    else V R (min (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z))
      (max (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z)) (z-s)
def curve (atG : Bool) (r z x : ℝ) : ℝ :=
  if atG then upper r z x else min (upper r z x) (lower r z x)
def ratio (atG : Bool) (z : ℝ) : ℝ :=
  basicRatio atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z
def scalar (atG : Bool) (z x : ℝ) : ℝ :=
  baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) 0 z+
    Explicit.l .high z*(curve atG (ratio atG z) z x-1+
      R*OrdinaryCurvatureBounds.shape (ratio atG z))

theorem radical_tan {s : ℝ} (hs : s∈Icc 0 frameCap) :
    radical 1 (Real.tan s)=1/Real.cos s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hw := radical_positive (A:=1) (x:=Real.tan s) (by norm_num)
  have hw2 := radical_square (A:=1) (x:=Real.tan s) (by norm_num)
  have ht := (AffectedNorm.tan_identity hc).2
  have hp : 0<1/Real.cos s := one_div_pos.mpr hc
  nlinarith

theorem cosine_tan {s z : ℝ} (hs : s∈Icc 0 frameCap) :
    cosine z (Real.tan s)=Real.cos (z-s) := by
  rw [cosine_arctan,arctan_tan hs]

private theorem r70_high_dom {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    z∈Icc (Certificate.left .high:ℝ) (Certificate.right .high:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
  exact hz

theorem GA_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    value true k l c s z=baseline true k l c 0 z+
      l*(upper (k/l) z (Real.tan s)-1+R*OrdinaryCurvatureBounds.shape (k/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hcos : Real.cos (z-s)/Real.cos s=Real.cos z+Real.tan s*Real.sin z := by
    rw [Real.cos_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
  rw [value,baseline_eq_extension true k l c z hs]
  simp only [angularBaseline,affected,↓reduceIte,FlatTStress.secantCharge,V]
  rw [show -(z-s)=s-z by ring,AffectedPositive.rotation_norm hl hc k z,
    AffectedPositive.zero_norm hl k]
  dsimp [upper,NegativeAPositiveTD.secant]
  have hh := congrArg (fun a : ℝ => l*a) hcos
  field_simp [hl.ne',hc.ne'] at hh ⊢
  linear_combination (12*l)*hh

theorem AB_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    value false k l c s z=baseline false k l c 0 z+
      l*(min (upper (PositiveTD.tilted c z/l) z (Real.tan s))
        (lower (PositiveTD.tilted c z/l) z (Real.tan s))-1+
          R*OrdinaryCurvatureBounds.shape (PositiveTD.tilted c z/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hw := radical_tan hs
  have ht := cosine_tan (z:=z) hs
  have hcos : Real.cos (z-s)/Real.cos s=Real.cos z+Real.tan s*Real.sin z := by
    rw [Real.cos_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
  have hbranch := branch_difference (PositiveTD.tilted c z/l) z (Real.tan s)
  rcases le_total (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z) with hle | hle
  · have hr : radical 1 (Real.tan s)≤PositiveTD.tilted c z/l := by
      rw [hw]
      apply (le_div_iff₀ hl).2
      dsimp [NegativeAPositiveTD.secant] at hle
      rw [show 1/Real.cos s*l=l/Real.cos s by ring]
      exact hle
    have hp := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hr)
      (sub_nonpos.mpr (cosine_le_one z (Real.tan s)))
    have hmin : lower (PositiveTD.tilted c z/l) z (Real.tan s)≤
        upper (PositiveTD.tilted c z/l) z (Real.tan s) := by linarith
    rw [min_eq_right hmin,value,baseline_eq_extension false k l c z hs]
    simp only [angularBaseline,affected,Bool.false_eq_true,↓reduceIte,FlatTStress.secantCharge,
      min_eq_left hle,max_eq_right hle,V]
    simp only [pairNorm_symm (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z)]
    rw [show -(z-s)=s-z by ring,
      AffectedPositive.rotation_norm hl hc (PositiveTD.tilted c z) z,
      AffectedPositive.zero_norm hl (PositiveTD.tilted c z)]
    dsimp [lower]
    rw [hw,ht]
    dsimp [NegativeAPositiveTD.secant]
    field_simp [hl.ne']
    ring
  · have hr : PositiveTD.tilted c z/l≤radical 1 (Real.tan s) := by
      rw [hw]
      apply (div_le_iff₀ hl).2
      dsimp [NegativeAPositiveTD.secant] at hle
      rw [show 1/Real.cos s*l=l/Real.cos s by ring]
      exact hle
    have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr)
      (sub_nonpos.mpr (cosine_le_one z (Real.tan s)))
    have hmin : upper (PositiveTD.tilted c z/l) z (Real.tan s)≤
        lower (PositiveTD.tilted c z/l) z (Real.tan s) := by linarith
    rw [min_eq_left hmin,value,baseline_eq_extension false k l c z hs]
    simp only [angularBaseline,affected,Bool.false_eq_true,↓reduceIte,FlatTStress.secantCharge,
      min_eq_right hle,max_eq_left hle,V]
    rw [show -(z-s)=s-z by ring,
      AffectedPositive.rotation_norm hl hc (PositiveTD.tilted c z) z,
      AffectedPositive.zero_norm hl (PositiveTD.tilted c z)]
    dsimp [upper,NegativeAPositiveTD.secant]
    have hh := congrArg (fun a : ℝ => l*a) hcos
    field_simp [hl.ne',hc.ne'] at hh ⊢
    linear_combination (12*l)*hh

theorem scalar_at_original (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 frameCap) :
    scalar atG z (Real.tan s)=
      value atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z := by
  have hl := (Explicit.family_positive .high (r70_high_dom hz)).2.1
  cases atG
  · simpa [scalar,curve,ratio,basicRatio,affected] using (AB_identity hl hs).symm
  · simpa [scalar,curve,ratio,basicRatio,affected] using (GA_identity hl hs).symm

theorem curve_concave (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    ConcaveOn ℝ (Icc 0 (Real.tan z)) (curve atG (ratio atG z) z) := by
  have hzframe : z∈Icc 0 frameCap := ⟨by linarith [hz.1],hz.2⟩
  cases atG
  · have hr := HighUnaffected.AB_ratio hz
    have hlarge : 1<ratio false z→z≤1/4 := by
      intro hh
      by_contra hnot
      have hm := Explicit.high_tilted_quarter ⟨(lt_of_not_ge hnot).le,hz.2⟩
      have hl := (Explicit.family_positive .high (r70_high_dom hz)).2.1
      have hratio : ratio false z<1 := by
        change Explicit.m .high z/Explicit.l .high z<1
        exact (div_lt_one hl).2 hm
      linarith
    exact AffectedNegativeCurvature.minimum_concave hr hzframe hlarge
  · have hr : ratio true z∈Icc 0 (17/20:ℝ) := HighUnaffected.GA_ratio hz
    exact upper_concave (AffectedNorm.second_coordinate_pos
      ⟨hr.1,by linarith [hr.2]⟩ hzframe)

theorem scalar_concave (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    ConcaveOn ℝ (Icc 0 (Real.tan z)) (scalar atG z) := by
  have hcurve := curve_concave atG hz
  have hl := (Explicit.family_positive .high (r70_high_dom hz)).2.1
  refine ⟨hcurve.1,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hcurve.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have hp := mul_le_mul_of_nonneg_left hh hl.le
  dsimp [scalar]
  nlinarith [congrArg (fun t : ℝ => t*
    (baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) 0 z+
      Explicit.l .high z*(-1+R*OrdinaryCurvatureBounds.shape (ratio atG z)))) hab]

theorem scalar_zero (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<scalar atG z 0 := by
  have he := scalar_at_original atG hz
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  rw [Real.tan_zero] at he
  rw [he]
  cases atG
  · simpa [value,NegativeAPositiveTD.secant,baseline_zero,Explicit.m] using
      (Certificate.high_endpoints hz).2.2.1
  · simpa [value,NegativeAPositiveTD.secant,baseline_zero] using
      (Certificate.high_endpoints hz).2.1

theorem scalar_equal (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<scalar atG z (Real.tan z) := by
  rw [scalar_at_original atG hz ⟨by linarith [hz.1],hz.2⟩]
  cases atG
  · simpa [value] using (Certificate.high_endpoints hz).2.2.2.2
  · simpa [value] using (Certificate.high_endpoints hz).2.2.2.1

theorem original (atG : Bool) {s z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (hsz : s≤z) :
    0<value atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z := by
  have hsframe := (Explicit.angle_domain atG hs).2
  have hzframe : z∈Icc 0 frameCap := ⟨by linarith [hz.1],hz.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan z) :=
    ⟨tan_nonnegative hsframe,tan_monotone hsframe hzframe hsz⟩
  have hh := concave_gt_of_endpoints (scalar_concave atG hz) hx
    (scalar_zero atG hz) (scalar_equal atG hz)
  rwa [scalar_at_original atG hz hsframe] at hh

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.HighAffected
end
end
end
