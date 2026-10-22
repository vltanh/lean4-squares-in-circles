module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SecantBounds

/-!
# The unaffected negative-angle curvature estimates

Uncompiled transcription of (68)--(74) and (76).  The ordinary signed
tangents give a convex expression in the remaining angle. Its two
endpoints are compared exactly as in the hand proof. The final AB
combination uses the displayed degree-six polynomial on its whole
interval, followed by the separate late-ratio estimate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.UnaffectedCurvature
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
  have hl : -b≤min (-bracket C D E x 0) (-bracket C D E x frameCap) :=
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
  nlinarith only [hdiv,hr]

theorem AB_negative_curvature {p q z x : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hratio : p≤(21/25)*q)
    (hx : 0≤x) (hθ : z-Real.arctan x∈Icc 0 frameCap) :
    negativeSecond p q z x≤q*rational (-(373/1000)) (1273/500) x := by
  have hq := hp.trans_le hpq
  obtain ⟨hC,hD⟩ := Curvature.restricted_constants .wide hp hpq
    (show p≤(Curvature.ratioEnd .wide:ℝ)*q by simpa [Curvature.ratioEnd] using hratio)
  have hE := Curvature.restricted_C1 hp hpq hqp hratio
  norm_num [Curvature.C0End,Curvature.D0End] at hC hD
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
  have hd : Differentiable ℝ combination := by dsimp [combination]; fun_prop
  convert (hd x).hasDerivAt using 1
  simp (disch := fun_prop) [combination,combinationFirst]
  ring

theorem combination_upper {x : ℝ} (hx : x∈Icc 0 (7/20:ℝ)) :
    combination x<-(6/625:ℝ) := by
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
  have he : combination (7/20:ℝ)<-(6/625:ℝ) := by norm_num [combination]
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
    pureSecond l r p q z x<-(461/10000)*l := by
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
    pureSecond l r p q z x<-(1/1000)*l := by
  have hq := hp.trans_le hpq
  have hx0 : 0≤x := by linarith [hx.1]
  have hb := mul_lt_mul_of_pos_left (AB_late_base_curvature hr hx) hl
  have hv := AB_negative_curvature hp hpq hqp hratio hx0 hθ
  have hrb := mul_lt_mul_of_pos_left (AB_rational_upper ⟨hx0,hx.2⟩) hq
  dsimp [pureSecond]
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.UnaffectedCurvature
