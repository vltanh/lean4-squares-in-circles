module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Angular

/-!
# The widened quarter-angle negative comparison and curvature

Uncompiled Section 5. The larger-coefficient comparison uses exactly
q/k at most 5/3 and t at most 1/4. The stated sqrt(34) denominator is
weakened to 6 as in the hand proof, leaving a rational .0255 reserve.
The resulting H comparison has secant-coordinate curvature below -.037.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LowNegative
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
      Bool.false_eq_true,↓reduceIte,Matrix.cons_val_succ,Matrix.cons_val_zero] at hw ⊢
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LowNegative
