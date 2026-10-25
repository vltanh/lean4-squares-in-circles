module

public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CurvatureConstants
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CutData

/-!
# Eight squares: the low negative-angle comparison with the H pair

The B
comparison uses the prescribed chord and tangent. The G comparison
extends the larger-coefficient derivative to the full ratio interval
`[1/2,1]` at angles at most `1/5`.
-/

section
/-!
## Coefficient-pair domains after the original negative-A secant weight

The ordered H/G/B pairs, including either possible secant assignment,
satisfy the coefficient hypotheses of the proved concentration lemmas.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Explicit
open Candidate Secondary
open Certificate (Family)

def angleCut (atG : Bool) : ℝ := if atG then 1/4 else 19/50

theorem angle_domain (atG : Bool) {s : ℝ} (hs : s∈Icc 0 (angleCut atG)) :
    s∈Icc 0 (19/50:ℝ) ∧ s∈Icc 0 frameCap := by
  cases atG <;> dsimp [angleCut,frameCap] at hs ⊢ <;>
    exact ⟨⟨hs.1,by linarith [hs.2]⟩,⟨hs.1,by linarith [hs.2]⟩⟩

theorem family_basic_domain (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    k f z∈Icc (1/2:ℝ) (17/20:ℝ) ∧
      c f z∈Icc (k f z) 2 ∧ 1<l f z ∧ k f z<l f z ∧
      (11/20)*l f z<k f z ∧ (77/100)*l f z< m f z ∧ m f z<(71/50)*l f z := by
  cases f
  · have hz' : z∈Icc (0:ℝ) (1/5) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
      exact hz
    obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := low_ranges hz'
    have hkl := (low_ratio hz').1
    have hm := low_tilted hz'
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
      by linarith,by linarith,hkl,by linarith [hm.1],hm.2⟩
  · have hz' : z∈Icc (1/5:ℝ) (7/10) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split,
        PositiveTD.Certificate.h] at hz
      exact hz
    obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi,hkc,hkl⟩ := high_ranges hz'
    have hkr := high_ratio_lower hz'
    have hm := high_tilted hz'
    exact ⟨⟨by linarith,by linarith⟩,⟨hkc.le,by linarith⟩,
      by linarith,hkl,by linarith,hm.1,by linarith [hm.2.1]⟩

theorem secant_bounds (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) :
    l f z≤ secant (l f z) s ∧ secant (l f z) s<2*k f z ∧
      secant (l f z) s<2*m f z := by
  have hr := family_basic_domain f hz
  have hl : 0<l f z := by linarith [hr.2.2.1]
  have hcos := AB_cut_cosine (angle_domain atG hs).1
  have hc : 0<Real.cos s := by linarith
  have hp : l f z≤ secant (l f z) s := by
    apply (le_div_iff₀ hc).2
    nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one s) hl.le]
  have hK₁ := mul_lt_mul_of_pos_right hr.2.2.2.2.1 hc
  have hK₂ := mul_lt_mul_of_pos_left hcos
    (show 0<(11/20)*l f z by positivity)
  have hM₁ := mul_lt_mul_of_pos_right hr.2.2.2.2.2.1 hc
  have hM₂ := mul_lt_mul_of_pos_left hcos
    (show 0<(77/100)*l f z by positivity)
  refine ⟨hp,?_,?_⟩
  · apply (div_lt_iff₀ hc).2
    nlinarith
  · apply (div_lt_iff₀ hc).2
    nlinarith

theorem family_coefficient_domain (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) :
    k f z∈Icc (1/2:ℝ) (17/20:ℝ) ∧
    lambdaG atG (l f z) s∈Icc (k f z) (2*k f z) ∧
    0<lambdaB atG (l f z) s ∧ c f z∈Icc (k f z) 2 ∧
    (lambdaB atG (l f z) s≤2*m f z ∧ m f z≤2*lambdaB atG (l f z) s) := by
  have hr := family_basic_domain f hz
  obtain ⟨hp,hpk,hpm⟩ := secant_bounds f atG hz hs
  have hl : 0<l f z := by linarith [hr.2.2.1]
  have hupper : m f z<2*l f z := by linarith [hr.2.2.2.2.2.2]
  cases atG <;> simp only [lambdaG,lambdaB,Bool.false_eq_true,↓reduceIte]
  · exact ⟨hr.1,⟨hr.2.2.2.1.le,by linarith [hr.2.2.2.2.1]⟩,hl.trans_le hp,hr.2.1,
      hpm.le,by linarith⟩
  · exact ⟨hr.1,⟨hr.2.2.2.1.le.trans hp,hpk.le⟩,hl,hr.2.1,
      by linarith [hr.2.2.2.2.2.1],hupper.le⟩

theorem ordered_pair_domain (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (angleCut atG)) (i : Fin 4) :
    0<Source.pWeights atG (k f z) (l f z) (m f z) s i ∧
      Source.pWeights atG (k f z) (l f z) (m f z) s i≤
        Source.qWeights atG (k f z) (l f z) (m f z) s i ∧
      Source.qWeights atG (k f z) (l f z) (m f z) s i≤
        2*Source.pWeights atG (k f z) (l f z) (m f z) s i := by
  obtain ⟨hk,hG,hB,_,hm⟩ := family_coefficient_domain f atG hz hs
  exact Source.coefficient_domain hk hG hB (family_positive f hz).2.2.2 hm i

theorem minmax_ratio {a b r : ℝ} (hab : r*a<b) (hba : r*b<a) :
    r*max a b< min a b := by
  rcases le_total a b with hh | hh
  · simpa [max_eq_right hh,min_eq_left hh] using hba
  · simpa [max_eq_left hh,min_eq_right hh] using hab

theorem high_GA_pair_bounds {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) (i : Fin 4) :
    (51/80)*Source.qWeights true (k .high z) (l .high z) (m .high z) s i<
      Source.pWeights true (k .high z) (l .high z) (m .high z) s i ∧
    1≤Source.qWeights true (k .high z) (l .high z) (m .high z) s i ∧
    Source.qWeights true (k .high z) (l .high z) (m .high z) s i<11/10 := by
  have hzc : z∈Icc ((Certificate.left .high:ℚ):ℝ) ((Certificate.right .high:ℚ):ℝ) := by
    norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
    exact hz
  obtain ⟨hklo,hkhi,hllo,hlhi,_,_,_,_⟩ := high_ranges hz
  have hkr := high_ratio_lower hz
  have hmr := high_tilted hz
  have hcos := GA_cut_cosine hs
  have hc : 0<Real.cos s := by linarith
  have hl : 0<l .high z := by linarith
  have hsec := (secant_bounds .high true hzc hs).1
  have hsecHi : secant (l .high z) s<11/10 := by
    apply (div_lt_iff₀ hc).2
    nlinarith
  have hG : (51/80)*secant (l .high z) s<k .high z := by
    have hp₁ := mul_lt_mul_of_pos_right hkr hc
    have hp₂ := mul_lt_mul_of_pos_left hcos (show 0<(659/1000)*l .high z by positivity)
    dsimp [secant]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hc).2
    nlinarith
  have hB := minmax_ratio
    (show (51/80)*l .high z < m .high z by linarith [hmr.1])
    (show (51/80)*m .high z<l .high z by nlinarith [hmr.2.1])
  have hmaxLo : 1 ≤ max (l .high z) (m .high z) :=
    (by linarith : (1:ℝ) ≤ l .high z).trans (le_max_left _ _)
  have hmaxHi : max (l .high z) (m .high z)<11/10 := by
    apply max_lt
    · linarith
    · nlinarith [hmr.2.1]
  fin_cases i
  · show (51/80)*1<k .high z ∧ 1 ≤ (1:ℝ) ∧ (1:ℝ)<11/10
    exact ⟨by linarith,le_rfl,by norm_num⟩
  · show (51/80)*secant (l .high z) s<k .high z ∧ 1 ≤ secant (l .high z) s ∧
      secant (l .high z) s<11/10
    exact ⟨hG,by linarith,hsecHi⟩
  · show (51/80)*max (l .high z) (m .high z) < min (l .high z) (m .high z) ∧
      1 ≤ max (l .high z) (m .high z) ∧ max (l .high z) (m .high z)<11/10
    exact ⟨hB,hmaxLo,hmaxHi⟩
  · show (51/80)*1<k .high z ∧ 1 ≤ (1:ℝ) ∧ (1:ℝ)<11/10
    exact ⟨by linarith,le_rfl,by norm_num⟩

theorem high_AB_pair_bounds {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) (i : Fin 4) :
    (13/20)*Source.qWeights false (k .high z) (l .high z) (m .high z) s i<
      Source.pWeights false (k .high z) (l .high z) (m .high z) s i ∧
    1≤Source.qWeights false (k .high z) (l .high z) (m .high z) s i ∧
    Source.qWeights false (k .high z) (l .high z) (m .high z) s i<23/20 := by
  have hzc : z∈Icc ((Certificate.left .high:ℚ):ℝ) ((Certificate.right .high:ℚ):ℝ) := by
    norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
    exact hz
  obtain ⟨hklo,hkhi,hllo,hlhi,_,_,_,_⟩ := high_ranges hz
  have hkr := high_ratio_lower hz
  have hmr := high_tilted hz
  have hcos := AB_cut_cosine hs
  have hc : 0<Real.cos s := by linarith
  have hl : 0<l .high z := by linarith
  have hsec := (secant_bounds .high false hzc hs).1
  have hsecHi : secant (l .high z) s<23/20 := by
    apply (div_lt_iff₀ hc).2
    nlinarith
  have hB₁ : (13/20)*secant (l .high z) s < m .high z := by
    have hp₁ := mul_lt_mul_of_pos_right hmr.1 hc
    have hp₂ := mul_lt_mul_of_pos_left hcos (show 0<(77/100)*l .high z by positivity)
    dsimp [secant]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hc).2
    nlinarith
  have hB₂ : (13/20)*m .high z<secant (l .high z) s := by
    nlinarith [hmr.2.1]
  have hB := minmax_ratio hB₁ hB₂
  have hmaxLo : 1 ≤ max (secant (l .high z) s) (m .high z) :=
    (by linarith : (1:ℝ) ≤ secant (l .high z) s).trans (le_max_left _ _)
  have hmaxHi : max (secant (l .high z) s) (m .high z)<23/20 := by
    apply max_lt hsecHi
    nlinarith [hmr.2.1]
  fin_cases i
  · show (13/20)*1<k .high z ∧ 1 ≤ (1:ℝ) ∧ (1:ℝ)<23/20
    exact ⟨by linarith,le_rfl,by norm_num⟩
  · show (13/20)*l .high z<k .high z ∧ 1 ≤ l .high z ∧ l .high z<23/20
    exact ⟨by linarith,by linarith,by linarith⟩
  · show (13/20)*max (secant (l .high z) s) (m .high z) < min (secant (l .high z) s) (m .high z) ∧
      1 ≤ max (secant (l .high z) s) (m .high z) ∧ max (secant (l .high z) s) (m .high z)<23/20
    exact ⟨hB,hmaxLo,hmaxHi⟩
  · show (13/20)*1<k .high z ∧ 1 ≤ (1:ℝ) ∧ (1:ℝ)<23/20
    exact ⟨by linarith,le_rfl,by norm_num⟩

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Explicit
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowNegativeComparison
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope OrdinaryNegativeEnvelope PairNormCalculus
open VaryingBFunctions

private theorem r41_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc ((Certificate.left .low:ℚ):ℝ) ((Certificate.right .low:ℚ):ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

theorem integrand_lower {r u : ℝ} (hr : r∈Icc (1/2:ℝ) 1)
    (hu : u∈Icc 0 (1/5:ℝ)) : (4/75:ℝ)≤ integrand r u := by
  have hr0 : 0<r := by linarith [hr.1]
  have hu' : u∈Icc 0 frameCap := ⟨hu.1,by dsimp [frameCap]; linarith [hu.2]⟩
  have hn := root_pos r hu'
  have hn2 := root_sq r hu'
  have hsq : (root r u)^2≤5*r^2 := by
    have hp := mul_nonneg hr0.le hu.1
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.1) (show (0:ℝ)≤r+1/2 by linarith)]
  have hnU : root r u≤(9/4)*r :=
    le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (by positivity) (by nlinarith [sq_nonneg r])
  have hn3 : (root r u)^3≤(45/4)*r^3 := by
    have hprod := mul_le_mul hsq hnU hn.le (by positivity : (0:ℝ)≤5*r^2)
    nlinarith only [hprod]
  have hnum : (3/5)*r^3≤r^2*(r-u) := by
    have hh : u≤(2/5)*r := by linarith [hu.2,hr.1]
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hh)]
  exact (le_div_iff₀ (pow_pos hn 3)).2 (by nlinarith only [hn3,hnum])

theorem gain_lower {r u : ℝ} (hr : r∈Icc (1/2:ℝ) 1)
    (hu : u∈Icc 0 (1/5:ℝ)) : (4/75)*u≤gain r u := by
  have hdomain {x : ℝ} (hx : x∈Icc 0 (1/5:ℝ)) : x∈Icc 0 frameCap :=
    ⟨hx.1,by dsimp [frameCap]; linarith [hx.2]⟩
  have hh := derivative_reserve
    (f:=gain r) (df:=integrand r) (k:=(4/75:ℝ))
    (fun x hx => (gain_hasDerivAt_u r (hdomain hx)).continuousAt.continuousWithinAt)
    (fun x hx => gain_hasDerivAt_u r (hdomain (Ioo_subset_Icc_self hx)))
    (fun x hx => integrand_lower hr (Ioo_subset_Icc_self hx))
    (show (0:ℝ)∈Icc 0 (1/5:ℝ) by norm_num) hu hu.1
  simpa only [gain_zero,sub_zero] using hh

theorem small_trig {t : ℝ} (ht : t∈Icc 0 (1/5:ℝ)) :
    (149/150)*t≤Real.sin t ∧ 1-t^2/2≤Real.cos t ∧
      Real.sin t∈Icc 0 (1/5:ℝ) := by
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  have hs := Real.sin_ge_sub_cube ht.1
  have hc := cos_lower_six ht.1
  have htail : 0≤t^4/24-t^6/720 := by
    have hh := mul_nonneg (pow_nonneg ht.1 4) (show 0≤30-t^2 by nlinarith)
    nlinarith only [hh]
  have hcube := mul_le_mul_of_nonneg_right ht2 ht.1
  have hframe : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  exact ⟨by nlinarith,by linarith,
    ⟨(transport_trig hframe).2.2.1,(Real.sin_le ht.1).trans ht.2⟩⟩

theorem D_small_nonnegative {r t : ℝ}
    (hr : r∈Icc (1/2:ℝ) 1) (ht : t∈Icc 0 (1/5:ℝ)) :
    (614/140625)*t≤D R r t := by
  obtain ⟨hs,hc,hsdom⟩ := small_trig ht
  have hg := gain_lower hr hsdom
  have hgs := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤4/75)
  have hR := Curvature.radius_bounds.1
  have hprod := mul_le_mul_of_nonneg_left hg
    (by linarith : (0:ℝ)≤R)
  have hRprod := mul_le_mul_of_nonneg_right hR.le
    (mul_nonneg (by norm_num : (0:ℝ)≤4/75) hsdom.1)
  have ht2 : t^2/2≤t/10 := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  unfold VaryingBFunctions.D
  linarith only [hprod,hRprod,hgs,hc,ht2]

theorem larger_coefficient {p a b t : ℝ}
    (hp : 0<p) (hpa : p≤a) (hab : a≤b) (hbp : b≤2*p)
    (ht : t∈Icc 0 (1/5:ℝ)) : V R p a t≤V R p b t := by
  have htframe : t∈Icc 0 frameCap := ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  have hcoeff {q : ℝ} (hq : q∈Icc a b) :
      0<q ∧ p/q∈Icc (1/2:ℝ) 1 := by
    have hq0 : 0<q := hp.trans_le (hpa.trans hq.1)
    exact ⟨hq0,⟨(le_div_iff₀ hq0).2 (by linarith [hq.2]),
      (div_le_one hq0).2 (hpa.trans hq.1)⟩⟩
  have hm : MonotoneOn (fun q => V R p q t) (Icc a b) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro q hq
      exact (VaryingBComparison.V_hasDerivAt_q hp (hcoeff hq).1 htframe).continuousAt.continuousWithinAt
    · intro q hq
      exact VaryingBComparison.V_hasDerivAt_q hp (hcoeff (Ioo_subset_Icc_self hq)).1 htframe
    · intro q hq
      exact (mul_nonneg (by norm_num : (0:ℝ)≤614/140625) ht.1).trans
        (D_small_nonnegative (hcoeff (Ioo_subset_Icc_self hq)).2 ht)
  exact hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab

theorem H_tangent {k t : ℝ} (hk : k∈Icc (2/3:ℝ) (187/250:ℝ))
    (ht : t∈Icc 0 frameCap) : V R k 1 t≤(593/500)*t := by
  have hk0 : 0<k := by linarith [hk.1]
  have hk1 : k≤1 := by linarith [hk.2]
  have hd := (Curvature.restricted_constants .middle hk0 hk1
    (show k≤(Curvature.ratioEnd .middle:ℝ)*1 by simpa [Curvature.ratioEnd] using hk.2)).2
  norm_num [Curvature.D0End] at hd
  have he : Vd R k 1 0=Curvature.slopeZero k 1 := by
    simp only [Vd,mixedNDerivative,Curvature.slopeZero,normD1,Real.sin_zero,Real.cos_zero,
      neg_mul,sub_zero,mul_one]
    ring
  have hh := V_tangent_zero hk0 hk1 (by linarith [hk.1]) ht
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hd.le ht.1)

theorem B_dominates_H (atG : Bool) {s z t : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (ht : t∈Icc 0 frameCap) :
    V R (Explicit.k .low z) 1 t≤
      V R (Source.pWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s 2)
        (Source.qWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s 2) t := by
  have hzf := r41_low_dom hz
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  have hm := Explicit.low_tilted hz
  have hp := (Explicit.secant_bounds .low atG hzf hs).1
  have hpone : 1≤Source.pWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s 2 := by
    cases atG
    · change 1 ≤ min (secant (Explicit.l .low z) s) (Explicit.m .low z)
      exact le_min (by linarith) (by linarith [hm.1])
    · change 1 ≤ min (Explicit.l .low z) (Explicit.m .low z)
      exact le_min (by linarith) (by linarith [hm.1])
  obtain ⟨hpp,hpq,hqp⟩ := Explicit.ordered_pair_domain .low atG hzf hs 2
  have hh := H_tangent ⟨hklo.le,hkhi⟩ ht
  have hb := V_chord_lower hpp hpq hqp ht
  have hscale := mul_le_mul_of_nonneg_right hpone ht.1
  linarith only [hh,hb,hscale,ht.1]

theorem original (atG : Bool) {s z t : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (ht : t∈Icc 0 (1/5:ℝ)) (i : Fin 4) :
    V R (Explicit.k .low z) 1 t≤
      V R (Source.pWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s i)
        (Source.qWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s i) t := by
  have hzf := r41_low_dom hz
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  have hlG : 1≤lambdaG atG (Explicit.l .low z) s := by
    have hp := (Explicit.secant_bounds .low atG hzf hs).1
    cases atG <;> simp [lambdaG] <;> linarith
  have hG := (Explicit.family_coefficient_domain .low atG hzf hs).2.1
  fin_cases i
  · simp [Source.pWeights,Source.qWeights]
  · simpa [Source.pWeights,Source.qWeights] using
      larger_coefficient (by linarith : 0<Explicit.k .low z)
        (by linarith : Explicit.k .low z≤1) hlG hG.2 ht
  · exact B_dominates_H atG hz hs ⟨ht.1,by dsimp [frameCap]; linarith [ht.2]⟩
  · simp [Source.pWeights,Source.qWeights]

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowNegativeComparison
end
end
end
