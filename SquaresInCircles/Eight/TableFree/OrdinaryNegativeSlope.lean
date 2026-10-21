module

public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeEnvelope

/-!
# Quantitative negative-angle growth and the zero-angle tangent

Uncompiled source draft. The derivative is decreasing with angle, so its
whole-interval lower bound is the actual far endpoint. At that endpoint
the normalized coefficient ratio is monotone, and its intrinsic endpoint
`2/3` has a direct rational square reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.OrdinaryNegativeSlope
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope VaryingBFunctions VaryingBComparison

def Vd (R p q t : ℝ) : ℝ := mixedNDerivative R p q 0 t

theorem V_hasDerivAt {R p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) : HasDerivAt (V R p q) (Vd R p q t) t := by
  simpa only [mixedBlock_zero_left] using mixedN_hasDerivAt (R := R) hp hq
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht

theorem Vd_hasDerivAt {R p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : t∈Icc 0 frameCap) :
    HasDerivAt (Vd R p q) (curvature R p q (-t)-q*Real.cos t) t := by
  simpa only [zero_sub] using mixedNDerivative_hasDerivAt (R := R) hp hq
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht

theorem Vd_antitone {R p q : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    AntitoneOn (Vd R p q) (Icc 0 frameCap) := by
  have hq := hp.trans_le hpq
  apply antiOn_of_hasDeriv_nonpos
  · intro t ht
    exact (Vd_hasDerivAt hp hq ht).continuousAt.continuousWithinAt
  · intro t ht
    exact Vd_hasDerivAt hp hq (Ioo_subset_Icc_self ht)
  · intro t ht
    have h := mixedN_second_lt hR hQ hp hpq hqp
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) (Ioo_subset_Icc_self ht)
    simp only [zero_sub] at h
    linarith

theorem normalized_fraction_mono {a b u : ℝ}
    (ha : 0≤a) (hab : a≤b) (hb : b≤1) (hu : u∈Icc 0 frameCap) :
    a/root a u≤b/root b u := by
  have hb0 : 0≤b := ha.trans hab
  have hA := root_pos a hu
  have hB := root_pos b hu
  have hA2 := root_sq a hu
  have hB2 := root_sq b hu
  have hprod : a*b≤a := by nlinarith [mul_nonneg ha (sub_nonneg.mpr hb)]
  have hmul := mul_le_mul_of_nonneg_left hu.2 (mul_nonneg ha hb0)
  have hfactor : 0≤a+b-2*a*b*u := by
    dsimp [frameCap] at hmul
    nlinarith
  have hnon := mul_nonneg (sub_nonneg.mpr hab) hfactor
  have he : (b*root a u)^2-(a*root b u)^2=(b-a)*(a+b-2*a*b*u) := by
    calc
      (b*root a u)^2-(a*root b u)^2=b^2*(root a u)^2-a^2*(root b u)^2 := by ring
      _=(b-a)*(a+b-2*a*b*u) := by rw [hA2,hB2]; ring
  have hcross : a*root b u≤b*root a u := by
    rw [← he] at hnon
    nlinarith [mul_nonneg ha hB.le,mul_nonneg hb0 hA.le]
  exact (div_le_div_iff₀ hA hB).2 hcross

theorem endpoint_normalized_slope :
    (2/3 : ℝ)< -Real.sin frameCap+
      Real.sqrt qCap*(2/3)*Real.cos frameCap/root (2/3) (Real.sin frameCap) := by
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hN := root_pos (2/3) (sin_mem hh)
  have hN2 := root_sq (2/3) (sin_mem hh)
  have hNhi : root (2/3) (Real.sin frameCap)<1913/2500 := by
    nlinarith [cap_sin_lower]
  have hc := (transport_trig hh).1
  have hs := (transport_trig hh).2.2.2.1
  have hC0 : 0<Real.cos frameCap := by linarith
  have hnum1 := mul_lt_mul_of_pos_right sqrt_cap_lower hC0
  have hnum2 := mul_lt_mul_of_pos_left hc (by norm_num : (0:ℝ)<19787/10000)
  have hupper := mul_lt_mul_of_pos_left hNhi
    (show 0<(2/3 : ℝ)+Real.sin frameCap by linarith [(transport_trig hh).2.2.1])
  have hupper2 := mul_lt_mul_of_pos_right hs (by norm_num : (0:ℝ)<1913/2500)
  have hcross : ((2/3 : ℝ)+Real.sin frameCap)*root (2/3) (Real.sin frameCap)<
      Real.sqrt qCap*(2/3)*Real.cos frameCap := by nlinarith
  have hdiv := (lt_div_iff₀ hN).2 hcross
  linarith

theorem Vd_normalized {R p q t : ℝ} (hq : 0<q) :
    Vd R p q t=q*(-Real.sin t+
      R*(p/q)*Real.cos t/root (p/q) (Real.sin t)) := by
  dsimp [Vd,mixedNDerivative,normD1,pairProduct]
  rw [zero_sub,Real.cos_neg,negativeNorm_normalized hq]
  field_simp [hq.ne']
  ring

theorem Vd_lower {p q t : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (ht : t∈Icc 0 frameCap) :
    (2/3)*q<Vd (Real.sqrt qCap) p q t := by
  have hq := hp.trans_le hpq
  have hqp : q≤2*p := by linarith
  have hrlo : 2/3≤p/q := (le_div_iff₀ hq).2 hratio
  have hrhi : p/q≤1 := (div_le_one hq).2 hpq
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hfrac := normalized_fraction_mono (by norm_num : (0:ℝ)≤2/3) hrlo hrhi (sin_mem hh)
  have hmul := mul_le_mul_of_nonneg_left hfrac
    (show 0≤Real.sqrt qCap*Real.cos frameCap by
      exact mul_nonneg (Real.sqrt_nonneg _) (by linarith [(transport_trig hh).1]))
  have hnorm : (2/3 : ℝ)< -Real.sin frameCap+
      Real.sqrt qCap*(p/q)*Real.cos frameCap/root (p/q) (Real.sin frameCap) := by
    have hbase := endpoint_normalized_slope
    nlinarith only [hmul,hbase]
  have hend : (2/3)*q<Vd (Real.sqrt qCap) p q frameCap := by
    rw [Vd_normalized hq]
    nlinarith only [mul_lt_mul_of_pos_left hnorm hq]
  have hanti := Vd_antitone (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hp hpq hqp
  exact hend.trans_le (hanti ht hh ht.2)

theorem V_growth {p q t u : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (ht : t∈Icc 0 frameCap)
    (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    (2/3)*q*(u-t)≤V (Real.sqrt qCap) p q u-V (Real.sqrt qCap) p q t := by
  have hq := hp.trans_le hpq
  exact derivative_reserve
    (fun x hx => (V_hasDerivAt hp hq hx).continuousAt.continuousWithinAt)
    (fun x hx => V_hasDerivAt hp hq (Ioo_subset_Icc_self hx))
    (fun x hx => (Vd_lower hp hpq hratio (Ioo_subset_Icc_self hx)).le) ht hu htu

theorem V_tangent_zero {p q t : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (ht : t∈Icc 0 frameCap) :
    V (Real.sqrt qCap) p q t≤Vd (Real.sqrt qCap) p q 0*t := by
  have hq := hp.trans_le hpq
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hp hpq hqp
  have h := derivative_reserve
    (f := fun x => -V (Real.sqrt qCap) p q x)
    (df := fun x => -Vd (Real.sqrt qCap) p q x)
    (k := -Vd (Real.sqrt qCap) p q 0)
    (fun x hx => (V_hasDerivAt hp hq hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (V_hasDerivAt hp hq (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (hanti hz (Ioo_subset_Icc_self hx) hx.1.le)) hz ht ht.1
  simp only [V_zero,neg_zero,sub_zero] at h
  linarith

end SquaresInCircles.Eight.TableFree.OrdinaryNegativeSlope
