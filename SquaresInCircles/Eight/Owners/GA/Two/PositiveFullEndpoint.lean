module

public import SquaresInCircles.Eight.Owners.GA.Two.PositiveHighTransfer

/-!
# Eight squares: the full-circle form of the six certified A/T endpoint inequalities

These statements expose the
stronger expressions proved by the same six polynomial numerators, so
the positive-A/TD0 proof can use its fourth ordinary circle block.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.TwoPositive.Certificate
open Polynomial Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveTD
open PositiveTD.Certificate

def fullEndpointBase (e : Endpoint) (t : ℝ) : ℝ :=
  endpointBase e t+clippedSupport 1 (cAt t)-fullSupport 1 (cAt t)

theorem full_H_identity (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+Real.cos t-1-
      R*(pairNorm (kAt t) (lAt t) 0+pairNorm (lAt t) (mAt e t) 0+
        pairNorm (kAt t) 1 (-t)+pairNorm (cAt t) 1 0)=
      fullEndpointBase e t+V R (kAt t) 1 t := by
  simp only [fullEndpointBase,endpointNonradical,endpointBase,baseline,fullSupport_pair,mAt,V]
  ring

theorem full_G_identity (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+lAt t*(Real.cos t-1)-
      R*(pairNorm (kAt t) 1 0+pairNorm (lAt t) (mAt e t) 0+
        pairNorm (kAt t) (lAt t) (-t)+pairNorm (cAt t) 1 0)=
      fullEndpointBase e t+V R (kAt t) (lAt t) t := by
  simp only [fullEndpointBase,endpointNonradical,endpointBase,baseline,fullSupport_pair,mAt,V]
  ring

theorem full_B_identity (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+max (lAt t) (mAt e t)*(Real.cos t-1)-
      R*(pairNorm (kAt t) 1 0+pairNorm (kAt t) (lAt t) 0+
        pairNorm (lAt t) (mAt e t) (-t)+pairNorm (cAt t) 1 0)=
      fullEndpointBase e t+
        V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t := by
  simp only [V,sorted_pair_norm]
  simp only [fullEndpointBase,endpointNonradical,endpointBase,baseline,fullSupport_pair,mAt]
  ring

theorem high_H_full_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<fullEndpointBase e t+V R (kAt t) 1 t := by
  have hn := high_norm_bounds e ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hA : aeval t (highA e+C10-1)≤endpointNonradical e t+Real.cos t-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [high_nonradical_lower e ht,htrig.2.2.2.2.1]
  have hrG : 0<aeval t highRG := by simpa [mass] using masses_positive e 1 ht
  have hrB : 0<aeval t (highRB e) := by simpa [mass] using masses_positive e 3 ht
  have hrH : 0<aeval t highRHminus := by simpa [mass] using masses_positive e 4 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrG hrB hrH hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.1 hA (highNH_positive e ht)
  simpa only [full_H_identity] using hp

theorem high_G_full_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<fullEndpointBase e t+V R (kAt t) (lAt t) t := by
  have hn := high_norm_bounds e ht
  have hr := high_ranges ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hcos := mul_le_mul_of_nonneg_left (sub_le_sub_right htrig.2.2.2.2.1 1)
    (show 0≤lAt t by linarith [hr.2.2.1])
  have hA : aeval t (highA e+highL*(C10-1))≤
      endpointNonradical e t+lAt t*(Real.cos t-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [high_nonradical_lower e ht]
  have hrH : 0<aeval t highRH := by simpa [mass] using masses_positive e 0 ht
  have hrB : 0<aeval t (highRB e) := by simpa [mass] using masses_positive e 3 ht
  have hrG : 0<aeval t highRGminus := by simpa [mass] using masses_positive e 5 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrH hrB hrG hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.1 hA (highNG_positive e ht)
  simpa only [full_G_identity] using hp

theorem high_B_full_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<fullEndpointBase e t+
      V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t := by
  have hn := high_norm_bounds e ht
  have hr := high_ranges ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hQ := high_Q_bound e ht
  have hQ0 : 0≤aeval t highQ := by
    have hlq := (le_max_left (lAt t) (mAt e t)).trans hQ
    linarith [hr.2.2.1]
  have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right htrig.2.2.2.2.1 1) hQ0
  have h₂ := mul_le_mul_of_nonpos_right hQ (sub_nonpos.mpr (Real.cos_le_one t))
  have hA : aeval t (highA e+highQ*(C10-1))≤endpointNonradical e t+
      max (lAt t) (mAt e t)*(Real.cos t-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [high_nonradical_lower e ht]
  have hrH : 0<aeval t highRH := by simpa [mass] using masses_positive e 0 ht
  have hrG : 0<aeval t highRG := by simpa [mass] using masses_positive e 1 ht
  have hrB : 0<aeval t (highRBminus e) := by simpa [mass] using masses_positive e 6 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrH hrG hrB hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.2.2.2.2 hn.2.2.1 hA (highNB_positive e ht)
  simpa only [full_B_identity] using hp

/-- All six polynomial certificates apply before the sorted D support
is restored. -/
theorem high_six_full_scalars_positive (e : Endpoint) {t : ℝ}
    (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<fullEndpointBase e t+V R (kAt t) 1 t ∧
    0<fullEndpointBase e t+V R (kAt t) (lAt t) t ∧
    0<fullEndpointBase e t+
      V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t :=
  ⟨high_H_full_positive e ht,high_G_full_positive e ht,high_B_full_positive e ht⟩

end SquaresInCircles.Eight.GlobalGA.TwoPositive.Certificate
