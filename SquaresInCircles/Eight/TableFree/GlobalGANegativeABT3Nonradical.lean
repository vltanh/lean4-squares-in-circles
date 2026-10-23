module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3ScalarData

/-!
# Nonradical lower bounds for the reference endpoints

Uncompiled Section 7. The low diagonal term uses its rational upper
constant. Every cosine-scaled positive baseline factor is proved
positive first, and the negative angular cost is multiplied by the
upper cosine polynomial, as required by its sign.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

namespace Certificate
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem baseline_factor_certificate (e : Curve) :
    WholeIntervalPolynomial.centered 0 (length e) (baseA e-lAt e)=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered 0 (length e) (baseA e-lAt e)) ∧
    0<WholeIntervalPolynomial.lowerOn 14 0 (length e) (baseA e-lAt e) := by
  cases e <;> decide

theorem elementary_lower (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) : aeval z (elementary f)≤NegativeABT3.nonradical f z := by
  have hzf := Explicit.frame_domain f hz
  have hm := (Explicit.positive f hz).2.2
  have ht := PositiveTD.Certificate.taylor_bounds hzf
  have hs := (transport_trig hzf).2.2.1
  have hc0 : 0≤Real.cos z := by linarith [(transport_trig hzf).1]
  have hD := PositiveTD.Certificate.diagonal_le_cbar
  have hS := NonnegativeTotals.Charges.sigma_upper
  cases f
  · have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
      (show (0:ℝ)≤3/2-(PositiveTD.Certificate.cbar:ℝ) by norm_num [PositiveTD.Certificate.cbar])
    have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
      (show (1/2:ℝ)+(293/1000)*(1-(PositiveTD.Certificate.cbar:ℝ))-
        (PositiveTD.Certificate.sigmabar:ℝ)≤0 by norm_num [PositiveTD.Certificate.cbar,PositiveTD.Certificate.sigmabar])
    have hdc := mul_le_mul_of_nonneg_right hD hc0
    have hds := mul_le_mul_of_nonneg_right hD hs
    have hss := mul_le_mul_of_nonneg_right hS hs
    have hinner : 1+(3/2-(PositiveTD.Certificate.cbar:ℝ))*aeval z PositiveTD.Certificate.C10+
        (1/2+(293/1000)*(1-(PositiveTD.Certificate.cbar:ℝ))-(PositiveTD.Certificate.sigmabar:ℝ))*
          aeval z PositiveTD.Certificate.S9≤
      1+(3/2-diagonal)*Real.cos z+(1/2+PositiveTD.eta*(1-diagonal)-PositiveTD.sigma)*Real.sin z := by
      dsimp [PositiveTD.eta]
      linarith
    have hprod := mul_le_mul_of_nonneg_left hinner hm.le
    simp only [elementary,NegativeABT3.nonradical,↓reduceIte,map_add,map_sub,map_mul,
      map_one,aeval_C,Explicit.k_eval,Explicit.l_eval,Explicit.m_eval]
    push_cast
    dsimp [PositiveTD.Certificate.etaQ]
    linarith
  · have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
      (show (1/2:ℝ)+3*(293/1000)/2-(PositiveTD.Certificate.sigmabar:ℝ)≤0 by
        norm_num [PositiveTD.Certificate.sigmabar])
    have hss := mul_le_mul_of_nonneg_right hS hs
    have hinner : 1+2*aeval z PositiveTD.Certificate.C10+
        (1/2+3*(293/1000)/2-(PositiveTD.Certificate.sigmabar:ℝ))*aeval z PositiveTD.Certificate.S9≤
      1+2*Real.cos z+(1/2+3*PositiveTD.eta/2-PositiveTD.sigma)*Real.sin z := by
      dsimp [PositiveTD.eta]
      linarith [ht.2.2.2.2.1]
    have hprod := mul_le_mul_of_nonneg_left hinner hm.le
    simp only [elementary,NegativeABT3.nonradical,↓reduceIte,map_add,map_sub,map_mul,
      map_one,aeval_C,Explicit.k_eval,Explicit.l_eval,Explicit.m_eval]
    push_cast
    dsimp [PositiveTD.Certificate.etaQ]
    linarith
end Certificate

namespace Analytic
open Certificate (Curve)

theorem cost_nonnegative (e : Curve) {z : ℝ} (hz : Domain e z) : 0≤cost e z := by
  have hl := (Explicit.positive (Certificate.family e) (domains e hz).1).2.1
  cases e <;> simp [cost,Certificate.selected] <;> linarith

theorem base_lower (e : Curve) {z : ℝ} (hz : Domain e z) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.baseA e)≤
      NegativeABT3.nonradical (Certificate.family e) z := by
  simpa [Certificate.baseA,aeval_comp] using Certificate.elementary_lower (Certificate.family e) (domains e hz).1

theorem base_factor_positive (e : Curve) {z : ℝ} (hz : Domain e z) :
    0<aeval (z-(Certificate.start e:ℝ)) (Certificate.baseA e)-Explicit.l (Certificate.family e) z := by
  have hh := WholeIntervalPolynomial.positive_on_interval (Certificate.length_positive e)
    (Certificate.baseline_factor_certificate e).1 (Certificate.baseline_factor_certificate e).2
    (native_domain e hz)
  simpa using hh

theorem extra_lower (e : Curve) {z : ℝ} (hz : Domain e z) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.extraA e)≤extra e z := by
  have hd := domains e hz
  have hn := PositiveTD.Certificate.taylor_bounds hd.2.2.1
  have hcoeff := cost_nonnegative e hz
  have hcost := mul_le_mul_of_nonneg_left (sub_le_sub_right hn.2.2.2.2.1 1) hcoeff
  by_cases he : e=.lowM
  · subst e
    have hrest := PositiveTD.Certificate.taylor_bounds hd.2.2.2
    have hcap := PositiveTD.Certificate.taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
    have hb := Explicit.positive .low hd.1
    have h₁ := mul_le_mul_of_nonneg_left
      (show aeval (frameCap-z) PositiveTD.Certificate.C10+aeval (frameCap-z) PositiveTD.Certificate.S11-1≤
        phi (frameCap-z)-1 by dsimp [phi]; linarith [hrest.2.1,hrest.2.2.2.2.1]) hb.1.le
    have h₂ := mul_le_mul_of_nonneg_left (sub_le_sub_right hcap.2.2.2.2.1 1)
      (show 0≤Explicit.l .low z by linarith [hb.2.1])
    simp [Certificate.extraA,extra,Certificate.family,aeval_comp,PositiveTD.Certificate.h,frameCap]
    exact add_le_add h₁ h₂
  · simp only [Certificate.extraA,if_neg he,extra,if_neg he,map_sub,map_mul,aeval_comp,
      native_cost,native_negativeAngle,aeval_C,map_one,native_z]
    split_ifs <;> norm_num [PositiveTD.Certificate.h,frameCap] <;> linarith

theorem scaled_extra_nonpositive (e : Curve) {z : ℝ} (he : Certificate.scaled e=true)
    (hz : Domain e z) : extra e z≤0 := by
  have hcost := mul_nonpos_of_nonneg_of_nonpos (cost_nonnegative e hz)
    (sub_nonpos.mpr (Real.cos_le_one (negativeAngle e z)))
  cases e <;> simp only [Certificate.scaled] at he <;> first | contradiction |
    simpa [extra,Certificate.separated] using hcost

theorem nonradical_lower (e : Curve) {z : ℝ} (hz : Domain e z) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.A e)≤nonradical e z := by
  have hd := domains e hz
  have ht := PositiveTD.Certificate.taylor_bounds hd.2.1
  have hc0 : 0≤Real.cos (angle e z) := by linarith [(transport_trig hd.2.1).1]
  have hbase := base_lower e hz
  have hextra := extra_lower e hz
  by_cases he : Certificate.scaled e=true
  · have hl : 0≤Explicit.l (Certificate.family e) z :=
      by linarith [(Explicit.positive (Certificate.family e) hd.1).2.1]
    have hpos := base_factor_positive e hz
    have h₁ := mul_le_mul ht.2.2.2.2.1 (sub_le_sub_right hbase (Explicit.l (Certificate.family e) z))
      hpos.le hc0
    have h₂ := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤(13/12)*Explicit.l (Certificate.family e) z by positivity)
    have he0 := scaled_extra_nonpositive e he hz
    have h₃ := mul_le_mul_of_nonpos_right ht.2.2.2.2.2 (hextra.trans he0)
    have h₄ := mul_le_mul_of_nonneg_left hextra hc0
    simp only [Certificate.A,if_pos he,nonradical,if_pos he,map_add,map_mul,map_sub,
      aeval_comp,native_angle,native_l,aeval_C]
    push_cast
    linarith
  · simp only [Certificate.A,if_neg he,nonradical,if_neg he,map_add]
    exact add_le_add hbase hextra

end Analytic
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
