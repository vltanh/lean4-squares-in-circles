module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Data

/-!
# Whole-interval domains for the reference BT3 weights

Uncompiled Section 4. The low quadratic ratios use their exact endpoint
chords and completed square. The rotating coefficient uses the stated
Taylor polynomials: the low upper polynomial has negative second
derivative, and the high upper polynomial is convex. No angular
subdivision is introduced by these coefficient estimates.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

namespace Explicit
theorem low_ranges {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    k .low z∈Icc (2/3:ℝ) (163/240) ∧
    l .low z∈Icc (513/500:ℝ) (533/500) ∧
    (241/250:ℝ)<m .low z ∧ m .low z<1181/1000 := by
  have hchord := mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
  dsimp [k,l,m]
  refine ⟨⟨by linarith [hz.1],by linarith [hz.2]⟩,
    ⟨by linarith [hz.2],by linarith [hz.1]⟩,?_,?_⟩
  · nlinarith [hz.2]
  · nlinarith [sq_nonneg (z-(1/10)/(2*(769/200)))]

theorem low_ratios {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    (11/20)*l .low z<k .low z ∧ k .low z<(2/3)*l .low z ∧
    (47/50)*l .low z<m .low z ∧ m .low z<(113/100)*l .low z ∧ k .low z<m .low z := by
  have hb := low_ranges hz
  have hchord := mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
  refine ⟨by linarith [hb.1.1,hb.2.1.2],by linarith [hb.1.2,hb.2.1.1],?_,?_,
    by linarith [hb.1.2,hb.2.2.1]⟩
  · dsimp [l,m]
    nlinarith [hz.2]
  · dsimp [l,m]
    nlinarith [sq_nonneg (z-(351/1250)/(2*(769/200)))]

theorem high_k_derivative (z : ℝ) :
    HasDerivAt (k .high) (1/5+(9/5)*(z-1/5)-(39/10)*(z-1/5)^2) z := by
  have hd : Differentiable ℝ (k .high) := by dsimp [k]; fun_prop
  convert (hd z).hasDerivAt using 1
  simp (disch := fun_prop) [k]
  ring

theorem high_k_monotone : MonotoneOn (k .high) (Icc (1/4:ℝ) (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg (by dsimp [k]; fun_prop) (fun z _ => high_k_derivative z)
  intro z hz
  have ht : z-1/5∈Icc (1/20:ℝ) (1/2) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  nlinarith [mul_nonneg ht.1.le (show 0≤1/2-(z-1/5) by linarith [ht.2])]

theorem high_ranges {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    k .high z∈Icc (55047/80000:ℝ) (1677/2000) ∧
    l .high z∈Icc (4141/4000:ℝ) (799/750) ∧
    (8579/10000:ℝ)<m .high z ∧ m .high z≤24/25 := by
  have hk0 := high_k_monotone (show (1/4:ℝ)∈Icc (1/4:ℝ) (7/10) by norm_num) hz hz.1
  have hk1 := high_k_monotone hz (show (7/10:ℝ)∈Icc (1/4:ℝ) (7/10) by norm_num) hz.2
  norm_num [k] at hk0 hk1
  have ht : z-1/5∈Icc (1/20:ℝ) (1/2) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hr : z-1/4∈Icc (0:ℝ) (9/20) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hlchord := mul_nonneg (show 0≤z-1/5-1/20 by linarith [ht.1])
    (show 0≤1/2-(z-1/5) by linarith [ht.2])
  have hmchord := mul_nonneg hr.1 (sub_nonneg.mpr hr.2)
  refine ⟨⟨hk0,hk1⟩,?_,?_,?_⟩
  · dsimp [l]
    exact ⟨by nlinarith [ht.1],by nlinarith [sq_nonneg (z-1/5-11/30)]⟩
  · dsimp [m]
    nlinarith [sq_nonneg (z-1/4-7/24)]
  · dsimp [m]
    nlinarith [hr.1]

theorem high_ratios {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    (659/1000)*l .high z<k .high z ∧ k .high z<(41/50)*l .high z ∧
    (4/5)*l .high z<m .high z ∧ m .high z<(129/125)*l .high z ∧ m .high z<l .high z := by
  have hb := high_ranges hz
  have hh := NegativeAPositiveTD.Explicit.high_ratio_lower
    (show z∈Icc (1/5:ℝ) (7/10) from ⟨by linarith [hz.1],hz.2⟩)
  have hkl : (659/1000)*l .high z<k .high z := by
    simpa [k,l,NegativeAPositiveTD.Explicit.k,NegativeAPositiveTD.Explicit.l,
      NegativeAPositiveTD.Explicit.highKAt,NegativeAPositiveTD.Explicit.highLAt] using hh
  exact ⟨hkl,by linarith [hb.1.2,hb.2.1.1],by linarith [hb.2.1.2,hb.2.2.1],
    by linarith [hb.2.1.1,hb.2.2.2],by linarith [hb.2.1.1,hb.2.2.2]⟩

theorem high_ratio_late {z : ℝ} (hz : z∈Icc (1/3:ℝ) (7/10:ℝ)) :
    m .high z<(23/25)*l .high z := by
  have hb := high_ranges (show z∈Icc (1/4:ℝ) (7/10) from ⟨by linarith [hz.1],hz.2⟩)
  have hr : z-1/4∈Icc (1/12:ℝ) (9/20) := ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hprod := mul_nonneg (show 0≤z-1/4-1/12 by linarith [hr.1])
    (show 0≤9/20-(z-1/4) by linarith [hr.2])
  have hm : m .high z≤91/100 := by dsimp [m]; nlinarith [hr.1,hr.2]
  linarith [hb.2.1.1]

theorem positive (f : Certificate.Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    0<k f z ∧ 1023/1000<l f z ∧ 0<m f z := by
  cases f
  · have hb := low_ranges hz
    exact ⟨by linarith [hb.1.1],by linarith [hb.2.1.1],by linarith [hb.2.2.1]⟩
  · have hb := high_ranges hz
    exact ⟨by linarith [hb.1.1],by linarith [hb.2.1.1],by linarith [hb.2.2.1]⟩
end Explicit

namespace Certificate
def rotationLo (f : Family) : ℚ[X] := m f*(PositiveTD.Certificate.C10+
  C (293/1000)*PositiveTD.Certificate.S11)
def rotationHi (f : Family) : ℚ[X] := m f*(PositiveTD.Certificate.C12+
  C (293/1000)*PositiveTD.Certificate.S9)
def highDifference : ℚ[X] := rotationLo .high-k .high

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_rotation_certificate :
    WholeIntervalPolynomial.centered 0 (1/4) (rotationLo .low)=
      WholeIntervalPolynomial.expansion 14 (WholeIntervalPolynomial.centered 0 (1/4) (rotationLo .low)) ∧
    (2009/2000:ℚ)<WholeIntervalPolynomial.lowerOn 14 0 (1/4) (rotationLo .low) ∧
    WholeIntervalPolynomial.centered 0 (1/4) (rotationHi .low).derivative.derivative=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered 0 (1/4) (rotationHi .low).derivative.derivative) ∧
    WholeIntervalPolynomial.upperOn 14 0 (1/4) (rotationHi .low).derivative.derivative<-(44/5:ℚ) ∧
    (rotationHi .low).eval 0=59/50 ∧ (rotationHi .low).derivative.eval 0=22287/50000 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_rotation_certificate :
    WholeIntervalPolynomial.centered (1/4) (7/10) (rotationLo .high)=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered (1/4) (7/10) (rotationLo .high)) ∧
    (2017/2500:ℚ)<WholeIntervalPolynomial.lowerOn 14 (1/4) (7/10) (rotationLo .high) ∧
    WholeIntervalPolynomial.centered (1/4) (7/10) highDifference.derivative=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered (1/4) (7/10) highDifference.derivative) ∧
    WholeIntervalPolynomial.upperOn 14 (1/4) (7/10) highDifference.derivative<-(61/500:ℚ) ∧
    (829/100000:ℚ)<highDifference.eval (7/10) ∧
    WholeIntervalPolynomial.centered (1/4) (7/10) (rotationHi .high).derivative.derivative=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered (1/4) (7/10) (rotationHi .high).derivative.derivative) ∧
    (111/100:ℚ)<WholeIntervalPolynomial.lowerOn 14 (1/4) (7/10) (rotationHi .high).derivative.derivative ∧
    (rotationHi .high).eval (1/4)<499873/500000 ∧
    (rotationHi .high).eval (7/10)<211699/250000 := by decide
end Certificate

namespace Explicit
open Certificate (Family)

theorem rotation_bounds (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    aeval z (Certificate.rotationLo f)≤c f z ∧ c f z≤aeval z (Certificate.rotationHi f) := by
  have ht := PositiveTD.Certificate.taylor_bounds (frame_domain f hz)
  have hm := (positive f hz).2.2
  have hlo := mul_le_mul_of_nonneg_left
    (show aeval z PositiveTD.Certificate.C10+(293/1000)*aeval z PositiveTD.Certificate.S11≤
      Real.cos z+(293/1000)*Real.sin z by linarith [ht.2.2.2.2.1,ht.2.1]) hm.le
  have hhi := mul_le_mul_of_nonneg_left
    (show Real.cos z+(293/1000)*Real.sin z≤
      aeval z PositiveTD.Certificate.C12+(293/1000)*aeval z PositiveTD.Certificate.S9 by
        linarith [ht.2.2.2.2.2,ht.2.2.1]) hm.le
  simpa [Certificate.rotationLo,Certificate.rotationHi,c,PositiveBT3.tilted,PositiveTD.eta] using ⟨hlo,hhi⟩

theorem low_rotation_upper {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    aeval z (Certificate.rotationHi .low)<149/125 := by
  let p := Certificate.rotationHi .low
  have hc := Certificate.low_rotation_certificate
  have hsecond (x : ℝ) (hx : x∈Icc 0 (1/4:ℝ)) : aeval x p.derivative.derivative<-(44/5:ℝ) :=
    WholeIntervalPolynomial.upper_on_interval (by norm_num) hc.2.2.1 hc.2.2.2.1 hx
  have hDanti : AntitoneOn (fun x : ℝ => aeval x p.derivative+(44/5)*x) (Icc 0 (1/4:ℝ)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => ((CenteredMonomialBounds.aeval_hasDerivAt p.derivative x).add
        ((hasDerivAt_id x).const_mul (44/5))).continuousAt.continuousWithinAt)
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt p.derivative x).add
        ((hasDerivAt_id x).const_mul (44/5)))
    intro x hx
    linarith [hsecond x (Ioo_subset_Icc_self hx)]
  have hD (x : ℝ) (hx : x∈Icc 0 (1/4:ℝ)) : aeval x p.derivative≤22287/50000-(44/5)*x := by
    have hh := hDanti (show (0:ℝ)∈Icc 0 (1/4:ℝ) by norm_num) hx hx.1
    have he : aeval (0:ℝ) p.derivative=22287/50000 := by exact_mod_cast hc.2.2.2.2.2
    simpa only [he,mul_zero,add_zero,le_sub_iff_add_le] using hh
  have hanti : AntitoneOn (fun x : ℝ => aeval x p-(22287/50000)*x+(22/5)*x^2)
      (Icc 0 (1/4:ℝ)) := by
    apply antiOn_of_hasDeriv_nonpos
      (by fun_prop)
      (fun x _ => ((CenteredMonomialBounds.aeval_hasDerivAt p x).sub
        ((hasDerivAt_id x).const_mul (22287/50000))).add
        (((hasDerivAt_id x).pow 2).const_mul (22/5)))
    intro x hx
    have hh := hD x (Ioo_subset_Icc_self hx)
    simp only [pow_one]
    linarith
  have hh := hanti (show (0:ℝ)∈Icc 0 (1/4:ℝ) by norm_num) hz hz.1
  have he : aeval (0:ℝ) p=59/50 := by exact_mod_cast hc.2.2.2.2.1
  simp only [he,mul_zero,zero_pow,sub_zero,add_zero] at hh
  nlinarith [sq_nonneg (z-(22287/50000)/(2*(22/5)))]

theorem low_rotation {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) : 1<c .low z ∧ c .low z<6/5 := by
  have hc := Certificate.low_rotation_certificate
  have hlo := WholeIntervalPolynomial.positive_on_interval (by norm_num) hc.1 hc.2.1 hz
  have hb := rotation_bounds .low hz
  exact ⟨by linarith [hb.1],by linarith [hb.2,low_rotation_upper hz]⟩

theorem high_rotation {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10:ℝ)) :
    (2017/2500:ℝ)<c .high z ∧ k .high z<c .high z ∧ c .high z<1 := by
  have hc := Certificate.high_rotation_certificate
  have hlo := WholeIntervalPolynomial.positive_on_interval (by norm_num) hc.1 hc.2.1 hz
  have hdiff : AntitoneOn (fun z : ℝ => aeval z Certificate.highDifference)
      (Icc (1/4:ℝ) (7/10)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt Certificate.highDifference z).continuousAt.continuousWithinAt)
      (fun z _ => CenteredMonomialBounds.aeval_hasDerivAt Certificate.highDifference z)
    intro z hz
    have hh := WholeIntervalPolynomial.upper_on_interval (by norm_num)
      hc.2.2.1 hc.2.2.2.1 (Ioo_subset_Icc_self hz)
    linarith
  have hright : (829/100000:ℝ)<aeval (7/10:ℝ) Certificate.highDifference := by
    exact_mod_cast hc.2.2.2.2.1
  have hmin := hdiff hz (show (7/10:ℝ)∈Icc (1/4:ℝ) (7/10) by norm_num) hz.2
  have hconc : ConcaveOn ℝ (Icc (1/4:ℝ) (7/10))
      (fun x : ℝ => 1-aeval x (Certificate.rotationHi .high)) := by
    apply concave_of_deriv2
      (fun x _ => (hasDerivAt_const x (1:ℝ)).sub
        (CenteredMonomialBounds.aeval_hasDerivAt (Certificate.rotationHi .high) x))
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt (Certificate.rotationHi .high).derivative x).neg)
    intro x hx
    have hh := WholeIntervalPolynomial.positive_on_interval (by norm_num)
      hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hx
    linarith
  have hleft : 0<1-aeval (1/4:ℝ) (Certificate.rotationHi .high) := by
    have hh : aeval (1/4:ℝ) (Certificate.rotationHi .high)<499873/500000 :=
      by exact_mod_cast hc.2.2.2.2.2.2.2.1
    linarith
  have hright' : 0<1-aeval (7/10:ℝ) (Certificate.rotationHi .high) := by
    have hh : aeval (7/10:ℝ) (Certificate.rotationHi .high)<211699/250000 :=
      by exact_mod_cast hc.2.2.2.2.2.2.2.2
    linarith
  have hupper := concave_gt_of_endpoints hconc hz hleft hright'
  have hb := rotation_bounds .high hz
  simp only [Certificate.highDifference,map_sub,k_eval] at hmin hright
  exact ⟨hlo.trans_le hb.1,by linarith [hb.1],by linarith [hb.2]⟩

end Explicit
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
