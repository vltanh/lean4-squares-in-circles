module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2Polynomial

/-!
# The prescribed joint-negative coefficient domains

Uncompiled transcription of Section 2 of the scalar companion. The
degree-six k family is increasing by its one centered derivative
certificate. The low tilted coefficient decreases, and its two actual
endpoint values give the stronger low-row coefficient bound.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Explicit
open Candidate Secondary Polynomial Certificate (Row)
open PowerTailBounds DirectedPowerBounds

def tiltFactor (z : ℝ) : ℝ := Real.cos z+eta*Real.sin z
def tiltSlope (z : ℝ) : ℝ := -Real.sin z+eta*Real.cos z

theorem tiltFactor_derivative (z : ℝ) : HasDerivAt tiltFactor (tiltSlope z) z := by
  simpa [tiltFactor,tiltSlope] using (Real.hasDerivAt_cos z).add ((Real.hasDerivAt_sin z).const_mul eta)
theorem tiltSlope_derivative (z : ℝ) : HasDerivAt tiltSlope (-tiltFactor z) z := by
  convert (Real.hasDerivAt_sin z).neg.add ((Real.hasDerivAt_cos z).const_mul eta) using 1
  · rfl
  · dsimp [tiltSlope,tiltFactor]; ring

theorem tiltFactor_bounds {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (24/25:ℝ)<tiltFactor z ∧ tiltFactor z<(209/200:ℝ) := by
  have hpos (t : ℝ) (ht : t∈Icc 0 frameCap) : 0<tiltFactor t := by
    have hh := transport_trig ht
    dsimp [tiltFactor,eta]
    linarith [hh.1,hh.2.2.1]
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) tiltFactor :=
    concave_of_deriv2 (fun t _ => tiltFactor_derivative t)
      (fun t _ => tiltSlope_derivative t) (fun t ht => neg_nonpos.mpr (hpos t ht).le)
  have hleft : (24/25:ℝ)<tiltFactor 0 := by norm_num [tiltFactor]
  have hright : (24/25:ℝ)<tiltFactor frameCap := by
    have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor
      (show (7/10:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    norm_num [NegativeAPositiveTD.NegativeSlope.sinLo,NegativeAPositiveTD.NegativeSlope.cosLo,
      PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,
      PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
    dsimp [tiltFactor,eta,frameCap]
    linarith [ht.1,ht.2.2.1]
  refine ⟨concave_gt_of_endpoints hconc hz hleft hright,?_⟩
  have hid := Real.sin_sq_add_cos_sq z
  have hsq := sq_nonneg (eta*Real.cos z-Real.sin z)
  have hp := hpos z hz
  dsimp [tiltFactor,eta] at ⊢ hp hsq
  nlinarith

theorem tiltFactor_low {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    1≤tiltFactor z ∧ tiltSlope z≤eta := by
  have ht := transport_trig (show z∈Icc 0 frameCap from ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩)
  have hc := cos_lower_two hz.1
  have hzs : 0≤z*(eta-z/2-eta*z^2/6) := by
    apply mul_nonneg hz.1
    have h2 := pow_le_pow_left₀ hz.1 hz.2 2
    norm_num [eta] at ⊢
    nlinarith
  have hs3 : z-z^3/6≤Real.sin z := sin_lower_three hz.1
  constructor
  · dsimp [tiltFactor]
    nlinarith
  · dsimp [tiltSlope,eta]
    linarith [ht.2.2.1,Real.cos_le_one z]

def highDerivative : ℚ[X] := DirectedPowerBounds.shift (17/40) (Certificate.k .full).derivative

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem high_derivative_certificate :
    highDerivative=C (highDerivative.coeff 0)+tail highDerivative 1 5 ∧
      (23/1000:ℚ)<highDerivative.coeff 0-PowerTailBounds.norm highDerivative 1 5 (11/40) := by
  decide

theorem high_k_derivative_positive {z : ℝ} (hz : z∈Icc (3/20:ℝ) (7/10)) :
    (23/1000:ℝ)<aeval z (Certificate.k .full).derivative := by
  have hu : |z-(17/40:ℝ)|≤(11/40:ℝ) := by
    apply abs_le.mpr
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hh := DirectedPowerBounds.constant_lower high_derivative_certificate.1 hu
  have hr : (23/1000:ℝ)<(highDerivative.coeff 0:ℝ)-
      (PowerTailBounds.norm highDerivative 1 5 (11/40):ℝ) := by
    exact_mod_cast high_derivative_certificate.2
  have hid : aeval (z-(17/40:ℝ)) highDerivative=aeval z (Certificate.k .full).derivative := by
    simp [highDerivative]
  rw [hid] at hh
  exact hr.trans_le hh

theorem high_k_ranges {z : ℝ} (hz : z∈Icc (3/20:ℝ) (7/10)) :
    (13/20:ℝ)<k .full z ∧ k .full z<(751/1000:ℝ) := by
  have hm : MonotoneOn (k .full) (Icc (3/20:ℝ) (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt (Certificate.k .full) x).continuousAt.continuousWithinAt)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt (Certificate.k .full) x)
    intro x hx
    linarith [high_k_derivative_positive (Ioo_subset_Icc_self hx)]
  have hlo := hm (show (3/20:ℝ)∈Icc (3/20:ℝ) (7/10) by norm_num) hz hz.1
  have hhi := hm hz (show (7/10:ℝ)∈Icc (3/20:ℝ) (7/10) by norm_num) hz.2
  norm_num [k,Certificate.k] at hlo hhi
  exact ⟨by linarith,by linarith⟩

theorem c_derivative (r : Row) (z : ℝ) :
    HasDerivAt (c r) (if r=.low then -13/5+(28/5)*z else -9/10+(11/10)*z) z := by
  have hh := CenteredMonomialBounds.aeval_hasDerivAt (Certificate.c r) z
  cases r <;> simpa [c,Certificate.c] using hh

theorem c_antitone (r : Row) :
    AntitoneOn (c r) (Icc 0 (if r=.low then (3/20:ℝ) else frameCap)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun z _ => (c_derivative r z).continuousAt.continuousWithinAt)
    (fun z _ => c_derivative r z)
  intro z hz
  cases r <;> simp only [if_true,if_false,reduceCtorEq] at hz ⊢ <;>
    norm_num [frameCap] at hz <;> linarith [hz.2]

theorem low_c_ranges {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    c .low z∈Icc (1053/1000:ℝ) (69/50) := by
  have hm := c_antitone .low
  have hlo := hm hz (show (3/20:ℝ)∈Icc 0 (3/20:ℝ) by norm_num) hz.2
  have hhi := hm (show (0:ℝ)∈Icc 0 (3/20:ℝ) by norm_num) hz hz.1
  norm_num [c,Certificate.c] at hlo hhi
  exact ⟨hlo,hhi⟩

theorem high_c_ranges {z : ℝ} (hz : z∈Icc (3/20:ℝ) (7/10)) :
    c .full z∈Icc (158129/200000:ℝ) (25713/25000) := by
  have hz' : z∈Icc 0 frameCap := ⟨by linarith [hz.1],hz.2⟩
  have hlo := c_antitone .full hz' (show (7/10:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.2
  have hhi := c_antitone .full (show (3/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz' hz.1
  norm_num [c,Certificate.c] at hlo hhi
  exact ⟨hlo,hhi⟩

theorem low_m_derivative {z : ℝ} :
    HasDerivAt (m .low)
      ((-13/5+(28/5)*z)*tiltFactor z+c .low z*tiltSlope z) z := by
  simpa only [m,tilted,tiltFactor] using (c_derivative .low z).mul (tiltFactor_derivative z)

theorem low_m_antitone : AntitoneOn (m .low) (Icc (0:ℝ) (3/20)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun z _ => low_m_derivative.continuousAt.continuousWithinAt)
    (fun z _ => low_m_derivative)
  intro z hz
  have hc := low_c_ranges (Ioo_subset_Icc_self hz)
  have ht := tiltFactor_low (Ioo_subset_Icc_self hz)
  have hd : -13/5+(28/5)*z≤-(44/25:ℝ) := by linarith [hz.2]
  have hfirst := mul_le_mul_of_nonpos_left ht.1 (show -13/5+(28/5)*z≤0 by linarith)
  have hsecond := mul_le_mul_of_nonneg_left ht.2 (show 0≤c .low z by linarith [hc.1])
  have hthird := mul_le_mul_of_nonneg_right hc.2 (show 0≤eta by norm_num [eta])
  norm_num [eta] at hsecond hthird
  nlinarith

theorem low_m_ranges {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    (136/125:ℝ)<m .low z ∧ m .low z≤69/50 := by
  have hlo := low_m_antitone hz (show (3/20:ℝ)∈Icc 0 (3/20:ℝ) by norm_num) hz.2
  have hhi := low_m_antitone (show (0:ℝ)∈Icc 0 (3/20:ℝ) by norm_num) hz hz.1
  have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor
    (show (3/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  norm_num [NegativeAPositiveTD.NegativeSlope.sinLo,NegativeAPositiveTD.NegativeSlope.cosLo,
    PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
  norm_num [m,tilted,c,Certificate.c,eta] at hlo hhi
  exact ⟨by linarith [ht.1,ht.2.2.1],hhi⟩

theorem ranges (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    k r z∈Icc (13/20:ℝ) (751/1000) ∧ k r z≤c r z ∧ c r z<7/5 ∧
      k r z≤m r z ∧ m r z≤cap r z ∧ cap r z≤69/50 ∧
      (r≠.low → m r z<539/500) := by
  cases r
  · have hc := low_c_ranges hz
    have hm := low_m_ranges hz
    norm_num [k,Certificate.k,cap] at ⊢
    exact ⟨by linarith [hc.1],by linarith [hc.2],by linarith [hm.1],hm.2⟩
  · have hz' : z∈Icc (3/20:ℝ) (7/10) := ⟨hz.1,by norm_num [Certificate.right] at hz; linarith [hz.2]⟩
    have hk := high_k_ranges hz'
    have hc := high_c_ranges hz'
    have ht := tiltFactor_bounds (frame_domain .transition hz)
    have hm : (751/1000:ℝ)<m .transition z ∧ m .transition z<(539/500:ℝ) := by
      have hlow := mul_lt_mul_of_pos_left ht.1 (show 0<c .full z by linarith [hc.1])
      have hhigh := mul_lt_mul_of_pos_left ht.2 (show 0<c .full z by linarith [hc.1])
      change (751/1000:ℝ)<c .full z*tiltFactor z ∧
        c .full z*tiltFactor z<(539/500:ℝ)
      constructor <;> nlinarith [hc.1,hc.2]
    simpa [k,c,Certificate.k,Certificate.c,cap] using
      (show k .full z∈Icc (13/20:ℝ) (751/1000) ∧ k .full z≤c .full z ∧
        c .full z<7/5 ∧ k .full z≤m .transition z ∧ m .transition z≤539/500 ∧
        (539/500:ℝ)≤69/50 ∧ (Row.transition≠.low → m .transition z<539/500) from
        ⟨⟨hk.1.le,hk.2.le⟩,by linarith [hc.1],by linarith [hc.2],
          by linarith [hm.1],hm.2.le,by norm_num,fun _=>hm.2⟩)
  · have hk := high_k_ranges ⟨by norm_num [Certificate.left] at hz; linarith [hz.1],hz.2⟩
    have hc := high_c_ranges ⟨by norm_num [Certificate.left] at hz; linarith [hz.1],hz.2⟩
    have ht := tiltFactor_bounds (frame_domain .full hz)
    have hlow := mul_lt_mul_of_pos_left ht.1 (show 0<c .full z by linarith [hc.1])
    have hhigh := mul_lt_mul_of_pos_left ht.2 (show 0<c .full z by linarith [hc.1])
    have hm : (751/1000:ℝ)<m .full z ∧ m .full z<(539/500:ℝ) := by
      change (751/1000:ℝ)<c .full z*tiltFactor z ∧ c .full z*tiltFactor z<(539/500:ℝ)
      constructor <;> nlinarith [hc.1,hc.2]
    refine ⟨⟨hk.1.le,hk.2.le⟩,by linarith [hc.1],by linarith [hc.2],
      by linarith [hm.1],?_,?_,fun _=>hm.2⟩ <;> simp [cap] <;> linarith [hm.2]

theorem D_branch (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    (Certificate.diagonalD r=true → 1≤c r z) ∧
      (Certificate.diagonalD r=false → c r z≤1) := by
  cases r
  · have hh := low_c_ranges hz
    simp [Certificate.diagonalD]
    linarith [hh.1]
  · have hmono := c_antitone .transition (frame_domain .transition hz)
      (show (19/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.2
    norm_num [c,Certificate.c] at hmono
    simpa [Certificate.diagonalD] using hmono
  · have hmono := c_antitone .full (show (19/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
      (frame_domain .full hz) hz.1
    norm_num [c,Certificate.c] at hmono
    simpa [Certificate.diagonalD] using hmono

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Explicit
