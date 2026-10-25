module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2NegativeSlopes

/-!
# Eight squares: the prescribed joint-negative coefficient domains

The
degree-six k family is increasing by its one centered derivative
certificate. The low tilted coefficient decreases, and its two actual
endpoint values give the stronger low-row coefficient bound.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Explicit
open Candidate Secondary Polynomial
open Certificate (Row)
open PowerTailBounds DirectedPowerBounds

def tiltFactor (z : ℝ) : ℝ := Real.cos z+eta*Real.sin z
def tiltSlope (z : ℝ) : ℝ := -Real.sin z+eta*Real.cos z

theorem tiltFactor_derivative (z : ℝ) : HasDerivAt tiltFactor (tiltSlope z) z := by
  convert (Real.hasDerivAt_cos z).add ((Real.hasDerivAt_sin z).const_mul eta) using 1
  · rfl
  · dsimp [tiltSlope]
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
    have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor (t:=7/10) (by norm_num)
    norm_num [NegativeAPositiveTD.NegativeSlope.sinLo,NegativeAPositiveTD.NegativeSlope.cosLo,NegativeAPositiveTD.NegativeSlope.sinHi,NegativeAPositiveTD.NegativeSlope.cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
    dsimp [tiltFactor,eta,frameCap]
    linarith [ht.1,ht.2.2.1]
  refine ⟨concave_gt_of_endpoints hconc hz hleft hright,?_⟩
  have hid := Real.sin_sq_add_cos_sq z
  have hsq := sq_nonneg ((303/1000:ℝ)*Real.cos z-Real.sin z)
  have hp := hpos z hz
  dsimp [tiltFactor,eta] at ⊢ hp
  nlinarith

theorem tiltFactor_low {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    1≤tiltFactor z ∧ tiltSlope z≤eta := by
  have ht := transport_trig (show z∈Icc 0 frameCap from ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩)
  have hc := Real.one_sub_sq_div_two_le_cos (x:=z)
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  have hzs : 0≤z*((303/1000:ℝ)-z/2-(303/1000)*z^2/6) := by
    apply mul_nonneg hz.1
    linarith [hz.2]
  have hs3 : z-z^3/6≤Real.sin z := Real.sin_ge_sub_cube hz.1
  constructor
  · dsimp only [tiltFactor,eta]
    nlinarith
  · dsimp only [tiltSlope,eta]
    linarith [ht.2.2.1,Real.cos_le_one z]

def highDerivative : ℚ[X] := DirectedPowerBounds.shift (17/40) (Certificate.k .full).derivative

theorem high_derivative_certificate :
    highDerivative=C (highDerivative.coeff 0)+tail highDerivative 1 5 ∧
      (23/1000:ℚ)<highDerivative.coeff 0-PowerTailBounds.norm highDerivative 1 5 (11/40) := by
  have hE : highDerivative=C (227090007284743/1280000000000000)+C (396173824453/800000000000)*X+
      C (2992781577/80000000000)*X^2+C (556739253/1000000000)*X^3+C (41434123/100000000)*X^4+
      C (2746731/3125000)*X^5 := by
    apply Polynomial.funext
    intro x
    simp only [highDerivative,DirectedPowerBounds.shift,Certificate.k,eval_comp,derivative_add,
      derivative_sub,derivative_mul,derivative_C,derivative_X_pow,derivative_X,eval_add,eval_sub,
      eval_mul,eval_C,eval_X,eval_pow,zero_mul,zero_add,eval_zero,eval_one]
    push_cast
    ring
  rw [hE]
  refine ⟨?_,?_⟩
  · simp only [tail,Fin.sum_univ_five,coeff_add,coeff_C_mul,coeff_C,coeff_X_pow,
      coeff_X,Fin.val_zero,Fin.val_one,Fin.val_two]
    norm_num
    ring
  · simp only [PowerTailBounds.norm,Fin.sum_univ_five,coeff_add,coeff_C_mul,coeff_C,coeff_X_pow,
      coeff_X,Fin.val_zero,Fin.val_one,Fin.val_two]
    norm_num

theorem high_k_derivative_positive {z : ℝ} (hz : z∈Icc (3/20:ℝ) (7/10)) :
    (23/1000:ℝ)<aeval z (Certificate.k .full).derivative := by
  have hu : |z-(17/40:ℝ)|≤((11/40:ℚ):ℝ) := by
    apply abs_le.mpr
    push_cast
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hh := DirectedPowerBounds.constant_lower high_derivative_certificate.1 hu
  have hr : (23/1000:ℝ)<(highDerivative.coeff 0:ℝ)-
      (PowerTailBounds.norm highDerivative 1 5 (11/40):ℝ) := by
    have h' := Rat.cast_lt (K:=ℝ) |>.mpr high_derivative_certificate.2
    push_cast at h'
    exact h'
  have hid : aeval (z-(17/40:ℝ)) highDerivative=aeval z (Certificate.k .full).derivative := by
    rw [highDerivative,DirectedPowerBounds.shift_eval,
      show ((17/40:ℚ):ℝ)+(z-17/40)=z by push_cast; ring]
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
  have e1 : k .full (3/20)=1043387704139577/1600000000000000 := by norm_num [k,Certificate.k]
  have e2 : k .full (7/10)=37523719389789/50000000000000 := by norm_num [k,Certificate.k]
  rw [e1] at hlo
  rw [e2] at hhi
  exact ⟨by linarith,by linarith⟩

theorem c_derivative (r : Row) (z : ℝ) :
    HasDerivAt (c r) (if r=.low then -13/5+(28/5)*z else -9/10+(11/10)*z) z := by
  have hh := CenteredMonomialBounds.aeval_hasDerivAt (Certificate.c r) z
  refine hh.congr_deriv ?_
  cases r <;> simp [Certificate.c] <;> ring

theorem c_antitone (r : Row) :
    AntitoneOn (c r) (Icc 0 (if r=.low then (3/20:ℝ) else frameCap)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun z _ => (c_derivative r z).continuousAt.continuousWithinAt)
    (fun z _ => c_derivative r z)
  intro z hz
  cases r <;> simp only [ite_true,ite_false,reduceCtorEq] at hz ⊢ <;>
    norm_num [frameCap] at hz <;> linarith [hz.2]

theorem low_c_ranges {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    c .low z∈Icc (1053/1000:ℝ) (69/50) := by
  have hm : AntitoneOn (c .low) (Icc 0 (3/20:ℝ)) := by simpa using c_antitone .low
  have hlo := hm hz (show (3/20:ℝ)∈Icc 0 (3/20:ℝ) by norm_num) hz.2
  have hhi := hm (show (0:ℝ)∈Icc 0 (3/20:ℝ) by norm_num) hz hz.1
  have e1 : c .low (3/20)=1053/1000 := by norm_num [c,Certificate.c]
  have e2 : c .low 0=69/50 := by norm_num [c,Certificate.c]
  rw [e1] at hlo
  rw [e2] at hhi
  exact ⟨hlo,hhi⟩

theorem high_c_ranges {z : ℝ} (hz : z∈Icc (3/20:ℝ) (7/10)) :
    c .full z∈Icc (158129/200000:ℝ) (25713/25000) := by
  have hm : AntitoneOn (c .full) (Icc 0 frameCap) := by simpa using c_antitone .full
  have hz' : z∈Icc 0 frameCap := ⟨by linarith [hz.1],hz.2⟩
  have hlo := hm hz' (show (7/10:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.2
  have hhi := hm (show (3/20:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz' hz.1
  have e1 : c .full (7/10)=158129/200000 := by norm_num [c,Certificate.c]
  have e2 : c .full (3/20)=25713/25000 := by norm_num [c,Certificate.c]
  rw [e1] at hlo
  rw [e2] at hhi
  exact ⟨hlo,hhi⟩

theorem low_m_derivative {z : ℝ} :
    HasDerivAt (m .low)
      ((-13/5+(28/5)*z)*tiltFactor z+c .low z*tiltSlope z) z := by
  have hh := (c_derivative .low z).mul (tiltFactor_derivative z)
  simp only at hh
  exact hh

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
    (136/125:ℝ)< m .low z ∧ m .low z≤69/50 := by
  have hlo := low_m_antitone hz (show (3/20:ℝ)∈Icc 0 (3/20:ℝ) by norm_num) hz.2
  have hhi := low_m_antitone (show (0:ℝ)∈Icc 0 (3/20:ℝ) by norm_num) hz hz.1
  have ht := NegativeAPositiveTD.NegativeSlope.rational_taylor (t:=3/20) (by norm_num)
  norm_num [NegativeAPositiveTD.NegativeSlope.sinLo,NegativeAPositiveTD.NegativeSlope.cosLo,NegativeAPositiveTD.NegativeSlope.sinHi,NegativeAPositiveTD.NegativeSlope.cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4] at ht
  have e1 : m .low (3/20)=1053/1000*(Real.cos (3/20)+303/1000*Real.sin (3/20)) := by
    norm_num [m,tilted,c,Certificate.c,eta]
  have e2 : m .low 0=69/50 := by norm_num [m,tilted,c,Certificate.c]
  rw [e1] at hlo
  rw [e2] at hhi
  exact ⟨by linarith [ht.1,ht.2.2.1],hhi⟩

theorem ranges (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    k r z∈Icc (13/20:ℝ) (751/1000) ∧ k r z≤c r z ∧ c r z<7/5 ∧
      k r z≤ m r z ∧ m r z≤cap r z ∧ cap r z≤69/50 ∧
      (r≠.low → m r z<539/500) := by
  cases r
  · have hzl : z∈Icc (0:ℝ) (3/20) := by simpa [Certificate.left,Certificate.right] using hz
    have hc := low_c_ranges hzl
    have hm := low_m_ranges hzl
    have hk : k .low z=13/20 := by simp [k,Certificate.k]
    have hcap : cap .low z=m .low z := by simp [cap]
    rw [hk,hcap]
    refine ⟨by norm_num,by linarith [hc.1],by linarith [hc.2],by linarith [hm.1],le_rfl,hm.2,
      fun h => absurd rfl h⟩
  · have hz' : z∈Icc (3/20:ℝ) (19/100) := by simpa [Certificate.left,Certificate.right] using hz
    have hz7 : z∈Icc (3/20:ℝ) (7/10) := ⟨hz'.1,by linarith [hz'.2]⟩
    have hk := high_k_ranges hz7
    have hc := high_c_ranges hz7
    have ht := tiltFactor_bounds (frame_domain .transition hz)
    have hkk : k .transition z=k .full z := by simp [k,Certificate.k]
    have hcc : c .transition z=c .full z := by simp [c,Certificate.c]
    have hmm : m .transition z=c .full z*tiltFactor z := by
      simp only [m,tilted,tiltFactor,hcc]
    have hcap : cap .transition z=539/500 := by simp [cap]
    have hlow := mul_lt_mul_of_pos_left ht.1 (show 0<c .full z by linarith [hc.1])
    have hhigh := mul_lt_mul_of_pos_left ht.2 (show 0<c .full z by linarith [hc.1])
    rw [hkk,hcc,hmm,hcap]
    refine ⟨⟨hk.1.le,hk.2.le⟩,by linarith [hc.1],by linarith [hc.2],by nlinarith [hc.1],
      by nlinarith [hc.2],by norm_num,fun _ => by nlinarith [hc.2]⟩
  · have hz' : z∈Icc (19/100:ℝ) (7/10) := by simpa [Certificate.left,Certificate.right] using hz
    have hz7 : z∈Icc (3/20:ℝ) (7/10) := ⟨by linarith [hz'.1],hz'.2⟩
    have hk := high_k_ranges hz7
    have hc := high_c_ranges hz7
    have ht := tiltFactor_bounds (frame_domain .full hz)
    have hmm : m .full z=c .full z*tiltFactor z := by
      simp only [m,tilted,tiltFactor]
    have hcap : cap .full z=539/500 := by simp [cap]
    have hlow := mul_lt_mul_of_pos_left ht.1 (show 0<c .full z by linarith [hc.1])
    have hhigh := mul_lt_mul_of_pos_left ht.2 (show 0<c .full z by linarith [hc.1])
    rw [hmm,hcap]
    refine ⟨⟨hk.1.le,hk.2.le⟩,by linarith [hc.1],by linarith [hc.2],by nlinarith [hc.1],
      by nlinarith [hc.2],by norm_num,fun _ => by nlinarith [hc.2]⟩

theorem D_branch (r : Row) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    (Certificate.diagonalD r=true → 1≤c r z) ∧
      (Certificate.diagonalD r=false → c r z≤1) := by
  cases r
  · have hzl : z∈Icc (0:ℝ) (3/20) := by simpa [Certificate.left,Certificate.right] using hz
    have hh := low_c_ranges hzl
    simp only [Certificate.diagonalD,Bool.true_eq_false,false_imp_iff,and_true,forall_const]
    linarith [hh.1]
  · have hm : AntitoneOn (c .transition) (Icc 0 frameCap) := by simpa using c_antitone .transition
    have hz' : z∈Icc (3/20:ℝ) (19/100) := by simpa [Certificate.left,Certificate.right] using hz
    have hmono := hm (frame_domain .transition hz)
      (show (19/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz'.2
    norm_num [c,Certificate.c] at hmono
    simp only [Certificate.diagonalD,Bool.true_eq_false,false_imp_iff,and_true,forall_const]
    simp only [c,Certificate.c] at hmono ⊢
    norm_num at hmono ⊢
    linarith
  · have hm : AntitoneOn (c .full) (Icc 0 frameCap) := by simpa using c_antitone .full
    have hz' : z∈Icc (19/100:ℝ) (7/10) := by simpa [Certificate.left,Certificate.right] using hz
    have hmono := hm (show (19/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
      (frame_domain .full hz) hz'.1
    simp only [Certificate.diagonalD,Bool.false_eq_true,false_imp_iff,true_and,forall_const]
    simp only [c,Certificate.c] at hmono ⊢
    norm_num at hmono ⊢
    linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Explicit
