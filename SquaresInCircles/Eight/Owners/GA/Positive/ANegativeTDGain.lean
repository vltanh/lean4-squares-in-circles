module

public import SquaresInCircles.Eight.Owners.GA.Two.PositiveASupport

/-!
# Eight squares: the secant TD2 gain with a positive original A error

The signed tangent of T cancels algebraically. The remaining bound uses
its true-core primary lower bound and the actual sorted D circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveANegativeTD
open Candidate Secondary PositiveAngularEnvelope

/-- The gain (6), written over its positive cosine denominator. -/
def gain (c s a b : ℝ) : ℝ :=
  c*((a+1/2)*Real.sin s+(1/2-b)*(1-Real.cos s))/Real.cos s

theorem half_tangent_upper {s : ℝ} (hs : s∈Icc 0 frameCap) :
    Real.tan (s/2)<183/500 := by
  have hhalf : s/2∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> dsimp [frameCap] at hs <;> linarith [hs.1,hs.2,Real.pi_gt_three]
  have hend : (7/20:ℝ)∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_gt_three]
  have hm := Real.strictMonoOn_tan.monotoneOn hhalf hend
    (show s/2≤(7/20:ℝ) by dsimp [frameCap] at hs; linarith [hs.2])
  have hc := Real.cos_pos_of_mem_Ioo hend
  have ht : Real.tan (7/20:ℝ)<183/500 := by
    rw [Real.tan_eq_sin_div_cos,div_lt_iff₀ hc]
    have hsin := sin_upper_five (x:=(7/20:ℝ)) (by norm_num)
    have hcos := cos_lower_six (x:=(7/20:ℝ)) (by norm_num)
    norm_num at hsin hcos ⊢
    linarith
  exact hm.trans_lt ht

theorem one_sub_cos_upper {s : ℝ} (hs : s∈Icc 0 frameCap) :
    1-Real.cos s≤(183/500)*Real.sin s := by
  have hhalf := TwoPositive.ASupport.half_trig hs
  have ht := half_tangent_upper hs
  rw [Real.tan_eq_sin_div_cos,div_lt_iff₀ hhalf.2] at ht
  have hh := TwoPositive.ASupport.double_angle s
  have hm := mul_le_mul_of_nonneg_left ht.le
    (show 0≤2*Real.sin (s/2) by linarith [hhalf.1])
  nlinarith only [hh.1,hh.2,hm]

theorem sine_ge_angle_cos {s : ℝ} (hs : s∈Icc 0 frameCap) :
    s*Real.cos s≤Real.sin s := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => Real.sin x-x*Real.cos x) (x*Real.sin x) x := by
    have h : HasDerivAt (fun x : ℝ => Real.sin x-x*Real.cos x)
        (Real.cos x-(1*Real.cos x+x*(-Real.sin x))) x :=
      (Real.hasDerivAt_sin x).sub ((hasDerivAt_id' x).mul (Real.hasDerivAt_cos x))
    exact h.congr_deriv (by ring)
  have hm : MonotoneOn (fun x : ℝ => Real.sin x-x*Real.cos x) (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => hd x
    · intro x hx
      have hsin := (transport_trig (Ioo_subset_Icc_self hx)).2.2.1
      exact mul_nonneg hx.1.le hsin
  have hh := hm (by norm_num [frameCap]) hs hs.1
  norm_num at hh
  linarith

theorem gain_lower {c s a b : ℝ} (hc : 0≤c) (hs : s∈Icc 0 frameCap)
    (ha : 447/800≤a) (hb : b≤9/10) :
    (9/10)*c*s≤gain c s a b := by
  have ht := transport_trig hs
  have hcos : 0<Real.cos s := by linarith [ht.1]
  have ha' := mul_le_mul_of_nonneg_right ha ht.2.2.1
  have hb' := mul_le_mul_of_nonneg_right hb
    (sub_nonneg.mpr (Real.cos_le_one s))
  have hhalf := one_sub_cos_upper hs
  have htan := sine_ge_angle_cos hs
  have hnum : (9/10)*s*Real.cos s≤
      (a+1/2)*Real.sin s+(1/2-b)*(1-Real.cos s) := by
    have hzero := ht.2.2.1
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hnum hc
  rw [gain,le_div_iff₀ hcos]
  nlinarith only [hm]

theorem actual_gain_lower {q c s : ℝ} {T D : SignedPoint}
    (hT : T.Sorted) (hcore : T.AvoidsCore) (hTc : T.Contained q)
    (hD : D.Sorted) (hy : D.y≤0) (hDc : D.Contained q)
    (hq : q≤qCap) (hc : 0≤c) (hs : s∈Icc 0 frameCap) :
    (9/10)*c*s≤gain c s T.a (-D.y) := by
  have hTbound := SignedPoint.coordinate_bounds hT hcore hTc hq
  have hDbound := actual_coordinate_bounds (P:=D.reflect)
    (by simpa using hD) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hy)
    (by simpa using hDc) hq
  apply gain_lower hc hs hTbound.1.le
  have hh := hDbound.2.1
  dsimp [SignedPoint.reflect] at hh
  linarith [diagonal_bounds.2]

end SquaresInCircles.Eight.GlobalGA.PositiveANegativeTD
